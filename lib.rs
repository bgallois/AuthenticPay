#![cfg_attr(not(feature = "std"), no_std, no_main)]
///
/// This smart contract is developed by Benjamin Gallois (benjamin@gallois.cc).
///
/// Licensed under the Apache License, Version 2.0 (the "License");
/// you may not use this file except in compliance with the License.
/// You may obtain a copy of the License at
///
///     http://www.apache.org/licenses/LICENSE-2.0
///
/// Unless required by applicable law or agreed to in writing, software
/// distributed under the License is distributed on an "AS IS" BASIS,
/// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
/// See the License for the specific language governing permissions and
/// limitations under the License.
///
/// # Description
/// This smart contract, `PackaPay`, is a simple example contract implementing functionalities
/// such as funding and settling transactions between a sender and a receiver.
///
/// # License
/// Apache License 2.0
///
/// Licensed under the Apache License, Version 2.0 (the "License");
/// you may not use this file except in compliance with the License.
/// You may obtain a copy of the License at
///
///     http://www.apache.org/licenses/LICENSE-2.0
///
/// Unless required by applicable law or agreed to in writing, software
/// distributed under the License is distributed on an "AS IS" BASIS,
/// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
/// See the License for the specific language governing permissions and
/// limitations under the License.
use ink_prelude::string::String;
use sp_arithmetic::per_things::Perquintill;
use core::ops::Mul;

#[ink::contract]
mod packa_pay {
    use super::*;

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    pub enum Status {
        Initiated,
        Funded,
    }

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    pub enum Error {
        PaymentTooLarge,
        PaymentNotAuthorized,
        NotAuthorized,
        FundingNotMet,
        InvalidCode,
        InvalidTransaction,
    }

    pub type Result<T> = core::result::Result<T, Error>;

    #[ink(event)]
    pub struct Funded {
        from: AccountId,
        value: Balance,
    }

    #[ink(event)]
    pub struct Signed {
        from: AccountId,
        to: AccountId,
    }

    /// `PackaPay` represents the state of a payment transaction between a sender and a receiver.
    /// It stores the details of the involved parties, the amounts due, transaction status, and the security code.
    #[ink(storage)]
    pub struct PackaPay {
        /// The account ID of the sender, who is intended to receive the payment and sends the package.
        sender: AccountId,
        /// The account ID of the receiver, who is intended to receive the pacakge and sends the payment.
        receiver: AccountId,
        /// The amount that the sender still owes before the contract can be started.
        sender_due_amount: Balance,
        /// The amount that the receiver still owes before the contract can be started.
        receiver_due_amount: Balance,
        /// The current status of the payment transaction.
        status: Status,
        /// The security code that the sender will ship with the package.
        code: Option<Hash>,
        security_amount: Balance,
    }

    impl PackaPay {
        #[ink(constructor)]
        pub fn new(receiver: AccountId, amount: Balance) -> Self {
            let caller = Self::env().caller();
            let security_amount = Perquintill::from_percent(20).mul(amount);
            Self {
                sender: caller,
                sender_due_amount: amount.saturating_add(security_amount),
                receiver,
                receiver_due_amount: amount,
                status: Status::Initiated,
                code: None,
                security_amount,
            }
        }

        /// Finalizes the contract process based on the verification code provided by the receiver.
        ///
        /// # Parameters:
        /// - `code`: A `String` that represents the verification code required to settle the transaction.
        ///
        /// # Returns:
        /// - `Ok(())`: If the code verification is successful, and the transfer and termination are completed.
        /// - `Err(Error::NotAuthorized)`: If the caller is not the receiver.
        /// - `Err(Error::InvalidCode)`: If the provided code does not match the stored hash. (Ensure that this error variant exists in your `Error` enum if you use it.)
        #[ink(message)]
        pub fn settle(&mut self, code: String) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.receiver {
                return Err(Error::NotAuthorized);
            }

            let mut message_hash: [u8; 32] = [0; 32];
            ink_env::hash_bytes::<ink_env::hash::Keccak256>(code.as_bytes(), &mut message_hash);
            let hash: Hash = message_hash.into();
            if let Some(stored_hash) = self.code {
                if stored_hash == hash {
                    self.env()
                        .transfer(self.env().caller(), self.security_amount)
                        .map_err(|_| Error::InvalidTransaction)?;
                    self.env().terminate_contract(self.sender);
                }
                Ok(())
            } else {
                Err(Error::InvalidCode)
            }
        }

        /// Returns the due amount for the caller (either the sender or receiver).
        ///
        /// # Returns:
        /// - `Some(Balance)`: If the caller is the `sender`, it returns the `sender_due_amount`.
        /// - If the caller is the `receiver`, it returns the `receiver_due_amount`.
        /// - `None`: If the caller is neither the `sender` nor the `receiver`, no amount is returned.
        #[ink(message)]
        pub fn get_due_amount(&mut self) -> Option<Balance> {
            let caller = self.env().caller();
            if caller == self.sender {
                Some(self.sender_due_amount)
            } else if caller == self.receiver {
                Some(self.receiver_due_amount)
            } else {
                None
            }
        }

        /// Allows the sender to sign and start the contract by providing a secret code
        /// that will be included inside the package.
        /// The contract's status is updated to `Funded` after signing, and an event is emitted.
        ///
        /// # Parameters:
        /// - `input`: A `String` input representing the secret code that the sender will physically include with the package.
        ///
        /// # Returns:
        /// - `Ok(())`: If the caller is the sender and the signing process succeeds.
        /// - `Err(Error::NotAuthorized)`: If the caller is not the sender.
        #[ink(message)]
        pub fn sign(&mut self, input: String) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.sender {
                return Err(Error::NotAuthorized);
            }

            if self.sender_due_amount != 0 || self.receiver_due_amount != 0 {
                return Err(Error::FundingNotMet);
            }

            let mut message_hash: [u8; 32] = [0; 32];
            ink_env::hash_bytes::<ink_env::hash::Keccak256>(input.as_bytes(), &mut message_hash);
            let hash: Hash = message_hash.into();
            self.code = Some(hash);
            self.status = Status::Funded;

            Self::env().emit_event(Signed {
                from: caller,
                to: self.receiver,
            });
            Ok(())
        }

        /// Allows the sender or receiver to fund their respective due amounts.
        ///
        /// The function handles payments sent by either the `sender` or `receiver` and updates their due amounts accordingly.
        /// It emits a `Funded` event each time a payment is successfully processed.
        ///
        /// # Returns:
        /// - `Ok(())`: If the payment is processed successfully and the due amount is updated.
        /// - `Err(Error::PaymentTooLarge)`: If the transferred amount is greater than the due amount for the caller.
        /// - `Err(Error::PaymentTooSmall)`: If the transferred amount is less than the due amount for the receiver.
        /// - `Err(Error::PaymentNotAuthorized)`: If the caller is neither the `sender` nor the `receiver`.
        #[ink(message, payable)]
        pub fn fund(&mut self) -> Result<()> {
            let caller = self.env().caller();
            let transferred = self.env().transferred_value();

            if caller == self.sender {
                if transferred > self.sender_due_amount {
                    Err(Error::PaymentTooLarge)
                } else {
                    self.sender_due_amount = self.sender_due_amount.saturating_sub(transferred);
                    Self::env().emit_event(Funded {
                        from: caller,
                        value: transferred,
                    });
                    Ok(())
                }
            } else if caller == self.receiver {
                if transferred < self.receiver_due_amount {
                    return Err(Error::PaymentTooLarge);
                } else {
                    self.receiver_due_amount = self.receiver_due_amount.saturating_sub(transferred);
                    Self::env().emit_event(Funded {
                        from: caller,
                        value: transferred,
                    });
                    Ok(())
                }
            } else {
                return Err(Error::PaymentNotAuthorized);
            }
        }
    }
}
