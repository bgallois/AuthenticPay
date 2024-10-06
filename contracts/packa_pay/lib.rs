#![cfg_attr(not(feature = "std"), no_std, no_main)]
use core::ops::Mul;
///
/// This smart contract is developed by Benjamin Gallois (benjamin@gallois.cc).
///
/// Licensed under the Apache License, Version 2.0 (the "License");
/// you may not use this file except in compliance with the License.
/// You may obtain a copy of the License at
///
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
///
/// Unless required by applicable law or agreed to in writing, software
/// distributed under the License is distributed on an "AS IS" BASIS,
/// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
/// See the License for the specific language governing permissions and
/// limitations under the License.
use ink_prelude::string::String;
use sp_arithmetic::per_things::Perquintill;

#[ink::contract]
mod packa_pay {
    use super::*;

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    #[derive(Debug, PartialEq)]
    pub enum Status {
        /// Contract is initiated and waiting for funding.
        Initiated,
        /// Contract is signed and awaiting settlement.
        Signed,
    }

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    #[derive(Debug, PartialEq)]
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
        /// The security amount.
        security_amount: Balance,
        /// The transaction amount.
        amount: Balance,
    }

    impl PackaPay {
        #[ink(constructor)]
        pub fn new(receiver: AccountId, amount: Balance) -> Self {
            let caller = Self::env().caller();
            assert!(caller != receiver);
            let security_amount = Perquintill::from_percent(20).mul(amount);
            Self {
                sender: caller,
                sender_due_amount: security_amount,
                receiver,
                receiver_due_amount: amount.saturating_add(security_amount),
                status: Status::Initiated,
                code: None,
                security_amount,
                amount,
            }
        }

        /// Breaks the contract if certain conditions are met.
        ///
        /// This function can only be called by either the `sender` or the `receiver`
        /// involved in the contract. If the caller is not one of these, an error is returned.
        ///
        /// Additionally, the contract can only be broken if the current `status` of the
        /// contract is `Initiated`. If the contract has already progressed to a later stage,
        /// an error is returned.
        ///
        /// On successful execution, the following occurs:
        /// 1. The `sender` is refunded any remaining security amount that has not been
        ///    deducted by their due amount.
        /// 2. The `receiver` is refunded the security amount plus the full contract
        ///    amount minus any deductions from their due amount.
        /// 3. The contract is terminated, returning any remaining balance to the `sender`
        ///    if the execution is not in a test environment.
        ///
        #[ink(message)]
        pub fn r#break(&mut self) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.receiver && caller != self.sender {
                return Err(Error::NotAuthorized);
            }

            if self.status != Status::Initiated {
                return Err(Error::NotAuthorized);
            }

            let sender_amount = self.security_amount.saturating_sub(self.sender_due_amount);
            let receiver_amount = self
                .security_amount
                .saturating_add(self.amount)
                .saturating_sub(self.receiver_due_amount);

            self.env()
                .transfer(self.sender, sender_amount)
                .map_err(|_| Error::InvalidTransaction)?;

            self.env()
                .transfer(self.receiver, receiver_amount)
                .map_err(|_| Error::InvalidTransaction)?;

            #[cfg(not(test))]
            self.env().terminate_contract(self.sender);
            #[cfg(test)]
            Ok(())
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
                        .transfer(
                            self.sender,
                            self.security_amount.saturating_add(self.amount),
                        )
                        .map_err(|_| Error::InvalidTransaction)?;
                    self.env()
                        .transfer(self.receiver, self.security_amount)
                        .map_err(|_| Error::InvalidTransaction)?;

                    #[cfg(not(test))]
                    self.env().terminate_contract(self.sender);

                    #[cfg(test)]
                    Ok(())
                } else {
                    Err(Error::InvalidCode)
                }
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
        pub fn get_due_amount(&self) -> Option<Balance> {
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
            self.status = Status::Signed;

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
                if transferred > self.receiver_due_amount {
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
    #[cfg(test)]
    mod tests {
        use super::*;

        fn default_accounts() -> ink::env::test::DefaultAccounts<ink::env::DefaultEnvironment> {
            ink::env::test::default_accounts::<Environment>()
        }

        #[ink::test]
        fn test_successful() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            let amount = 100u128;
            let security_amount = Perquintill::from_percent(20).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = PackaPay::new(receiver, amount);
            assert_eq!(contract.sender, sender);
            assert_eq!(contract.receiver, receiver);
            assert_eq!(contract.status, Status::Initiated);
            assert_eq!(contract.security_amount, security_amount);
            assert_eq!(contract.amount, amount);
            assert!(contract.code.is_none());
            assert_eq!(contract.sender_due_amount, security_amount);
            assert_eq!(contract.receiver_due_amount, amount + security_amount);

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount),
                Ok(())
            );

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount + amount),
                Ok(())
            );
            assert_eq!(
                ink_env::balance::<ink_env::DefaultEnvironment>(),
                amount + 2 * security_amount
            );

            // Sign contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.sign("TEST".to_string()), Ok(()));
            assert_eq!(contract.status, Status::Signed);

            // Settle contract
            let sender_balance =
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap();
            let receiver_balance =
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap();
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.settle("TEST".to_string()), Ok(()));
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                sender_balance + security_amount + amount
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap(),
                receiver_balance + security_amount
            );
        }

        #[ink::test]
        #[should_panic]
        fn test_origin_constructor() {
            let accounts = default_accounts();
            let sender = accounts.eve;

            let amount = 100u128;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let _ = PackaPay::new(sender, amount);
        }

        #[ink::test]
        fn test_origin() {
            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;
            let alice = accounts.alice;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            let amount = 100u128;
            let security_amount = Perquintill::from_percent(20).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = PackaPay::new(receiver, amount);
            assert_eq!(contract.sender, sender);
            assert_eq!(contract.receiver, receiver);

            // Nobody should be able to fund the contract except receiver and sender
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount),
                Err(Error::PaymentNotAuthorized)
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount),
                Ok(())
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount + amount),
                Ok(())
            );

            // Nobody should be able to break contract except sender
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.r#break(), Err(Error::NotAuthorized));

            // Nobody should be able to sign contract except sender
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.sign("TEST".to_string()), Err(Error::NotAuthorized));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.sign("TEST".to_string()), Err(Error::NotAuthorized));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.sign("TEST".to_string()), Ok(()));

            // Nobody should be able to break signed contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.r#break(), Err(Error::NotAuthorized));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.r#break(), Err(Error::NotAuthorized));

            // Nobody shoudle be able to settle contract except receiver
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(
                contract.settle("TEST".to_string()),
                Err(Error::NotAuthorized)
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                contract.settle("TEST".to_string()),
                Err(Error::NotAuthorized)
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.settle("TEST".to_string()), Ok(()));
        }

        #[ink::test]
        fn test_funding() {
            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 100_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 100_000);

            let amount = 100u128;
            let security_amount = Perquintill::from_percent(20).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = PackaPay::new(receiver, amount);
            assert_eq!(contract.sender, sender);
            assert_eq!(contract.receiver, receiver);

            // Fail if too many
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount * 10),
                Err(Error::PaymentTooLarge)
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), amount * 10),
                Err(Error::PaymentTooLarge)
            );

            // Fund by parts
            for _ in 0..10 {
                ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
                assert_eq!(contract.sign("TEST".to_string()), Err(Error::FundingNotMet));
                ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
                assert_eq!(
                    ink_env::pay_with_call!(contract.fund(), security_amount / 10),
                    Ok(())
                );
                ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
                assert_eq!(
                    ink_env::pay_with_call!(contract.fund(), (security_amount + amount) / 10),
                    Ok(())
                );
            }
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.sign("TEST".to_string()), Ok(()));
        }

        #[ink::test]
        fn test_breaking() {
            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 100_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 100_000);

            let amount = 100u128;
            let security_amount = Perquintill::from_percent(20).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = PackaPay::new(receiver, amount);
            assert_eq!(contract.sender, sender);
            assert_eq!(contract.receiver, receiver);

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount),
                Ok(())
            );

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount + amount),
                Ok(())
            );

            // Break contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.r#break(), Ok(()));
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                100_000
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap(),
                100_000
            );

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = PackaPay::new(receiver, amount);
            assert_eq!(contract.sender, sender);
            assert_eq!(contract.receiver, receiver);

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount),
                Ok(())
            );

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(
                ink_env::pay_with_call!(contract.fund(), security_amount + amount),
                Ok(())
            );

            // Break contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.r#break(), Ok(()));
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                100_000
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap(),
                100_000
            );
        }
    }
}
