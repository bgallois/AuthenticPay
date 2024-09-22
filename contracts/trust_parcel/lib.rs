#![cfg_attr(not(feature = "std"), no_std, no_main)]
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
/// This smart contract, `TrustParcel`, is a simple example contract implementing functionalities
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

#[ink::contract]
mod trust_parcel {
    use core::ops::{Div, Mul, Sub};
    use ink::storage::Mapping;
    use ink_prelude::string::String;
    use ink_prelude::vec::Vec;
    use sp_arithmetic::per_things::Perquintill;

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
        UpgradeFailed,
        FundingNotMet,
        InvalidCode,
        InvalidTransaction,
        InvalidReceiver,
        ContractNotFound,
    }

    pub type Result<T> = core::result::Result<T, Error>;

    #[ink(event)]
    pub struct Signed {
        from: AccountId,
        to: AccountId,
    }

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    #[derive(Debug, PartialEq)]
    pub struct Contract {
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
        /// The security amount of the sender.
        sender_security_amount: Balance,
        /// The security amount of the receiver.
        receiver_security_amount: Balance,
        /// The transaction amount.
        amount: Balance,
        /// The transaction id.
        id: u128,
        /// The block of the signature.
        block: BlockNumber,
    }

    /// `TrustParcel` represents the state of a payment transaction between a sender and a receiver.
    /// It stores the details of the involved parties, the amounts due, transaction status, and the security code.
    #[ink(storage)]
    pub struct TrustParcel {
        /// All the contributors.
        contributors: Vec<AccountId>,
        /// All the balances.
        balances: Mapping<AccountId, Balance>,
        /// All the reputations.
        reputations: Mapping<AccountId, u64>,
        /// All the contracts.
        contracts: Mapping<u128, Contract>,
        /// The running contract id count.
        current_id: u128,
        /// The unclaimed fund.
        treasury: Balance,
        /// The root account.
        root: AccountId,
    }
    impl Default for TrustParcel {
        fn default() -> Self {
            Self::new()
        }
    }

    impl TrustParcel {
        #[ink(constructor)]
        pub fn new() -> Self {
            Self {
                contributors: Vec::default(),
                balances: Mapping::default(),
                reputations: Mapping::default(),
                contracts: Mapping::default(),
                current_id: 0u128,
                treasury: 0u128,
                root: Self::env().caller(),
            }
        }

        /// Allows an account to fund its TrustParcel account and updates their balance.
        #[ink(message, payable)]
        pub fn fund_account(&mut self) {
            let caller = self.env().caller();
            let transferred = self.env().transferred_value();

            if !self.contributors.contains(&caller) {
                self.contributors.push(caller);
                self.balances.insert(caller, &transferred);
            } else if let Some(balance) = self.balances.get(caller) {
                self.balances
                    .insert(caller, &balance.saturating_add(transferred));
            }
        }

        /// Allows an account to defund its TrustParcel account by withdrawing their balance.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the defunding is successful, or an error if it fails.
        #[ink(message)]
        pub fn defund_account(&mut self) -> Result<()> {
            let caller = self.env().caller();

            if !self.contributors.contains(&caller) {
                return Err(Error::NotAuthorized);
            }

            let balance = self.balances.get(caller).unwrap_or(0);
            self.balances.insert(caller, &0);
            self.env()
                .transfer(caller, balance)
                .map_err(|_| Error::InvalidTransaction)
        }

        /// Retrieves the balance of the caller.
        ///
        /// # Returns
        /// - `Option<Balance>`: Returns the caller's balance if it exists, or `None` if the caller has no balance.
        #[ink(message)]
        pub fn get_balance(&mut self) -> Option<Balance> {
            let caller = self.env().caller();
            self.balances.get(caller)
        }

        /// Retrieves the reputation score of a specified account.
        ///
        /// # Arguments
        /// - `account`: The `AccountId` of the account whose reputation score is to be retrieved.
        ///
        /// # Returns
        /// - `Option<u64>`: Returns the reputation score if it exists, or `None` if the account has no reputation score.
        #[ink(message)]
        pub fn get_reputation(&mut self, account: AccountId) -> Option<u64> {
            self.reputations.get(account)
        }

        /// Initiates a contract between the caller and a specified receiver.
        ///
        /// # Arguments
        /// - `receiver`: The `AccountId` of the account that will receive the funds.
        /// - `amount`: The package value in tokens.
        ///
        /// # Returns
        /// - `Result<u128>`: Returns the ID of the initiated contract if successful, or an error if it fails.
        #[ink(message)]
        pub fn initiate_contract(&mut self, receiver: AccountId, amount: Balance) -> Result<u128> {
            let caller = self.env().caller();
            if caller == receiver {
                return Err(Error::InvalidReceiver);
            }

            let sender_reputation = self.reputations.get(caller).unwrap_or(0);
            let sender_security_amount = Perquintill::from_percent(25)
                .sub(
                    Perquintill::from_percent(20)
                        .div(Perquintill::from_percent(100))
                        .mul(Perquintill::from_percent(sender_reputation)),
                )
                .mul(amount);

            let receiver_reputation = self.reputations.get(receiver).unwrap_or(0);
            let receiver_security_amount = Perquintill::from_percent(25)
                .sub(
                    Perquintill::from_percent(20)
                        .div(Perquintill::from_percent(100))
                        .mul(Perquintill::from_percent(receiver_reputation)),
                )
                .mul(amount);

            self.current_id = self.current_id.saturating_add(1);

            let contract = Contract {
                sender: caller,
                sender_due_amount: sender_security_amount,
                receiver,
                receiver_due_amount: amount.saturating_add(receiver_security_amount),
                status: Status::Initiated,
                code: None,
                sender_security_amount,
                receiver_security_amount,
                amount,
                id: self.current_id,
                block: self.env().block_number(),
            };

            self.contracts.insert(contract.id, &contract);
            Ok(contract.id)
        }

        /// Retrieves a contract by its ID.
        ///
        /// # Arguments
        /// - `id`: The unique identifier of the contract to be retrieved.
        ///
        /// # Returns
        /// - `Option<Contract>`: Returns the `Contract` if it exists, or `None` if no contract with the given ID is found.
        #[ink(message)]
        pub fn get_contract(&mut self, id: u128) -> Option<Contract> {
            self.contracts.get(id)
        }

        /// Retrieves all contracts associated with a specified sender and receiver.
        ///
        /// # Arguments
        /// - `sender`: The `AccountId` of the sender whose contracts are to be retrieved.
        /// - `receiver`: The `AccountId` of the receiver whose contracts are to be retrieved.
        ///
        /// # Returns
        /// - `Vec<Contract>`: A vector of `Contract` instances matching the specified sender and receiver.
        #[ink(message)]
        pub fn get_contracts(&mut self, sender: AccountId, receiver: AccountId) -> Vec<Contract> {
            let mut contracts = Vec::default();
            for i in 0..self.current_id {
                if let Some(contract) = self.contracts.get(i) {
                    if contract.sender == sender && contract.receiver == receiver {
                        contracts.push(contract);
                    }
                }
            }
            contracts
        }

        /// Funds a specified contract by allowing the caller to contribute to it.
        ///
        /// # Arguments
        /// - `contract_id`: The unique identifier of the contract to be funded.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the funding is successful, or an error if it fails.
        #[ink(message)]
        pub fn fund_contract(&mut self, contract_id: u128) -> Result<()> {
            let mut contract = self
                .contracts
                .get(contract_id)
                .ok_or(Error::ContractNotFound)?;

            let caller = self.env().caller();

            let balance = self.balances.get(caller).unwrap_or(0);
            if caller == contract.sender {
                let new_balance = balance.saturating_sub(contract.sender_due_amount);
                contract.sender_due_amount = contract.sender_due_amount.saturating_sub(balance);
                self.balances.insert(caller, &new_balance);
            } else if caller == contract.receiver {
                let new_balance = balance.saturating_sub(contract.receiver_due_amount);
                contract.receiver_due_amount = contract.receiver_due_amount.saturating_sub(balance);
                self.balances.insert(caller, &new_balance);
            } else {
                return Err(Error::NotAuthorized);
            }
            self.contracts.insert(contract_id, &contract);
            Ok(())
        }

        /// Signs a specified contract with a secret code.
        ///
        /// # Arguments
        /// - `contract_id`: The unique identifier of the contract to be signed.
        /// - `input`: A `String` representing the message to be hashed and signed.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the signing is successful, or an error if it fails.
        #[ink(message)]
        pub fn sign_contract(&mut self, contract_id: u128, input: String) -> Result<()> {
            let mut contract = self
                .contracts
                .get(contract_id)
                .ok_or(Error::ContractNotFound)?;

            let caller = self.env().caller();
            if caller != contract.sender {
                return Err(Error::NotAuthorized);
            }

            if contract.sender_due_amount != 0 || contract.receiver_due_amount != 0 {
                return Err(Error::FundingNotMet);
            }

            let mut message_hash: [u8; 32] = [0; 32];
            ink_env::hash_bytes::<ink_env::hash::Keccak256>(input.as_bytes(), &mut message_hash);
            let hash: Hash = message_hash.into();
            contract.code = Some(hash);
            contract.status = Status::Signed;

            Self::env().emit_event(Signed {
                from: caller,
                to: contract.receiver,
            });
            self.contracts.insert(contract_id, &contract);
            Ok(())
        }

        /// Settles a specified contract by validating a secret code.
        ///
        /// # Arguments
        /// - `contract_id`: The unique identifier of the contract to be settled.
        /// - `code`: A `String` representing the code to be validated against the contract's hash.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the settlement is successful, or an error if it fails.
        #[ink(message)]
        pub fn settle_contract(&mut self, contract_id: u128, code: String) -> Result<()> {
            let contract = self
                .contracts
                .get(contract_id)
                .ok_or(Error::ContractNotFound)?;

            let caller = self.env().caller();
            if caller != contract.receiver {
                return Err(Error::NotAuthorized);
            }

            let mut message_hash: [u8; 32] = [0; 32];
            ink_env::hash_bytes::<ink_env::hash::Keccak256>(code.as_bytes(), &mut message_hash);
            let hash: Hash = message_hash.into();
            if let Some(stored_hash) = contract.code {
                if stored_hash == hash {
                    let new_sender_balance = self
                        .balances
                        .get(contract.sender)
                        .unwrap_or(0u128)
                        .saturating_add(contract.sender_security_amount)
                        .saturating_add(contract.amount);
                    let new_receiver_balance = self
                        .balances
                        .get(contract.receiver)
                        .unwrap_or(0u128)
                        .saturating_add(contract.receiver_security_amount);

                    self.balances.insert(contract.sender, &new_sender_balance);
                    self.balances
                        .insert(contract.receiver, &new_receiver_balance);

                    let sender_reputation = self
                        .reputations
                        .get(contract.sender)
                        .unwrap_or(50)
                        .saturating_add(1);
                    let receiver_reputation = self
                        .reputations
                        .get(contract.receiver)
                        .unwrap_or(50)
                        .saturating_add(1);

                    self.reputations.insert(contract.sender, &sender_reputation);
                    self.reputations
                        .insert(contract.receiver, &receiver_reputation);

                    self.contracts.remove(contract_id);

                    Ok(())
                } else {
                    Err(Error::InvalidCode)
                }
            } else {
                Err(Error::InvalidCode)
            }
        }

        /// Aborts a specified contract, returning the funds to the sender and receiver.
        ///
        /// # Arguments
        /// - `contract_id`: The unique identifier of the contract to be aborted.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the abortion is successful, or an error if it fails.
        #[ink(message)]
        pub fn abort_contract(&mut self, contract_id: u128) -> Result<()> {
            let contract = self
                .contracts
                .get(contract_id)
                .ok_or(Error::ContractNotFound)?;

            let caller = self.env().caller();

            if caller != contract.receiver && caller != contract.sender {
                return Err(Error::NotAuthorized);
            }

            if contract.status != Status::Initiated {
                return Err(Error::NotAuthorized);
            }

            let new_sender_balance = self
                .balances
                .get(contract.sender)
                .unwrap_or(0u128)
                .saturating_add(
                    contract
                        .sender_security_amount
                        .saturating_sub(contract.sender_due_amount),
                );
            let new_receiver_balance = self
                .balances
                .get(contract.receiver)
                .unwrap_or(0u128)
                .saturating_add(
                    contract
                        .receiver_security_amount
                        .saturating_add(contract.amount)
                        .saturating_sub(contract.receiver_due_amount),
                );

            let sender_reputation = self
                .reputations
                .get(contract.sender)
                .unwrap_or(50)
                .saturating_sub(1);
            let receiver_reputation = self
                .reputations
                .get(contract.receiver)
                .unwrap_or(50)
                .saturating_sub(1);

            self.reputations.insert(contract.sender, &sender_reputation);
            self.reputations
                .insert(contract.receiver, &receiver_reputation);

            self.balances.insert(contract.sender, &new_sender_balance);
            self.balances
                .insert(contract.receiver, &new_receiver_balance);
            self.contracts.remove(contract_id);
            Ok(())
        }

        /// Denounces a specified contract, reducing the reputations of both parties and transferring funds to the treasury.
        ///
        /// # Arguments
        /// - `contract_id`: The unique identifier of the contract to be denounced.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the denouncement is successful, or an error if it fails.
        #[ink(message)]
        pub fn denonce_contract(&mut self, contract_id: u128) -> Result<()> {
            let contract = self
                .contracts
                .get(contract_id)
                .ok_or(Error::ContractNotFound)?;

            let caller = self.env().caller();

            if caller != contract.receiver && caller != contract.sender {
                return Err(Error::NotAuthorized);
            }

            if contract.status != Status::Signed {
                return Err(Error::NotAuthorized);
            }

            let sender_reputation = self
                .reputations
                .get(contract.sender)
                .unwrap_or(0)
                .saturating_sub(1);
            let receiver_reputation = self
                .reputations
                .get(contract.receiver)
                .unwrap_or(0)
                .saturating_sub(1);

            self.reputations.insert(contract.sender, &sender_reputation);
            self.reputations
                .insert(contract.receiver, &receiver_reputation);

            self.treasury = self
                .treasury
                .saturating_add(contract.amount)
                .saturating_add(contract.sender_security_amount)
                .saturating_add(contract.sender_security_amount);

            self.contracts.remove(contract_id);
            Ok(())
        }

        /// Upgrades the contract to a new code version.
        ///
        /// # Arguments
        /// - `code_hash`: The `Hash` of the new code to be set for the contract.
        ///
        /// # Returns
        /// - `Result<()>`: Returns `Ok(())` if the upgrade is successful, or an error if it fails.
        #[ink(message)]
        pub fn upgrade(&mut self, code_hash: Hash) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.root {
                return Err(Error::NotAuthorized);
            }

            self.env()
                .set_code_hash(&code_hash)
                .map_err(|_| Error::UpgradeFailed)?;

            Ok(())
        }

        #[ink(message)]
        pub fn clean(&mut self) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.root {
                return Err(Error::NotAuthorized);
            }

            for contract_id in 0..self.current_id {
                if let Some(contract) = self.contracts.get(contract_id) {
                    if 2_628_000u32.saturating_sub(contract.block) == 0 {
                        let sender_reputation = self
                            .reputations
                            .get(contract.sender)
                            .unwrap_or(0)
                            .saturating_sub(1);
                        let receiver_reputation = self
                            .reputations
                            .get(contract.receiver)
                            .unwrap_or(0)
                            .saturating_sub(1);

                        self.reputations.insert(contract.sender, &sender_reputation);
                        self.reputations
                            .insert(contract.receiver, &receiver_reputation);

                        self.treasury = self
                            .treasury
                            .saturating_add(contract.amount)
                            .saturating_add(contract.sender_security_amount)
                            .saturating_add(contract.sender_security_amount);

                        self.contracts.remove(contract_id);
                    }
                }
            }
            Ok(())
        }

        #[ink(message)]
        pub fn spend_treasury(&mut self, beneficiary: AccountId, amount: Balance) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.root {
                return Err(Error::NotAuthorized);
            }

            self.env()
                .transfer(beneficiary, amount)
                .map_err(|_| Error::InvalidTransaction)?;

            self.treasury = self.treasury.saturating_sub(amount);

            Ok(())
        }
    }
    #[cfg(test)]
    mod tests {
        use super::*;

        fn default_accounts() -> ink::env::test::DefaultAccounts<ink::env::DefaultEnvironment> {
            ink::env::test::default_accounts::<Environment>()
        }

        #[ink::test]
        fn test_treasury_and_root() {
            let accounts = default_accounts();
            let root = accounts.eve;
            let alice = accounts.alice;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(root);
            let mut contract = TrustParcel::new();

            // Assert root
            assert_eq!(contract.root, root);

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.upgrade(Hash::default()), Err(Error::NotAuthorized));
            assert_eq!(contract.clean(), Err(Error::NotAuthorized));
            assert_eq!(
                contract.spend_treasury(alice, 100),
                Err(Error::NotAuthorized)
            );

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(root);
            assert_eq!(contract.clean(), Ok(()));
            assert_eq!(contract.spend_treasury(alice, 100), Ok(()));
        }

        #[ink::test]
        fn test_fund_account() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;
            let alice = accounts.alice;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = TrustParcel::new();

            // Add fund
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            ink_env::pay_with_call!(contract.fund_account(), 500);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            ink_env::pay_with_call!(contract.fund_account(), 600);
            assert_eq!(ink_env::balance::<ink_env::DefaultEnvironment>(), 1_100);
            assert_eq!(contract.balances.get(sender).unwrap(), 500);
            assert_eq!(contract.balances.get(receiver).unwrap(), 600);
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                500
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap(),
                400
            );

            // Defund account
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.defund_account(), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.defund_account(), Ok(()));
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                1_000
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(sender).unwrap(),
                1_000
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(receiver)
                    .unwrap(),
                1_000
            );
            assert_eq!(contract.balances.get(sender).unwrap(), 0);
            assert_eq!(contract.balances.get(receiver).unwrap(), 0);

            assert_eq!(contract.defund_account(), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.defund_account(), Err(Error::NotAuthorized));
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
            let alice = accounts.alice;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = TrustParcel::new();

            // Add fund
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);

            let amount = 100u128;
            let security_amount = Perquintill::from_percent(25).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.get_contract(1), None);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(1));
            assert_eq!(contract.get_contract(1).unwrap().sender, sender);
            assert_eq!(contract.get_contract(1).unwrap().receiver, receiver);
            assert_eq!(contract.get_contract(1).unwrap().status, Status::Initiated);
            assert!(contract.get_reputation(sender).is_none());
            assert!(contract.get_reputation(receiver).is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_security_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_security_amount,
                security_amount
            );
            assert_eq!(contract.get_contract(1).unwrap().amount, amount);
            assert!(contract.get_contract(1).unwrap().code.is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_due_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_due_amount,
                amount + security_amount
            );
            assert_eq!(contract.get_contract(1).unwrap().block, 0);

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.fund_contract(1), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.fund_contract(1), Ok(()));
            assert_eq!(
                contract.balances.get(sender).unwrap(),
                1_000 - security_amount
            );
            assert_eq!(
                contract.balances.get(receiver).unwrap(),
                1_000 - security_amount - amount
            );

            // Should be impossible to fund
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.abort_contract(1), Err(Error::NotAuthorized));

            // Should be impossible to sign
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(
                contract.sign_contract(1, "TEST".to_string()),
                Err(Error::NotAuthorized)
            );

            // Sign contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.sign_contract(1, "TEST".to_string()), Ok(()));
            assert_eq!(contract.get_contract(1).unwrap().status, Status::Signed);

            // Should be impossible to abort
            assert_eq!(contract.abort_contract(1), Err(Error::NotAuthorized));

            // Should be impossible to sign
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(
                contract.settle_contract(1, "TEST".to_string()),
                Err(Error::NotAuthorized)
            );
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(
                contract.settle_contract(1, "TEST".to_string()),
                Err(Error::NotAuthorized)
            );

            // Settle contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.settle_contract(1, "TEST".to_string()), Ok(()));
            assert_eq!(contract.balances.get(sender).unwrap(), 1_000 + amount);
            assert_eq!(contract.balances.get(receiver).unwrap(), 1_000 - amount);
            assert_eq!(contract.get_reputation(sender).unwrap(), 51);
            assert_eq!(contract.get_reputation(receiver).unwrap(), 51);
        }

        #[ink::test]
        fn test_denonce() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;
            let alice = accounts.alice;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = TrustParcel::new();

            // Add fund
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);

            let amount = 100u128;
            // With a starting reputation of 0
            let security_amount = Perquintill::from_percent(25).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.get_contract(1), None);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(1));
            assert_eq!(contract.get_contract(1).unwrap().sender, sender);
            assert_eq!(contract.get_contract(1).unwrap().receiver, receiver);
            assert_eq!(contract.get_contract(1).unwrap().status, Status::Initiated);
            assert!(contract.get_reputation(sender).is_none());
            assert!(contract.get_reputation(receiver).is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_security_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_security_amount,
                security_amount
            );
            assert_eq!(contract.get_contract(1).unwrap().amount, amount);
            assert!(contract.get_contract(1).unwrap().code.is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_due_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_due_amount,
                amount + security_amount
            );

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.fund_contract(1), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.fund_contract(1), Ok(()));
            assert_eq!(
                contract.balances.get(sender).unwrap(),
                1_000 - security_amount
            );
            assert_eq!(
                contract.balances.get(receiver).unwrap(),
                1_000 - security_amount - amount
            );

            // Denonce contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.denonce_contract(1), Err(Error::NotAuthorized));
            assert!(contract.get_contract(1).is_some());

            // Denonce contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.denonce_contract(1), Err(Error::NotAuthorized));
            assert!(contract.get_contract(1).is_some());
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.denonce_contract(1), Err(Error::NotAuthorized));
            assert!(contract.get_contract(1).is_some());

            // Sign contract
            assert_eq!(contract.sign_contract(1, "TEST".to_string()), Ok(()));

            // Denonce contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.denonce_contract(1), Ok(()));
            assert!(contract.get_contract(1).is_none());
            assert_eq!(contract.treasury, amount + 2 * security_amount);

            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(2));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.fund_contract(2), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.fund_contract(2), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.sign_contract(2, "TEST".to_string()), Ok(()));

            // Denonce contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.denonce_contract(2), Ok(()));
            assert!(contract.get_contract(2).is_none());
            assert_eq!(contract.treasury, 2 * amount + 4 * security_amount);
        }

        #[ink::test]
        fn test_abort() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;
            let alice = accounts.alice;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(sender, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(receiver, 1_000);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = TrustParcel::new();

            // Add fund
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            ink_env::pay_with_call!(contract.fund_account(), 1_000);

            let amount = 100u128;
            // With a starting reputation of 0
            let security_amount = Perquintill::from_percent(25).mul(amount);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.get_contract(1), None);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(1));
            assert_eq!(contract.get_contract(1).unwrap().sender, sender);
            assert_eq!(contract.get_contract(1).unwrap().receiver, receiver);
            assert_eq!(contract.get_contract(1).unwrap().status, Status::Initiated);
            assert!(contract.get_reputation(sender).is_none());
            assert!(contract.get_reputation(receiver).is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_security_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_security_amount,
                security_amount
            );
            assert_eq!(contract.get_contract(1).unwrap().amount, amount);
            assert!(contract.get_contract(1).unwrap().code.is_none());
            assert_eq!(
                contract.get_contract(1).unwrap().sender_due_amount,
                security_amount
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_due_amount,
                amount + security_amount
            );

            // Fund contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.fund_contract(1), Ok(()));
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.fund_contract(1), Ok(()));
            assert_eq!(
                contract.balances.get(sender).unwrap(),
                1_000 - security_amount
            );
            assert_eq!(
                contract.balances.get(receiver).unwrap(),
                1_000 - security_amount - amount
            );

            // Should be impossible to abort
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.abort_contract(1), Err(Error::NotAuthorized));

            // Abort contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.abort_contract(1), Ok(()));
            assert!(contract.get_contract(1).is_none());
            assert_eq!(contract.get_reputation(sender).unwrap(), 49);
            assert_eq!(contract.get_reputation(receiver).unwrap(), 49);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.get_contract(2), None);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(2));

            // Should be impossible to abort
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(alice);
            assert_eq!(contract.abort_contract(2), Err(Error::NotAuthorized));

            // Abort contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(receiver);
            assert_eq!(contract.abort_contract(2), Ok(()));
            assert!(contract.get_contract(2).is_none());
            assert_eq!(contract.get_reputation(sender).unwrap(), 48);
            assert_eq!(contract.get_reputation(receiver).unwrap(), 48);
        }

        #[ink::test]
        fn test_security_amount() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let sender = accounts.eve;
            let receiver = accounts.bob;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            let mut contract = TrustParcel::new();

            let amount = 100u128;

            // Set reputations
            contract.reputations.insert(sender, &0u64);
            contract.reputations.insert(receiver, &100u64);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(1));
            assert_eq!(
                contract.get_contract(1).unwrap().sender_security_amount,
                Perquintill::from_percent(25).mul(amount)
            );
            assert_eq!(
                contract.get_contract(1).unwrap().receiver_security_amount,
                Perquintill::from_percent(5).mul(amount)
            );

            // Set reputations
            contract.reputations.insert(sender, &25u64);
            contract.reputations.insert(receiver, &75u64);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(2));
            assert_eq!(
                contract.get_contract(2).unwrap().sender_security_amount,
                Perquintill::from_percent(20).mul(amount)
            );
            assert_eq!(
                contract.get_contract(2).unwrap().receiver_security_amount,
                Perquintill::from_percent(10).mul(amount)
            );

            // Set reputations
            contract.reputations.insert(sender, &45u64);
            contract.reputations.insert(receiver, &55u64);

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(sender);
            assert_eq!(contract.initiate_contract(receiver, amount), Ok(3));
            assert_eq!(
                contract.get_contract(3).unwrap().sender_security_amount,
                Perquintill::from_percent(16).mul(amount)
            );
            assert_eq!(
                contract.get_contract(3).unwrap().receiver_security_amount,
                Perquintill::from_percent(14).mul(amount)
            );
        }
    }
}
