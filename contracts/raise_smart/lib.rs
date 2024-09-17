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
///
/// The `RaiseSmart` smart contract is a straightforward implementation of a crowdfunding
/// mechanism using the ink! smart contract framework for the Polkadot/Substrate ecosystem.
///
/// This contract provides a basic structure for managing a crowdfunding campaign, allowing
/// users to contribute funds towards a specified financial goal. It includes functionalities
/// for:
///
/// - **Donations**: Users can make financial contributions to the campaign. The contract
///   tracks each contributor's contributions and updates the total amount raised.
/// - **Goal Achievement**: The contract monitors the progress towards the fundraising goal.
///   Once the goal is reached, it triggers appropriate actions, such as transferring the
///   funds to the campaign's beneficiary or terminating the contract, depending on the
///   environment (test or production).
/// - **Fund Management**: In case the campaign needs to be aborted, the contract supports
///   refunding all contributors and terminating the contract. This ensures that contributors
///   are reimbursed if the campaign does not proceed as planned.
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
mod raise_smart {
    use ink::storage::Mapping;
    use ink_prelude::vec::Vec;

    #[cfg_attr(feature = "std", derive(ink::storage::traits::StorageLayout))]
    #[ink::scale_derive(Encode, Decode, TypeInfo)]
    #[derive(Debug, PartialEq)]
    pub enum Error {
        NotAuthorized,
    }

    pub type Result<T> = core::result::Result<T, Error>;

    #[ink(event)]
    pub struct Donated {
        from: AccountId,
        amount: Balance,
    }

    #[ink(storage)]
    pub struct RaiseSmart {
        /// All the contributors.
        contributors: Vec<AccountId>,
        /// All the contributions.
        contributions: Mapping<AccountId, Balance>,
        /// The pot amount.
        amount: Balance,
        /// The funding objective.
        objective: Balance,
        /// The funding beneficiary.
        beneficiary: AccountId,
    }

    impl RaiseSmart {
        #[ink(constructor)]
        pub fn new(beneficiary: AccountId, objective: Balance) -> Self {
            Self {
                contributions: Mapping::default(),
                contributors: Vec::default(),
                amount: 0,
                objective,
                beneficiary,
            }
        }

        /// Aborts the crowdfunding campaign and refunds all contributors.
        ///
        /// This function can only be called by the beneficiary of the crowdfunding campaign.
        ///
        #[ink(message)]
        pub fn abort(&mut self) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.beneficiary {
                return Err(Error::NotAuthorized);
            }

            for contributor in &self.contributors {
                if let Some(contribution) = self.contributions.get(contributor) {
                    let _ = self.env().transfer(*contributor, contribution);
                }
            }

            #[cfg(not(test))]
            self.env().terminate_contract(self.beneficiary);

            #[cfg(test)]
            Ok(())
        }

        /// Closes the crowdfunding campaign and transfers the funds to the beneficiary.
        ///
        /// This function can only be called by the beneficiary of the crowdfunding campaign.
        /// It performs the following actions based on whether the contract is in test mode or not:
        ///
        #[ink(message)]
        pub fn close(&mut self) -> Result<()> {
            let caller = self.env().caller();

            if caller != self.beneficiary {
                return Err(Error::NotAuthorized);
            }

            #[cfg(test)]
            let _ = self.env().transfer(self.beneficiary, self.amount);

            #[cfg(not(test))]
            self.env().terminate_contract(self.beneficiary);

            #[cfg(test)]
            Ok(())
        }

        /// Returns the current gap between the fundraising objective and the amount raised.
        ///
        #[ink(message)]
        pub fn get_gap(&mut self) -> Balance {
            self.objective.saturating_sub(self.amount)
        }

        /// Handles a donation to the crowdfunding campaign.
        ///
        /// This function allows users to donate funds to the campaign. It performs the following actions:
        ///
        #[ink(message, payable)]
        pub fn donate(&mut self) {
            let caller = self.env().caller();
            let transferred = self.env().transferred_value();

            if !self.contributors.contains(&caller) {
                self.contributors.push(caller);
                self.contributions.insert(caller, &transferred);
            } else {
                if let Some(contribution) = self.contributions.get(&caller) {
                    self.contributions
                        .insert(caller, &contribution.saturating_add(transferred));
                }
            }

            self.amount = self.amount.saturating_add(transferred);
            self.env().emit_event(Donated {
                from: caller,
                amount: transferred,
            });

            if self.objective.saturating_sub(self.amount) == 0 {
                #[cfg(test)]
                let _ = self.env().transfer(self.beneficiary, self.amount);

                #[cfg(not(test))]
                self.env().terminate_contract(self.beneficiary);
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
            let beneficiary = accounts.eve;
            let contributor_0 = accounts.bob;
            let contributor_1 = accounts.charlie;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(beneficiary, 0);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_0, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_1, 1_000);

            let objective = 100u128;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            let mut contract = RaiseSmart::new(beneficiary, objective);
            assert_eq!(contract.amount, 0);
            assert_eq!(contract.objective, 100);

            // Contribute
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            ink_env::pay_with_call!(contract.donate(), 50);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_1);
            ink_env::pay_with_call!(contract.donate(), 51);

            // Funds should be released because the objective has been reached
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(beneficiary)
                    .unwrap(),
                101
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_0)
                    .unwrap(),
                1_000 - 50
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_1)
                    .unwrap(),
                1_000 - 51
            );
        }

        #[ink::test]
        fn test_early_close() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let beneficiary = accounts.eve;
            let contributor_0 = accounts.bob;
            let contributor_1 = accounts.charlie;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(beneficiary, 0);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_0, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_1, 1_000);

            let objective = 100u128;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            let mut contract = RaiseSmart::new(beneficiary, objective);
            assert_eq!(contract.amount, 0);
            assert_eq!(contract.objective, 100);

            // Contribute
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            ink_env::pay_with_call!(contract.donate(), 1);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_1);
            ink_env::pay_with_call!(contract.donate(), 1);

            // Early close should not be possible
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            assert_eq!(contract.close(), Err(Error::NotAuthorized));

            // Early close
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(beneficiary);
            assert_eq!(contract.close(), Ok(()));

            // Funds should be released
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(beneficiary)
                    .unwrap(),
                2
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_0)
                    .unwrap(),
                1_000 - 1
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_1)
                    .unwrap(),
                1_000 - 1
            );
        }

        #[ink::test]
        fn test_abort() {
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(
                ink_env::account_id::<ink_env::DefaultEnvironment>(),
                0,
            );

            let accounts = default_accounts();
            let beneficiary = accounts.eve;
            let contributor_0 = accounts.bob;
            let contributor_1 = accounts.charlie;

            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(beneficiary, 0);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_0, 1_000);
            ink_env::test::set_account_balance::<ink_env::DefaultEnvironment>(contributor_1, 1_000);

            let objective = 100u128;

            // Initiate contract
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            let mut contract = RaiseSmart::new(beneficiary, objective);
            assert_eq!(contract.amount, 0);
            assert_eq!(contract.objective, 100);

            // Contribute
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            ink_env::pay_with_call!(contract.donate(), 50);
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_1);
            ink_env::pay_with_call!(contract.donate(), 49);

            // Abort should not be possible
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(contributor_0);
            assert_eq!(contract.abort(), Err(Error::NotAuthorized));

            // Abort
            ink_env::test::set_caller::<ink_env::DefaultEnvironment>(beneficiary);
            assert_eq!(contract.abort(), Ok(()));

            // Funds should be released
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(beneficiary)
                    .unwrap(),
                0
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_0)
                    .unwrap(),
                1_000
            );
            assert_eq!(
                ink_env::test::get_account_balance::<ink_env::DefaultEnvironment>(contributor_1)
                    .unwrap(),
                1_000
            );
        }
    }
}
