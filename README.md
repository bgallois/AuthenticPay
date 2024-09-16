
# Analyzable Smart Contract Repository

## Description

Analyzable develops smart contracts to securely handle transactions between individuals, ensuring safe and transparent transfers without the need for third-party intermediaries. The project focuses on providing secure, self-sufficient contracts that cater to individual needs, eliminating the reliance on external trust.

## Features
- **Direct Contracting**: Allows individuals to directly fund and settle transactions between a sender and a receiver without needing a third party.
- **Security-Driven**: Ensures both parties fulfill their obligations through a security deposit mechanism.
- **Self-Termination**: The contract can automatically terminate itself after the transaction is completed, returning unused funds to the respective parties.
- **Funded Transactions**: Allows both sender and receiver to fund the transaction, with the contract settling payments accordingly.

## Contracts

### PackaPay

#### Description
The `PackaPay` contract allows for secure transactions between a sender (who sends a package) and a receiver (who pays for the package). The contract ensures that both parties are held accountable by requiring a security deposit, and only when the conditions are met (such as package arrival), the funds are transferred.

#### Key Features:
- **Initiate Contract**: The contract is initiated by specifying a receiver and an amount for the transaction.
- **Fund**: Both sender and receiver must fund their due amounts before the contract can proceed.
- **Sign**: The sender provides a secret code to finalize their part of the contract.
- **Settle**: The receiver can settle the contract by verifying the secret code, completing the transaction.
- **Break**: Either party can break the contract if conditions are met, refunding both parties.

### RaiseSmart

#### Description
The `RaiseSmart` contract facilitates a crowdfunding campaign by managing contributions from backers and distributing funds to a designated beneficiary once the campaign goal is met. The contract ensures transparency and accountability by tracking individual contributions and enforcing campaign objectives. It also provides mechanisms for both completing the campaign successfully and handling situations where the campaign needs to be aborted.

#### Key Features:
- **Initiate Campaign**: The contract is initialized with a specified fundraising objective and beneficiary. This sets the goal and the recipient of the funds once the campaign is successful.
- **Donate**: Contributors can make financial contributions towards the campaign goal. The contract records each contributor’s donation and updates the total amount raised.
- **Close**: Once the campaign goal is reached, the contract handles the finalization of the campaign by either transferring the funds to the beneficiary (in production) or transferring the funds for testing purposes (in test mode).
- **Abort**: The beneficiary can abort the campaign if necessary. The contract refunds all contributors and terminates itself, ensuring that funds are returned if the campaign does not proceed as planned.
- **Get Gap**: Provides a method to check the current gap between the amount raised and the fundraising goal, helping to track progress and motivate further contributions.

## About Analyzable

The contracts in this project are developed by Analyzable, led by Benjamin Gallois. Our mission is to deliver robust, secure, and transparent smart contract solutions for individual transactions. All code is licensed under the Apache License 2.0, ensuring open access and compliance with the specified terms. For more information or inquiries, please contact [Benjamin Gallois](mailto:benjamin@gallois.cc).

