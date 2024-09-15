
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

## About Analyzable

The contracts in this project are developed by Analyzable, led by Benjamin Gallois. Our mission is to deliver robust, secure, and transparent smart contract solutions for individual transactions. All code is licensed under the Apache License 2.0, ensuring open access and compliance with the specified terms. For more information or inquiries, please contact [Benjamin Gallois](mailto:benjamin@gallois.cc).

