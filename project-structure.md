# zooReals Project Structure

## Standard Agda Project Structure

Based on common conventions for Agda projects, especially those using the cubical library, here's a recommended structure:

```
zooReals/
├── README.md
├── zooReals.agda-lib
├── src/
│   ├── Reals/
│   │   ├── Dedekind/
│   │   │   ├── Basic.agda
│   │   │   ├── Properties.agda
│   │   │   └── Operations.agda
│   │   ├── Cauchy/
│   │   │   ├── Basic.agda
│   │   │   ├── Properties.agda
│   │   │   └── Operations.agda
│   │   ├── Interval/
│   │   │   └── Basic.agda
│   │   ├── Base.agda
│   │   ├── Equivalences.agda
│   │   └── Counterexamples.agda
│   └── Examples/
│       └── BasicExamples.agda
└── doc/
    └── design.md
```

## Directory Descriptions

- `src/`: Contains all Agda source files
  - `Reals/`: Main directory for real number implementations
    - `Dedekind/`: Implementation of Dedekind reals
    - `Cauchy/`: Implementation of Cauchy reals
    - `Interval/`: Implementation using the interval constructor from cubical Agda
    - `Base.agda`: Common definitions and imports
    - `Equivalences.agda`: Proofs of equivalences between different real number types
    - `Counterexamples.agda`: Examples showing differences or limitations
  - `Examples/`: Example usage and demonstrations
- `doc/`: Documentation files
- `zooReals.agda-lib`: Agda library configuration file
- `README.md`: Project overview and instructions