# zooReals Directory Structure

This document describes the directory structure for the zooReals project.

## Root Directory
```
zooReals/
├── README.md
├── zooReals.agda-lib
├── directory-structure.md
├── project-structure.md
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
      - `Basic.agda`: Definition of Dedekind reals
      - `Properties.agda`: Properties of Dedekind reals
      - `Operations.agda`: Arithmetic operations on Dedekind reals
    - `Cauchy/`: Implementation of Cauchy reals
      - `Basic.agda`: Definition of Cauchy reals
      - `Properties.agda`: Properties of Cauchy reals
      - `Operations.agda`: Arithmetic operations on Cauchy reals
    - `Interval/`: Implementation using the interval constructor from cubical Agda
      - `Basic.agda`: Real numbers based on the interval constructor
    - `Base.agda`: Common definitions and imports used across real number implementations
    - `Equivalences.agda`: Proofs of equivalences between different real number types
    - `Counterexamples.agda`: Examples showing differences or limitations between real number types
  - `Examples/`: Example usage and demonstrations
    - `BasicExamples.agda`: Simple examples using the implemented real number types
- `doc/`: Documentation files
  - `design.md`: Detailed design documentation
- `zooReals.agda-lib`: Agda library configuration file
- `README.md`: Project overview and instructions
- `project-structure.md`: Original project structure planning document
- `directory-structure.md`: This file describing the actual directory structure