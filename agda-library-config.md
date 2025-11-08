# Agda Library Configuration

## zooReals.agda-lib File

The `zooReals.agda-lib` file is the configuration file that tells Agda how to handle our library. This file should contain:

```
name: zooReals
include: src
depend: cubical
```

### Explanation:

- `name: zooReals`: The name of our library
- `include: src`: Tells Agda to look for modules in the src directory
- `depend: cubical`: Indicates that our library depends on the cubical library

This configuration allows Agda to properly resolve imports and dependencies when working with our real number implementations.