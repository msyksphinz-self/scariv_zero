# How to run specified test case

## Compile test benches

```sh
cd ../tests/ && ./build_tests.sh
```

## Compile RTL and run simulation

### Execute simple test (rv64ui-p-simple)

```sh
../scripts/runtest.py --docker --isa rv64imafdc -c tiny -t rv64ui-p-simple
```

### Execute sanity tests parallel

```sh
../scripts/runtest.py --docker --isa rv64imafdc -c tiny -t sanity
```
