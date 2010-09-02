.PHONY: test all python3

all:
	python setup.py build_ext -i -f
	python setup.py build sdist

python3:
	python3 setup.py build_ext -i -f
	python3 setup.py build sdist

test:
	nosetests test
