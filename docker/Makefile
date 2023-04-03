.PHONY: build run

DOCKER_IMAGE ?= msyksphinz/scariv:run_env
TZFULL=$(subst /, ,$(shell readlink /etc/localtime))
TZ=$(word $(shell expr $(words $(TZFULL)) - 1 ),$(TZFULL))/$(word $(words $(TZFULL)),$(TZFULL))

REPO_HOME = $(abspath ../)

build: Dockerfile
	docker build --build-arg TZ_ARG=$(TZ) $(DOCKER_BUILD_OPT) -f $(<) -t $(DOCKER_IMAGE) .

run:
	docker run --cap-add=SYS_PTRACE --security-opt="seccomp=unconfined" \
		--rm -it -v "$(REPO_HOME):/work/scariv" --user $(shell id -u):$(shell id -g) -w "/work/scariv" $(DOCKER_IMAGE) "/work/scariv/docker_regression/run_regression.sh"

debug:
	docker run --cap-add=SYS_PTRACE --security-opt="seccomp=unconfined" \
		--rm -it -v "$(REPO_HOME):/work/scariv" --user $(shell id -u):$(shell id -g) -w "/work/scariv" $(DOCKER_IMAGE) "/bin/bash"
