ARG DOCKER_IMAGE_BASE
FROM ${DOCKER_IMAGE_BASE}

# Build arguments. This can be changed when invoking
# `docker build`.
ARG Z3_SRC_DIR=/home/user/z3_src

ENV \
  Z3_SRC_DIR=${Z3_SRC_DIR} \
  Z3_BUILD_DIR=/home/user/z3_build

# We add context across incrementally to maximal cache reuse

# Build Z3
RUN mkdir -p "${Z3_SRC_DIR}" && \
  mkdir -p "${Z3_SRC_DIR}/contrib/ci/scripts" && \
  mkdir -p "${Z3_SRC_DIR}/third-parties-lib" && \
  mkdir -p "${Z3_SRC_DIR}/contrib/suppressions/sanitizers"

# Install dependencies
ADD \
	/ci/scripts/install-lib.sh \
  	/contrib/ci/scripts/run_quiet.sh \
	${Z3_SRC_DIR}/third-parties-lib/
RUN ${Z3_SRC_DIR}/third-parties-lib/install-lib.sh

# Deliberately leave out `contrib`
ADD /cmake ${Z3_SRC_DIR}/cmake/
ADD /doc ${Z3_SRC_DIR}/doc/
ADD /examples ${Z3_SRC_DIR}/examples/
ADD /scripts ${Z3_SRC_DIR}/scripts/
ADD /src ${Z3_SRC_DIR}/src/
ADD *.txt *.md RELEASE_NOTES ${Z3_SRC_DIR}/

ADD /ci/scripts/build_z3_cmake.sh ${Z3_SRC_DIR}/
RUN ${Z3_SRC_DIR}/build_z3_cmake.sh
