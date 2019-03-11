#!/bin/bash

# Based on contrib/ci/scripts/travis_ci_linux_entry_point.sh

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
ORIG_SCRIPT_DIR="$SCRIPT_DIR/../../contrib/ci/scripts/"

set -x
set -e
set -o pipefail

DOCKER_FILE_DIR="$(cd ${SCRIPT_DIR}/../Dockerfiles; echo $PWD)"

# Sanity check. Current working directory should be repo root
if [ ! -f "./README.md" ]; then
  echo "Current working directory should be repo root"
  exit 1
fi

# Get defaults
source "${ORIG_SCRIPT_DIR}/ci_defaults.sh"

BUILD_OPTS=()
# Pass Docker build arguments
# ...

BASE_DOCKER_FILE="${DOCKER_FILE_DIR}/z3_base_ubuntu_16.04.Dockerfile"
BASE_DOCKER_IMAGE_NAME="z3_base_ubuntu:16.04"

# Initially assume that we need to build the base Docker image
MUST_BUILD=1

# Travis CI persistent cache.
#
# This inspired by http://rundef.com/fast-travis-ci-docker-build .
# The idea is to cache the built image for subsequent builds to
# reduce build time.
if [ -n "${DOCKER_TRAVIS_CI_CACHE_DIR}" ]; then
  CHECKSUM_FILE="${DOCKER_TRAVIS_CI_CACHE_DIR}/${BASE_DOCKER_IMAGE_NAME}.chksum"
  CACHED_DOCKER_IMAGE="${DOCKER_TRAVIS_CI_CACHE_DIR}/${BASE_DOCKER_IMAGE_NAME}.gz"
  if [ -f "${CACHED_DOCKER_IMAGE}" ]; then
    # There's a cached image to use. Check the checksums of the Dockerfile
    # match. If they don't that implies we need to build a fresh image.
    if [ -f "${CHECKSUM_FILE}" ]; then
      CURRENT_DOCKERFILE_CHECKSUM=$(sha256sum "${BASE_DOCKER_FILE}" | awk '{ print $1 }')
      CACHED_DOCKERFILE_CHECKSUM=$(cat "${CHECKSUM_FILE}")
      if [ "X${CURRENT_DOCKERFILE_CHECKSUM}" = "X${CACHED_DOCKERFILE_CHECKSUM}" ]; then
        # Load the cached image
        MUST_BUILD=0
        gunzip --stdout "${CACHED_DOCKER_IMAGE}" | docker load
      fi
    fi
  fi
fi

if [ "${MUST_BUILD}" -eq 1 ]; then
  # The base image contains all the dependencies we want to build
  # Z3.
  docker build -t "${BASE_DOCKER_IMAGE_NAME}" - < "${BASE_DOCKER_FILE}"

  if [ -n "${DOCKER_TRAVIS_CI_CACHE_DIR}" ]; then
    # Write image and checksum to cache
    docker save "${BASE_DOCKER_IMAGE_NAME}" | \
      gzip > "${CACHED_DOCKER_IMAGE}"
    sha256sum "${BASE_DOCKER_FILE}" | awk '{ print $1 }' > \
      "${CHECKSUM_FILE}"
  fi
fi


DOCKER_MAJOR_VERSION=$(docker info --format '{{.ServerVersion}}' | sed 's/^\([0-9]\+\)\.\([0-9]\+\).*$/\1/')
DOCKER_MINOR_VERSION=$(docker info --format '{{.ServerVersion}}' | sed 's/^\([0-9]\+\)\.\([0-9]\+\).*$/\2/')
DOCKER_BUILD_FILE="${DOCKER_FILE_DIR}/z3_build.Dockerfile"

if [ "${DOCKER_MAJOR_VERSION}${DOCKER_MINOR_VERSION}" -lt 1705 ]; then
  # Workaround limitation in older Docker versions where the FROM
  # command cannot be parameterized with an ARG.
  sed \
    -e '/^ARG DOCKER_IMAGE_BASE/d' \
    -e 's/${DOCKER_IMAGE_BASE}/'"${BASE_DOCKER_IMAGE_NAME}/" \
    "${DOCKER_BUILD_FILE}" > "${DOCKER_BUILD_FILE}.patched"
  DOCKER_BUILD_FILE="${DOCKER_BUILD_FILE}.patched"
else
  # This feature landed in Docker 17.05
  # See https://github.com/moby/moby/pull/31352
  BUILD_OPTS+=( \
    "--build-arg" \
    "DOCKER_IMAGE_BASE=${BASE_DOCKER_IMAGE_NAME}" \
  )
fi

# Now build Z3 and test it using the created base image
docker build \
  -f "${DOCKER_BUILD_FILE}" \
  "${BUILD_OPTS[@]}" \
  .
