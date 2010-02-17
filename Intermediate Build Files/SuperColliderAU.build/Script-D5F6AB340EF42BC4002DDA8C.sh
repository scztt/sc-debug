#!/bin/sh
mkdir -p $BUILD_DIR/SuperColliderAU.component/Contents/Resources/plugins
cp  $BUILD_DIR/plugins/*.scx $BUILD_DIR/SuperColliderAU.component/Contents/Resources/plugins
mkdir -p $BUILD_DIR/SuperColliderAU.component/Contents/Resources/synthdefs
