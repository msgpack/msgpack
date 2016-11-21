/*
 * MessagePack for C version information
 *
 * Copyright (C) 2008-2009 FURUHASHI Sadayuki
 *
 *    Licensed under the Apache License, Version 2.0 (the "License");
 *    you may not use this file except in compliance with the License.
 *    You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *    Unless required by applicable law or agreed to in writing, software
 *    distributed under the License is distributed on an "AS IS" BASIS,
 *    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *    See the License for the specific language governing permissions and
 *    limitations under the License.
 */
#ifndef MSGPACK_VERSION_H__
#define MSGPACK_VERSION_H__

#ifdef __cplusplus
extern "C" {
#endif


const char* msgpack_version(void);
int msgpack_version_major(void);
int msgpack_version_minor(void);

#define MSGPACK_VERSION "0.5.6"
#define MSGPACK_VERSION_MAJOR 0
#define MSGPACK_VERSION_MINOR 5


#ifdef __cplusplus
}
#endif

#endif /* msgpack/version.h */

