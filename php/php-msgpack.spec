%define php_apiver %((echo 0; php -i 2>/dev/null | sed -n 's/^PHP API => //p') | tail -1)
%{!?php_extdir: %{expand: %%define php_extdir %(php-config --extension-dir)}}

Summary: PHP extension for interfacing with MessagePack
Name: php-msgpack
Version: 0.5.0
Release: 1%{?dist}
Source: php-msgpack-%{version}.tar.gz
License: New BSD License
Group: Development/Libraries
Packager: advect <advect@gmail.com>
Provides: php-pecl-msgpack
BuildRoot: %{_tmppath}/%{name}-%{version}-root
BuildRequires: php-devel
%if 0%{?php_zend_api}
Requires: php(zend-abi) = %{php_zend_api}
Requires: php(api) = %{php_core_api}
%else
Requires: php-api = %{php_apiver}
%endif

%description
PHP extension for interfacing with MessagePack.

%prep
%setup -q -n php-msgpack

%build
phpize
%configure
%{__make}

%install
%makeinstall INSTALL_ROOT=%{buildroot}

%{__install} -d %{buildroot}%{_sysconfdir}/php.d
%{__cat} > %{buildroot}%{_sysconfdir}/php.d/msgpack.ini <<EOF
; Enable msgpack extension module
extension=msgpack.so
EOF

%check
export NO_INTERACTION=1 REPORT_EXIT_STATUS=1
%{__make} test
unset NO_INTERACTION REPORT_EXIT_STATUS

if [ -n "`find tests -name \*.diff -type f -print`" ];  then
    exit 1
fi

%clean
%{__rm} -rf %{buildroot}

%files
%attr(-, root, root)
%{_includedir}/php/ext/msgpack/php_msgpack.h
%{php_extdir}/msgpack.so
%config(noreplace) %{_sysconfdir}/php.d/msgpack.ini
