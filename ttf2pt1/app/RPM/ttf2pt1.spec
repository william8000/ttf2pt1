Summary: TrueType font converter
Name: ttf2pt1
Version: 311
Release: 1jv
Source: %{name}-%{version}.tgz
Patch0: %{name}-%{version}.patch0
Copyright: Distributable
Group: Utilities/Printing
BuildRoot: /var/tmp/ttf2pt1

%description
 * True Type Font to Adobe Type 1 font converter 
 * By Mark Heath <mheath@netspace.net.au> 
 * Based on ttf2pfa by Andrew Weeks <ccsaw@bath.ac.uk> 
 * With help from Frank M. Siegert <fms@this.net> 

%prep 
%setup
%patch0

%build
make ttf2pt1 docs

%install
rm -fr $RPM_BUILD_ROOT
mkdir -p $RPM_BUILD_ROOT/usr/bin
mkdir -p $RPM_BUILD_ROOT/usr/share/%{name}
mkdir -p $RPM_BUILD_ROOT/usr/doc

install -s -m 0555 ttf2pt1 $RPM_BUILD_ROOT/usr/bin
install -m 0555 scripts/* $RPM_BUILD_ROOT/usr/share/%{name}
chmod 0444 $RPM_BUILD_ROOT/usr/share/%{name}/convert.cfg.sample

%clean
rm -rf $RPM_BUILD_ROOT

%files
%defattr(644, root, root, 755)
%doc README INSTALL
/usr/bin/ttf2pt1
/usr/share/%{name}

