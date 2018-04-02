function handleTimeout() {
	if (document.cookie.search(/BOCLAST=(\d*)/) < 0)
		return;

	var remaining = parseInt(RegExp.$1) + 598000 - (new Date()).getTime();

	if (remaining < 1000)
		document.getElementById('timeoutp').innerHTML = 'Session timed out due to inactivity.  <a href="boc.pl?logout=1">Login again</a>';
	else if (remaining < 121000) {
		setTimeout(function(){handleTimeout()}, 5000);

		var secs = Math.floor((remaining / 1000) % 60);
		secs = (secs < 10) ? '0' + secs : secs;
		var mins = Math.floor(remaining / 60000);
		document.getElementById('timeoutp').innerHTML = 'Session inactivity timeout: ' + mins + ':' + secs;
		document.getElementById('timeout').style.visibility = 'visible';
		return;
	} else {
		setTimeout(function(){handleTimeout()}, remaining - 120999);
		document.getElementById('timeout').style.visibility = 'hidden';
	}
}

document.cookie = 'BOCLAST=' + (new Date()).getTime();

var d = document.createElement('div');
d.setAttribute('id', 'timeout');
d.style.position = 'fixed';
d.style.top = '30px';
d.style.right = '60px';
d.style.backgroundColor = 'rgba(70%, 70%, 70%, 0.5)';
d.style.padding = '0px 10px';
d.style.borderRadius = '10px';
d.style.visibility = 'hidden';
d.innerHTML = '<p id="timeoutp"></p>';
document.body.appendChild(d);

handleTimeout();
