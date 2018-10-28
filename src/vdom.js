(function(){
    var ownProp = function(o,p) {
        return Object.prototype.hasOwnProperty.call(o,p);
    };
    window.pamperscript = window.pamperscript || {};
    window.pamperscript.makeElement = function makeElement(type, attrs, text, children) {
        text = text || '';
        if (type === 'text') {
            return text;
        }
        children = children || [];
        attrs = attrs || [];
        return { type:type, attrs:attrs, children:children };
    };
    window.pamperscript.makeAttr = function makeAttr(k, v, o) {
        o = o || {};
        o[k] = v;
        return o;
    };
    window.pamperscript.createElement = function createElement(node) {
        if (typeof node === 'string') {
            return document.createTextNode(node);
        }
        var el = document.createElement(node.type);
        for (var key in node.attrs) {
            if (ownProp(node.attrs, key)) {
                el[key] = node.attrs[key];
            }
        }
        for (var i=0; i<node.children.length; i++) {
            el.appendChild(createElement(node.children[i]));
        }
        return el;
    }
    window.pamperscript.mountElement = function mountElement(el, root) {
        root.appendChild(el);
    }
    function nodeChanged(node1, node2) {
        return (
            typeof node1 !== typeof node2 ||
            typeof node1 === 'string' && node1 !== node2 ||
            node1.type !== node2.type
        );

    }
    window.pamperscript.updateElement = function updateElement(parent, newNode, oldNode, index) {
        index = index || 0;
        if (!oldNode) {
            parent.appendChild(window.pamperscript.createElement(newNode));
        } else if (!newNode) {
            parent.removeChild(parent.childNodes[index]);
        } else if (nodeChanged(newNode, oldNode)) {
            parent.replaceChild(window.pamperscript.createElement(newNode), parent.childNodes[index]);
        } else if (newNode.type) {
            var newLength = newNode.children.length;
            var oldLength = oldNode.children.length;
            // TODO: This maybe isn't so efficient
            while (oldLength > newLength) {
                var i = oldLength - 1;
                updateElement(parent.childNodes[index], newNode.children[i], oldNode.children[i], i);
                oldLength--;
            }
            for (var i = 0; i < newLength || i < oldLength; i++) {
                updateElement(parent.childNodes[index], newNode.children[i], oldNode.children[i], i);
            }
        }
    }
})();
