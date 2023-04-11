/*! For license information please see jsonMode.js.LICENSE.txt */
!function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vs/language/json/workerManager",["require","exports"],e)}((function(e,n){function t(e){var n,t,o=new r((function(e,r){n=e,t=r}),(function(){}));return e.then(n,t),o}Object.defineProperty(n,"__esModule",{value:!0});var r=monaco.Promise,o=function(){function e(e){var n=this;this._defaults=e,this._worker=null,this._idleCheckInterval=setInterval((function(){return n._checkIfIdle()}),3e4),this._lastUsedTime=0,this._configChangeListener=this._defaults.onDidChange((function(){return n._stopWorker()}))}return e.prototype._stopWorker=function(){this._worker&&(this._worker.dispose(),this._worker=null),this._client=null},e.prototype.dispose=function(){clearInterval(this._idleCheckInterval),this._configChangeListener.dispose(),this._stopWorker()},e.prototype._checkIfIdle=function(){this._worker&&Date.now()-this._lastUsedTime>12e4&&this._stopWorker()},e.prototype._getClient=function(){return this._lastUsedTime=Date.now(),this._client||(this._worker=monaco.editor.createWebWorker({moduleId:"vs/language/json/jsonWorker",label:this._defaults.languageId,createData:{languageSettings:this._defaults.diagnosticsOptions,languageId:this._defaults.languageId}}),this._client=this._worker.getProxy()),this._client},e.prototype.getLanguageServiceWorker=function(){for(var e=this,n=[],r=0;r<arguments.length;r++)n[r]=arguments[r];var o;return t(this._getClient().then((function(e){o=e})).then((function(t){return e._worker.withSyncedResources(n)})).then((function(e){return o})))},e}();n.WorkerManager=o})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vscode-languageserver-types/main",["require","exports"],e)}((function(e,n){var t,r,o,i,a;Object.defineProperty(n,"__esModule",{value:!0}),function(e){e.create=function(e,n){return{line:e,character:n}},e.is=function(e){var n=e;return l.defined(n)&&l.number(n.line)&&l.number(n.character)}}(t=n.Position||(n.Position={})),function(e){e.create=function(e,n,r,o){if(l.number(e)&&l.number(n)&&l.number(r)&&l.number(o))return{start:t.create(e,n),end:t.create(r,o)};if(t.is(e)&&t.is(n))return{start:e,end:n};throw new Error("Range#create called with invalid arguments["+e+", "+n+", "+r+", "+o+"]")},e.is=function(e){var n=e;return l.defined(n)&&t.is(n.start)&&t.is(n.end)}}(r=n.Range||(n.Range={})),function(e){e.create=function(e,n){return{uri:e,range:n}},e.is=function(e){var n=e;return l.defined(n)&&r.is(n.range)&&(l.string(n.uri)||l.undefined(n.uri))}}(n.Location||(n.Location={})),function(e){e.Error=1,e.Warning=2,e.Information=3,e.Hint=4}(n.DiagnosticSeverity||(n.DiagnosticSeverity={})),function(e){e.create=function(e,n,t,r,o){var i={range:e,message:n};return l.defined(t)&&(i.severity=t),l.defined(r)&&(i.code=r),l.defined(o)&&(i.source=o),i},e.is=function(e){var n=e;return l.defined(n)&&r.is(n.range)&&l.string(n.message)&&(l.number(n.severity)||l.undefined(n.severity))&&(l.number(n.code)||l.string(n.code)||l.undefined(n.code))&&(l.string(n.source)||l.undefined(n.source))}}(o=n.Diagnostic||(n.Diagnostic={})),function(e){e.create=function(e,n){for(var t=[],r=2;r<arguments.length;r++)t[r-2]=arguments[r];var o={title:e,command:n};return l.defined(t)&&t.length>0&&(o.arguments=t),o},e.is=function(e){var n=e;return l.defined(n)&&l.string(n.title)&&l.string(n.title)}}(i=n.Command||(n.Command={})),function(e){e.replace=function(e,n){return{range:e,newText:n}},e.insert=function(e,n){return{range:{start:e,end:e},newText:n}},e.del=function(e){return{range:e,newText:""}}}(a=n.TextEdit||(n.TextEdit={})),function(e){e.create=function(e,n){return{textDocument:e,edits:n}},e.is=function(e){var n=e;return l.defined(n)&&c.is(n.textDocument)&&Array.isArray(n.edits)}}(n.TextDocumentEdit||(n.TextDocumentEdit={}));var c,u=function(){function e(e){this.edits=e}return e.prototype.insert=function(e,n){this.edits.push(a.insert(e,n))},e.prototype.replace=function(e,n){this.edits.push(a.replace(e,n))},e.prototype.delete=function(e){this.edits.push(a.del(e))},e.prototype.add=function(e){this.edits.push(e)},e.prototype.all=function(){return this.edits},e.prototype.clear=function(){this.edits.splice(0,this.edits.length)},e}(),s=function(){function e(e){var n=this;this._textEditChanges=Object.create(null),e&&(this._workspaceEdit=e,e.documentChanges?e.documentChanges.forEach((function(e){var t=new u(e.edits);n._textEditChanges[e.textDocument.uri]=t})):e.changes&&Object.keys(e.changes).forEach((function(t){var r=new u(e.changes[t]);n._textEditChanges[t]=r})))}return Object.defineProperty(e.prototype,"edit",{get:function(){return this._workspaceEdit},enumerable:!0,configurable:!0}),e.prototype.getTextEditChange=function(e){if(c.is(e)){if(this._workspaceEdit||(this._workspaceEdit={documentChanges:[]}),!this._workspaceEdit.documentChanges)throw new Error("Workspace edit is not configured for versioned document changes.");var n=e;if(!(r=this._textEditChanges[n.uri])){var t={textDocument:n,edits:o=[]};this._workspaceEdit.documentChanges.push(t),r=new u(o),this._textEditChanges[n.uri]=r}return r}if(this._workspaceEdit||(this._workspaceEdit={changes:Object.create(null)}),!this._workspaceEdit.changes)throw new Error("Workspace edit is not configured for normal text edit changes.");var r;if(!(r=this._textEditChanges[e])){var o=[];this._workspaceEdit.changes[e]=o,r=new u(o),this._textEditChanges[e]=r}return r},e}();n.WorkspaceChange=s,function(e){e.create=function(e){return{uri:e}},e.is=function(e){var n=e;return l.defined(n)&&l.string(n.uri)}}(n.TextDocumentIdentifier||(n.TextDocumentIdentifier={})),function(e){e.create=function(e,n){return{uri:e,version:n}},e.is=function(e){var n=e;return l.defined(n)&&l.string(n.uri)&&l.number(n.version)}}(c=n.VersionedTextDocumentIdentifier||(n.VersionedTextDocumentIdentifier={})),function(e){e.create=function(e,n,t,r){return{uri:e,languageId:n,version:t,text:r}},e.is=function(e){var n=e;return l.defined(n)&&l.string(n.uri)&&l.string(n.languageId)&&l.number(n.version)&&l.string(n.text)}}(n.TextDocumentItem||(n.TextDocumentItem={})),function(e){e.Text=1,e.Method=2,e.Function=3,e.Constructor=4,e.Field=5,e.Variable=6,e.Class=7,e.Interface=8,e.Module=9,e.Property=10,e.Unit=11,e.Value=12,e.Enum=13,e.Keyword=14,e.Snippet=15,e.Color=16,e.File=17,e.Reference=18}(n.CompletionItemKind||(n.CompletionItemKind={})),function(e){e.PlainText=1,e.Snippet=2}(n.InsertTextFormat||(n.InsertTextFormat={})),function(e){e.create=function(e){return{label:e}}}(n.CompletionItem||(n.CompletionItem={})),function(e){e.create=function(e,n){return{items:e||[],isIncomplete:!!n}}}(n.CompletionList||(n.CompletionList={})),function(e){e.fromPlainText=function(e){return e.replace(/[\\`*_{}[\]()#+\-.!]/g,"\\$&")}}(n.MarkedString||(n.MarkedString={})),function(e){e.create=function(e,n){return n?{label:e,documentation:n}:{label:e}}}(n.ParameterInformation||(n.ParameterInformation={})),function(e){e.create=function(e,n){for(var t=[],r=2;r<arguments.length;r++)t[r-2]=arguments[r];var o={label:e};return l.defined(n)&&(o.documentation=n),l.defined(t)?o.parameters=t:o.parameters=[],o}}(n.SignatureInformation||(n.SignatureInformation={})),function(e){e.Text=1,e.Read=2,e.Write=3}(n.DocumentHighlightKind||(n.DocumentHighlightKind={})),function(e){e.create=function(e,n){var t={range:e};return l.number(n)&&(t.kind=n),t}}(n.DocumentHighlight||(n.DocumentHighlight={})),function(e){e.File=1,e.Module=2,e.Namespace=3,e.Package=4,e.Class=5,e.Method=6,e.Property=7,e.Field=8,e.Constructor=9,e.Enum=10,e.Interface=11,e.Function=12,e.Variable=13,e.Constant=14,e.String=15,e.Number=16,e.Boolean=17,e.Array=18}(n.SymbolKind||(n.SymbolKind={})),function(e){e.create=function(e,n,t,r,o){var i={name:e,kind:n,location:{uri:r,range:t}};return o&&(i.containerName=o),i}}(n.SymbolInformation||(n.SymbolInformation={})),function(e){e.create=function(e){return{diagnostics:e}},e.is=function(e){var n=e;return l.defined(n)&&l.typedArray(n.diagnostics,o.is)}}(n.CodeActionContext||(n.CodeActionContext={})),function(e){e.create=function(e,n){var t={range:e};return l.defined(n)&&(t.data=n),t},e.is=function(e){var n=e;return l.defined(n)&&r.is(n.range)&&(l.undefined(n.command)||i.is(n.command))}}(n.CodeLens||(n.CodeLens={})),function(e){e.create=function(e,n){return{tabSize:e,insertSpaces:n}},e.is=function(e){var n=e;return l.defined(n)&&l.number(n.tabSize)&&l.boolean(n.insertSpaces)}}(n.FormattingOptions||(n.FormattingOptions={}));var d=function(){};n.DocumentLink=d,function(e){e.create=function(e,n){return{range:e,target:n}},e.is=function(e){var n=e;return l.defined(n)&&r.is(n.range)&&(l.undefined(n.target)||l.string(n.target))}}(d=n.DocumentLink||(n.DocumentLink={})),n.DocumentLink=d,n.EOL=["\n","\r\n","\r"],function(e){e.create=function(e,n,t,r){return new f(e,n,t,r)},e.is=function(e){var n=e;return!!(l.defined(n)&&l.string(n.uri)&&(l.undefined(n.languageId)||l.string(n.languageId))&&l.number(n.lineCount)&&l.func(n.getText)&&l.func(n.positionAt)&&l.func(n.offsetAt))}}(n.TextDocument||(n.TextDocument={})),function(e){e.Manual=1,e.AfterDelay=2,e.FocusOut=3}(n.TextDocumentSaveReason||(n.TextDocumentSaveReason={}));var l,f=function(){function e(e,n,t,r){this._uri=e,this._languageId=n,this._version=t,this._content=r,this._lineOffsets=null}return Object.defineProperty(e.prototype,"uri",{get:function(){return this._uri},enumerable:!0,configurable:!0}),Object.defineProperty(e.prototype,"languageId",{get:function(){return this._languageId},enumerable:!0,configurable:!0}),Object.defineProperty(e.prototype,"version",{get:function(){return this._version},enumerable:!0,configurable:!0}),e.prototype.getText=function(){return this._content},e.prototype.update=function(e,n){this._content=e.text,this._version=n,this._lineOffsets=null},e.prototype.getLineOffsets=function(){if(null===this._lineOffsets){for(var e=[],n=this._content,t=!0,r=0;r<n.length;r++){t&&(e.push(r),t=!1);var o=n.charAt(r);t="\r"===o||"\n"===o,"\r"===o&&r+1<n.length&&"\n"===n.charAt(r+1)&&r++}t&&n.length>0&&e.push(n.length),this._lineOffsets=e}return this._lineOffsets},e.prototype.positionAt=function(e){e=Math.max(Math.min(e,this._content.length),0);var n=this.getLineOffsets(),r=0,o=n.length;if(0===o)return t.create(0,e);for(;r<o;){var i=Math.floor((r+o)/2);n[i]>e?o=i:r=i+1}var a=r-1;return t.create(a,e-n[a])},e.prototype.offsetAt=function(e){var n=this.getLineOffsets();if(e.line>=n.length)return this._content.length;if(e.line<0)return 0;var t=n[e.line],r=e.line+1<n.length?n[e.line+1]:this._content.length;return Math.max(Math.min(t+e.character,r),t)},Object.defineProperty(e.prototype,"lineCount",{get:function(){return this.getLineOffsets().length},enumerable:!0,configurable:!0}),e}();!function(e){var n=Object.prototype.toString;e.defined=function(e){return void 0!==e},e.undefined=function(e){return void 0===e},e.boolean=function(e){return!0===e||!1===e},e.string=function(e){return"[object String]"===n.call(e)},e.number=function(e){return"[object Number]"===n.call(e)},e.func=function(e){return"[object Function]"===n.call(e)},e.typedArray=function(e,n){return Array.isArray(e)&&e.every(n)}}(l||(l={}))})),define("vscode-languageserver-types",["vscode-languageserver-types/main"],(function(e){return e})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vs/language/json/languageFeatures",["require","exports","vscode-languageserver-types"],e)}((function(e,n){function t(e){switch(e){case m.DiagnosticSeverity.Error:return monaco.Severity.Error;case m.DiagnosticSeverity.Warning:return monaco.Severity.Warning;case m.DiagnosticSeverity.Information:case m.DiagnosticSeverity.Hint:default:return monaco.Severity.Info}}function r(e,n){var r="number"==typeof n.code?String(n.code):n.code;return{severity:t(n.severity),startLineNumber:n.range.start.line+1,startColumn:n.range.start.character+1,endLineNumber:n.range.end.line+1,endColumn:n.range.end.character+1,message:n.message,code:r,source:n.source}}function o(e){if(e)return{character:e.column-1,line:e.lineNumber-1}}function i(e){if(e)return{start:o(e.getStartPosition()),end:o(e.getEndPosition())}}function a(e){if(e)return new h(e.start.line+1,e.start.character+1,e.end.line+1,e.end.character+1)}function c(e){var n=monaco.languages.CompletionItemKind;switch(e){case m.CompletionItemKind.Text:return n.Text;case m.CompletionItemKind.Method:return n.Method;case m.CompletionItemKind.Function:return n.Function;case m.CompletionItemKind.Constructor:return n.Constructor;case m.CompletionItemKind.Field:return n.Field;case m.CompletionItemKind.Variable:return n.Variable;case m.CompletionItemKind.Class:return n.Class;case m.CompletionItemKind.Interface:return n.Interface;case m.CompletionItemKind.Module:return n.Module;case m.CompletionItemKind.Property:return n.Property;case m.CompletionItemKind.Unit:return n.Unit;case m.CompletionItemKind.Value:return n.Value;case m.CompletionItemKind.Enum:return n.Enum;case m.CompletionItemKind.Keyword:return n.Keyword;case m.CompletionItemKind.Snippet:return n.Snippet;case m.CompletionItemKind.Color:return n.Color;case m.CompletionItemKind.File:return n.File;case m.CompletionItemKind.Reference:return n.Reference}return n.Property}function u(e){if(e)return{range:a(e.range),text:e.newText}}function s(e){if(e)return Array.isArray(e)?e:[e]}function d(e){return{uri:g.parse(e.uri),range:a(e.range)}}function l(e){var n=monaco.languages.SymbolKind;switch(e){case m.SymbolKind.File:return n.Array;case m.SymbolKind.Module:return n.Module;case m.SymbolKind.Namespace:return n.Namespace;case m.SymbolKind.Package:return n.Package;case m.SymbolKind.Class:return n.Class;case m.SymbolKind.Method:return n.Method;case m.SymbolKind.Property:return n.Property;case m.SymbolKind.Field:return n.Field;case m.SymbolKind.Constructor:return n.Constructor;case m.SymbolKind.Enum:return n.Enum;case m.SymbolKind.Interface:return n.Interface;case m.SymbolKind.Function:return n.Function;case m.SymbolKind.Variable:return n.Variable;case m.SymbolKind.Constant:return n.Constant;case m.SymbolKind.String:return n.String;case m.SymbolKind.Number:return n.Number;case m.SymbolKind.Boolean:return n.Boolean;case m.SymbolKind.Array:return n.Array}return n.Function}function f(e){return{tabSize:e.tabSize,insertSpaces:e.insertSpaces}}function p(e,n){return n.cancel&&e.onCancellationRequested((function(){return n.cancel()})),n}Object.defineProperty(n,"__esModule",{value:!0});var m=e("vscode-languageserver-types"),g=monaco.Uri,h=monaco.Range,v=function(){function e(e,n){var t=this;this._languageId=e,this._worker=n,this._disposables=[],this._listener=Object.create(null);var r=function(e){var n,r=e.getModeId();r===t._languageId&&(t._listener[e.uri.toString()]=e.onDidChangeContent((function(){clearTimeout(n),n=setTimeout((function(){return t._doValidate(e.uri,r)}),500)})),t._doValidate(e.uri,r))},o=function(e){monaco.editor.setModelMarkers(e,t._languageId,[]);var n=e.uri.toString(),r=t._listener[n];r&&(r.dispose(),delete t._listener[n])};this._disposables.push(monaco.editor.onDidCreateModel(r)),this._disposables.push(monaco.editor.onWillDisposeModel((function(e){o(e),t._resetSchema(e.uri)}))),this._disposables.push(monaco.editor.onDidChangeModelLanguage((function(e){o(e.model),r(e.model),t._resetSchema(e.model.uri)}))),this._disposables.push({dispose:function(){for(var e in t._listener)t._listener[e].dispose()}}),monaco.editor.getModels().forEach(r)}return e.prototype.dispose=function(){this._disposables.forEach((function(e){return e&&e.dispose()})),this._disposables=[]},e.prototype._resetSchema=function(e){this._worker().then((function(n){n.resetSchema(e.toString())}))},e.prototype._doValidate=function(e,n){this._worker(e).then((function(t){return t.doValidation(e.toString()).then((function(t){var o=t.map((function(e){return r(0,e)})),i=monaco.editor.getModel(e);i.getModeId()===n&&monaco.editor.setModelMarkers(i,n,o)}))})).then(void 0,(function(e){console.error(e)}))},e}();n.DiagnostcsAdapter=v;var y=function(){function e(e){this._worker=e}return Object.defineProperty(e.prototype,"triggerCharacters",{get:function(){return[" ",":"]},enumerable:!0,configurable:!0}),e.prototype.provideCompletionItems=function(e,n,t){var r=(e.getWordUntilPosition(n),e.uri);return p(t,this._worker(r).then((function(e){return e.doComplete(r.toString(),o(n))})).then((function(e){if(e){var n=e.items.map((function(e){var n={label:e.label,insertText:e.insertText,sortText:e.sortText,filterText:e.filterText,documentation:e.documentation,detail:e.detail,kind:c(e.kind)};return e.textEdit&&(n.range=a(e.textEdit.range),n.insertText=e.textEdit.newText),e.insertTextFormat===m.InsertTextFormat.Snippet&&(n.insertText={value:n.insertText}),n}));return{isIncomplete:e.isIncomplete,items:n}}})))},e}();n.CompletionAdapter=y;var k=function(){function e(e){this._worker=e}return e.prototype.provideHover=function(e,n,t){var r=e.uri;return p(t,this._worker(r).then((function(e){return e.doHover(r.toString(),o(n))})).then((function(e){if(e)return{range:a(e.range),contents:s(e.contents)}})))},e}();n.HoverAdapter=k;var C=function(){function e(e){this._worker=e}return e.prototype.provideDocumentSymbols=function(e,n){var t=e.uri;return p(n,this._worker(t).then((function(e){return e.findDocumentSymbols(t.toString())})).then((function(e){if(e)return e.map((function(e){return{name:e.name,containerName:e.containerName,kind:l(e.kind),location:d(e.location)}}))})))},e}();n.DocumentSymbolAdapter=C;var b=function(){function e(e){this._worker=e}return e.prototype.provideDocumentFormattingEdits=function(e,n,t){var r=e.uri;return p(t,this._worker(r).then((function(e){return e.format(r.toString(),null,f(n)).then((function(e){if(e&&0!==e.length)return e.map(u)}))})))},e}();n.DocumentFormattingEditProvider=b;var E=function(){function e(e){this._worker=e}return e.prototype.provideDocumentRangeFormattingEdits=function(e,n,t,r){var o=e.uri;return p(r,this._worker(o).then((function(e){return e.format(o.toString(),i(n),f(t)).then((function(e){if(e&&0!==e.length)return e.map(u)}))})))},e}();n.DocumentRangeFormattingEditProvider=E})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vscode-nls/vscode-nls",["require","exports"],e)}((function(e,n){function t(e,n){for(var t=[],r=2;r<arguments.length;r++)t[r-2]=arguments[r];return function(e,n){return 0===n.length?e:e.replace(/\{(\d+)\}/g,(function(e,t){var r=t[0];return void 0!==n[r]?n[r]:e}))}(n,t)}function r(e){return t}Object.defineProperty(n,"__esModule",{value:!0}),n.loadMessageBundle=r,n.config=function(e){return r}})),define("vscode-nls",["vscode-nls/vscode-nls"],(function(e){return e})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("jsonc-parser/main",["require","exports","vscode-nls"],e)}((function(e,n){function t(e,n){function t(n,t){for(var r=0,o=0;r<n||!t;){var i=e.charCodeAt(l);if(i>=48&&i<=57)o=16*o+i-48;else if(i>=65&&i<=70)o=16*o+i-65+10;else{if(!(i>=97&&i<=102))break;o=16*o+i-97+10}l++,r++}return r<n&&(o=-1),o}function a(){for(var n="",r=l;;){if(l>=f){n+=e.substring(r,l),h=u.UnexpectedEndOfString;break}var i=e.charCodeAt(l);if(34===i){n+=e.substring(r,l),l++;break}if(92!==i){if(i>=0&&i<=31){if(o(i)){n+=e.substring(r,l),h=u.UnexpectedEndOfString;break}h=u.InvalidCharacter}l++}else{if(n+=e.substring(r,l),++l>=f){h=u.UnexpectedEndOfString;break}switch(i=e.charCodeAt(l++)){case 34:n+='"';break;case 92:n+="\\";break;case 47:n+="/";break;case 98:n+="\b";break;case 102:n+="\f";break;case 110:n+="\n";break;case 114:n+="\r";break;case 116:n+="\t";break;case 117:var a=t(4,!0);a>=0?n+=String.fromCharCode(a):h=u.InvalidUnicode;break;default:h=u.InvalidEscapeCharacter}r=l}}return n}function c(){if(p="",h=u.None,m=l,l>=f)return m=f,g=s.EOF;var n=e.charCodeAt(l);if(r(n)){do{l++,p+=String.fromCharCode(n),n=e.charCodeAt(l)}while(r(n));return g=s.Trivia}if(o(n))return l++,p+=String.fromCharCode(n),13===n&&10===e.charCodeAt(l)&&(l++,p+="\n"),g=s.LineBreakTrivia;switch(n){case 123:return l++,g=s.OpenBraceToken;case 125:return l++,g=s.CloseBraceToken;case 91:return l++,g=s.OpenBracketToken;case 93:return l++,g=s.CloseBracketToken;case 58:return l++,g=s.ColonToken;case 44:return l++,g=s.CommaToken;case 34:return l++,p=a(),g=s.StringLiteral;case 47:var t=l-1;if(47===e.charCodeAt(l+1)){for(l+=2;l<f&&!o(e.charCodeAt(l));)l++;return p=e.substring(t,l),g=s.LineCommentTrivia}if(42===e.charCodeAt(l+1)){l+=2;for(var c=f-1,v=!1;l<c;){if(42===e.charCodeAt(l)&&47===e.charCodeAt(l+1)){l+=2,v=!0;break}l++}return v||(l++,h=u.UnexpectedEndOfComment),p=e.substring(t,l),g=s.BlockCommentTrivia}return p+=String.fromCharCode(n),l++,g=s.Unknown;case 45:if(p+=String.fromCharCode(n),++l===f||!i(e.charCodeAt(l)))return g=s.Unknown;case 48:case 49:case 50:case 51:case 52:case 53:case 54:case 55:case 56:case 57:return p+=function(){var n=l;if(48===e.charCodeAt(l))l++;else for(l++;l<e.length&&i(e.charCodeAt(l));)l++;if(l<e.length&&46===e.charCodeAt(l)){if(!(++l<e.length&&i(e.charCodeAt(l))))return h=u.UnexpectedEndOfNumber,e.substring(n,l);for(l++;l<e.length&&i(e.charCodeAt(l));)l++}var t=l;if(l<e.length&&(69===e.charCodeAt(l)||101===e.charCodeAt(l)))if((++l<e.length&&43===e.charCodeAt(l)||45===e.charCodeAt(l))&&l++,l<e.length&&i(e.charCodeAt(l))){for(l++;l<e.length&&i(e.charCodeAt(l));)l++;t=l}else h=u.UnexpectedEndOfNumber;return e.substring(n,t)}(),g=s.NumericLiteral;default:for(;l<f&&d(n);)l++,n=e.charCodeAt(l);if(m!==l){switch(p=e.substring(m,l)){case"true":return g=s.TrueKeyword;case"false":return g=s.FalseKeyword;case"null":return g=s.NullKeyword}return g=s.Unknown}return p+=String.fromCharCode(n),l++,g=s.Unknown}}function d(e){if(r(e)||o(e))return!1;switch(e){case 125:case 93:case 123:case 91:case 34:case 58:case 44:return!1}return!0}void 0===n&&(n=!1);var l=0,f=e.length,p="",m=0,g=s.Unknown,h=u.None;return{setPosition:function(e){l=e,p="",m=0,g=s.Unknown,h=u.None},getPosition:function(){return l},scan:n?function(){var e;do{e=c()}while(e>=s.LineCommentTrivia&&e<=s.Trivia);return e}:c,getToken:function(){return g},getTokenValue:function(){return p},getTokenOffset:function(){return m},getTokenLength:function(){return l-m},getTokenError:function(){return h}}}function r(e){return 32===e||9===e||11===e||12===e||160===e||5760===e||e>=8192&&e<=8203||8239===e||8287===e||12288===e||65279===e}function o(e){return 10===e||13===e||8232===e||8233===e}function i(e){return e>=48&&e<=57}function a(e){switch(typeof e){case"boolean":return"boolean";case"number":return"number";case"string":return"string";default:return"null"}}function c(e,n,r){function o(e){return e?function(){return e(l.getTokenOffset(),l.getTokenLength())}:function(){return!0}}function i(e){return e?function(n){return e(n,l.getTokenOffset(),l.getTokenLength())}:function(){return!0}}function a(){for(;;){var e=l.scan();switch(e){case s.LineCommentTrivia:case s.BlockCommentTrivia:C&&c(d.InvalidSymbol);break;case s.Unknown:c(d.InvalidSymbol);break;case s.Trivia:case s.LineBreakTrivia:break;default:return e}}}function c(e,n,t){if(void 0===n&&(n=[]),void 0===t&&(t=[]),k(e),n.length+t.length>0)for(var r=l.getToken();r!==s.EOF;){if(-1!==n.indexOf(r)){a();break}if(-1!==t.indexOf(r))break;r=a()}}function u(e){var n=l.getTokenValue();return e?v(n):p(n),a(),!0}var l=t(e,!1),f=o(n.onObjectBegin),p=i(n.onObjectProperty),m=o(n.onObjectEnd),g=o(n.onArrayBegin),h=o(n.onArrayEnd),v=i(n.onLiteralValue),y=i(n.onSeparator),k=i(n.onError),C=r&&r.disallowComments,b=r&&r.allowTrailingComma;return a(),l.getToken()===s.EOF||(function e(){switch(l.getToken()){case s.OpenBracketToken:return function(){g(),a();for(var n=!1;l.getToken()!==s.CloseBracketToken&&l.getToken()!==s.EOF;)l.getToken()===s.CommaToken?(n||c(d.ValueExpected,[],[]),y(","),a()):n&&c(d.CommaExpected,[],[]),e()||c(d.ValueExpected,[],[s.CloseBracketToken,s.CommaToken]),n=!0;return h(),l.getToken()!==s.CloseBracketToken?c(d.CloseBracketExpected,[s.CloseBracketToken],[]):a(),!0}();case s.OpenBraceToken:return function(){f(),a();for(var n=!1;l.getToken()!==s.CloseBraceToken&&l.getToken()!==s.EOF;){if(l.getToken()===s.CommaToken){if(n||c(d.ValueExpected,[],[]),y(","),a(),l.getToken()===s.CloseBraceToken&&b)break}else n&&c(d.CommaExpected,[],[]);(l.getToken()!==s.StringLiteral?(c(d.PropertyNameExpected,[],[s.CloseBraceToken,s.CommaToken]),!1):(u(!1),l.getToken()===s.ColonToken?(y(":"),a(),e()||c(d.ValueExpected,[],[s.CloseBraceToken,s.CommaToken])):c(d.ColonExpected,[],[s.CloseBraceToken,s.CommaToken]),!0))||c(d.ValueExpected,[],[s.CloseBraceToken,s.CommaToken]),n=!0}return m(),l.getToken()!==s.CloseBraceToken?c(d.CloseBraceExpected,[s.CloseBraceToken],[]):a(),!0}();case s.StringLiteral:return u(!0);default:return function(){switch(l.getToken()){case s.NumericLiteral:var e=0;try{"number"!=typeof(e=JSON.parse(l.getTokenValue()))&&(c(d.InvalidNumberFormat),e=0)}catch(e){c(d.InvalidNumberFormat)}v(e);break;case s.NullKeyword:v(null);break;case s.TrueKeyword:v(!0);break;case s.FalseKeyword:v(!1);break;default:return!1}return a(),!0}()}}()?(l.getToken()!==s.EOF&&c(d.EndOfFileExpected,[],[]),!0):(c(d.ValueExpected,[],[]),!1))}var u,s,d,l=e("vscode-nls").loadMessageBundle();!function(e){e[e.None=0]="None",e[e.UnexpectedEndOfComment=1]="UnexpectedEndOfComment",e[e.UnexpectedEndOfString=2]="UnexpectedEndOfString",e[e.UnexpectedEndOfNumber=3]="UnexpectedEndOfNumber",e[e.InvalidUnicode=4]="InvalidUnicode",e[e.InvalidEscapeCharacter=5]="InvalidEscapeCharacter",e[e.InvalidCharacter=6]="InvalidCharacter"}(u=n.ScanError||(n.ScanError={})),function(e){e[e.Unknown=0]="Unknown",e[e.OpenBraceToken=1]="OpenBraceToken",e[e.CloseBraceToken=2]="CloseBraceToken",e[e.OpenBracketToken=3]="OpenBracketToken",e[e.CloseBracketToken=4]="CloseBracketToken",e[e.CommaToken=5]="CommaToken",e[e.ColonToken=6]="ColonToken",e[e.NullKeyword=7]="NullKeyword",e[e.TrueKeyword=8]="TrueKeyword",e[e.FalseKeyword=9]="FalseKeyword",e[e.StringLiteral=10]="StringLiteral",e[e.NumericLiteral=11]="NumericLiteral",e[e.LineCommentTrivia=12]="LineCommentTrivia",e[e.BlockCommentTrivia=13]="BlockCommentTrivia",e[e.LineBreakTrivia=14]="LineBreakTrivia",e[e.Trivia=15]="Trivia",e[e.EOF=16]="EOF"}(s=n.SyntaxKind||(n.SyntaxKind={})),n.createScanner=t,n.stripComments=function(e,n){var r,o,i=t(e),a=[],c=0;do{switch(o=i.getPosition(),r=i.scan()){case s.LineCommentTrivia:case s.BlockCommentTrivia:case s.EOF:c!==o&&a.push(e.substring(c,o)),void 0!==n&&a.push(i.getTokenValue().replace(/[^\r\n]/g,n)),c=i.getPosition()}}while(r!==s.EOF);return a.join("")},function(e){e[e.InvalidSymbol=0]="InvalidSymbol",e[e.InvalidNumberFormat=1]="InvalidNumberFormat",e[e.PropertyNameExpected=2]="PropertyNameExpected",e[e.ValueExpected=3]="ValueExpected",e[e.ColonExpected=4]="ColonExpected",e[e.CommaExpected=5]="CommaExpected",e[e.CloseBraceExpected=6]="CloseBraceExpected",e[e.CloseBracketExpected=7]="CloseBracketExpected",e[e.EndOfFileExpected=8]="EndOfFileExpected"}(d=n.ParseErrorCode||(n.ParseErrorCode={})),n.getParseErrorMessage=function(e){switch(e){case d.InvalidSymbol:return l("error.invalidSymbol","Invalid symbol");case d.InvalidNumberFormat:return l("error.invalidNumberFormat","Invalid number format");case d.PropertyNameExpected:return l("error.propertyNameExpected","Property name expected");case d.ValueExpected:return l("error.valueExpected","Value expected");case d.ColonExpected:return l("error.colonExpected","Colon expected");case d.CommaExpected:return l("error.commaExpected","Comma expected");case d.CloseBraceExpected:return l("error.closeBraceExpected","Closing brace expected");case d.CloseBracketExpected:return l("error.closeBracketExpected","Closing bracket expected");case d.EndOfFileExpected:return l("error.endOfFileExpected","End of file expected");default:return""}},n.getLocation=function(e,n){function t(e,n,t,r){u.value=e,u.offset=n,u.length=t,u.type=r,u.columnOffset=void 0,i=u}var r=[],o=new Object,i=void 0,u={value:void 0,offset:void 0,length:void 0,type:void 0},s=!1;try{c(e,{onObjectBegin:function(e,t){if(n<=e)throw o;i=void 0,s=n>e,r.push("")},onObjectProperty:function(e,i,a){if(n<i)throw o;if(t(e,i,a,"property"),r[r.length-1]=e,n<=i+a)throw o},onObjectEnd:function(e,t){if(n<=e)throw o;i=void 0,r.pop()},onArrayBegin:function(e,t){if(n<=e)throw o;i=void 0,r.push(0)},onArrayEnd:function(e,t){if(n<=e)throw o;i=void 0,r.pop()},onLiteralValue:function(e,r,i){if(n<r)throw o;if(t(e,r,i,a(e)),n<=r+i)throw o},onSeparator:function(e,t,a){if(n<=t)throw o;if(":"===e&&"property"===i.type)i.columnOffset=t,s=!1,i=void 0;else if(","===e){var c=r[r.length-1];"number"==typeof c?r[r.length-1]=c+1:(s=!0,r[r.length-1]=""),i=void 0}}})}catch(e){if(e!==o)throw e}return{path:r,previousNode:i,isAtPropertyKey:s,matches:function(e){for(var n=0,t=0;n<e.length&&t<r.length;t++)if(e[n]===r[t]||"*"===e[n])n++;else if("**"!==e[n])return!1;return n===e.length}}},n.parse=function(e,n,t){function r(e){Array.isArray(i)?i.push(e):o&&(i[o]=e)}void 0===n&&(n=[]);var o=null,i=[],a=[],u={onObjectBegin:function(){var e={};r(e),a.push(i),i=e,o=null},onObjectProperty:function(e){o=e},onObjectEnd:function(){i=a.pop()},onArrayBegin:function(){var e=[];r(e),a.push(i),i=e,o=null},onArrayEnd:function(){i=a.pop()},onLiteralValue:r,onError:function(e,t,r){n.push({error:e,offset:t,length:r})}};return c(e,u,t),i[0]},n.parseTree=function(e,n,t){function r(e){"property"===i.type&&(i.length=e-i.offset,i=i.parent)}function o(e){return i.children.push(e),e}void 0===n&&(n=[]);var i={type:"array",offset:-1,length:-1,children:[]},u={onObjectBegin:function(e){i=o({type:"object",offset:e,length:-1,parent:i,children:[]})},onObjectProperty:function(e,n,t){(i=o({type:"property",offset:n,length:-1,parent:i,children:[]})).children.push({type:"string",value:e,offset:n,length:t,parent:i})},onObjectEnd:function(e,n){i.length=e+n-i.offset,i=i.parent,r(e+n)},onArrayBegin:function(e,n){i=o({type:"array",offset:e,length:-1,parent:i,children:[]})},onArrayEnd:function(e,n){i.length=e+n-i.offset,i=i.parent,r(e+n)},onLiteralValue:function(e,n,t){o({type:a(e),offset:n,length:t,parent:i,value:e}),r(n+t)},onSeparator:function(e,n,t){"property"===i.type&&(":"===e?i.columnOffset=n:","===e&&r(n))},onError:function(e,t,r){n.push({error:e,offset:t,length:r})}};c(e,u,t);var s=i.children[0];return s&&delete s.parent,s},n.findNodeAtLocation=function(e,n){if(e){for(var t=e,r=0,o=n;r<o.length;r++){var i=o[r];if("string"==typeof i){if("object"!==t.type)return;for(var a=!1,c=0,u=t.children;c<u.length;c++){var s=u[c];if(s.children[0].value===i){t=s.children[1],a=!0;break}}if(!a)return}else{var d=i;if("array"!==t.type||d<0||d>=t.children.length)return;t=t.children[d]}}return t}},n.getNodeValue=function e(n){if("array"===n.type)return n.children.map(e);if("object"===n.type){for(var t={},r=0,o=n.children;r<o.length;r++){var i=o[r];t[i.children[0].value]=e(i.children[1])}return t}return n.value},n.visit=c})),define("jsonc-parser",["jsonc-parser/main"],(function(e){return e})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vs/language/json/tokenization",["require","exports","jsonc-parser"],e)}((function(e,n){function t(e,t,i,a,c){void 0===a&&(a=0);var u=0,s=!1;switch(i.scanError){case r.ScanError.UnexpectedEndOfString:t='"'+t,u=1;break;case r.ScanError.UnexpectedEndOfComment:t="/*"+t,u=2}var d,l,f=r.createScanner(t),p=i.lastWasColon;for(l={tokens:[],endState:i.clone()};;){var m=a+f.getPosition(),g="";if((d=f.scan())===r.SyntaxKind.EOF)break;if(m===a+f.getPosition())throw new Error("Scanner did not advance, next 3 characters are: "+t.substr(f.getPosition(),3));switch(s&&(m-=u),s=u>0,d){case r.SyntaxKind.OpenBraceToken:case r.SyntaxKind.CloseBraceToken:g=n.TOKEN_DELIM_OBJECT,p=!1;break;case r.SyntaxKind.OpenBracketToken:case r.SyntaxKind.CloseBracketToken:g=n.TOKEN_DELIM_ARRAY,p=!1;break;case r.SyntaxKind.ColonToken:g=n.TOKEN_DELIM_COLON,p=!0;break;case r.SyntaxKind.CommaToken:g=n.TOKEN_DELIM_COMMA,p=!1;break;case r.SyntaxKind.TrueKeyword:case r.SyntaxKind.FalseKeyword:g=n.TOKEN_VALUE_BOOLEAN,p=!1;break;case r.SyntaxKind.NullKeyword:g=n.TOKEN_VALUE_NULL,p=!1;break;case r.SyntaxKind.StringLiteral:g=p?n.TOKEN_VALUE_STRING:n.TOKEN_PROPERTY_NAME,p=!1;break;case r.SyntaxKind.NumericLiteral:g=n.TOKEN_VALUE_NUMBER,p=!1}if(e)switch(d){case r.SyntaxKind.LineCommentTrivia:g=n.TOKEN_COMMENT_LINE;break;case r.SyntaxKind.BlockCommentTrivia:g=n.TOKEN_COMMENT_BLOCK}l.endState=new o(i.getStateData(),f.getTokenError(),p),l.tokens.push({startIndex:m,scopes:g})}return l}Object.defineProperty(n,"__esModule",{value:!0});var r=e("jsonc-parser");n.createTokenizationSupport=function(e){return{getInitialState:function(){return new o(null,null,!1)},tokenize:function(n,r,o,i){return t(e,n,r,o)}}},n.TOKEN_DELIM_OBJECT="delimiter.bracket.json",n.TOKEN_DELIM_ARRAY="delimiter.array.json",n.TOKEN_DELIM_COLON="delimiter.colon.json",n.TOKEN_DELIM_COMMA="delimiter.comma.json",n.TOKEN_VALUE_BOOLEAN="keyword.json",n.TOKEN_VALUE_NULL="keyword.json",n.TOKEN_VALUE_STRING="string.value.json",n.TOKEN_VALUE_NUMBER="number.json",n.TOKEN_PROPERTY_NAME="string.key.json",n.TOKEN_COMMENT_BLOCK="comment.block.json",n.TOKEN_COMMENT_LINE="comment.line.json";var o=function(){function e(e,n,t){this._state=e,this.scanError=n,this.lastWasColon=t}return e.prototype.clone=function(){return new e(this._state,this.scanError,this.lastWasColon)},e.prototype.equals=function(n){return n===this||!!(n&&n instanceof e)&&this.scanError===n.scanError&&this.lastWasColon===n.lastWasColon},e.prototype.getStateData=function(){return this._state},e.prototype.setStateData=function(e){this._state=e},e}()})),function(e){if("object"==typeof module&&"object"==typeof module.exports){var n=e(require,exports);void 0!==n&&(module.exports=n)}else"function"==typeof define&&define.amd&&define("vs/language/json/jsonMode",["require","exports","./workerManager","./languageFeatures","./tokenization"],e)}((function(e,n){Object.defineProperty(n,"__esModule",{value:!0});var t=e("./workerManager"),r=e("./languageFeatures"),o=e("./tokenization");n.setupMode=function(e){var n=[],a=new t.WorkerManager(e);n.push(a);var c=function(){for(var e=[],n=0;n<arguments.length;n++)e[n]=arguments[n];return a.getLanguageServiceWorker.apply(a,e)},u=e.languageId;n.push(monaco.languages.registerCompletionItemProvider(u,new r.CompletionAdapter(c))),n.push(monaco.languages.registerHoverProvider(u,new r.HoverAdapter(c))),n.push(monaco.languages.registerDocumentSymbolProvider(u,new r.DocumentSymbolAdapter(c))),n.push(monaco.languages.registerDocumentFormattingEditProvider(u,new r.DocumentFormattingEditProvider(c))),n.push(monaco.languages.registerDocumentRangeFormattingEditProvider(u,new r.DocumentRangeFormattingEditProvider(c))),n.push(new r.DiagnostcsAdapter(u,c)),n.push(monaco.languages.setTokensProvider(u,o.createTokenizationSupport(!0))),n.push(monaco.languages.setLanguageConfiguration(u,i))};var i={wordPattern:/(-?\d*\.\d\w*)|([^\[\{\]\}\:\"\,\s]+)/g,comments:{lineComment:"//",blockComment:["/*","*/"]},brackets:[["{","}"],["[","]"]],autoClosingPairs:[{open:"{",close:"}",notIn:["string"]},{open:"[",close:"]",notIn:["string"]},{open:'"',close:'"',notIn:["string"]}]}}));