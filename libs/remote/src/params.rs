//! Parameter schemas shared by inspect consumers and their tool manifests.
//! Validation runs on the request thread, before a command can wait or mutate anything.

/// Top-level properties of a JSON-schema properties fragment. Nested properties and quoted
/// braces (descriptions, enums, anyOf) are skipped; the fragments are static trusted schemas.
pub fn properties(params: &str) -> Vec<(&str, &str)> {
    let mut fields = Vec::new();
    let (mut depth, mut quoted, mut escaped, mut start) = (0usize, false, false, 0usize);
    for (i, b) in params.bytes().enumerate() {
        if quoted {
            if escaped { escaped = false; }
            else if b == b'\\' { escaped = true; }
            else if b == b'"' { quoted = false; }
        } else {
            match b {
                b'"' => quoted = true,
                b'{' | b'[' => depth += 1,
                b'}' | b']' => depth -= 1,
                b',' if depth == 0 => {
                    field(&params[start..i], &mut fields);
                    start = i + 1;
                }
                _ => {}
            }
        }
    }
    field(&params[start..], &mut fields);
    fields
}

fn field<'a>(s: &'a str, fields: &mut Vec<(&'a str, &'a str)>) {
    let s = s.trim();
    if let Some((key, _)) = s.strip_prefix('"').and_then(|s| s.split_once('"')) {
        fields.push((key, s));
    }
}

/// `full` belongs to the cmd envelope, which consumes it before any family dispatch.
pub fn validate<'a>(keys: impl IntoIterator<Item = &'a str>, params: &str) -> Result<(), String> {
    let properties = properties(params);
    for key in keys {
        if key != "full" && !properties.iter().any(|(known, _)| *known == key) {
            let mut known: Vec<_> = properties.iter().map(|(key, _)| *key).collect();
            if !known.contains(&"full") { known.push("full"); }
            return Err(format!("unknown parameter {key:?}; known: {}", known.join(", ")));
        }
    }
    Ok(())
}

macro_rules! params {
    ($($key:literal : $ty:literal),* $(,)?) => {
        concat!($("\"", $key, "\":{\"type\":\"", $ty, "\"},",)*)
    };
}

macro_rules! ui_common {
    () => { params!("app": "string", "machine": "string", "w": "string", "json": "boolean", "timeout_ms": "integer") };
}
macro_rules! selectors {
    () => { params!("q": "string", "node": "string", "role": "string", "class": "string", "path": "string", "state": "string", "states": "string", "text": "string", "text~": "string", "value": "string", "value~": "string", "name~": "string", "nth": "integer", "id": "string", "actions": "string") };
}

/// Each UI verb has one parameter definition, used for both validation and the manifest.
pub fn ui(verb: &str) -> Option<&'static str> {
    Some(match verb {
        "" => concat!(ui_common!(), selectors!(), params!("name": "string", "action": "string", "depth": "integer")),
        "find" => concat!(ui_common!(), selectors!(), params!("name": "string", "action": "string")),
        "act" => concat!(ui_common!(), selectors!(), params!("action": "string", "name": "string", "v": "string", "t": "string", "from": "integer", "to": "integer", "dx": "number", "dy": "number", "ms": "number", "hz": "number", "legs": "integer", "x": "number", "y": "number", "b": "integer", "mods": "string", "wait": "boolean", "if_user_seq": "integer")),
        "type" => concat!(ui_common!(), selectors!(), params!("name": "string", "action": "string", "t": "string", "from": "integer", "to": "integer", "wait": "boolean", "if_user_seq": "integer")),
        "wait" => concat!(ui_common!(), selectors!(), params!("name": "string", "action": "string", "gone": "boolean", "changed": "boolean", "count": "integer")),
        "snap" => concat!(ui_common!(), params!("name": "string")),
        "diff" => concat!(ui_common!(), params!("a": "string", "b": "string")),
        "speak" => concat!(ui_common!(), selectors!(), params!("name": "string", "action": "string", "since": "integer")),
        "lint" => concat!(ui_common!()),
        "oscheck" => concat!(ui_common!(), params!("act": "boolean")),
        _ => return None,
    }.trim_end_matches(','))
}

/// HAL inspectors and the native sampler; full command words select the parameter schema.
pub fn inspect(words: &str) -> Option<&'static str> {
    Some(match words {
        "gpu" => "",
        "gpu device" => "",
        "gpu top" => params!("by": "string", "n": "integer"),
        "gpu idle" => params!("frames": "integer", "n": "integer"),
        "gpu snap" => "",
        "gpu diff" => "",
        "gpu path" => "",
        "hal pump" => "",
        "hal pace" => "",
        "hal shell" => "",
        "gpu prof start" => params!("s": "integer", "split": "integer", "hz": "number", "ablate": "string", "every": "integer", "as": "string"),
        "gpu prof stop" => params!("save": "string", "sid": "integer", "as": "string"),
        "gpu prof shader" => params!("save": "string", "as": "string"),
        "gpu prof status" => params!("as": "string"),
        "gpu prof frames" => params!("sid": "integer", "n": "integer", "as": "string"),
        "gpu prof frame" => params!("sid": "integer", "as": "string"),
        "gpu prof top" => params!("sid": "integer", "by": "string", "frames": "string", "n": "integer", "as": "string"),
        "gpu prof ablate" => params!("sid": "integer", "as": "string"),
        "gpu prof runs" => params!("sid": "integer", "pass": "string", "n": "integer", "as": "string"),
        "gpu prof lanes" => params!("sid": "integer", "width": "integer", "as": "string"),
        "gpu prof util" => params!("sid": "integer", "frames": "string", "as": "string"),
        "gpu prof diff" => params!("sid": "integer", "as": "string"),
        "cap grab" => params!("session": "integer", "window": "integer", "timeout": "integer", "file": "string"),
        "cap list" => "",
        "cap save" => "",
        "cap scanout" => params!("png": "string", "timeout": "integer"),
        "prof" => params!("s": "integer", "hz": "integer", "n": "integer", "wall": "boolean", "ev": "string", "threads": "string", "raw": "string", "save": "boolean"),
        "why-slow" => params!("s": "integer", "n": "integer"),
        "cap frame" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer"),
        "cap draws" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "pass": "string", "owner": "string", "sort": "string", "n": "integer", "pixels": "boolean"),
        "cap draw" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer"),
        "cap code" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer"),
        "cap rt" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "png": "string", "max": "integer", "mark": "boolean", "wire": "boolean"),
        "cap pixel" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "pass": "string"),
        "cap overdraw" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "png": "string", "max": "integer"),
        "cap mesh" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "n": "integer"),
        "cap tex" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "png": "string", "max": "integer"),
        "cap time" => params!("file": "string", "session": "integer", "window": "integer", "timeout": "integer", "n": "integer", "repeat": "integer"),
        _ => return None,
    }.trim_end_matches(','))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schemas_reject_unknown_parameters() {
        let nested = r#""value":{"anyOf":[{"type":"string"},{"type":"number"}],"description":"braces }, comma, and \"quote\""},"count":{"type":"integer"}"#;
        assert!(validate(["value", "count", "full"], nested).is_ok());
        assert!(validate(["type"], nested).unwrap_err().contains("known: value, count, full"));
        for verb in ["", "find", "act", "type", "wait", "snap", "diff", "speak", "lint", "oscheck"] {
            let schema = ui(verb).unwrap();
            assert!(validate(["timeout_ms", "json", "w", "app", "machine"], schema).is_ok());
            assert!(validate(["timeout"], schema).unwrap_err().contains("timeout_ms"));
        }
    }

    #[test]
    fn sampler_rejects_unknown_parameters() {
        let prof = inspect("prof").unwrap();
        assert!(validate(["s", "hz", "n", "wall", "ev", "threads", "raw", "save"], prof).is_ok());
        assert!(validate(["seconds"], prof).unwrap_err().contains("known: s, hz"));
        let slow = inspect("why-slow").unwrap();
        assert!(validate(["s", "n"], slow).is_ok());
        assert!(validate(["hz"], slow).is_err());
    }
}
