#!/usr/bin/env ruby
# frozen_string_literal: true

# Checks the Palomar submission surface of this repository against the
# mechanical requirements in
# https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
# (sections 2.1-2.5 and 3.1-3.2).  It needs only the Ruby standard library.
#
# Usage: ruby scripts/check-submission-files.rb [repository-root]

require "json"
require "yaml"

root = File.expand_path(ARGV.fetch(0, File.join(__dir__, "..")))
errors = []
warnings = []

def read(root, name)
  path = File.join(root, name)
  raise "missing #{name}" unless File.file?(path)
  File.read(path, encoding: "UTF-8")
end

# ---------------------------------------------------------------- Lake files
lakefiles = %w[lakefile.toml lakefile.lean].select { |f| File.file?(File.join(root, f)) }
errors << "expected exactly one of lakefile.toml / lakefile.lean, found #{lakefiles.inspect}" unless lakefiles.size == 1
errors << "lake-manifest.json must be committed" unless File.file?(File.join(root, "lake-manifest.json"))

begin
  toolchain = read(root, "lean-toolchain").strip
  errors << "lean-toolchain #{toolchain.inspect} is not of the form leanprover/lean4:vX.Y.Z[-rcN]" unless toolchain.match?(%r{\Aleanprover/lean4:v\d+\.\d+\.\d+(-rc\d+)?\z})
rescue => e
  errors << e.message
end

begin
  manifest = JSON.parse(read(root, "lake-manifest.json"))
  manifest.fetch("packages", []).each do |pkg|
    next unless pkg["type"] == "git"
    url = pkg["url"].to_s
    rev = pkg["rev"].to_s
    errors << "manifest package #{pkg["name"]}: url #{url} is not a plain https://github.com/owner/repo URL" unless url.match?(%r{\Ahttps://github\.com/[^/?#\s]+/[^/?#\s]+(\.git)?\z})
    errors << "manifest package #{pkg["name"]}: rev #{rev} is not a 40-character lowercase SHA" unless rev.match?(/\A[0-9a-f]{40}\z/)
  end
rescue => e
  errors << "lake-manifest.json: #{e.message}"
end

# ------------------------------------------------------------------ licence
licence_names = Dir.children(root).select do |f|
  f.match?(/\A(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?\z/i) && File.file?(File.join(root, f))
end
errors << "expected exactly one root licence file, found #{licence_names.inspect}" unless licence_names.size == 1
licence_text = licence_names.size == 1 ? read(root, licence_names.first) : ""
errors << "LICENSE does not look like Apache License 2.0" unless licence_text.include?("Apache License") && licence_text.include?("Version 2.0")

# ------------------------------------------------------------ comparator.json
begin
  comparator = JSON.parse(read(root, "comparator.json"))
  errors << "comparator.json must be a JSON object" unless comparator.is_a?(Hash)
  allowed = %w[challenge_module solution_module theorem_names permitted_axioms definition_names enable_nanoda]
  extra = comparator.keys - allowed
  errors << "comparator.json has unexpected keys #{extra.inspect}" unless extra.empty?
  %w[challenge_module solution_module theorem_names permitted_axioms].each do |k|
    errors << "comparator.json is missing #{k}" unless comparator.key?(k)
  end
  module_re = /\A[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*\z/
  %w[challenge_module solution_module].each do |k|
    errors << "comparator.json #{k} #{comparator[k].inspect} is not a valid module name" unless comparator[k].to_s.match?(module_re)
  end
  errors << "comparator.json challenge_module and solution_module must differ" if comparator["challenge_module"] == comparator["solution_module"]
  names = comparator.fetch("theorem_names", [])
  errors << "comparator.json theorem_names must be a nonempty array of nonempty strings" unless names.is_a?(Array) && !names.empty? && names.all? { |n| n.is_a?(String) && !n.empty? }
  defs = comparator.fetch("definition_names", [])
  errors << "comparator.json definition_names must be an array of nonempty strings" unless defs.is_a?(Array) && defs.all? { |n| n.is_a?(String) && !n.empty? }
  axioms = comparator.fetch("permitted_axioms", [])
  bad = axioms - %w[propext Quot.sound Classical.choice]
  errors << "comparator.json permitted_axioms contains #{bad.inspect}" unless bad.empty?

  # The challenge and solution sources must exist and the declared names must be stated in both.
  [["challenge_module", comparator["challenge_module"]], ["solution_module", comparator["solution_module"]]].each do |k, mod|
    path = File.join(root, "#{mod.to_s.tr(".", "/")}.lean")
    errors << "#{k}: source file #{path} not found" unless File.file?(path)
  end
  challenge_path = File.join(root, "#{comparator["challenge_module"].to_s.tr(".", "/")}.lean")
  if File.file?(challenge_path)
    src = File.read(challenge_path, encoding: "UTF-8")
    lines = src.lines.size
    bytes = src.bytesize
    errors << "Challenge is #{lines} lines (> 1000)" if lines > 1000
    errors << "Challenge is #{bytes} bytes (> 100 KiB)" if bytes > 100 * 1024
    warnings << "Challenge is #{lines} lines (> 300; harder to audit)" if lines > 300
    warnings << "Challenge is #{bytes} bytes (> 32 KiB; harder to audit)" if bytes > 32 * 1024
    src.scan(/^import\s+(\S+)/).flatten.each do |imp|
      errors << "Challenge imports #{imp}, which is neither Lean core nor Mathlib" unless imp.match?(/\A(Mathlib|Lean|Init|Std|Batteries)(\.|\z)/)
    end
    (names + defs).each do |n|
      short = n.split(".").last
      errors << "Challenge does not declare #{n} (no `theorem|def ... #{short}`)" unless src.match?(/^\s*(theorem|lemma|def|noncomputable def)\s+#{Regexp.escape(short)}\b/)
    end
  end
rescue => e
  errors << "comparator.json: #{e.message}"
end

# --------------------------------------------------------- formalization.yaml
begin
  text = read(root, "formalization.yaml")
  errors << "formalization.yaml is #{text.bytesize} bytes (> 256 KiB)" if text.bytesize > 256 * 1024
  errors << "formalization.yaml contains retained TEMPLATE values" if text.match?(/\bTEMPLATE\b/)
  meta = YAML.safe_load(text, aliases: false)
  errors << "formalization.yaml must be a mapping" unless meta.is_a?(Hash)
  meta ||= {}

  project = meta.fetch("project", {})
  name = project["name"].to_s
  errors << "project.name must be 1..300 characters" unless (1..300).cover?(name.length)
  desc = project["description"].to_s
  errors << "project.description must be 1..10000 characters" unless (1..10_000).cover?(desc.length)
  %w[authors responsible_maintainers].each do |k|
    list = project[k]
    ok = list.is_a?(Array) && !list.empty? && list.all? { |x| (x.is_a?(String) && !x.strip.empty?) || (x.is_a?(Hash) && !x["name"].to_s.strip.empty?) }
    errors << "project.#{k} must be a nonempty list of names" unless ok
  end
  errors << "project.license must be Apache-2.0 to match LICENSE" unless project["license"] == "Apache-2.0"
  errors << "repository must be omitted for a substantive development" if meta.key?("repository") && meta["repository"].to_h.key?("substantive_formalization") == false && meta["repository"].to_h["role"] == "thin-wrapper"

  cls = meta.fetch("classification", {})
  arxiv = cls["arxiv"]
  errors << "classification.arxiv must list 1..8 distinct arXiv codes" unless arxiv.is_a?(Array) && (1..8).cover?(arxiv.size) && arxiv.uniq.size == arxiv.size && arxiv.all? { |c| c.to_s.match?(/\A[a-z\-]+(\.[A-Z]{2})?\z/) }
  msc = cls["msc2020"] || []
  errors << "classification.msc2020 must list at most 8 distinct five-character MSC codes" unless msc.is_a?(Array) && msc.size <= 8 && msc.uniq.size == msc.size && msc.all? { |c| c.to_s.match?(/\A\d\d[A-Z-]\d\d\z/) }

  sources = meta["sources"]
  if sources.is_a?(Array) && !sources.empty?
    rels = %w[formalizes adapts independently-proves background other]
    types = %w[paper book web\ discussion folklore original-proof other]
    sources.each_with_index do |s, i|
      errors << "sources[#{i}] needs a nonempty title" if s["title"].to_s.strip.empty?
      errors << "sources[#{i}].relationship #{s["relationship"].inspect} is not one of #{rels.inspect}" unless rels.include?(s["relationship"])
      errors << "sources[#{i}].type #{s["type"].inspect} is not one of #{types.inspect}" if s.key?("type") && !types.include?(s["type"])
      (s["contributors"] || []).each do |c|
        errors << "sources[#{i}].contributors entries need name and role (<= 200 chars)" unless c.is_a?(Hash) && !c["name"].to_s.empty? && (1..200).cover?(c["role"].to_s.length)
      end
    end
    originals = sources.select { |s| s["type"] == "original-proof" }
    substantive = sources.select { |s| %w[formalizes adapts independently-proves].include?(s["relationship"]) }
    if originals.any?
      errors << "original-proof sources must have relationship: other" unless originals.all? { |s| s["relationship"] == "other" }
      errors << "an original result may not also formalize/adapt/independently-prove a source" unless substantive.empty?
    else
      errors << "a source-based result needs at least one formalizes/adapts/independently-proves source" if substantive.empty?
    end
  else
    errors << "sources must be a nonempty list"
  end

  (meta["related_formalizations"] || []).each_with_index do |r, i|
    errors << "related_formalizations[#{i}] needs an id" if r["id"].to_s.empty?
  end

  methods = meta.fetch("automation", {})["methods"]
  errors << "automation.methods must be a nonempty list of mappings with a nonempty method" unless methods.is_a?(Array) && !methods.empty? && methods.all? { |m| m.is_a?(Hash) && !m["method"].to_s.strip.empty? }
  errors << "review.status must be a nonempty string" if meta.fetch("review", {})["status"].to_s.strip.empty?

  status = meta.fetch("status", {})
  %w[sorry_count sorry_in_definitions].each do |k|
    errors << "status.#{k} must be an unquoted nonnegative integer" unless status[k].is_a?(Integer) && status[k] >= 0
  end
rescue => e
  errors << "formalization.yaml: #{e.message}"
end

# ------------------------------------------------------- compiled artifacts
bad_suffixes = %w[.olean .ilean .a .bc .dll .dylib .o .obj .so .trace]
Dir.glob(File.join(root, "**", "*"), File::FNM_DOTMATCH).each do |f|
  next unless File.file?(f)
  rel = f.sub("#{root}/", "")
  next if rel.start_with?(".lake/", ".git/", ".cache/") || rel.include?("/.lake/")
  errors << "compiled artifact committed outside .lake: #{rel}" if bad_suffixes.include?(File.extname(rel))
end

warnings.each { |w| warn "warning: #{w}" }
if errors.empty?
  puts "submission files OK"
else
  errors.each { |e| warn "error: #{e}" }
  exit 1
end
