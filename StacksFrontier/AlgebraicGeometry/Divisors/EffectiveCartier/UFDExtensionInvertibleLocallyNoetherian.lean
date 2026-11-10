module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal

/-!
# Extending an invertible module across a factorial locus: the locally Noetherian case

Let `X` be a locally Noetherian scheme and `U ⊆ X` an open subscheme such that the local ring
`𝒪_{X, x}` is a unique factorization domain at every point `x` outside `U`. Then every invertible
`𝒪_U`-module is the restriction of an invertible `𝒪_X`-module. This is
[Stacks, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9); no quasi-compactness is assumed,
so this is the tag itself and not the Noetherian case of
`AlgebraicGeometry.exists_isInvertible_pullback_iso_of_uniqueFactorization`.

## The argument

The source extends `ℒ` over one affine chart at a time and assembles the chart extensions with
Zorn's lemma, the comparison isomorphism `β` between two extensions being *unique* after a
reduction to a schematically dense `U`. Uniqueness is what makes the comparisons of a chain
compose correctly, and it is the only thing the reduction is used for.

The assembly below replaces uniqueness by **rigidity**. A `Stacks.UFDExtensionZorn.Sys` — a
extension datum — carries not just the opens extended over but, as *data*, a module on each
chart and the comparison of each pair of charts on sections, with the restriction law and the
cocycle condition of Tag 00AM. Extension data are ordered by "has all the charts, and
compares them by the very same comparisons". Then:

* a chain of extension data has an upper bound with no choice to make: its charts are all the
  charts of all its members and its comparisons are theirs, well defined because any two charts
  of a chain lie in a common member (`Stacks.UFDExtensionZorn.Sys.chainBound`);
* a extension datum that misses a point can be enlarged by an affine chart around that point
  (`Stacks.UFDExtensionZorn.Sys.exists_le_mem_support`), which is where the affine-chart step
  `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization`, and
  with it Tag 0BD8 and the unique factorization hypothesis, is used;
* so a maximal extension datum covers `X`, and the module it glues to is the extension.

The reduction to a dense and schematically dense `U` therefore does not appear, and neither does
any statement about uniqueness of comparisons.

## Enlarging a extension datum

Adding the chart `(W, A)` needs the comparison of `A` with each old chart over the opens
contained in both. All of these are taken through the module `G` the old charts glue to
(`Stacks.UFDExtensionZorn.Sys.glued`): with `S` the open the old charts cover, an open contained
in `W` and in an old chart is contained in `S ⊓ W`, where `G` and `A` are compared by hypothesis,
and the comparison of `G` with an old chart is Tag 00AM's chart comparison
(`Stacks.UFDExtensionZorn.Sys.sigma`). The cocycle condition for a new pair is then the
compatibility `Stacks.SheafOfModules.OModuleGlueData.trans_chartLinearEquiv` of the chart
comparisons with the comparisons of the datum. Over an open contained in no old chart the only
pair to compare is the new chart with itself, and the comparison is the identity.

## Main results

* `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isLocallyNoetherian`: Tag 0BD9.
* `Stacks.UFDExtensionZorn.Sys.exists_isInvertible_restrict_iso`: the same for a sheaf of
  `𝒪_X`-modules invertible on `U`, which is the form the Zorn argument produces.
* `Stacks.UFDExtensionZorn.Sys.chainBound`, `Stacks.UFDExtensionZorn.Sys.insertChart`: the two
  steps of Zorn's lemma.
* `Stacks.UFDExtensionZorn.isInvertible_restrict_iSup`: invertibility of a restriction propagates
  to a supremum of opens.

## References

* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
* [Stacks Project, Tag 0BD8](https://stacks.math.columbia.edu/tag/0BD8)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.UFDExtensionZorn

variable {X : Scheme.{u}}

/-- The ring of functions on an open of a scheme, in the spelling the glueing datum of Tag 00AM
uses for its scalars. -/
abbrev Fn (X : Scheme.{u}) (Z : X.Opens) : Type u := ToType (X.ringCatSheaf.obj.obj (op Z))

/-- The module of sections of a sheaf of modules over an open. -/
abbrev Sec (M : X.Modules) (Z : X.Opens) : Type u := ToType (M.val.obj (op Z))

/-- Transport of the module of sections along an equality of sheaves of modules. -/
def secEquiv {A B : X.Modules} (e : A = B) (Z : X.Opens) : Sec A Z ≃ₗ[Fn X Z] Sec B Z :=
  @Eq.rec X.Modules A (fun C _ => Sec A Z ≃ₗ[Fn X Z] Sec C Z) (LinearEquiv.refl _ _) B e

@[simp] theorem secEquiv_rfl (A : X.Modules) (Z : X.Opens) :
    secEquiv (rfl : A = A) Z = LinearEquiv.refl _ _ := rfl

/-- The transport of sections commutes with the restriction maps. -/
theorem secEquiv_map {A B : X.Modules} (e : A = B) {Z W : X.Opens} (h : W ≤ Z) (s : Sec A Z) :
    secEquiv e W (A.val.map (homOfLE h).op s) = B.val.map (homOfLE h).op (secEquiv e Z s) := by
  subst e; rfl

/-- Two transports of sections compose to a transport of sections. -/
theorem secEquiv_comp {A B C : X.Modules} (e : A = B) (e' : B = C) (e'' : A = C) (Z : X.Opens)
    (s : Sec A Z) : secEquiv e' Z (secEquiv e Z s) = secEquiv e'' Z s := by
  subst e; subst e'; rfl

/-- **Invertibility of a restriction propagates to a supremum of opens.** If a sheaf of modules
restricts to an invertible sheaf on each member of a family of opens, it restricts to an
invertible sheaf on their supremum. -/
theorem isInvertible_restrict_iSup (M : X.Modules) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (V i).toScheme.sheaf.obj
      (V i).toScheme.ringCatSheaf.property (M.restrict (V i).ι)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (⨆ i, V i : X.Opens).toScheme.sheaf.obj
      (⨆ i, V i : X.Opens).toScheme.ringCatSheaf.property
      (M.restrict (⨆ i, V i : X.Opens).ι) := by
  refine Stacks.UFDExtensionGlobal.isInvertible_of_isInvertible_restrict _
    (fun i => (⨆ i, V i : X.Opens).ι ⁻¹ᵁ V i) ?_ ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
    exact ⟨i, hi⟩
  · intro i
    exact Stacks.UFDExtensionGlobal.isInvertible_restrict_of_range_eq
      (X.homOfLE (le_iSup V i)) ((⨆ i, V i : X.Opens).ι ⁻¹ᵁ V i).ι
      (Stacks.UFDExtensionGlobal.range_eq_of_opensRange_eq (by simp)) _
      (Stacks.UFDExtensionGlobal.isInvertible_of_iso
        (Stacks.UFDExtensionGlobal.restrictCongrComp (X.homOfLE_ι (le_iSup V i)) M) (hV i))

/-- A chart of a extension datum: an open of `X` together with a sheaf of `𝒪_X`-modules that is
invertible on it. -/
structure Chart (X : Scheme.{u}) where
  /-- The open the chart is carried by. -/
  opn : X.Opens
  /-- The sheaf of `𝒪_X`-modules the chart attaches to its open. -/
  mod : X.Modules

/-- **A extension datum of `N` across the charts it has already been extended over.** A finite
or infinite family of charts, pairwise compared on sections over the opens contained in two of
them, with the cocycle condition; the distinguished chart `(U, N)` is a member. The comparisons
are recorded as data, so a extension datum is *rigid*: it can be enlarged by one more chart
without disturbing the comparisons it already has, which is what makes Zorn's lemma apply. -/
structure Sys (X : Scheme.{u}) (U : X.Opens) (N : X.Modules) where
  /-- The charts extended over so far. -/
  charts : Set (Chart X)
  /-- The open `U` with the module `N` is one of the charts. -/
  base_mem : (⟨U, N⟩ : Chart X) ∈ charts
  /-- A chart is determined by its open. -/
  opn_inj : ∀ c ∈ charts, ∀ d ∈ charts, c.opn = d.opn → c = d
  /-- The module of a chart is invertible on the chart's open. -/
  isInvertible : ∀ c ∈ charts,
    AlgebraicGeometry.SheafOfModules.IsInvertible c.opn.toScheme.sheaf.obj
      c.opn.toScheme.ringCatSheaf.property (c.mod.restrict c.opn.ι)
  /-- The comparison of two charts on sections over an open contained in both. -/
  tr : ∀ c ∈ charts, ∀ d ∈ charts, ∀ Z : X.Opens, Z ≤ c.opn → Z ≤ d.opn →
    Sec c.mod Z ≃ₗ[Fn X Z] Sec d.mod Z
  /-- The comparisons commute with the restriction maps. -/
  tr_map : ∀ (c : Chart X) (hc : c ∈ charts) (d : Chart X) (hd : d ∈ charts) (Z W : X.Opens)
      (hZc : Z ≤ c.opn) (hZd : Z ≤ d.opn) (hWZ : W ≤ Z) (s : Sec c.mod Z),
    tr c hc d hd W (hWZ.trans hZc) (hWZ.trans hZd) (c.mod.val.map (homOfLE hWZ).op s)
      = d.mod.val.map (homOfLE hWZ).op (tr c hc d hd Z hZc hZd s)
  /-- The comparisons satisfy the cocycle condition. -/
  tr_trans : ∀ (c : Chart X) (hc : c ∈ charts) (d : Chart X) (hd : d ∈ charts) (e : Chart X)
      (he : e ∈ charts) (Z : X.Opens) (hZc : Z ≤ c.opn) (hZd : Z ≤ d.opn) (hZe : Z ≤ e.opn)
      (s : Sec c.mod Z),
    tr d hd e he Z hZd hZe (tr c hc d hd Z hZc hZd s) = tr c hc e he Z hZc hZe s

namespace Sys

variable {U : X.Opens} {N : X.Modules}

/-- **The ordering of extension data.** One extension datum precedes another if the second
has all the charts of the first and compares them exactly as the first does. The comparisons are
required to agree *on the nose*, which is why no uniqueness statement about them is needed. -/
structure Le (p q : Sys X U N) : Prop where
  /-- Every chart of `p` is a chart of `q`. -/
  subset : p.charts ⊆ q.charts
  /-- On the charts of `p`, the comparisons of `q` are those of `p`. -/
  tr_eq : ∀ (c : Chart X) (hc : c ∈ p.charts) (d : Chart X) (hd : d ∈ p.charts) (Z : X.Opens)
      (hZc : Z ≤ c.opn) (hZd : Z ≤ d.opn),
    q.tr c (subset hc) d (subset hd) Z hZc hZd = p.tr c hc d hd Z hZc hZd

theorem Le.refl (p : Sys X U N) : Le p p := ⟨fun _ h => h, fun _ _ _ _ _ _ _ => rfl⟩

theorem Le.trans {p q r : Sys X U N} (h₁ : Le p q) (h₂ : Le q r) : Le p r where
  subset := h₁.subset.trans h₂.subset
  tr_eq c hc d hd Z hZc hZd :=
    (h₂.tr_eq c (h₁.subset hc) d (h₁.subset hd) Z hZc hZd).trans (h₁.tr_eq c hc d hd Z hZc hZd)

/-- **The smallest extension datum:** the single chart `(U, N)`. -/
def base (U : X.Opens) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (N.restrict U.ι)) :
    Sys X U N where
  charts := {⟨U, N⟩}
  base_mem := rfl
  opn_inj c hc d hd _ := hc.trans hd.symm
  isInvertible c hc := by subst hc; exact hN
  tr c hc d hd Z _ _ := secEquiv (congrArg Chart.mod (hc.trans hd.symm)) Z
  tr_map c hc d hd Z W hZc hZd hWZ s := secEquiv_map _ hWZ s
  tr_trans c hc d hd e he Z hZc hZd hZe s := secEquiv_comp _ _ _ Z s

/-- The opens carrying a chart. -/
def opens (p : Sys X U N) : Set X.Opens := {V | ∃ c ∈ p.charts, c.opn = V}

/-- The chart carried by an open of `p.opens`. -/
noncomputable def chartOf (p : Sys X U N) (V : p.opens) : Chart X := V.2.choose

theorem chartOf_mem (p : Sys X U N) (V : p.opens) : p.chartOf V ∈ p.charts := V.2.choose_spec.1

theorem chartOf_opn (p : Sys X U N) (V : p.opens) : (p.chartOf V).opn = (V : X.Opens) :=
  V.2.choose_spec.2

/-- A chart is the chart chosen for its own open. -/
theorem chartOf_eq (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) :
    p.chartOf ⟨c.opn, ⟨c, hc, rfl⟩⟩ = c :=
  p.opn_inj _ (p.chartOf_mem _) c hc (p.chartOf_opn _)

/-- **The glueing datum of Tag 00AM carried by a extension datum.** -/
noncomputable def data (p : Sys X U N) :
    Stacks.SheafOfModules.OModuleGlueData X.ringCatSheaf
      (fun V : p.opens => (p.chartOf V).opn) :=
  Stacks.SheafOfModules.OModuleGlueData.ofModules (fun V => (p.chartOf V).mod)
    (fun i j {Z} hi hj => p.tr _ (p.chartOf_mem i) _ (p.chartOf_mem j) Z hi hj)
    (fun i j {Z W} => p.tr_map _ (p.chartOf_mem i) _ (p.chartOf_mem j) Z W)
    (fun i j k {Z} => p.tr_trans _ (p.chartOf_mem i) _ (p.chartOf_mem j) _ (p.chartOf_mem k) Z)

/-- **The sheaf of modules a extension datum glues to.** -/
noncomputable def glued (p : Sys X U N) : X.Modules := p.data.gluedModules

/-- An open contained in a chart's open is contained in the open of the chart chosen for it. -/
theorem le_chartOf_opn (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) {Z : X.Opens}
    (h : Z ≤ c.opn) : Z ≤ (p.chartOf ⟨c.opn, ⟨c, hc, rfl⟩⟩).opn :=
  h.trans (le_of_eq (p.chartOf_opn ⟨c.opn, ⟨c, hc, rfl⟩⟩).symm)

/-- **The comparison of the glued module with a chart's module, on sections.** -/
noncomputable def sigma (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) (Z : X.Opens)
    (h : Z ≤ c.opn) : Sec p.glued Z ≃ₗ[Fn X Z] Sec c.mod Z :=
  (p.data.chartLinearEquiv ⟨c.opn, ⟨c, hc, rfl⟩⟩ (p.le_chartOf_opn hc h)).trans
    (secEquiv (congrArg Chart.mod (p.chartOf_eq hc)) Z)

theorem sigma_apply (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) (Z : X.Opens)
    (h : Z ≤ c.opn) (s : Sec p.glued Z) :
    p.sigma hc Z h s = secEquiv (congrArg Chart.mod (p.chartOf_eq hc)) Z
      (p.data.chartLinearEquiv ⟨c.opn, ⟨c, hc, rfl⟩⟩ (p.le_chartOf_opn hc h) s) := rfl

/-- A comparison read at charts replaced by equal ones. -/
theorem tr_congr (p : Sys X U N) {c c' d d' : Chart X} (hc : c ∈ p.charts) (hc' : c' ∈ p.charts)
    (hd : d ∈ p.charts) (hd' : d' ∈ p.charts) (ec : c = c') (ed : d = d') (Z : X.Opens)
    (h1 : Z ≤ c.opn) (h2 : Z ≤ d.opn) (h3 : Z ≤ c'.opn) (h4 : Z ≤ d'.opn) (s : Sec c.mod Z) :
    p.tr c' hc' d' hd' Z h3 h4 (secEquiv (congrArg Chart.mod ec) Z s)
      = secEquiv (congrArg Chart.mod ed) Z (p.tr c hc d hd Z h1 h2 s) := by
  subst ec; subst ed; rfl

/-- **The comparisons of the charts are the comparisons through the glued module.** -/
theorem tr_sigma (p : Sys X U N) {c d : Chart X} (hc : c ∈ p.charts) (hd : d ∈ p.charts)
    (Z : X.Opens) (hZc : Z ≤ c.opn) (hZd : Z ≤ d.opn) (s : Sec p.glued Z) :
    p.tr c hc d hd Z hZc hZd (p.sigma hc Z hZc s) = p.sigma hd Z hZd s := by
  exact (p.tr_congr (p.chartOf_mem _) hc (p.chartOf_mem _) hd (p.chartOf_eq hc)
      (p.chartOf_eq hd) Z (p.le_chartOf_opn hc hZc) (p.le_chartOf_opn hd hZd) hZc hZd _).trans
    (congrArg (fun x => secEquiv (congrArg Chart.mod (p.chartOf_eq hd)) Z x)
      (p.data.trans_chartLinearEquiv ⟨c.opn, ⟨c, hc, rfl⟩⟩ ⟨d.opn, ⟨d, hd, rfl⟩⟩
        (p.le_chartOf_opn hc hZc) (p.le_chartOf_opn hd hZd) s))

/-- The comparison with a chart commutes with the restriction maps. -/
theorem sigma_map (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) {Z W : X.Opens}
    (hZc : Z ≤ c.opn) (hWZ : W ≤ Z) (s : Sec p.glued Z) :
    p.sigma hc W (hWZ.trans hZc) (p.glued.val.map (homOfLE hWZ).op s)
      = c.mod.val.map (homOfLE hWZ).op (p.sigma hc Z hZc s) := by
  exact (congrArg (fun x => secEquiv (congrArg Chart.mod (p.chartOf_eq hc)) W x)
      (p.data.chartLinearEquiv_restrict ⟨c.opn, ⟨c, hc, rfl⟩⟩
        (p.le_chartOf_opn hc hZc) hWZ s)).trans
    (secEquiv_map (congrArg Chart.mod (p.chartOf_eq hc)) hWZ _)

/-- The glued module, restricted to the open of a chart, is the chart's module there. -/
noncomputable def chartRestrictIso (p : Sys X U N) (V : p.opens) :
    p.glued.restrict (p.chartOf V).opn.ι ≅ (p.chartOf V).mod.restrict (p.chartOf V).opn.ι :=
  Stacks.SheafOfModules.OModuleGlueData.ofModulesRestrictIso _ _ _ _ V

/-- **The open a extension datum has extended `N` over:** the union of the opens of its
charts. -/
noncomputable def support (p : Sys X U N) : X.Opens := ⨆ V : p.opens, (p.chartOf V).opn

theorem le_support (p : Sys X U N) {c : Chart X} (hc : c ∈ p.charts) : c.opn ≤ p.support :=
  le_of_eq (p.chartOf_opn ⟨c.opn, ⟨c, hc, rfl⟩⟩).symm |>.trans
    (le_iSup (fun V : p.opens => (p.chartOf V).opn) ⟨c.opn, ⟨c, hc, rfl⟩⟩)

/-- The glued module is invertible on the open of each chart. -/
theorem isInvertible_glued_chart (p : Sys X U N) (V : p.opens) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (p.chartOf V).opn.toScheme.sheaf.obj
      (p.chartOf V).opn.toScheme.ringCatSheaf.property
      (p.glued.restrict (p.chartOf V).opn.ι) :=
  Stacks.UFDExtensionGlobal.isInvertible_of_iso (p.chartRestrictIso V).symm
    (p.isInvertible _ (p.chartOf_mem V))

/-- **The glued module is invertible on the open the extension datum covers.** -/
theorem isInvertible_glued_support (p : Sys X U N) :
    AlgebraicGeometry.SheafOfModules.IsInvertible p.support.toScheme.sheaf.obj
      p.support.toScheme.ringCatSheaf.property (p.glued.restrict p.support.ι) :=
  isInvertible_restrict_iSup p.glued (fun V : p.opens => (p.chartOf V).opn)
    p.isInvertible_glued_chart

/-- **The glued module restricts on `U` to `N`.** -/
theorem glued_restrict_base (p : Sys X U N) :
    Nonempty (p.glued.restrict U.ι ≅ N.restrict U.ι) := by
  have h := p.chartOf_eq p.base_mem
  have e := p.chartRestrictIso ⟨(⟨U, N⟩ : Chart X).opn, ⟨⟨U, N⟩, p.base_mem, rfl⟩⟩
  rw [h] at e
  exact ⟨e⟩

/-- The comparison of two charts is the comparison through the glued module. -/
theorem sigma_symm_trans (p : Sys X U N) {d e : Chart X} (hd : d ∈ p.charts) (he : e ∈ p.charts)
    (Z : X.Opens) (hZd : Z ≤ d.opn) (hZe : Z ≤ e.opn) :
    (p.sigma hd Z hZd).symm.trans (p.sigma he Z hZe) = p.tr d hd e he Z hZd hZe := by
  refine LinearEquiv.ext fun t => ?_
  have h := p.tr_sigma hd he Z hZd hZe ((p.sigma hd Z hZd).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

section Insert

variable {U : X.Opens} {N : X.Modules} (p : Sys X U N) (V : X.Opens) (A : X.Modules)
  (τ : ∀ Z : X.Opens, Z ≤ V → Z ≤ p.support → Sec p.glued Z ≃ₗ[Fn X Z] Sec A Z)
  (hτ : ∀ (Z W : X.Opens) (hZV : Z ≤ V) (hZS : Z ≤ p.support) (hWZ : W ≤ Z)
    (s : Sec p.glued Z), τ W (hWZ.trans hZV) (hWZ.trans hZS)
        (p.glued.val.map (homOfLE hWZ).op s)
      = A.val.map (homOfLE hWZ).op (τ Z hZV hZS s))
  (hVnew : ∀ c ∈ p.charts, c.opn ≠ V)
  (hA : AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
    V.toScheme.ringCatSheaf.property (A.restrict V.ι))

/-- Two charts of a family enlarged by one chart on `V` that share an open not contained in the
open already covered are both the new chart. -/
theorem eq_of_not_le_support {d e : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (he : e ∈ insert (⟨V, A⟩ : Chart X) p.charts) {Z : X.Opens} (hZd : Z ≤ d.opn)
    (hZe : Z ≤ e.opn) (hZS : ¬ Z ≤ p.support) : d = e := by
  rcases hd with rfl | hd
  · rcases he with rfl | he
    · rfl
    · exact absurd (hZe.trans (p.le_support he)) hZS
  · exact absurd (hZd.trans (p.le_support hd)) hZS

open Classical in
/-- The comparison of the glued module of `p` with a chart of the family enlarged by `(V, A)`. -/
noncomputable def insTau (d : Chart X) (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (Z : X.Opens) (hZd : Z ≤ d.opn) (hZS : Z ≤ p.support) :
    Sec p.glued Z ≃ₗ[Fn X Z] Sec d.mod Z :=
  if hdn : d = (⟨V, A⟩ : Chart X) then
    (τ Z (hZd.trans (le_of_eq (congrArg Chart.opn hdn))) hZS).trans
      (secEquiv (congrArg Chart.mod hdn.symm) Z)
  else p.sigma (hd.resolve_left hdn) Z hZd

open Classical in
/-- On the new chart the comparison with the glued module is the given one. -/
theorem insTau_apply_of_eq {d : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (hdn : d = (⟨V, A⟩ : Chart X)) (Z : X.Opens) (hZd : Z ≤ d.opn) (hZS : Z ≤ p.support)
    (s : Sec p.glued Z) :
    p.insTau V A τ d hd Z hZd hZS s = secEquiv (congrArg Chart.mod hdn.symm) Z
      (τ Z (hZd.trans (le_of_eq (congrArg Chart.opn hdn))) hZS s) := by
  rw [insTau, dite_eq_left hdn]; rfl

open Classical in
/-- On a chart other than the new one the comparison with the glued module is the one `p` already
had. -/
theorem insTau_of_ne {d : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (hdn : d ≠ (⟨V, A⟩ : Chart X)) (Z : X.Opens) (hZd : Z ≤ d.opn) (hZS : Z ≤ p.support) :
    p.insTau V A τ d hd Z hZd hZS = p.sigma (hd.resolve_left hdn) Z hZd :=
  dite_eq_right hdn

include hVnew in
/-- On an old chart the comparison with the glued module is the one `p` already had. -/
theorem insTau_of_mem {d : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (hd' : d ∈ p.charts) (Z : X.Opens) (hZd : Z ≤ d.opn) (hZS : Z ≤ p.support) :
    p.insTau V A τ d hd Z hZd hZS = p.sigma hd' Z hZd :=
  dite_eq_right fun h => hVnew d hd' (congrArg Chart.opn h)

include hτ in
/-- The comparison of the glued module with a chart commutes with the restriction maps. -/
theorem insTau_map (d : Chart X) (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts) {Z W : X.Opens}
    (hZd : Z ≤ d.opn) (hZS : Z ≤ p.support) (hWZ : W ≤ Z) (s : Sec p.glued Z) :
    p.insTau V A τ d hd W (hWZ.trans hZd) (hWZ.trans hZS)
        (p.glued.val.map (homOfLE hWZ).op s)
      = d.mod.val.map (homOfLE hWZ).op (p.insTau V A τ d hd Z hZd hZS s) := by
  classical
  by_cases hdn : d = (⟨V, A⟩ : Chart X)
  · rw [p.insTau_apply_of_eq V A τ hd hdn W (hWZ.trans hZd) (hWZ.trans hZS)
      (p.glued.val.map (homOfLE hWZ).op s), p.insTau_apply_of_eq V A τ hd hdn Z hZd hZS s]
    exact (congrArg (fun x => secEquiv (congrArg Chart.mod hdn.symm) W x)
        (hτ Z W _ hZS hWZ s)).trans (secEquiv_map (congrArg Chart.mod hdn.symm) hWZ _)
  · rw [p.insTau_of_ne V A τ hd hdn W (hWZ.trans hZd) (hWZ.trans hZS),
      p.insTau_of_ne V A τ hd hdn Z hZd hZS]
    exact p.sigma_map (hd.resolve_left hdn) hZd hWZ s

open Classical in
/-- The comparison of two charts of the family enlarged by `(V, A)`. -/
noncomputable def insTr (d : Chart X) (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (e : Chart X) (he : e ∈ insert (⟨V, A⟩ : Chart X) p.charts) (Z : X.Opens) (hZd : Z ≤ d.opn)
    (hZe : Z ≤ e.opn) : Sec d.mod Z ≃ₗ[Fn X Z] Sec e.mod Z :=
  if hZS : Z ≤ p.support then
    (p.insTau V A τ d hd Z hZd hZS).symm.trans (p.insTau V A τ e he Z hZe hZS)
  else secEquiv (congrArg Chart.mod (p.eq_of_not_le_support V A hd he hZd hZe hZS)) Z

open Classical in
theorem insTr_pos {d e : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (he : e ∈ insert (⟨V, A⟩ : Chart X) p.charts) (Z : X.Opens) (hZd : Z ≤ d.opn)
    (hZe : Z ≤ e.opn) (hZS : Z ≤ p.support) (s : Sec d.mod Z) :
    p.insTr V A τ d hd e he Z hZd hZe s
      = p.insTau V A τ e he Z hZe hZS ((p.insTau V A τ d hd Z hZd hZS).symm s) := by
  rw [insTr, dite_eq_left hZS]; rfl

open Classical in
theorem insTr_neg {d e : Chart X} (hd : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (he : e ∈ insert (⟨V, A⟩ : Chart X) p.charts) (Z : X.Opens) (hZd : Z ≤ d.opn)
    (hZe : Z ≤ e.opn) (hZS : ¬ Z ≤ p.support) (s : Sec d.mod Z) :
    p.insTr V A τ d hd e he Z hZd hZe s
      = secEquiv (congrArg Chart.mod (p.eq_of_not_le_support V A hd he hZd hZe hZS)) Z s := by
  rw [insTr, dite_eq_right hZS]

/-- The comparison of a chart with itself is the identity. -/
@[simp] theorem insTr_self (d : Chart X) (hd hd' : d ∈ insert (⟨V, A⟩ : Chart X) p.charts)
    (Z : X.Opens) (hZd hZd' : Z ≤ d.opn) (s : Sec d.mod Z) :
    p.insTr V A τ d hd d hd' Z hZd hZd' s = s := by
  by_cases hZS : Z ≤ p.support
  · rw [p.insTr_pos V A τ hd hd' Z hZd hZd' hZS s]
    exact LinearEquiv.apply_symm_apply _ _
  · rw [p.insTr_neg V A τ hd hd' Z hZd hZd' hZS s]
    rfl

include hτ hVnew hA in
/-- **A extension datum enlarged by one chart.** The comparison of the new chart with an old one
is taken through the module the old charts glue to; over an open met by no old chart the two
charts compared are both the new one, and the comparison is the identity. -/
noncomputable def insertChart : Sys X U N where
  charts := insert (⟨V, A⟩ : Chart X) p.charts
  base_mem := Set.mem_insert_of_mem _ p.base_mem
  opn_inj d hd e he hde := by
    rcases hd with rfl | hd
    · rcases he with rfl | he
      · rfl
      · exact absurd hde.symm (hVnew e he)
    · rcases he with rfl | he
      · exact absurd hde (hVnew d hd)
      · exact p.opn_inj d hd e he hde
  isInvertible d hd := by
    rcases hd with rfl | hd
    · exact hA
    · exact p.isInvertible d hd
  tr := p.insTr V A τ
  tr_map d hd e he Z W hZd hZe hWZ s := by
    by_cases hZS : Z ≤ p.support
    · obtain ⟨g, rfl⟩ : ∃ g, s = p.insTau V A τ d hd Z hZd hZS g :=
        ⟨_, (LinearEquiv.apply_symm_apply _ _).symm⟩
      rw [p.insTr_pos V A τ hd he W (hWZ.trans hZd) (hWZ.trans hZe) (hWZ.trans hZS)
          (d.mod.val.map (homOfLE hWZ).op (p.insTau V A τ d hd Z hZd hZS g)),
        p.insTr_pos V A τ hd he Z hZd hZe hZS (p.insTau V A τ d hd Z hZd hZS g),
        LinearEquiv.symm_apply_apply, ← p.insTau_map V A τ hτ d hd hZd hZS hWZ g]
      exact (congrArg (fun x => p.insTau V A τ e he W (hWZ.trans hZe) (hWZ.trans hZS) x)
        (LinearEquiv.symm_apply_apply _ _)).trans (p.insTau_map V A τ hτ e he hZe hZS hWZ g)
    · obtain rfl := p.eq_of_not_le_support V A hd he hZd hZe hZS
      exact (p.insTr_self V A τ d hd he W (hWZ.trans hZd) (hWZ.trans hZe) _).trans
        (congrArg (fun x => d.mod.val.map (homOfLE hWZ).op x)
          (p.insTr_self V A τ d hd he Z hZd hZe s).symm)
  tr_trans d hd e he f hf Z hZd hZe hZf s := by
    by_cases hZS : Z ≤ p.support
    · rw [p.insTr_pos V A τ hd he Z hZd hZe hZS s,
        p.insTr_pos V A τ he hf Z hZe hZf hZS
          (p.insTau V A τ e he Z hZe hZS ((p.insTau V A τ d hd Z hZd hZS).symm s)),
        p.insTr_pos V A τ hd hf Z hZd hZf hZS s, LinearEquiv.symm_apply_apply]
    · obtain rfl := p.eq_of_not_le_support V A hd he hZd hZe hZS
      obtain rfl := p.eq_of_not_le_support V A hd hf hZd hZf hZS
      exact ((congrArg (fun x => p.insTr V A τ d he d hf Z hZe hZf x)
          (p.insTr_self V A τ d hd he Z hZd hZe s)).trans
        (p.insTr_self V A τ d he hf Z hZe hZf s)).trans
        (p.insTr_self V A τ d hd hf Z hZd hZf s).symm

theorem le_insertChart : Le p (p.insertChart V A τ hτ hVnew hA) where
  subset := Set.subset_insert _ _
  tr_eq d hd e he Z hZd hZe := by
    refine LinearEquiv.ext fun s => ?_
    change p.insTr V A τ d _ e _ Z hZd hZe s = _
    rw [p.insTr_pos V A τ _ _ Z hZd hZe (hZd.trans (p.le_support hd)) s,
      p.insTau_of_mem V A τ hVnew _ hd, p.insTau_of_mem V A τ hVnew _ he]
    exact LinearEquiv.congr_fun (p.sigma_symm_trans hd he Z hZd hZe) s

theorem mem_insertChart :
    (⟨V, A⟩ : Chart X) ∈ (p.insertChart V A τ hτ hVnew hA).charts := Set.mem_insert _ _

end Insert

section Chain

variable {U : X.Opens} {N : X.Modules} {C : Set (Sys X U N)}

theorem total (hC : IsChain Le C) {p q : Sys X U N} (hp : p ∈ C) (hq : q ∈ C) :
    Le p q ∨ Le q p := by
  by_cases h : p = q
  · subst h; exact Or.inl (Le.refl p)
  · exact hC hp hq h

theorem exists_upper (hC : IsChain Le C) {p q : Sys X U N} (hp : p ∈ C) (hq : q ∈ C) :
    ∃ r ∈ C, Le p r ∧ Le q r :=
  (total hC hp hq).elim (fun h => ⟨q, hq, h, Le.refl q⟩) fun h => ⟨p, hp, Le.refl p, h⟩

/-- The charts of all the members of a chain of extension data. -/
def chainCharts (C : Set (Sys X U N)) : Set (Chart X) := {d | ∃ p ∈ C, d ∈ p.charts}

theorem exists_common (hC : IsChain Le C) {d e : Chart X} (hd : d ∈ chainCharts C)
    (he : e ∈ chainCharts C) : ∃ p ∈ C, d ∈ p.charts ∧ e ∈ p.charts := by
  obtain ⟨p, hp, hdp⟩ := hd
  obtain ⟨q, hq, heq⟩ := he
  obtain ⟨r, hr, h₁, h₂⟩ := exists_upper hC hp hq
  exact ⟨r, hr, h₁.subset hdp, h₂.subset heq⟩

theorem exists_common₃ (hC : IsChain Le C) {d e f : Chart X} (hd : d ∈ chainCharts C)
    (he : e ∈ chainCharts C) (hf : f ∈ chainCharts C) :
    ∃ p ∈ C, d ∈ p.charts ∧ e ∈ p.charts ∧ f ∈ p.charts := by
  obtain ⟨p, hp, hdp, hep⟩ := exists_common hC hd he
  obtain ⟨q, hq, hfq⟩ := hf
  obtain ⟨r, hr, h₁, h₂⟩ := exists_upper hC hp hq
  exact ⟨r, hr, h₁.subset hdp, h₁.subset hep, h₂.subset hfq⟩

/-- The comparison of two charts of a chain, read in any member containing both. -/
noncomputable def chainTr (hC : IsChain Le C) (d : Chart X) (hd : d ∈ chainCharts C)
    (e : Chart X) (he : e ∈ chainCharts C) (Z : X.Opens) (hZd : Z ≤ d.opn) (hZe : Z ≤ e.opn) :
    Sec d.mod Z ≃ₗ[Fn X Z] Sec e.mod Z :=
  (exists_common hC hd he).choose.tr d (exists_common hC hd he).choose_spec.2.1 e
    (exists_common hC hd he).choose_spec.2.2 Z hZd hZe

/-- The comparison of a chain is the comparison of any member containing both charts. -/
theorem chainTr_eq (hC : IsChain Le C) {p : Sys X U N} (hp : p ∈ C) {d e : Chart X}
    (hdp : d ∈ p.charts) (hep : e ∈ p.charts) (hd : d ∈ chainCharts C)
    (he : e ∈ chainCharts C) (Z : X.Opens) (hZd : Z ≤ d.opn) (hZe : Z ≤ e.opn) :
    chainTr hC d hd e he Z hZd hZe = p.tr d hdp e hep Z hZd hZe := by
  rcases total hC hp (exists_common hC hd he).choose_spec.1 with h | h
  · exact h.tr_eq d hdp e hep Z hZd hZe
  · exact (h.tr_eq d (exists_common hC hd he).choose_spec.2.1 e
      (exists_common hC hd he).choose_spec.2.2 Z hZd hZe).symm

/-- **An upper bound of a nonempty chain of extension data.** All the charts of all the
members, compared as they already are. -/
noncomputable def chainBound (hC : IsChain Le C) {p₀ : Sys X U N} (hp₀ : p₀ ∈ C) : Sys X U N where
  charts := chainCharts C
  base_mem := ⟨p₀, hp₀, p₀.base_mem⟩
  opn_inj d hd e he hde := by
    obtain ⟨p, _, hdp, hep⟩ := exists_common hC hd he
    exact p.opn_inj d hdp e hep hde
  isInvertible d hd := by
    obtain ⟨p, _, hdp⟩ := hd
    exact p.isInvertible d hdp
  tr := chainTr hC
  tr_map d hd e he Z W hZd hZe hWZ s := by
    obtain ⟨p, hp, hdp, hep⟩ := exists_common hC hd he
    simp only [chainTr_eq hC hp hdp hep]
    exact p.tr_map d hdp e hep Z W hZd hZe hWZ s
  tr_trans d hd e he f hf Z hZd hZe hZf s := by
    obtain ⟨p, hp, hdp, hep, hfp⟩ := exists_common₃ hC hd he hf
    simp only [chainTr_eq hC hp hdp hep, chainTr_eq hC hp hep hfp, chainTr_eq hC hp hdp hfp]
    exact p.tr_trans d hdp e hep f hfp Z hZd hZe hZf s

theorem le_chainBound (hC : IsChain Le C) {p₀ : Sys X U N} (hp₀ : p₀ ∈ C) {p : Sys X U N}
    (hp : p ∈ C) : Le p (chainBound hC hp₀) where
  subset d hd := ⟨p, hp, (hd : d ∈ p.charts)⟩
  tr_eq d hd e he Z hZd hZe :=
    chainTr_eq (d := d) (e := e) hC hp hd he ⟨p, hp, hd⟩ ⟨p, hp, he⟩ Z hZd hZe

end Chain

section Extend

variable {U : X.Opens} {N : X.Modules}

theorem support_mono {p q : Sys X U N} (h : Le p q) : p.support ≤ q.support := by
  rw [support]
  exact iSup_le fun V => q.le_support (h.subset (p.chartOf_mem V))

/-- **The chart step of [Stacks, Tag 0BD9].** A extension datum that misses a point of a
locally Noetherian scheme can be enlarged by an affine chart around that point: on a Noetherian
affine chart the module the extension datum glues to is extended by the affine-chart step, and
the extension is compared with the glued module over the overlap. -/
theorem exists_le_mem_support [IsLocallyNoetherian X]
    (hUFD : ∀ y : X, y ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk y)) (p : Sys X U N)
    {x : X} (hx : x ∉ p.support) : ∃ q : Sys X U N, Le p q ∧ x ∈ q.support := by
  obtain ⟨W, hWaff, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  have : IsAffine W.toScheme := hWaff
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWaff.isCompact
  have : IsNoetherian W.toScheme := (isNoetherian_iff W.toScheme).2 ⟨inferInstance, inferInstance⟩
  have hUS : U ≤ p.support := p.le_support p.base_mem
  have hrange : Set.range ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι).base
      = Set.range (p.support ⊓ W : X.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    simp [Set.range_comp, Set.image_preimage_eq_inter_range]
  have hfac : (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι)
      (p.support ⊓ W : X.Opens).ι hrange).hom ≫ (p.support ⊓ W : X.Opens).ι
      = (W.ι ⁻¹ᵁ p.support).ι ≫ W.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have hfac' : (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι)
      (p.support ⊓ W : X.Opens).ι hrange).inv ≫ ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι)
      = (p.support ⊓ W : X.Opens).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (W.ι ⁻¹ᵁ p.support).toScheme.sheaf.obj (W.ι ⁻¹ᵁ p.support).toScheme.ringCatSheaf.property
      (p.glued.restrict ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι)) :=
    Stacks.UFDExtensionGlobal.isInvertible_restrict_of_fac hfac p.glued
      (Stacks.UFDExtensionGlobal.isInvertible_restrict_of_fac
        (X.homOfLE_ι (inf_le_left : (p.support ⊓ W : X.Opens) ≤ p.support)) p.glued
        p.isInvertible_glued_support)
  have hUFDW : ∀ y : W.toScheme, y ∉ W.ι ⁻¹ᵁ p.support →
      UniqueFactorizationMonoid (W.toScheme.presheaf.stalk y) := fun y hy =>
    (W.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      (hUFD _ fun h => hy (hUS h))
  obtain ⟨M, hM, ⟨eM⟩⟩ :=
    exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization (W := W.toScheme)
      (W.ι ⁻¹ᵁ p.support) (p.glued.restrict ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι)) hUFDW
  have hA : AlgebraicGeometry.SheafOfModules.IsInvertible W.toScheme.sheaf.obj
      W.toScheme.ringCatSheaf.property
      (((Scheme.Modules.pushforward W.ι).obj M).restrict W.ι) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app M).symm hM
  have e₁ : p.glued.restrict ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι) ≅
      ((Scheme.Modules.pushforward W.ι).obj M).restrict ((W.ι ⁻¹ᵁ p.support).ι ≫ W.ι) :=
    eM ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback (W.ι ⁻¹ᵁ p.support).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctor (W.ι ⁻¹ᵁ p.support).ι).mapIso
        ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app M).symm ≪≫
      ((Scheme.Modules.restrictFunctorComp (W.ι ⁻¹ᵁ p.support).ι W.ι).app
        ((Scheme.Modules.pushforward W.ι).obj M)).symm
  have ψ : p.glued.restrict (p.support ⊓ W : X.Opens).ι ≅
      ((Scheme.Modules.pushforward W.ι).obj M).restrict (p.support ⊓ W : X.Opens).ι :=
    Stacks.UFDExtensionGlobal.restrictIsoCongr hfac' e₁
  have hVnew : ∀ c ∈ p.charts, c.opn ≠ W := fun c hc h => hx (p.le_support hc (h ▸ hxW))
  refine ⟨p.insertChart W ((Scheme.Modules.pushforward W.ι).obj M)
    (fun Z hZW hZS => localAppEquiv ψ Z (le_inf hZS hZW)) ?_ hVnew hA, ?_, ?_⟩
  · intro Z Z' hZW hZS hZ'Z s
    exact (localAppFun_naturality ψ.hom (le_inf hZS hZW)
      (le_inf (hZ'Z.trans hZS) (hZ'Z.trans hZW)) (homOfLE hZ'Z) s).symm
  · exact p.le_insertChart W _ _ _ hVnew hA
  · exact Sys.le_support _ (p.mem_insertChart W _ _ _ hVnew hA) hxW

/-- **[Stacks, Tag 0BD9] for a sheaf of `𝒪_X`-modules.** Let `X` be a locally Noetherian scheme,
let `U ⊆ X` be an open whose complementary points have unique factorization local rings, and let
`N` be a sheaf of `𝒪_X`-modules whose restriction to `U` is invertible. Then there is an
invertible sheaf of `𝒪_X`-modules whose restriction to `U` is isomorphic to that of `N`. -/
theorem exists_isInvertible_restrict_iso [IsLocallyNoetherian X] (U : X.Opens) (N : X.Modules)
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x))
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (N.restrict U.ι)) :
    ∃ N' : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N' ∧
        Nonempty (N.restrict U.ι ≅ N'.restrict U.ι) := by
  have hbound : ∀ C : Set (Sys X U N), IsChain Le C → ∃ ub, ∀ a ∈ C, Le a ub := by
    intro C hC
    rcases C.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
    · exact ⟨base U N hN, fun a ha => absurd ha (Set.notMem_empty a)⟩
    · exact ⟨chainBound hC hp₀, fun a ha => le_chainBound hC hp₀ ha⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound Le.trans
  · have htop : m.support = ⊤ := by
      by_contra h
      obtain ⟨x, hx⟩ : ∃ x : X, x ∉ m.support := by
        by_contra hc
        exact h (TopologicalSpace.Opens.ext
          (Set.eq_univ_of_forall fun y => not_not.mp fun hy => hc ⟨y, hy⟩))
      obtain ⟨q, hq, hxq⟩ := exists_le_mem_support hUFD m hx
      exact hx (support_mono (hm q hq) hxq)
    exact ⟨m.glued, Stacks.UFDExtensionGlobal.isInvertible_of_isInvertible_restrict m.glued
      (fun _ : Unit => m.support) (by simp [htop]) fun _ => m.isInvertible_glued_support,
      m.glued_restrict_base.elim fun e => ⟨e.symm⟩⟩

end Extend

end Sys

end Stacks.UFDExtensionZorn

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0BD9].** Let `X` be a locally Noetherian scheme, let `U ⊆ X` be an open
subscheme, and let `L` be an invertible `𝒪_U`-module. If the local ring `𝒪_{X, x}` is a unique
factorization domain at every point `x` outside `U`, then `L` is the restriction of an invertible
`𝒪_X`-module. -/
@[stacks 0BD9 "the locally Noetherian case, i.e. the tag itself"]
theorem exists_isInvertible_pullback_iso_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (L : U.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L]
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ L' : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
        Nonempty (L ≅ (Scheme.Modules.pullback U.ι).obj L') := by
  have c : ((Scheme.Modules.pushforward U.ι).obj L).restrict U.ι ≅ L :=
    (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app L
  obtain ⟨L', hL', ⟨e⟩⟩ := Stacks.UFDExtensionZorn.Sys.exists_isInvertible_restrict_iso U
    ((Scheme.Modules.pushforward U.ι).obj L) hUFD
    (Stacks.UFDExtensionGlobal.isInvertible_of_iso c.symm ‹_›)
  exact ⟨L', hL', ⟨c.symm ≪≫ e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L'⟩⟩

end AlgebraicGeometry

end
