module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs

/-!
# Descending a vector field along a morphism of schemes

Let `ν : Y ⟶ X` be a morphism of schemes over a field `k` whose comorphism `ν^♯` is injective
on sections over every open of `X`, so that `𝒪_X` is a subsheaf of `ν_* 𝒪_Y`. A vector field
`D'` on `Y` — a `k`-derivation of `𝒪_Y` in the sense of Section 53.26 — then comes from a
vector field on `X` exactly when it carries that subsheaf into itself, and the vector field it
comes from is unique. Moreover carrying the subsheaf into itself is a *local* condition on `X`:
it is enough that every local section be carried back into `𝒪_X` in a neighbourhood of each of
its points.

## Main definitions

* `Stacks.Curves.SheafDerivationOf` — `Der_k(𝒪_Y, 𝒪_Y)` for a structure morphism
  `g : Y ⟶ Spec k` given explicitly rather than by a `Y.Over (Spec k)` instance.
* `Stacks.Curves.SheafDerivationOf.onSections` — the value of a vector field on a local
  section, read as a local section.
* `Stacks.Curves.Preserves` — `D'` carries `ν^♯ Γ(X, U)` into itself for every open `U` of `X`.
* `Stacks.Curves.Preserves.descend` — the vector field on `X` that `D'` then comes from.

## Main results

* `Stacks.Curves.existsUnique_descend_iff_preserves` — with `ν^♯` injective on sections,
  `D'` is the image of a unique vector field on `X` if and only if it preserves `ν^♯ 𝒪_X`.
* `Stacks.Curves.preserves_of_forall_mem_exists` — preserving `ν^♯ 𝒪_X` is a local condition.
* `Stacks.Curves.SheafDerivationOf.ext'` — a vector field is determined by its values on
  local sections.
* `Stacks.Curves.app_injective_of_stalkFunctor_map_injective` and
  `Stacks.Curves.app_normalization_injective` — the injectivity hypothesis holds for the
  normalization of a reduced scheme.

## Implementation notes

A vector field is `AlgebraicGeometry.SheafOfModules.SheafDerivation` along the structural map
`g⁻¹ 𝒪_{Spec k} ⟶ 𝒪_Y`, which is the shape in which `Stacks.Curves.SheafDerivation` states Tag
0E66; the data is an additive map `Γ(Y, U) → Γ(Y, U)` for every open `U`, subject to the
Leibniz rule, compatibility with restriction, and the vanishing on the structural map. Here the
structure morphism is an explicit argument because the globalisation compares two of them at
once — `hX : X ⟶ Spec k` and its composite `ν ≫ hX` — and an equation between structure
morphisms would otherwise have to be transported across the opens the sections live on.

The descended field is built by choosing, over each open, the section whose pullback is
`D' (ν^♯ s)`; injectivity of `ν^♯` makes that section unique, hence additive, Leibniz and
compatible with restriction because its pullback is. The remaining axiom — vanishing on
`g⁻¹ 𝒪_{Spec k}`, whose sections over an open of `X` are a sheafified colimit and so not
directly computable — is supplied by
`AlgebraicGeometry.SheafOfModules.ofComorphism`, which upgrades a derivation along any
morphism of presheaves of rings (here the constant presheaf of integers, which imposes nothing)
to one along the structural map, provided it annihilates `hX^♯ b` for every local section `b`
of `𝒪_{Spec k}`. That last condition holds because `ν^♯ (hX^♯ b) = (ν ≫ hX)^♯ b`, which `D'`
annihilates.

Locality is the gluing argument: the local witnesses agree on overlaps because `ν^♯` is
injective there, so they glue to a section of `𝒪_X` over the whole open, and the glued section
has the required pullback because `𝒪_Y` is separated. The index set of the cover is the set of
points of the open, which lies in the same universe as the scheme, as the unique-gluing API
requires.

## What is not done here

This file does not prove Tag 0E68. That lemma identifies `Der_k(𝒪_X, 𝒪_X)`, for `X` a proper
connected at-worst-nodal curve over an algebraically closed field, with the vector fields on
the normalization `X^ν` fixing every point where `ν` is not an isomorphism, and its proof runs
through the exact sequence `0 → 𝒪_{X,x} → 𝒪_{X^ν,x'} × 𝒪_{X^ν,x''} → k → 0` at a node of Tag
0C1X. Nothing in this file verifies the hypothesis of `preserves_of_forall_mem_exists` at a
node. The exact sequence itself is
`Stacks.Curves.exact_integralClosure_of_isNodalAlgebra`, in equalizer form, and the descent it
yields is `Stacks.Curves.existsUnique_descend_normalization_of_fixes`, which takes the node data
at each point of `X` as a hypothesis rather than deriving it from `X` being an at-worst-nodal
curve over an algebraically closed field;
`Stacks.Curves.existsUnique_descend_normalization_of_hasAtWorstNodalSingularities` derives it.
The opposite direction of Tag 0E68 — extending a vector field from `X` to `X^ν`, which the
source gets from `𝒪_{X^ν,x'} = k + (u)` — is
`Stacks.Curves.existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities`, and
the tag itself, both inclusions together, is
`Stacks.Curves.NodalVectorFields.range_branchPair`.

What the normalization does supply is the injectivity hypothesis: on a reduced scheme the
stalks of `𝒪_X ⟶ ν_* 𝒪_{X^ν}` are injective, by
`Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationPushforwardStalk_map_injective`,
and `app_injective_of_stalkFunctor_map_injective` turns that into injectivity on sections.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- `Der_k(𝒪_Y, 𝒪_Y)` for a `k`-scheme whose structure morphism `g : Y ⟶ Spec k` is named
rather than taken from a `Y.Over (Spec k)` instance. For `g = Y ↘ Spec k` this is
`Stacks.Curves.SheafDerivation k Y`, by definition. -/
abbrev SheafDerivationOf {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) :=
  AlgebraicGeometry.SheafOfModules.SheafDerivation
    (AlgebraicGeometry.inverseImageStructureMap g)
    (SheafOfModules.unit Y.ringCatSheaf)

namespace SheafDerivationOf

variable {Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)}

/-- The value of a vector field on a local section, as a local section. -/
def onSections (D : SheafDerivationOf g) {U : Y.Opens} (s : Γ(Y, U)) : Γ(Y, U) :=
  D.d (X := op U) s

/-- `onSections D s` is the component of `D.d` at the open `U`, applied to `s`. -/
theorem onSections_eq_d (D : SheafDerivationOf g) {U : Y.Opens} (s : Γ(Y, U)) :
    D.onSections s = D.d (X := op U) s := rfl

/-- A vector field is additive on local sections. -/
@[simp] theorem onSections_add (D : SheafDerivationOf g) {U : Y.Opens} (s t : Γ(Y, U)) :
    D.onSections (s + t) = D.onSections s + D.onSections t :=
  map_add _ s t

/-- A vector field vanishes on the zero section. -/
@[simp] theorem onSections_zero (D : SheafDerivationOf g) {U : Y.Opens} :
    D.onSections (0 : Γ(Y, U)) = 0 :=
  map_zero _

/-- A vector field vanishes on the unit section. -/
@[simp] theorem onSections_one (D : SheafDerivationOf g) {U : Y.Opens} :
    D.onSections (1 : Γ(Y, U)) = 0 :=
  D.d_one _

/-- The Leibniz rule `D (s * t) = s * D t + t * D s` on local sections. -/
theorem onSections_mul (D : SheafDerivationOf g) {U : Y.Opens} (s t : Γ(Y, U)) :
    D.onSections (s * t) = s * D.onSections t + t * D.onSections s :=
  D.d_mul (X := op U) s t

/-- A vector field commutes with restriction of local sections. -/
theorem onSections_restrict (D : SheafDerivationOf g) {U V : Y.Opens} (h : V ≤ U)
    (s : Γ(Y, U)) :
    D.onSections ((Y.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map (homOfLE h).op).hom (D.onSections s) :=
  D.d_map (X := op U) (Y := op V) (homOfLE h).op s

/-- A vector field annihilates every local section pulled back from the base. -/
theorem onSections_app (D : SheafDerivationOf g) (W : (Spec (.of k)).Opens)
    (b : Γ(Spec (.of k), W)) :
    D.onSections ((g.app W).hom b) = 0 :=
  AlgebraicGeometry.SheafOfModules.d_comorphism_eq_zero g D W b

/-- Two vector fields agreeing on every local section are equal. -/
theorem ext' {D₁ D₂ : SheafDerivationOf g}
    (h : ∀ (U : Y.Opens) (s : Γ(Y, U)), D₁.onSections s = D₂.onSections s) : D₁ = D₂ := by
  ext W s
  exact h W.unop s

end SheafDerivationOf


section Descent

variable {X Y : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- A vector field on `Y` *preserves the sections pulled back along* `ν : Y ⟶ X` when, over
every open `U` of `X`, it carries the image of `Γ(X, U)` in `Γ(Y, ν ⁻¹ᵁ U)` into itself. -/
def Preserves (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) : Prop :=
  ∀ (U : X.Opens) (s : Γ(X, U)), ∃ t : Γ(X, U),
    (ν.app U).hom t = D'.onSections ((ν.app U).hom s)

namespace Preserves

variable {ν : Y ⟶ X} {D' : SheafDerivationOf (ν ≫ hX)}

/-- Restricting twice is restricting once. -/
theorem _root_.Stacks.Curves.presheaf_map_map {Z : Scheme.{u}} {U V W : Z.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(Z, U)) :
    (Z.presheaf.map (homOfLE h₂).op).hom ((Z.presheaf.map (homOfLE h₁).op).hom s) =
      (Z.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Pulling a section back along `ν` commutes with restriction. -/
theorem _root_.Stacks.Curves.app_restrict (ν : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hpre : ν ⁻¹ᵁ V ≤ ν ⁻¹ᵁ U) (s : Γ(X, U)) :
    (ν.app V).hom ((X.presheaf.map (homOfLE hVU).op).hom s) =
      (Y.presheaf.map (homOfLE hpre).op).hom ((ν.app U).hom s) := by
  simp

/-- Restricting a section `t` with `ν^♯ t = D' (ν^♯ s)` gives a pair with the same property. -/
private theorem app_restrict_eq_onSections {U V : X.Opens} (hVU : V ≤ U) {s t : Γ(X, U)}
    (h : (ν.app U).hom t = D'.onSections ((ν.app U).hom s)) :
    (ν.app V).hom ((X.presheaf.map (homOfLE hVU).op).hom t) =
      D'.onSections ((ν.app V).hom ((X.presheaf.map (homOfLE hVU).op).hom s)) := by
  rw [app_restrict ν hVU ((Opens.map ν.base).map (homOfLE hVU)).le, h,
    ← SheafDerivationOf.onSections_restrict,
    ← app_restrict ν hVU ((Opens.map ν.base).map (homOfLE hVU)).le]

variable (h : Preserves ν D')

/-- The local section of `𝒪_X` whose pullback along `ν` is `D' (ν^♯ s)`. -/
def descendSection (U : X.Opens) (s : Γ(X, U)) : Γ(X, U) := (h U s).choose

/-- The pullback along `ν` of `descendSection U s` is `D' (ν^♯ s)`. -/
theorem app_descendSection (U : X.Opens) (s : Γ(X, U)) :
    (ν.app U).hom (h.descendSection U s) = D'.onSections ((ν.app U).hom s) :=
  (h U s).choose_spec

variable (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom)

include hinj in
/-- If `ν^♯` is injective on sections, `descendSection U` is additive. -/
theorem descendSection_add (U : X.Opens) (s t : Γ(X, U)) :
    h.descendSection U (s + t) = h.descendSection U s + h.descendSection U t := by
  refine hinj U ?_
  simp only [map_add, h.app_descendSection, SheafDerivationOf.onSections_add]

include hinj in
/-- If `ν^♯` is injective on sections, `descendSection U` satisfies the Leibniz rule. -/
theorem descendSection_mul (U : X.Opens) (s t : Γ(X, U)) :
    h.descendSection U (s * t) =
      s * h.descendSection U t + t * h.descendSection U s := by
  refine hinj U ?_
  simp only [map_add, map_mul, h.app_descendSection, SheafDerivationOf.onSections_mul]

include hinj in
/-- If `ν^♯` is injective on sections, `descendSection U` vanishes on the unit section. -/
theorem descendSection_one (U : X.Opens) : h.descendSection U 1 = 0 := by
  refine hinj U ?_
  simp only [map_one, map_zero, h.app_descendSection, SheafDerivationOf.onSections_one]

include hinj in
/-- If `ν^♯` is injective on sections, `descendSection` commutes with restriction. -/
theorem descendSection_restrict {U V : X.Opens} (hVU : V ≤ U) (s : Γ(X, U)) :
    h.descendSection V ((X.presheaf.map (homOfLE hVU).op).hom s) =
      (X.presheaf.map (homOfLE hVU).op).hom (h.descendSection U s) := by
  exact hinj V ((h.app_descendSection V _).trans
    (app_restrict_eq_onSections hVU (h.app_descendSection U s)).symm)

include hinj in
/-- If `ν^♯` is injective on sections, `descendSection` vanishes on every local section
`hX^♯ b` pulled back from the base. -/
theorem descendSection_app (W : (Spec (.of k)).Opens) (b : Γ(Spec (.of k), W)) :
    h.descendSection (hX ⁻¹ᵁ W) ((hX.app W).hom b) = 0 := by
  refine hinj (hX ⁻¹ᵁ W) ?_
  rw [h.app_descendSection, map_zero]
  exact D'.onSections_app W b

/-- The compatible family `descendSection` read as a derivation of `𝒪_X` relative to the
constant presheaf of integers: all of the derivation axioms except the vanishing on the base,
which is imposed separately. -/
def descendData : (SheafOfModules.unit X.ringCatSheaf).val.Derivation'
    (AlgebraicGeometry.SheafOfModules.constIntMap X.presheaf) where
  d {W} := AddMonoidHom.mk' (fun s => h.descendSection W.unop s)
    (h.descendSection_add hinj W.unop)
  d_mul {W} a b := h.descendSection_mul hinj W.unop a b
  d_map {_ _} f x := h.descendSection_restrict hinj f.unop.le x
  d_app {W} a :=
    AlgebraicGeometry.SheafOfModules.constIntMap_app_eq_zero
      (AddMonoidHom.mk' (fun s => h.descendSection W.unop s) (h.descendSection_add hinj W.unop))
      (h.descendSection_one hinj W.unop) a

/-- **The descended vector field.** A vector field on `Y` preserving the sections pulled back
along `ν` is `ν^♯` applied to a unique vector field on `X`, as soon as `ν^♯` is injective on
sections. -/
def descend : SheafDerivationOf hX :=
  AlgebraicGeometry.SheafOfModules.ofComorphism hX (h.descendData hinj)
    (fun W b => h.descendSection_app hinj W b)

/-- The value of `descend` on a local section `s` over `U` is `descendSection U s`. -/
@[simp] theorem descend_onSections (U : X.Opens) (s : Γ(X, U)) :
    (h.descend hinj).onSections s = h.descendSection U s := rfl

/-- The descended vector field is compatible with `D'`: `ν^♯ (descend s) = D' (ν^♯ s)`. -/
theorem app_descend_onSections (U : X.Opens) (s : Γ(X, U)) :
    (ν.app U).hom ((h.descend hinj).onSections s) = D'.onSections ((ν.app U).hom s) :=
  h.app_descendSection U s

end Preserves

/-- A vector field on `Y` compatible with one on `X` along `ν` preserves the pulled-back
sections. -/
theorem preserves_of_compatible {ν : Y ⟶ X} (D : SheafDerivationOf hX)
    (D' : SheafDerivationOf (ν ≫ hX))
    (hD : ∀ (U : X.Opens) (s : Γ(X, U)),
      (ν.app U).hom (D.onSections s) = D'.onSections ((ν.app U).hom s)) :
    Preserves ν D' :=
  fun U s => ⟨D.onSections s, hD U s⟩

/-- **Preserving the pulled-back sections is a local condition on `X`.** If every local
section of `𝒪_X` is, in a neighbourhood of each of its points, carried by `D'` back into
`𝒪_X`, and `ν^♯` is injective on sections, then `D'` preserves `ν^♯ Γ(X, U)` for every open
`U` of `X`. This is the gluing step of the globalisation: the local witnesses agree on overlaps
because `ν^♯` is injective, so they glue, and the glued section has the required pullback because
`𝒪_Y` is a sheaf. -/
theorem preserves_of_forall_mem_exists {ν : Y ⟶ X} (D' : SheafDerivationOf (ν ≫ hX))
    (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom)
    (hloc : ∀ (U : X.Opens) (s : Γ(X, U)) (x : X), x ∈ U →
      ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ ∃ t : Γ(X, V),
        (ν.app V).hom t =
          D'.onSections ((ν.app V).hom ((X.presheaf.map (homOfLE hV).op).hom s))) :
    Preserves ν D' := by
  intro U s
  choose! V hV hmem t ht using fun (x : X) (hx : x ∈ U) => hloc U s x hx
  have hcover : U ≤ ⨆ i : {x : X // x ∈ U}, V i.1 := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem x hx⟩
  have hpre : ∀ i : {x : X // x ∈ U}, ν ⁻¹ᵁ V i.1 ≤ ν ⁻¹ᵁ U :=
    fun i _ hx => hV i.1 i.2 hx
  -- the local witness over `V x` restricts to the local witness over any smaller open
  have hkey : ∀ (x : X) (hx : x ∈ U) (Z : X.Opens) (hZ : Z ≤ V x),
      (ν.app Z).hom ((X.presheaf.map (homOfLE hZ).op).hom (t x)) =
        D'.onSections ((ν.app Z).hom
          ((X.presheaf.map (homOfLE (hZ.trans (hV x hx))).op).hom s)) := by
    intro x hx Z hZ
    rw [← presheaf_map_map (hV x hx) hZ s]
    exact Preserves.app_restrict_eq_onSections hZ (ht x hx)
  have hc : TopCat.Presheaf.IsCompatible X.presheaf (fun i : {x : X // x ∈ U} => V i.1)
      (fun i => t i.1) := fun i j =>
    hinj (V i.1 ⊓ V j.1)
      ((hkey i.1 i.2 (V i.1 ⊓ V j.1) inf_le_left).trans
        (hkey j.1 j.2 (V i.1 ⊓ V j.1) inf_le_right).symm)
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun i : {x : X // x ∈ U} => V i.1) U
    (fun i => homOfLE (hV i.1 i.2)) hcover (fun i => t i.1) hc
  have hg' : ∀ i : {x : X // x ∈ U},
      (X.presheaf.map (homOfLE (hV i.1 i.2)).op).hom g = t i.1 := fun i => hg i
  have hsheaf : ∀ A B : Γ(Y, ν ⁻¹ᵁ U),
      (∀ i : {x : X // x ∈ U}, (Y.presheaf.map (homOfLE (hpre i)).op).hom A =
        (Y.presheaf.map (homOfLE (hpre i)).op).hom B) → A = B := by
    intro A B hAB
    refine Y.sheaf.eq_of_locally_eq' (fun i : {x : X // x ∈ U} => ν ⁻¹ᵁ V i.1) (ν ⁻¹ᵁ U)
      (fun i => homOfLE (hpre i)) (fun x hx => ?_) A B hAB
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hx)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  refine ⟨g, hsheaf _ _ fun i => ?_⟩
  rw [← app_restrict ν (hV i.1 i.2) (hpre i) g, hg' i, ht i.1 i.2,
    app_restrict ν (hV i.1 i.2) (hpre i) s]
  exact SheafDerivationOf.onSections_restrict D' (hpre i) _

/-- A morphism of schemes injective on stalks of the structure sheaves is injective on
sections over every open: a section whose pullback vanishes has vanishing germs, and `𝒪_X` is
a sheaf. -/
theorem app_injective_of_stalkFunctor_map_injective (ν : Y ⟶ X)
    (hst : ∀ x : X, Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ν.c)))
    (U : X.Opens) : Function.Injective (ν.app U).hom := by
  intro s t hs
  have key : ∀ (x : X) (hx : x ∈ U),
      ConcreteCategory.hom (X.presheaf.germ U x hx) s =
        ConcreteCategory.hom (X.presheaf.germ U x hx) t := by
    intro x hx
    refine hst x ?_
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg _ hs
  exact TopCat.Presheaf.section_ext X.sheaf U s t key

/-- **The restriction of vector fields along `ν`, and its image.** When `ν^♯` is injective on
sections, a vector field on `Y` comes from a (then unique) vector field on `X` exactly when it
preserves the sections pulled back from `X`. -/
theorem existsUnique_descend_iff_preserves {ν : Y ⟶ X} (D' : SheafDerivationOf (ν ≫ hX))
    (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom) :
    (∃! D : SheafDerivationOf hX, ∀ (U : X.Opens) (s : Γ(X, U)),
      (ν.app U).hom (D.onSections s) = D'.onSections ((ν.app U).hom s)) ↔ Preserves ν D' := by
  refine ⟨fun hex => ?_, fun h => ?_⟩
  · obtain ⟨D, hD, -⟩ := hex
    exact preserves_of_compatible D D' hD
  refine ⟨h.descend hinj, h.app_descend_onSections hinj, fun D hD => ?_⟩
  refine SheafDerivationOf.ext' fun U s => hinj U ?_
  rw [hD U s, h.app_descend_onSections hinj]

/-- The normalization of a reduced scheme is injective on sections of the structure sheaf over
every open, so a vector field on the normalization descends as soon as it preserves the
subsheaf `𝒪_X`. -/
theorem app_normalization_injective (X : Scheme.{u}) [IsReduced X]
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) :
    Function.Injective ((AlgebraicGeometry.Scheme.normalization X hfin).app U).hom :=
  app_injective_of_stalkFunctor_map_injective _
    (Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationPushforwardStalk_map_injective
      X hfin) U

end Descent

end Stacks.Curves

end
