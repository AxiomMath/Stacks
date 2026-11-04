module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsolatedPoints
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SchemeTheoreticUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Contraction
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.ContractionComparison.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction

/-!
# The stable model of a nodal curve: the shape of the statement, and its formal half

Let `k` be a field and `X` a proper curve over `k` with `H⁰(X, 𝒪_X) = k`, genus `g ≥ 2` and
at-worst-nodal singularities. [Stacks, Tag 0E7Q] asserts that there is a morphism `c : X ⟶ Y`
over `k`, unique up to unique isomorphism, such that

1. `Y` is proper over `k` of dimension one with at-worst-nodal singularities,
2. `𝒪_Y = c_*𝒪_X` and `R^1 c_*𝒪_X = 0`,
3. `ω_Y` is ample.

This file names the three conditions (`Stacks.Curves.StableModel.IsStableContraction`) and proves
the formal part of "unique up to unique isomorphism": an isomorphism `Y ≅ Y'` under `X` between
two such contractions is unique, because `c` is dominant and `Y` is reduced
(`Stacks.Curves.StableModel.existsUnique_iso_of_nonempty`), and two contractions comparable to a
third are comparable to each other (`Stacks.Curves.StableModel.nonempty_iso_of_nonempty_iso`).

## Main definitions

* `Stacks.Curves.StableModel.IsStableContraction f gY c`: conditions (1), (2), (3) for
  `c : X ⟶ Y` over `k`, with `f` and `gY` the structure morphisms.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isDominant_of_isIso_unitToPushforwardObjUnit`: `𝒪_Y = c_*𝒪_X`
  makes `c` dominant.
* `Stacks.Curves.StableModel.IsStableContraction.ext`: morphisms out of `Y` over `k` agreeing
  after `c` are equal.
* `Stacks.Curves.StableModel.existsUnique_iso_of_nonempty`.
* `Stacks.Curves.StableModel.existsUnique_iso_of_pullback_dualizingSheafOverField_iso`: two stable
  contractions pulling the dualizing sheaves back to isomorphic modules are uniquely isomorphic.
* `Stacks.Curves.StableModel.IsStableContraction.comp` and
  `Stacks.Curves.StableModel.IsStableContraction.of_comp`: the conditions are stable under
  precomposition with, and descend along, an acyclic contraction.
* `Stacks.Curves.StableModel.hom_ext_of_isRationalTail`: a morphism out of `X` is determined by
  its restrictions to a rational tail and to the closure of its complement.
* `Stacks.Curves.StableModel.contraction_comp_eq_of_factors`: a morphism contracting a rational
  tail to its attaching point factors through the contraction of the tail.
* `Stacks.Curves.StableModel.exists_comp_eq_canonicalMapToAttachingPoint`: a morphism mapping a
  rational tail to a point factors through the canonical map to its attaching point.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (c : X ⟶ Y)

/-- **`𝒪_Y = c_*𝒪_X` makes `c` dominant**: an open of `Y` missing the image has empty preimage,
so its ring of sections is that of the empty open of `X`, which is zero, and the open is empty. -/
theorem isDominant_of_isIso_unitToPushforwardObjUnit
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) : IsDominant c := by
  refine ⟨?_⟩
  show Dense (Set.range c)
  rw [dense_iff_inter_open]
  intro W hW hne
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let W' : Y.Opens := ⟨W, hW⟩
  have hpre : c ⁻¹ᵁ W' = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hempty.subset ⟨hx, x, rfl⟩
  have : Nonempty W' := ⟨⟨hne.some, hne.some_mem⟩⟩
  have hsub : Subsingleton Γ(X, c ⁻¹ᵁ W') :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hpre)
  have hb := ConcreteCategory.bijective_of_isIso
    (@asIso _ _ _ _ _
      (Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO W')).hom
  exact not_subsingleton Γ(Y, W') hb.1.subsingleton

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X Y Y' : Scheme.{u}}

/-- **The three conditions of [Stacks, Tag 0E7Q]** on a morphism `c : X ⟶ Y` over `k`, where
`f : X ⟶ Spec k` and `gY : Y ⟶ Spec k` are the structure morphisms:

1. `Y` is proper over `k`, of dimension one, with at-worst-nodal singularities;
2. `𝒪_Y = c_*𝒪_X` and `R^1 c_*𝒪_X = 0`;
3. `ω_Y` is ample (in particular invertible). -/
structure IsStableContraction (f : X ⟶ Spec (.of k)) (gY : Y ⟶ Spec (.of k)) (c : X ⟶ Y) :
    Prop where
  /-- `c` is a morphism over `k`. -/
  comp_eq : c ≫ gY = f
  /-- `Y` is proper over `k`. -/
  isProper : IsProper gY
  /-- `Y` has dimension one. -/
  topologicalKrullDim_eq : topologicalKrullDim Y = 1
  /-- `Y` has at-worst-nodal singularities over `k`. -/
  hasAtWorstNodalSingularities :
    letI : Y.Over (Spec (.of k)) := ⟨gY⟩
    Stacks.Curves.HasAtWorstNodalSingularities k Y
  /-- The map `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism. -/
  isIso_unitToPushforwardObjUnit :
    IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)
  /-- `R^1 c_*𝒪_X = 0`. -/
  isZero_rightDerived_one : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
    (SheafOfModules.unit X.ringCatSheaf))
  /-- The dualizing sheaf `ω_Y` is invertible and ample. -/
  isAmple :
    letI := isProper
    ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
        (structureSheafRing Y.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField gY),
      Scheme.Modules.IsAmple Y (Stacks.Duality.dualizingSheafOverField gY)

namespace IsStableContraction

variable {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}

/-- The target of a stable contraction is reduced, its singularities being nodes. -/
theorem isReduced (h : IsStableContraction f gY c) : IsReduced Y := by
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : IsProper (Y ↘ Spec (.of k)) := h.isProper
  exact Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k Y h.hasAtWorstNodalSingularities

/-- A stable contraction is dominant. -/
theorem isDominant (h : IsStableContraction f gY c) : IsDominant c :=
  c.isDominant_of_isIso_unitToPushforwardObjUnit h.isIso_unitToPushforwardObjUnit

/-- **Morphisms out of the target of a stable contraction are determined after the
contraction**: if `c ≫ a = c ≫ b` for `a b : Y ⟶ Y'` with `Y'` separated over `k`, then `a = b`,
`Y` being reduced and `c` dominant. -/
theorem ext (h : IsStableContraction f gY c) {gY' : Y' ⟶ Spec (.of k)} [IsSeparated gY']
    {a b : Y ⟶ Y'} (hab : c ≫ a = c ≫ b) : a = b := by
  have := h.isReduced
  have := h.isDominant
  exact ext_of_isDominant_of_isSeparated gY'
    (ext_of_isDominant c (by rw [← Category.assoc, ← Category.assoc, hab])) c hab

end IsStableContraction

variable {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {gY' : Y' ⟶ Spec (.of k)}
  {c : X ⟶ Y} {c' : X ⟶ Y'}

/-- **The isomorphism between two stable contractions is unique**: an isomorphism `Y ≅ Y'` under
`X`, if there is one, is the only one. -/
theorem existsUnique_iso_of_nonempty (h : IsStableContraction f gY c)
    (h' : IsStableContraction f gY' c') (he : ∃ e : Y ≅ Y', c ≫ e.hom = c') :
    ∃! e : Y ≅ Y', c ≫ e.hom = c' := by
  have : IsProper gY' := h'.isProper
  obtain ⟨e, he⟩ := he
  exact ⟨e, he, fun e' he' => Iso.ext (h.ext (gY' := gY') (he'.trans he.symm))⟩

/-- An isomorphism under `X` composes and inverts: two contractions each comparable to a third
are comparable to each other. -/
theorem nonempty_iso_of_nonempty_iso {Y₀ : Scheme.{u}} {c₀ : X ⟶ Y₀}
    (he : ∃ e : Y₀ ≅ Y, c₀ ≫ e.hom = c) (he' : ∃ e : Y₀ ≅ Y', c₀ ≫ e.hom = c') :
    ∃ e : Y ≅ Y', c ≫ e.hom = c' := by
  obtain ⟨e, rfl⟩ := he
  obtain ⟨e', rfl⟩ := he'
  exact ⟨e.symm ≪≫ e', by simp⟩

/-- **Uniqueness up to unique isomorphism, from a reference contraction**: if every stable
contraction of `X` is isomorphic under `X` to a fixed one, then any two are related by a unique
isomorphism under `X`. -/
theorem existsUnique_iso_of_forall {Y₀ : Scheme.{u}} {c₀ : X ⟶ Y₀}
    (hall : ∀ {Z : Scheme.{u}} {gZ : Z ⟶ Spec (.of k)} {d : X ⟶ Z},
      IsStableContraction f gZ d → ∃ e : Y₀ ≅ Z, c₀ ≫ e.hom = d)
    (h : IsStableContraction f gY c) (h' : IsStableContraction f gY' c') :
    ∃! e : Y ≅ Y', c ≫ e.hom = c' :=
  existsUnique_iso_of_nonempty h h' (nonempty_iso_of_nonempty_iso (hall h) (hall h'))

/-- A stable contraction of a proper `X` is proper and surjective. -/
private theorem IsStableContraction.isProper_and_surjective [IsProper f]
    (h : IsStableContraction f gY c) : IsProper c ∧ Surjective c := by
  have := h.isProper
  have : IsProper (c ≫ gY) := by rw [h.comp_eq]; infer_instance
  have : IsProper c := IsProper.of_comp c gY
  exact ⟨this, c.surjective_of_isIso_app
    (Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
      h.isIso_unitToPushforwardObjUnit)⟩

/-- **Two stable contractions with isomorphic pulled-back dualizing sheaves are related by a unique
isomorphism.** If `c : X ⟶ Y` and `c' : X ⟶ Y'` satisfy the conditions of [Stacks, Tag 0E7Q] and
`c^*ω_Y ≅ c'^*ω_{Y'}`, then there is a unique `e : Y ≅ Y'` with `c ≫ e.hom = c'`: both targets are
reduced and separated, both contractions are surjective with `𝒪 = c_*𝒪`, and `ω_Y`, `ω_{Y'}` are
ample (`Stacks.ContractionComparison.exists_iso_comp_eq_of_isAmple`). This is the last step of the
uniqueness proof of [Stacks, Tag 0E7Q], where both pullbacks are `ω_X` by [Stacks, Tag 0E7P]. -/
theorem existsUnique_iso_of_pullback_dualizingSheafOverField_iso [IsProper f]
    (h : IsStableContraction f gY c) (h' : IsStableContraction f gY' c')
    (φ : haveI := h.isProper
      haveI := h'.isProper
      (Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField gY) ≅
        (Scheme.Modules.pullback c').obj (Stacks.Duality.dualizingSheafOverField gY')) :
    ∃! e : Y ≅ Y', c ≫ e.hom = c' := by
  refine existsUnique_iso_of_nonempty h h' ?_
  have : IsProper gY := h.isProper
  have : IsProper gY' := h'.isProper
  obtain ⟨_, _⟩ := h.isProper_and_surjective
  obtain ⟨_, _⟩ := h'.isProper_and_surjective
  have := h.isReduced
  have := h'.isReduced
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from gY]; infer_instance⟩
  have : Y'.IsSeparated := ⟨by rw [← terminal.comp_from gY']; infer_instance⟩
  obtain ⟨hinv, hL⟩ := h.isAmple
  obtain ⟨hinv', hL'⟩ := h'.isAmple
  exact Stacks.ContractionComparison.exists_iso_comp_eq_of_isAmple c c'
    h.isIso_unitToPushforwardObjUnit h'.isIso_unitToPushforwardObjUnit _ _ φ hL hL'

/-! ### Property (2) is stable under composition -/

section Composition

variable {Z : Scheme.{u}} (c₁ : X ⟶ Y) (c₂ : Y ⟶ Z)

/-- Given `𝒪_Y = c₁*𝒪_X`, the map `𝒪_Z ⟶ (c₁ ≫ c₂)_*𝒪_X` is an isomorphism iff
`𝒪_Z ⟶ c₂*𝒪_Y` is: on sections over `W` the map is `c₂^♯` followed by `c₁^♯`. -/
private theorem isIso_unitToPushforwardObjUnit_comp_iff
    (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (c₁ ≫ c₂).toRingCatSheafHom) ↔
      IsIso (SheafOfModules.unitToPushforwardObjUnit c₂.toRingCatSheafHom) := by
  constructor <;> intro h <;>
    refine isIso_unitToPushforwardObjUnit_of_forall_isIso_app _ fun W => ?_ <;>
    have a₁ := Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₁ h₁
      (c₂ ⁻¹ᵁ W.unop) <;>
    have a := Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit _ h
      W.unop
  · rw [Scheme.Hom.comp_app] at a
    have : IsIso (c₂.app W.unop) := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ a₁ a
    exact Functor.map_isIso (forget₂ CommRingCat RingCat) (c₂.app W.unop)
  · have : IsIso ((c₁ ≫ c₂).app W.unop) := by
      rw [Scheme.Hom.comp_app]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ a a₁
    exact Functor.map_isIso (forget₂ CommRingCat RingCat) ((c₁ ≫ c₂).app W.unop)

/-- `𝒪_Z = (c₂ ∘ c₁)_*𝒪_X` when `𝒪_Y = c₁*𝒪_X` and `𝒪_Z = c₂*𝒪_Y`. -/
theorem isIso_unitToPushforwardObjUnit_comp
    (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom))
    (h₂ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₂.toRingCatSheafHom)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (c₁ ≫ c₂).toRingCatSheafHom) :=
  (isIso_unitToPushforwardObjUnit_comp_iff c₁ c₂ h₁).2 h₂

/-- **Leray when the first factor is acyclic**: if `𝒪_Y = c₁*𝒪_X` and `R^i c₁*𝒪_X = 0` for
`i > 0`, then `R^n (c₂ ∘ c₁)_*𝒪_X ≅ R^n c₂*𝒪_Y`, as `R(c₂ ∘ c₁)_* = Rc₂_* ∘ Rc₁_*` and
`Rc₁_*𝒪_X = 𝒪_Y`. -/
def rightDerivedCompUnitIso [QuasiCompact c₁] [QuasiSeparated c₁] [CompactSpace Y]
    (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom))
    (hR₁ : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c₁).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf))) (n : ℕ) :
    ((Scheme.Modules.pushforward (c₁ ≫ c₂)).rightDerived n).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ((Scheme.Modules.pushforward c₂).rightDerived n).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso (c₁ ≫ c₂) 0 n n
      (by simp)).app (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    (DerivedCategory.homologyFunctor Z.Modules n).mapIso
      ((Stacks.Duality.derivedPushforwardCompIso c₁ c₂).symm.app _ ≪≫
        (Stacks.Duality.derivedPushforward c₂).mapIso
          (Stacks.Duality.nonempty_derivedPushforward_iso_of_isZero c₁ _
            (SheafOfModules.unit Y.ringCatSheaf) hR₁ (@asIso _ _ _ _ _ h₁).symm).some) ≪≫
    (Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso c₂ 0 n n
      (by simp)).app (SheafOfModules.unit Y.ringCatSheaf)

/-- `𝒪_Y = c₂*𝒪_Z`-style descent: if `𝒪_Z = (c₂ ∘ c₁)_*𝒪_X` and `𝒪_Y = c₁*𝒪_X`, then
`𝒪_Z = c₂*𝒪_Y`. -/
theorem isIso_unitToPushforwardObjUnit_of_comp
    (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom))
    (h : IsIso (SheafOfModules.unitToPushforwardObjUnit (c₁ ≫ c₂).toRingCatSheafHom)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit c₂.toRingCatSheafHom) :=
  (isIso_unitToPushforwardObjUnit_comp_iff c₁ c₂ h₁).1 h

/-- **A stable contraction factoring through an acyclic contraction factors through a stable
contraction**: if `c = d ≫ c'` where `𝒪_{X₁} = d_*𝒪_X` and `R^i d_*𝒪_X = 0` for `i > 0`, and `c`
satisfies the conditions of [Stacks, Tag 0E7Q], then so does `c'`. -/
theorem IsStableContraction.of_comp {X₁ : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    {f₁ : X₁ ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} (d : X ⟶ X₁) (c' : X₁ ⟶ Y)
    [QuasiCompact d] [QuasiSeparated d] [CompactSpace X₁] (hdf : d ≫ f₁ = f)
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (hRd : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward d).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (h : IsStableContraction f gY (d ≫ c')) : IsStableContraction f₁ gY c' where
  comp_eq := by
    have hiso : IsIso d.appTop :=
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit d hd ⊤
    refine ext_of_isAffine ((cancel_mono d.appTop).1 ?_)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Category.assoc, h.comp_eq, hdf]
  isProper := h.isProper
  topologicalKrullDim_eq := h.topologicalKrullDim_eq
  hasAtWorstNodalSingularities := h.hasAtWorstNodalSingularities
  isIso_unitToPushforwardObjUnit :=
    isIso_unitToPushforwardObjUnit_of_comp d c' hd h.isIso_unitToPushforwardObjUnit
  isZero_rightDerived_one :=
    h.isZero_rightDerived_one.of_iso (rightDerivedCompUnitIso d c' hd hRd 1).symm
  isAmple := h.isAmple

/-- **A stable contraction preceded by an acyclic contraction is a stable contraction**: if
`𝒪_{X₁} = d_*𝒪_X`, `Rⁱ d_*𝒪_X = 0` for `i > 0` and `c'` satisfies the conditions of
[Stacks, Tag 0E7Q] for `X₁`, then `d ≫ c'` satisfies them for `X`. This is how the existence
part of [Stacks, Tag 0E7Q] combines the contractions of rational tails and of rational bridges. -/
theorem IsStableContraction.comp {X₁ : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    {f₁ : X₁ ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} (d : X ⟶ X₁) (c' : X₁ ⟶ Y)
    [QuasiCompact d] [QuasiSeparated d] [CompactSpace X₁] (hdf : d ≫ f₁ = f)
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (hRd : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward d).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (h : IsStableContraction f₁ gY c') : IsStableContraction f gY (d ≫ c') where
  comp_eq := by rw [Category.assoc, h.comp_eq, hdf]
  isProper := h.isProper
  topologicalKrullDim_eq := h.topologicalKrullDim_eq
  hasAtWorstNodalSingularities := h.hasAtWorstNodalSingularities
  isIso_unitToPushforwardObjUnit :=
    isIso_unitToPushforwardObjUnit_comp d c' hd h.isIso_unitToPushforwardObjUnit
  isZero_rightDerived_one :=
    h.isZero_rightDerived_one.of_iso (rightDerivedCompUnitIso d c' hd hRd 1)
  isAmple := h.isAmple

end Composition

/-! ### Factoring through the contraction of a rational tail -/

section Tail

variable (k) (X) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A morphism out of `X` is determined by its restrictions to a rational tail `C` and to the
closure `X'` of its complement**: `X` is the scheme-theoretic union of `C` and `X'`, hence their
pushout over `C ∩ X'`. -/
theorem hom_ext_of_isRationalTail (hdim : topologicalKrullDim X = 1)
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X) {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) {Z : Scheme.{u}} {a b : X ⟶ Z}
    (htail : C.subschemeι ≫ a = C.subschemeι ≫ b)
    (hcomp : complementaryCurveι C ≫ a = complementaryCurveι C ≫ b) : a = b := by
  have hd : C ⊓ complementaryCurveIdeal C = ⊥ :=
    Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot k X hdim hnodal C hC
  have : IsIso (C ⊓ complementaryCurveIdeal C).subschemeι := hd ▸ inferInstance
  refine (cancel_epi (C ⊓ complementaryCurveIdeal C).subschemeι).1
    ((Scheme.IdealSheafData.isPushout_subscheme_inf C _).hom_ext ?_ ?_) <;>
    rwa [← Category.assoc, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

/-- **A morphism contracting a rational tail factors through the contraction of the tail**: if
the restriction of `c : X ⟶ Z` to the rational tail `C` factors through the canonical morphism
from `C` to its attaching point, then `c` is the contraction `X ⟶ X'` followed by the restriction
of `c` to `X'`. -/
theorem contraction_comp_eq_of_factors (hdim : topologicalKrullDim X = 1)
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X) {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) {cont : X ⟶ complementaryCurve C}
    (hcont : IsContractionOfRationalTail hC cont) {Z : Scheme.{u}} (c : X ⟶ Z)
    (hfac : ∃ q, C.subschemeι ≫ c = canonicalMapToAttachingPoint hC ≫ q) :
    cont ≫ (complementaryCurveι C ≫ c) = c := by
  obtain ⟨hcomp, p, hp, htail⟩ := (isContractionOfRationalTail_iff hC cont).mp hcont
  obtain ⟨q, hq⟩ := hfac
  refine hom_ext_of_isRationalTail k X hdim hnodal hC ?_ ?_
  · rw [← Category.assoc, htail, Category.assoc, hq]
    congr 1
    have hret : C.subscheme.fromSpecResidueField hC.attachingPoint ≫
        canonicalMapToAttachingPoint hC =
          𝟙 (Spec (C.subscheme.residueField hC.attachingPoint)) := by
      simp only [canonicalMapToAttachingPoint, Scheme.fromSpecResidueField,
        Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
        ← AlgebraicGeometry.Spec.map_comp]
      rw [← AlgebraicGeometry.Spec.map_id, AlgebraicGeometry.Spec.map_inj]
      simp [Scheme.Γevaluation, Scheme.evaluation]
    have hpt : C.subscheme.fromSpecResidueField hC.attachingPoint ≫ C.subschemeι ≫ c =
        C.subscheme.fromSpecResidueField hC.attachingPoint ≫ canonicalMapToAttachingPoint hC ≫ q :=
      by rw [hq]
    rw [← Category.assoc (C.subscheme.fromSpecResidueField hC.attachingPoint)
      (canonicalMapToAttachingPoint hC), hret, Category.id_comp] at hpt
    rw [← Category.assoc, hp, Category.assoc, hpt]
  · rw [← Category.assoc, hcomp, Category.id_comp]

/-- **A morphism into an affine open factors through the affinization**: if `g : T ⟶ Z` lands in
an affine open of `Z`, then `g = T.toSpecΓ ≫ q` for some `q : Spec Γ(T, ⊤) ⟶ Z`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_eq_toSpecΓ_comp {T Z : Scheme.{u}} (g : T ⟶ Z)
    {V : Z.Opens} (hV : IsAffineOpen V) (hg : Set.range g ⊆ V) :
    ∃ q : Spec Γ(T, ⊤) ⟶ Z, g = T.toSpecΓ ≫ q := by
  have : IsAffine V := hV
  let l := IsOpenImmersion.lift V.ι g (by rwa [Scheme.Opens.range_ι])
  refine ⟨Spec.map l.appTop ≫ inv V.toScheme.toSpecΓ ≫ V.ι, ?_⟩
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id_assoc,
    IsOpenImmersion.lift_fac]

omit [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **A morphism mapping a rational tail to a point factors through its attaching point**: if
`C.subschemeι ≫ c` has a one-point image, it factors through the canonical morphism from `C`
to the spectrum of the residue field of its attaching point, which is `C ⟶ Spec Γ(C, 𝒪_C)`. -/
theorem exists_comp_eq_canonicalMapToAttachingPoint {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) {Z : Scheme.{u}} (c : X ⟶ Z)
    (h : (Set.range (C.subschemeι ≫ c)).Subsingleton) :
    ∃ q, C.subschemeι ≫ c = canonicalMapToAttachingPoint hC ≫ q := by
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show (C.subschemeι ≫ c) hC.attachingPoint ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨q, hq⟩ := (C.subschemeι ≫ c).exists_eq_toSpecΓ_comp hV (fun _ hz => by
    rwa [h hz ⟨hC.attachingPoint, rfl⟩])
  have := hC.isIso_Γevaluation_attachingPoint
  refine ⟨Spec.map (C.subscheme.Γevaluation hC.attachingPoint) ≫ q, ?_⟩
  rw [hq, canonicalMapToAttachingPoint, Category.assoc, ← Spec.map_comp_assoc,
    IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

end Tail

end Stacks.Curves.StableModel
