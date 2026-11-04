module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionClassCases
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SectionOfSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute

/-!
# Independence of the Gysin map of a local complete intersection morphism on its factorization

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S`. For a
factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth, Stacks 0FF3
defines the Gysin map `i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧` (`Stacks.Chow.SmoothFactorization.gysinMap`).
**Stacks 0FF2** asserts that it does not depend on the factorization.

The proof is the source's. Two factorizations have a common refinement
(`Stacks.Chow.SmoothFactorization.exists_refines_both`), so it suffices to treat a factorization
`f = g' ∘ i'` through `P'` refining `f = g ∘ i` by a smooth `p : P' ⟶ P`. Then
`(g')^* = p^* ∘ g^*` (Stacks 02RD, `Stacks.Chow.completedFlatPullbackOfSmooth_comp`), and with the
cartesian square `X ×_P P'` of `i` and `p`, its projection `j : X ×_P P' ⟶ P'`, its retraction
`p̄ : X ×_P P' ⟶ X` and the section `s = (1, i')` of `p̄`:

* `(i')^! = s^! ∘ j^!` (Stacks 0FF0);
* `j^!` is the restriction of `i^!` along `p` (Stacks 0FBK), so `j^! ∘ p^* = p̄^* ∘ i^!`
  (`Stacks.Chow.completedBivariantRestriction_composite_completedFlatPullbackOfSmooth`);
* `s^! ∘ p̄^* = 1` (Stacks 0FF1,
  `Stacks.Chow.completedBivariantCompositeOfInvertible_completedFlatPullbackOfSmooth_of_section`);

and associativity and the unit law of the composition on completions conclude.

## Main results

* `Stacks.Chow.SmoothFactorization.gysinMap_eq_of_refines_of_regularImmersionCompositionCase` —
  the Gysin map is unchanged by a refinement of the factorization.
* `Stacks.Chow.SmoothFactorization.gysinMap_eq_of_regularImmersionCompositionCase` —
  Stacks 0FF2, granted Stacks 0FF0.
* `Stacks.Chow.SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase` —
  the Gysin map of any factorization is the Gysin map `f^!` of Stacks 0FF3, granted Stacks 0FF0.

## Implementation notes

The base-change clause of Stacks 0FBK enters through
`Stacks.Chow.regularImmersionSmoothBaseChangeCase`. Stacks 0FF0 enters as the hypothesis
`Stacks.Chow.RegularImmersionCompositionCase C`, stated exactly in the form in which the proof
applies it: for the classes of the normal sheaves of regular immersions attached to immersions by
Stacks 0FBQ (3).

## References

* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FF1](https://stacks.math.columbia.edu/tag/0FF1)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### Congruences -/

section Congr

variable (C : ChowSituation.{u})

/-- The composite on completions of classes for equal morphisms and equal structure morphisms,
equal up to `≍`, are equal up to `≍`. -/
theorem completedBivariantCompositeOfInvertible_heq_congr {X Y Z : Scheme.{u}}
    {sX sX' : X ⟶ C.S} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {sY sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] {sZ sZ' : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ'] {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] {g g' : Y ⟶ Z} [LocallyOfFiniteType g] [LocallyOfFiniteType g']
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (hX : sX = sX') (hY : sY = sY') (hZ : sZ = sZ') (hff : f = f') (hgg : g = g')
    {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} {hf' : f' ≫ sY' = sX'} {hg' : g' ≫ sZ' = sY'}
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    {c' : completedBivariantGroup C (gysinSystemOfInvertible C) sX' sY' f' hf'}
    {d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg}
    {d' : completedBivariantGroup C (gysinSystemOfInvertible C) sY' sZ' g' hg'}
    (hc : c ≍ c') (hd : d ≍ d') :
    completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d ≍
      completedBivariantCompositeOfInvertible C sX' sY' sZ' f' g' hf' hg' c' d' := by
  subst hX hY hZ hff hgg
  cases hc
  cases hd
  rfl

/-- The flat pullbacks on completions of equal smooth morphisms, for equal structure morphisms,
are equal up to `≍`. -/
theorem completedFlatPullbackOfSmooth_heq_congr {P Y : Scheme.{u}} {sP sP' : P ⟶ C.S}
    [LocallyOfFiniteType sP] [LocallyOfFiniteType sP'] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {g g' : P ⟶ Y} [Smooth g] [Smooth g'] [LocallyOfFiniteType g] [LocallyOfFiniteType g']
    (hP : sP = sP') (hgg : g = g') {hg : g ≫ sY = sP} {hg' : g' ≫ sY = sP'} :
    completedFlatPullbackOfSmooth C sP sY g hg ≍ completedFlatPullbackOfSmooth C sP' sY g' hg' := by
  subst hP hgg
  rfl

/-- The classes of the normal sheaves of equal regular immersions, for equal structure morphisms,
are equal up to `≍`. -/
theorem completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr
    {Z X : Scheme.{u}} [IsLocallyNoetherian Z] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    {sX sX' : X ⟶ C.S} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {i i' : Z ⟶ X}
    [IsImmersion i] [IsImmersion i'] (hX : sX = sX') (hii : i = i') {hi : i ≫ sX = sZ}
    {hi' : i' ≫ sX' = sZ} (hr : IsRegularImmersion i) (hr' : IsRegularImmersion i') :
    completedVirtualNormalGysinClassOfImmersion C sZ sX i hi
        (VirtualNormalBundle.ofIsRegularImmersion i hr) ≍
      completedVirtualNormalGysinClassOfImmersion C sZ sX' i' hi'
        (VirtualNormalBundle.ofIsRegularImmersion i' hr') := by
  subst hX hii
  rfl

end Congr


/-! ### Stacks 0FF2 -/

section Independence

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- **Stacks 0FF2, the refined case.** For a factorization `F'` of `f` refining `F` by a smooth
`p : P' ⟶ P`, the Gysin maps of the two factorizations agree. As in the source,
`(g')^* = p^* ∘ g^*` (Stacks 02RD) reduces this to `i^! = (i')^! ∘ p^*`; with `s = (1, i')` and
`j : X ×_P P' ⟶ P'`, `(i')^! = s^! ∘ j^!` (Stacks 0FF0), `j^!` is the restriction of `i^!` to `P'`
(Stacks 0FBK), so `j^! ∘ p^* = p̄^* ∘ i^!` (bivariant classes commute with flat pullback), and
`s^! ∘ p̄^* = 1` (Stacks 0FF1). -/
theorem SmoothFactorization.gysinMap_eq_of_refines_of_regularImmersionCompositionCase
    (hcomp : RegularImmersionCompositionCase C) {F F' : SmoothFactorization f}
    (h : F'.Refines F) (hlci : IsLocalCompleteIntersectionMorphism f) :
    F'.gysinMap C sX sY hf hlci = F.gysinMap C sX sY hf hlci := by
  obtain ⟨p, hpsm, hp, hpg⟩ := h
  have : Smooth p := hpsm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  have : IsLocallyNoetherian F'.ambient :=
    LocallyOfFiniteType.isLocallyNoetherian (F'.proj ≫ sY)
  have : IsLocallyNoetherian (F.refinementAmbient p) :=
    LocallyOfFiniteType.isLocallyNoetherian (F.refinementRetraction p ≫ sX)
  -- notation
  set sP := F.proj ≫ sY with hsP
  set sP' := p ≫ sP with hsP'
  set sW := F.refinementRetraction p ≫ sX
  have hP' : sP' = F'.proj ≫ sY := by rw [hsP', hsP, ← Category.assoc, hpg]
  have hiF := F.imm_comp_structureMorphism C sX sY hf
  have hiF' : F'.imm ≫ sP' = sX := by rw [hP']; exact F'.imm_comp_structureMorphism C sX sY hf
  have hri := F.isRegularImmersion hlci
  have hri' := F'.isRegularImmersion hlci
  have hjp := pullbackSnd_comp_structureMorphism_eq C sX sP F.imm hiF p
  have hsj := F.refinementSection_comp_proj p hp
  have hss := F.refinementSection_comp_retraction p hp
  have hsW : F.refinementSection p hp ≫ sW = sX := comp_structureMorphism_of_comp_eq_id rfl hss
  have hrs := F.isRegularImmersion_refinementSection p hp
  have hrj : IsRegularImmersion (F.refinementProj p) :=
    (isRegularImmersion_iff_isKoszulRegularImmersion _).2
      (F.isKoszulRegularImmersion_refinementProj p (F.isKoszulRegularImmersion_of_lci hlci))
  have hrsj : IsRegularImmersion (F.refinementSection p hp ≫ F.refinementProj p) := by
    convert hri'
  -- the classes
  set iB := completedVirtualNormalGysinClassOfImmersion C sX sP F.imm hiF
    (VirtualNormalBundle.ofIsRegularImmersion F.imm hri)
  set gB := completedFlatPullbackOfSmooth C sP sY F.proj rfl
  set pB := completedFlatPullbackOfSmooth C sP' sP p rfl
  set jB := completedVirtualNormalGysinClassOfImmersion C sW sP' (F.refinementProj p) hjp
    (VirtualNormalBundle.ofIsRegularImmersion (F.refinementProj p) hrj)
  set sB := completedVirtualNormalGysinClassOfImmersion C sX sW (F.refinementSection p hp) hsW
    (VirtualNormalBundle.ofIsRegularImmersion (F.refinementSection p hp) hrs)
  set pbB := completedFlatPullbackOfSmooth C sW sX (F.refinementRetraction p) rfl
  -- Stacks 0FF0: `(i')^! = s^! ∘ j^!`
  have h0 := hcomp sX sW sP' (F.refinementSection p hp) (F.refinementProj p) hsW hjp hrs hrj hrsj
  -- Stacks 0FBK: `j^!` is the restriction of `i^!`
  have h1 := regularImmersionSmoothBaseChangeCase C sX sP F.imm hiF p hri hrj
  -- `j^! ∘ p^* = p̄^* ∘ i^!`
  have h2 := completedBivariantRestriction_composite_completedFlatPullbackOfSmooth C sX sP F.imm
    hiF p iB
  rw [h1] at h2
  -- Stacks 0FF1: `s^! ∘ p̄^* = 1`
  have h3 := completedBivariantCompositeOfInvertible_completedFlatPullbackOfSmooth_of_section C sX
    sW (F.refinementRetraction p) rfl (F.refinementSection p hp) hss
  -- Stacks 02RD: `(g')^* = p^* ∘ g^*`
  have h4 := completedFlatPullbackOfSmooth_comp C sP' sP sY p F.proj rfl rfl
  -- `(i')^! ∘ p^* = i^!`
  set iB' := completedVirtualNormalGysinClassOfImmersion C sX sP' F'.imm hiF'
    (VirtualNormalBundle.ofIsRegularImmersion F'.imm hri')
  have hcore : completedBivariantCompositeOfInvertible C sX sP' sP F'.imm p hiF' rfl iB' pB ≍
      iB := by
    refine (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl hsj.symm rfl
      (hf' := comp_comp_structureMorphism_eq hsW hjp)
      (completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr C rfl hsj.symm
        (hi' := comp_comp_structureMorphism_eq hsW hjp) hri' hrsj) HEq.rfl).trans ?_
    rw [h0]
    refine (completedBivariantCompositeOfInvertible_assoc C ..).trans ?_
    refine (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl rfl
      pullback.condition.symm HEq.rfl h2).trans ?_
    refine (completedBivariantCompositeOfInvertible_assoc C ..).symm.trans ?_
    refine (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl hss rfl
      ((completedBivariantGroup.copy_heq C ..).symm.trans (heq_of_eq h3)) HEq.rfl).trans ?_
    exact completedIdentityClass_completedBivariantCompositeOfInvertible C sX sP F.imm hiF iB
  -- assembling
  refine eq_of_heq ((completedBivariantGroup.copy_heq C ..).trans (HEq.trans ?_
    (completedBivariantGroup.copy_heq C ..).symm))
  have hA : completedBivariantCompositeOfInvertible C sX (F'.proj ≫ sY) sY F'.imm F'.proj
      (F'.imm_comp_structureMorphism C sX sY hf) rfl
      (completedVirtualNormalGysinClassOfImmersion C sX (F'.proj ≫ sY) F'.imm
        (F'.imm_comp_structureMorphism C sX sY hf)
        (VirtualNormalBundle.ofIsRegularImmersion F'.imm hri'))
      (completedFlatPullbackOfSmooth C (F'.proj ≫ sY) sY F'.proj rfl) ≍
      completedBivariantCompositeOfInvertible C sX sP' sY F'.imm (p ≫ F.proj) hiF'
        (comp_comp_structureMorphism_eq rfl rfl)
        iB' (completedBivariantCompositeOfInvertible C sP' sP sY p F.proj rfl rfl pB gB) :=
    completedBivariantCompositeOfInvertible_heq_congr C rfl hP'.symm rfl rfl hpg.symm
      (completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr C hP'.symm rfl
        hri' hri')
      ((completedFlatPullbackOfSmooth_heq_congr C hP'.symm hpg.symm).trans (heq_of_eq h4.symm))
  refine hA.trans ?_
  refine (completedBivariantCompositeOfInvertible_assoc C ..).symm.trans ?_
  exact completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl hp rfl hcore HEq.rfl

/-- **Stacks 0FF2.** The Gysin map `i^! ∘ g^*` of a local complete intersection morphism `f` does
not depend on the factorization `f = g ∘ i` (`i` an immersion, `g` smooth): two factorizations are
refined by a common one (`Stacks.Chow.SmoothFactorization.exists_refines_both`), and the Gysin map
is unchanged by refinement
(`Stacks.Chow.SmoothFactorization.gysinMap_eq_of_refines_of_regularImmersionCompositionCase`). -/
theorem SmoothFactorization.gysinMap_eq_of_regularImmersionCompositionCase
    (hcomp : RegularImmersionCompositionCase C) (F F' : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    F.gysinMap C sX sY hf hlci = F'.gysinMap C sX sY hf hlci :=
  SmoothFactorization.eq_of_refines_invariant F F' (fun F ↦ F.gysinMap C sX sY hf hlci)
    fun _ _ h ↦
      SmoothFactorization.gysinMap_eq_of_refines_of_regularImmersionCompositionCase C sX sY hf
        hcomp h hlci

/-- **Stacks 0FF2, for the Gysin map `f^!`.** The Gysin map of any factorization of `f` as an
immersion followed by a smooth morphism is the Gysin map `f^!` of Stacks 0FF3. -/
theorem SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase
    (hcomp : RegularImmersionCompositionCase C) (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) :
    F.gysinMap C sX sY hf hlci = lciGysinMap C sX sY hf hlci h :=
  SmoothFactorization.gysinMap_eq_of_regularImmersionCompositionCase C sX sY hf hcomp F _ hlci

end Independence

end Stacks.Chow

end
