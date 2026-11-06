module

public import StacksFrontier.AlgebraicGeometry.Curves.PencilDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.LinearSystem
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# A smooth proper curve of genus zero over an algebraically closed field is `𝐏¹`

Let `K` be an algebraically closed field and `C` a smooth proper curve over `K` of genus `0`.
Then `C ≅ 𝐏¹_K` over `K`, where `𝐏¹_K` is `AlgebraicGeometry.projectiveSpaceOver 1 (Spec K)`
([Stacks, Tag 01NF]).

The proof is the classical one. The degree on `Pic(C)` is onto, so there is an invertible
module `ℒ` of degree `1`; by Riemann–Roch ([Stacks, Tag 0B90] in the form
`Stacks.Zeta.h0_eq_of_le`) `dim H⁰(C, ℒ) = 1 + 1 - 0 = 2`, so `(ℒ, H⁰(C, ℒ))` is a `𝔤¹_1`.
By [Stacks, Tag 0CCR] the attached morphism `p : C ⟶ 𝐏¹_K` is either nonconstant of degree
`≤ 1`, or constant with `H⁰(C, 𝒪_C) ≠ K`; the second alternative is impossible because
`H⁰(C, 𝒪_C) = K`. A nonconstant morphism of curves has positive degree, its extension of
function fields being finite (`AlgebraicGeometry.finiteDimensional_functionField_of_isCurve`),
so `deg p = 1`: `p` induces an isomorphism of function fields, and a morphism of normal proper
curves inducing an isomorphism of function fields is an isomorphism ([Stacks, Tag 0BY1], in the
form `AlgebraicGeometry.isIso_of_bijective_functionFieldMap`).

## Main results

* `AlgebraicGeometry.isIso_of_degreeOver_eq_one`: a morphism of degree one between normal proper
  curves over a field is an isomorphism.
* `AlgebraicGeometry.exists_isIso_projectiveSpaceOver_one_of_genus_eq_zero`: a smooth proper
  curve of genus zero over an algebraically closed field is isomorphic to `𝐏¹` over the field.
* `AlgebraicGeometry.one_le_genus_of_not_exists_iso_projectiveSpaceOver_one`: the contrapositive,
  in the form `X ≇ 𝐏¹ ⇒ genus ≥ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.isCurve_projectiveSpaceOver_one

variable {k : Type u} [Field k]

/-- The function-field map of a dominant morphism of integral schemes, in the two spellings
`AlgebraicGeometry.functionFieldMap` and `AlgebraicGeometry.dominantFunctionFieldMap`. -/
theorem functionFieldMap_eq_dominantFunctionFieldMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant h] :
    functionFieldMap h = dominantFunctionFieldMap h :=
  (congrArg CommRingCat.Hom.hom
    (stalkMap_cast_target h (genericPoint X) (map_genericPoint_of_isDominant h))).symm

/-- **A dominant morphism of curves over `k` has positive degree.** -/
theorem degreeOver_pos_of_isCurve {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsDominant f] [LocallyOfFiniteType f] : 0 < degreeOver f := by
  have hfin := finiteDimensional_functionField_of_isCurve pX pY f hf
  rw [functionFieldMap_eq_dominantFunctionFieldMap f] at hfin
  exact degreeOver_pos f hfin

set_option backward.isDefEq.respectTransparency false in
/-- **A morphism of degree one between normal proper curves over a field is an isomorphism.**
Degree one makes the extension of function fields an isomorphism, and a morphism of normal
proper curves is determined by, and exists for, every map of function fields ([Stacks, Tag
0BY1]). -/
theorem isIso_of_degreeOver_eq_one {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
    [IsNormal X] [IsNormal Y] (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f]
    [LocallyOfFiniteType f] (h1 : degreeOver f = 1) : IsIso f := by
  let V : Variety k := { toScheme := X, structureMap := pX }
  let W : Variety k := { toScheme := Y, structureMap := pY }
  have : IsCurve k V.structureMap := ‹IsCurve k pX›
  have : IsCurve k W.structureMap := ‹IsCurve k pY›
  have : IsProper V.structureMap := ‹IsProper pX›
  have : IsProper W.structureMap := ‹IsProper pY›
  have : IsNormal V.toScheme := ‹IsNormal X›
  have : IsNormal W.toScheme := ‹IsNormal Y›
  let g : Over.mk V.structureMap ⟶ Over.mk W.structureMap := Over.homMk f hf
  have : IsDominant g.left := ‹IsDominant f›
  have hbij : Function.Bijective (functionFieldMap g.left) := by
    change Function.Bijective (functionFieldMap f)
    have key : ∀ {A B : Type u} [Field A] [Field B] (φ : A →+* B),
        (letI := φ.toAlgebra; Module.finrank A B = 1) → Function.Bijective φ := by
      intro A B _ _ φ h
      letI := φ.toAlgebra
      exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h
    let := (functionFieldMap f).toAlgebra
    have hfr : Module.finrank Y.functionField X.functionField = 1 := by
      rwa [← degreeOver_eq_finrank f (functionFieldMap_eq_dominantFunctionFieldMap f)]
    exact key (functionFieldMap f) hfr
  have := isIso_of_bijective_functionFieldMap V W g hbij
  exact inferInstanceAs (IsIso ((Over.forget _).map g))

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (g : C ⟶ Spec (.of K))
  [IsCurve K g] [Smooth g] [IsProper g]

omit [IsCurve K g] [Smooth g] in
/-- On a proper integral scheme over an algebraically closed field, `H⁰(C, 𝒪_C)` has rank one. -/
theorem rank_cohomologyOverField_unit_zero_eq_one [IsIntegral C] :
    Module.rank K (cohomologyOverField K g (SheafOfModules.unit C.ringCatSheaf) 0) = 1 := by
  have h1 : Module.finrank K
      (cohomologyOverField K g (SheafOfModules.unit C.ringCatSheaf) 0) = 1 := by
    rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    exact finrank_globalSections_eq_one K g
  have : Module.Finite K
      (cohomologyOverField K g (SheafOfModules.unit C.ringCatSheaf) 0) :=
    Module.finite_of_finrank_pos (by omega)
  rw [← Module.finrank_eq_rank, h1, Nat.cast_one]

/-- **A smooth proper curve of genus zero over an algebraically closed field `K` is isomorphic
to `𝐏¹_K` over `K`.** -/
theorem exists_isIso_projectiveSpaceOver_one_of_genus_eq_zero (hg : genus g = 0) :
    ∃ p : C ⟶ projectiveSpaceOver 1 (Spec (.of K)), IsIso p ∧
      p ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) = g := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  have hdim : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := g)).le
  obtain ⟨c, hc⟩ := Stacks.Picard.picardDegree_surjective g 1
  have hh0 : Stacks.Zeta.h0 g c = 2 := by
    have hc' : Stacks.Picard.picardDegree g (Stacks.Zeta.topologicalKrullDim_le_one g) c = 1 :=
      hc
    have := Stacks.Zeta.h0_eq_of_le g c (by rw [hg, hc']; norm_num)
    rw [hg, hc'] at this
    omega
  let E : LinearSeries K g hdim 1 1 :=
    { L := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
      isInvertible :=
        (Stacks.Picard.picardRepresentative C.toRingedSpace c).property.toAlgebraicGeometry
      degree_eq := by
        exact_mod_cast (Stacks.Picard.picardDegree_apply g hdim c).symm.trans hc
      V := ⊤
      finrank_eq := by rwa [finrank_top] }
  obtain ⟨⟨b, p, hp, α, hα⟩, hall⟩ :=
    Stacks.LinearSeriesMorphism.degreeOver_le_or_constant_of_isRegular K g
      (isRegular_of_smooth_over_field g) E
  rcases hall b p hp α hα with ⟨hnc, hle⟩ | ⟨-, hrank⟩
  · have : LocallyOfFiniteType p := locallyOfFiniteType_of_isCurve_comp
      K g (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) p hp
    have : IsDominant p := isDominant_of_not_constant K g
      (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) p hnc
    have : IsNormal C := isNormal_of_isRegular C (isRegular_of_smooth_over_field g)
    have : IsNormal (projectiveSpaceOver 1 (Spec (.of K))) :=
      isNormal_of_isRegular _
        (isRegular_of_smooth_over_field (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)))
    have hpos := degreeOver_pos_of_isCurve g
      (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) p hp
    exact ⟨p, isIso_of_degreeOver_eq_one g _ p hp (by omega), hp⟩
  · rw [rank_cohomologyOverField_unit_zero_eq_one g] at hrank
    exact (lt_irrefl _ hrank).elim

/-- **If a smooth proper curve over an algebraically closed field `K` is not isomorphic to
`𝐏¹_K` over `K`, its genus is at least one.** -/
theorem one_le_genus_of_not_exists_iso_projectiveSpaceOver_one
    (h : ¬ ∃ e : C ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) = g) :
    1 ≤ genus g := by
  by_contra hlt
  obtain ⟨p, hiso, hp⟩ :=
    exists_isIso_projectiveSpaceOver_one_of_genus_eq_zero g (by omega)
  exact h ⟨asIso p, hp⟩

end AlgebraicGeometry

end
