module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BettiNumbersOnPointsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.RepresentedZariski

/-!
# Upper semicontinuity and constructible level sets for the Betti function of a pseudo-coherent
complex

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `E` be a pseudo-coherent
object of `D(𝒪_X)`.  The `i`-th Betti-number function `β_i : |X| → ℕ` of `E` is
`AlgebraicGeometry.Space.geometricFibreBettiFunction`.  This file proves clauses (2) and (3) of
[Stacks, Tag 0D1Y] for it, with no hypothesis beyond pseudo-coherence of `E`: `β_i` is upper
semicontinuous and each of its level sets is étale locally constructible.

The function `β_i` has the property `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`:
on every étale chart it agrees, under the homeomorphism `|h_U| ≅ U` of [Stacks, Tag 03BX], with
the derived-fibre Betti function of a pseudo-coherent complex on the charting scheme.

## Main results

* `AlgebraicGeometry.Space.exists_isPseudoCoherent_representedDerivedAssociatedModule_iso`: a
  pseudo-coherent object of `D(𝒪_{h_T})` on a represented algebraic space is `ε^*ω` for a
  pseudo-coherent `ω ∈ D(𝒪_T)`.
* `AlgebraicGeometry.Space.isEtaleLocallyDerivedFibreBetti_derivedFibreBetti`: the derived-fibre
  Betti function of a pseudo-coherent object of `D(𝒪_X)` is an `i`-th Betti-number function in
  the sense of `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`.
* `AlgebraicGeometry.Space.geometricFibreBetti_eq_derivedFibreBettiAt` and
  `AlgebraicGeometry.Space.geometricFibreBettiFunction_eq_derivedFibreBetti`: the Betti number at
  a geometric point is the derived-fibre Betti number at the underlying field-valued point, and
  the two functions on `|X|` agree.
* `AlgebraicGeometry.Space.upperSemicontinuous_geometricFibreBettiFunction`: **clause (2) of
  [Stacks, Tag 0D1Y]**.
* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_setOf_geometricFibreBettiFunction_eq`:
  **clause (3) of [Stacks, Tag 0D1Y]**.

## Implementation notes

*The comparison on a chart.*  For a chart `φ : h_U ⟶ X`, the derived pullback `Lφ^*E` is
pseudo-coherent ([Stacks, Tag 08H4] for algebraic spaces), hence lies in `D_QCoh`
([Stacks, Tag 08JL]), hence is `ε^*ω` for an object `ω` of `D(𝒪_U)` ([Stacks, Tag 071Q]), and
`ω` is pseudo-coherent by clause (2) ⇒ (1) of [Stacks, Tag 08HE] read on a represented space.

*The two Betti functions.*  The library carries two constructions of `β_i`: the dimension of the
cohomology of the derived fibre at a geometric point
(`AlgebraicGeometry.Space.geometricFibreBetti`) and the dimension of its global sections at a
field-valued point (`AlgebraicGeometry.Space.derivedFibreBettiAt`).  They are equal
(`AlgebraicGeometry.Space.geometricFibreBettiFunction_eq_derivedFibreBetti`).

*Pseudo-coherence.*  The source's hypothesis, "`E ∈ D(𝒪_X)` pseudo-coherent (for example
perfect)", is `AlgebraicGeometry.RingedSite.IsPseudoCoherent` on the small étale ringed site of
`X`.  No bound, no quasi-compactness and no separatedness is assumed of `X`.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pseudo-coherent objects on a represented algebraic space -/

/-- **A pseudo-coherent object of `D(𝒪_{h_T})` is `ε^*ω` for a pseudo-coherent `ω ∈ D(𝒪_T)`.**
See [Stacks, Tag 08JL], [Stacks, Tag 071Q] and clause (2) ⇒ (1) of [Stacks, Tag 08HE]. -/
theorem exists_isPseudoCoherent_representedDerivedAssociatedModule_iso
    (T : BigFppfOver B S hS)
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hK : (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherent K) :
    ∃ (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (_hω : RingedSpace.IsPseudoCoherent
        (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ω),
      Nonempty ((representedDerivedAssociatedModule B S hS T).obj ω ≅ K) := by
  obtain ⟨ω, _hωqc, ⟨eω⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T K
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) K hK)
  obtain ⟨P, hP, ⟨eP⟩⟩ := hK
  let L := DerivedCategory.Q.objPreimage ω
  let eL : DerivedCategory.Q.obj L ≅ ω := DerivedCategory.Q.objObjPreimageIso ω
  let εL := ((representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let eεL : DerivedCategory.Q.obj εL ≅ K :=
    ((representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactors.app L).symm ≪≫
      (representedDerivedAssociatedModule B S hS T).mapIso eL ≪≫ eω
  refine ⟨ω, ⟨L, fun m => ?_, ⟨eL⟩⟩, ⟨eω⟩⟩
  exact (isPseudoCoherentComplexFrom_representedAssociatedModule_iff B S hS T L m).1
    ((smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).isPseudoCoherentComplexFrom_of_iso_general K m
        ⟨P, hP m, ⟨eP⟩⟩ εL eεL)

variable {X : AlgebraicSpaces B S hS}

/-! ### The Betti function of a pseudo-coherent complex is a Betti-number function -/

/-- **The derived-fibre Betti function of a pseudo-coherent object of `D(𝒪_X)` is an `i`-th
Betti-number function.**  On every étale chart it agrees, under the homeomorphism of
[Stacks, Tag 03BX], with the derived-fibre Betti function of a pseudo-coherent complex on the
charting scheme. -/
theorem isEtaleLocallyDerivedFibreBetti_derivedFibreBetti
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (i : ℤ) :
    IsEtaleLocallyDerivedFibreBetti B S hS X.1 (derivedFibreBetti X E i) i := by
  have hEqc := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  intro U φ _
  let g : schemeSpace U ⟶ X := ObjectProperty.homMk φ
  let K := (smallEtaleDerivedModulePullback B S hS g).obj E
  have hK : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherent K :=
    isPseudoCoherent_smallEtaleDerivedModulePullback g E hE
  obtain ⟨ω, hω, ⟨eω⟩⟩ :=
    exists_isPseudoCoherent_representedDerivedAssociatedModule_iso B S hS U K hK
  refine ⟨ω, hω, ?_⟩
  funext z
  set x := (schemePointsHomeomorph B S hS U).symm z
  have hz : z = schemePoint B S hS U (Quot.out x) :=
    ((schemePointsHomeomorph B S hS U).apply_symm_apply z).symm.trans
      (congrArg (pointsToScheme B S hS U) (Quot.out_eq x)).symm
  have hclass : (FieldValuedPoint.map B S hS (yoneda.obj U) φ (Quot.out x)).class B S hS X.1 =
      pointsMap B S hS (yoneda.obj U) φ x :=
    (pointsMap_class B S hS (yoneda.obj U) φ (Quot.out x)).symm.trans
      (congrArg (pointsMap B S hS (yoneda.obj U) φ) (Quot.out_eq x))
  calc DerivedFibreBetti.derivedFiberBetti ((BigFppfOver.toScheme B S hS).obj U) ω hω i z
      = derivedFibreBettiAt (schemeSpace U)
          ((representedDerivedAssociatedModule B S hS U).obj ω) i (Quot.out x) := by
        rw [hz]
        exact (derivedFibreBettiAt_representedDerivedAssociatedModule_eq_derivedFiberBetti
          B S hS U ω hω i (Quot.out x)).symm
    _ = derivedFibreBettiAt (schemeSpace U) K i (Quot.out x) :=
        derivedFibreBettiAt_congr (schemeSpace U) eω i (Quot.out x)
    _ = derivedFibreBettiAt X E i
          (FieldValuedPoint.map B S hS (yoneda.obj U) φ (Quot.out x)) :=
        derivedFibreBettiAt_derivedPullback X g E i (Quot.out x)
    _ = derivedFibreBettiAt X E i (Quot.out (pointsMap B S hS (yoneda.obj U) φ x)) :=
        derivedFibreBettiAt_eq_of_class_eq B S hS X E hEqc i
          (hclass.trans (Quot.out_eq _).symm)
    _ = (derivedFibreBetti X E i ∘ pointsMap B S hS (yoneda.obj U) φ ∘
          (schemePointsHomeomorph B S hS U).symm) z := rfl

/-! ### The geometric-point and field-valued-point Betti functions agree -/

/-- Restriction of scalars along a bijective ring homomorphism does not change the dimension. -/
private theorem finrank_restrictScalars_of_bijective {R R' : Type u} [Ring R] [Ring R']
    (f : R →+* R') (hf : Function.Bijective f) (M : ModuleCat.{u} R') :
    Module.finrank R ((ModuleCat.restrictScalars f).obj M) = Module.finrank R' M :=
  congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (M := ((ModuleCat.restrictScalars f).obj M)) (M₁ := M) f
      (AddEquiv.refl M) hf fun _ _ => rfl)

/-- **The Betti number at a geometric point is the derived-fibre Betti number at the underlying
field-valued point.** -/
theorem geometricFibreBetti_eq_derivedFibreBettiAt
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i : ℤ) (x : GeometricPoint B S hS X.1) :
    geometricFibreBetti B S hS E i x = derivedFibreBettiAt X E i x.val := by
  rw [geometricFibreBetti_eq_finrank_idChart]
  have : IsIso x.val.fieldToSections :=
    inferInstanceAs (IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).inv))
  exact (finrank_restrictScalars_of_bijective x.val.fieldToSections.hom
    (ConcreteCategory.bijective_of_isIso x.val.fieldToSections) _).symm

/-- **The two Betti-number functions of a pseudo-coherent object of `D(𝒪_X)` on `|X|` agree.** -/
theorem geometricFibreBettiFunction_eq_derivedFibreBetti
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (i : ℤ) :
    geometricFibreBettiFunction B S hS E i = derivedFibreBetti X E i := by
  have hEqc := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  funext y
  exact (geometricFibreBetti_eq_derivedFibreBettiAt B S hS E i
    (canonicalGeometricPoint B S hS X.1 y)).trans
      (derivedFibreBettiAt_eq_of_class_eq B S hS X E hEqc i
        ((canonicalGeometricPoint_image B S hS X.1 y).trans (Quot.out_eq y).symm))

/-- **The Betti-number function `β_i` of [Stacks, Tag 0D1Y] of a pseudo-coherent object of
`D(𝒪_X)` is an `i`-th Betti-number function** in the sense of
`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`. -/
theorem isEtaleLocallyDerivedFibreBetti_geometricFibreBettiFunction
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (i : ℤ) :
    IsEtaleLocallyDerivedFibreBetti B S hS X.1 (geometricFibreBettiFunction B S hS E i) i := by
  rw [geometricFibreBettiFunction_eq_derivedFibreBetti B S hS E hE i]
  exact isEtaleLocallyDerivedFibreBetti_derivedFibreBetti B S hS E hE i

/-! ### Clauses (2) and (3) of Stacks 0D1Y -/

/-- **Stacks 0D1Y, clause (2): the functions `β_i` are upper semi-continuous.**  For a
pseudo-coherent object `E` of `D(𝒪_X)` on an algebraic space `X` over `S`, the `i`-th
Betti-number function `β_i : |X| → ℕ` of `E` is upper semicontinuous.

Nothing is assumed beyond pseudo-coherence of `E`.  The scheme-level input is part (2) of
[Stacks, Tag 0BDI]. -/
@[stacks 0D1Y "clause (2)"]
theorem upperSemicontinuous_geometricFibreBettiFunction
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (i : ℤ) :
    UpperSemicontinuous (geometricFibreBettiFunction B S hS E i) :=
  IsEtaleLocallyDerivedFibreBetti.upperSemicontinuous B S hS X.1
    (geometricFibreBettiFunction B S hS E i) i X.2
    (isEtaleLocallyDerivedFibreBetti_geometricFibreBettiFunction B S hS E hE i)

/-- **Stacks 0D1Y, clause (3): the level sets of `β_i` are étale locally constructible.**  For a
pseudo-coherent object `E` of `D(𝒪_X)` on an algebraic space `X` over `S` and a natural number
`n`, the level set `{x ∈ |X| : β_i(x) = n}` is étale locally constructible in the sense of
[Stacks, Tag 0ECU].

Nothing is assumed beyond pseudo-coherence of `E`.  The scheme-level input is part (3) of
[Stacks, Tag 0BDI]. -/
@[stacks 0D1Y "clause (3)"]
theorem isEtaleLocallyConstructible_setOf_geometricFibreBettiFunction_eq
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (i : ℤ) (n : ℕ) :
    IsEtaleLocallyConstructible B S hS X.1 {x | geometricFibreBettiFunction B S hS E i x = n} :=
  IsEtaleLocallyDerivedFibreBetti.isEtaleLocallyConstructible_setOf_eq B S hS X.1
    (geometricFibreBettiFunction B S hS E i) i
    (isEtaleLocallyDerivedFibreBetti_geometricFibreBettiFunction B S hS E hE i) n

end AlgebraicGeometry.Space

end
