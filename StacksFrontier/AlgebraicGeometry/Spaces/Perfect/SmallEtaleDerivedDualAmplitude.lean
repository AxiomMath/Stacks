module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.DerivedDualOfAStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex

/-!
# The derived dual of a strictly perfect complex in degrees `≥ m` lies in `D^{≤ -m}`

Let `X` be an algebraic space and `P` a bounded complex of `𝒪_X`-modules whose terms are
retracts of finite free modules and vanish in degrees `< m`. Then the derived dual
`(P)^∨ = R𝓗om(P, 𝒪_X)` (`AlgebraicGeometry.Space.smallEtaleDerivedDual`) lies in `D^{≤ -m}`.

The dual is read on the equi-universe model of the small étale site, where Stacks 08JH
(`AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplex`) computes it by the internal Hom
complex `𝑆heafHom(P, 𝒪[0])`. The degree `n` term of that complex is `𝑆heafHom(P^{-n}, 𝒪)`
(`AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso`), which vanishes for `n > -m`. The
inverse of the exact equivalence with the model preserves `D^{≤ -m}`.

## Main results

* `AlgebraicGeometry.Space.isLE_smallEtaleDerivedDual_Q_of_isStrictlyGE`: the statement above.
* `AlgebraicGeometry.Space.isLE_smallEtaleDerivedDual_of_iso_Q_of_isStrictlyGE`: the same for an
  object isomorphic to such a complex.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The derived dual of a strictly perfect complex in degrees `≥ m` lies in `D^{≤ -m}`.** Let
`P` be a complex of `𝒪_X`-modules on an algebraic space `X`, with finitely many nonzero terms, each
a retract of a finite free module, and with `P^i = 0` for `i < m`. Then
`R𝓗om(P, 𝒪_X) ∈ D^{≤ -m}`. -/
theorem isLE_smallEtaleDerivedDual_Q_of_isStrictlyGE
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) (P.X j))
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (m : ℤ) [P.IsStrictlyGE m] :
    (smallEtaleDerivedDual B S hS X (DerivedCategory.Q.obj P)).IsLE (-m) := by
  let e := smallEtaleModelModulesEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  let P' := (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP' : {i : ℤ | ¬ IsZero (P'.X i)}.Finite :=
    hbdd.subset fun i hi h => hi (e.functor.map_isZero h)
  have hterm : ∀ i, RingedSite.IsFiniteFreeSummand M (P'.X i) := fun i => by
    obtain ⟨n, a, b, hab⟩ := hP i
    refine (RingedSite.isFiniteFreeSummand_iff_retract_biproduct M _).2
      ⟨n, ⟨⟨e.functor.map a ≫ (e.functor.mapBiproduct
          (fun _ : Fin n => SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))).hom ≫
          (biproduct.mapIso fun _ => smallEtaleModelModulesUnitIso B S hS X).hom,
        (biproduct.mapIso fun _ => smallEtaleModelModulesUnitIso B S hS X).inv ≫
          (e.functor.mapBiproduct
            (fun _ : Fin n => SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))).inv ≫
            e.functor.map b, ?_⟩⟩⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp, hab]
    exact e.functor.map_id _
  let C := (RingedSite.sheafHomComplex M P' (RingedSite.structureSheafComplex M)).obj
  have hC : C.IsStrictlyLE (-m) := by
    refine (CochainComplex.isStrictlyLE_iff C (-m)).2 fun n hn => ?_
    refine (RingedSite.internalHomSheaf_isZero_of_isZero M ?_).of_iso
      (RingedSite.homStructureSheafDegreeIso M P' hP' n)
    exact e.functor.map_isZero (P.isZero_of_isStrictlyGE m (-n) (by omega))
  let D := ((RingedSite.derivedSheafHomBifunctor M).obj
      (op ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
        (DerivedCategory.Q.obj P)))).obj
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))))
  let i₁ : D ≅ DerivedCategory.Q.obj C :=
    ((RingedSite.derivedSheafHomBifunctor M).mapIso
        (e.functor.mapDerivedCategoryFactors.app P).symm.op).app _ ≪≫
      ((RingedSite.derivedSheafHomBifunctor M).obj (op (DerivedCategory.Q.obj P'))).mapIso
        (smallEtaleModelDerivedStructureSheafIso B S hS X) ≪≫
      RingedSite.derivedDualIsoSheafHomComplex M P' hP' hterm
  have : (DerivedCategory.Q.obj C).IsLE (-m) := inferInstance
  have := DerivedCategory.TStructure.t.isLE_of_iso i₁.symm (-m)
  exact Stacks.Homology.isLE_mapDerivedCategory_obj e.inverse D (-m)

/-- **The derived dual of an object with a strictly perfect model in degrees `≥ m` lies in
`D^{≤ -m}`.** -/
theorem isLE_smallEtaleDerivedDual_of_iso_Q_of_isStrictlyGE
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) (P.X j))
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (m : ℤ) [P.IsStrictlyGE m]
    (eK : K ≅ DerivedCategory.Q.obj P) :
    (smallEtaleDerivedDual B S hS X K).IsLE (-m) := by
  have : DerivedCategory.TStructure.t.IsLE (((smallEtaleDerivedSheafHom B S hS X).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))).obj
      (op (DerivedCategory.Q.obj P))) (-m) :=
    isLE_smallEtaleDerivedDual_Q_of_isStrictlyGE P hP hbdd m
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((smallEtaleDerivedSheafHom B S hS X).flip.obj _).mapIso eK.op) (-m)

end AlgebraicGeometry.Space

end
