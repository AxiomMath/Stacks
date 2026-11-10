module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.CochainShift
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality

/-!
# Derived Hom commutes with the shift in its target

Let `A` be a commutative ring and let `D(A)` be the derived category of `A`-modules. For a fixed
object `Ω` of `D(A)`, derived Hom into `Ω` is the contravariant functor `K ↦ RHom_A(K, Ω)` of
`Dualizing.dualizingDerivedHomFunctor`. This file proves that shifting the target commutes with
derived Hom, naturally in the source:

`RHom_A(K, Ω⟦i⟧) ≅ RHom_A(K, Ω)⟦i⟧`     naturally in `K`.

The construction descends the cochain-level identification
`StacksDraft.DerivedHom.HomShift.homComplexIntoShiftIso` through the K-injective Hom model
`StacksDraft.DerivedHom.derivedHomModelIso`. The descent is a localization lift and needs
exactly one piece of coherence that the model carries: the model is natural in the source
complex, because it is built from the bifunctor isomorphism
`StacksDraft.DerivedHom.derivedHomULiftIso` and from
`StacksDraft.DerivedHom.DerivedHomData.homIso`, whose naturality in both chain maps is the
structure field `StacksDraft.DerivedHom.DerivedHomData.homIso_naturality`. That naturality,
recorded here as `StacksDraft.DerivedHom.HomShift.derivedHomModelIso_naturality`, turns the
model into a `CategoryTheory.Localization.Lifting` datum for the localization functor
`Q ⋙ (restriction of scalars)`, whose opposite is again a localization functor; the cochain
identification then lifts to an isomorphism of functors on `D(A)ᵒᵖ` by
`CategoryTheory.Localization.liftNatIso`. No naturality of the Hom-complex shift in the
*target* complex is needed, and none is available, which is why the descent is arranged in the
source variable.

The K-injective model exists for every object, so the hypothesis of
`Dualizing.dualizingDerivedHomShiftIsoOfModel` can be discharged for an arbitrary `Ω`.

## Main definitions

* `StacksDraft.DerivedHom.HomShift.derivedHomShiftIsoOfModel` — the localization lift, for a
  target presented by a K-injective cochain complex of `ULift A`-modules.
* `Dualizing.dualizingDerivedHomShiftIso` — the shift identification for an arbitrary target,
  as an isomorphism of contravariant functors on `D(A)`.
* `Dualizing.dualizingDerivedHomShift` — its component
  `RHom_A(K, Ω⟦i⟧) ≅ RHom_A(K, Ω)⟦i⟧`.

## Main results

* `StacksDraft.DerivedHom.HomShift.derivedHomModelIso_naturality` — the K-injective Hom model
  is natural in the source complex.
* `Dualizing.dualizingDerivedHomShift_naturality` — the shift identification is natural in the
  source object, written at the spelling of the derived-Hom bifunctor itself.

## Implementation notes

The derived category of `A`-modules is taken at the standard model, as in
`StacksFrontier/RingTheory/Dualizing/DualizingDerivedHom.lean` and
`StacksFrontier/RingTheory/Dualizing/DerivedHomDuality/Duality.lean`: the model is baked
into the type
of `Dualizing.dualizingDerivedHomFunctor`, so it is forced here rather than chosen. No
statement in this file mentions coproducts, and the standard model is a legitimate derived
category of `ModuleCat A`, so nothing is weakened by the pin.

The scalar transport of derived categories commutes with the shift because it is the derived
functor of an exact functor, but instance resolution cannot see that through the tactic-mode
definition of `StacksDraft.DerivedHom.uliftDerivedEquivalence`; the identification is supplied
by hand as `StacksDraft.DerivedHom.HomShift.scalarEquivalenceCommShift`, in the same way as the
additivity instances next to that definition.

Only the shift in the target is proved here. The companion identification
`RHom_A(K⟦-i⟧, Ω) ≅ RHom_A(K, Ω)⟦i⟧`, which shifts the source, is a different statement and
does not follow formally from this one.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace StacksDraft.DerivedHom.HomShift

universe u v

attribute [local instance 5000] HasDerivedCategory.standard

section Model

universe u1 w1

/-- Every object of the derived category of modules is represented by a K-injective cochain
complex. -/
theorem exists_isKInjective_model {R : Type u1} [CommRing R]
    [HasDerivedCategory.{w1} (ModuleCat.{u1} R)] (X : DerivedCategory (ModuleCat.{u1} R)) :
    ∃ I : CochainComplex (ModuleCat.{u1} R) ℤ,
      I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ X) := by
  obtain ⟨I, f, hf, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage X)
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map f)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩

end Model

variable (A : Type u) [CommRing A]

/-- The localization of cochain complexes of `ULift A`-modules, followed by restriction of
scalars: the composite through which the K-injective Hom model of
`StacksDraft.DerivedHom.derivedHomModelIso` is stated. -/
abbrev scalarLocalization :
    Model.Complex (ULift.{v} A) ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  DerivedCategory.Q ⋙ (derivedScalarEquivalence.{u, v} A).functor

/-- Derived Hom into a fixed object is the derived-Hom bifunctor with its covariant variable
fixed. This is the form in which the shift identification is constructed, and it is the same
functor as `Dualizing.dualizingDerivedHomFunctor`. -/
theorem dualizingDerivedHomFunctor_eq_flip (Ω : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.dualizingDerivedHomFunctor.{u, v} A Ω =
      (Functor.curry.obj
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom).flip.obj Ω :=
  rfl

/-- **The K-injective Hom model is natural in the source complex.** The model is the bifunctor
isomorphism `StacksDraft.DerivedHom.derivedHomULiftIso` followed by the scalar transport of the
K-injective comparison, and both are natural: the first by being an isomorphism of bifunctors,
the second by `StacksDraft.DerivedHom.DerivedHomData.homIso_naturality`. -/
theorem derivedHomModelIso_naturality (L L' J : Model.Complex (ULift.{v} A))
    [J.IsKInjective] (f : L' ⟶ L) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
        (((derivedScalarEquivalence.{u, v} A).functor.map (DerivedCategory.Q.map f)).op,
          𝟙 ((derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj J))) ≫
      (derivedHomModelIso.{u, v} A L' J).hom =
    (derivedHomModelIso.{u, v} A L J).hom ≫
      (derivedScalarEquivalence.{u, v} A).functor.map
        (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} A) L' L J f)) :=
          by
  have h1 := (derivedHomULiftIso.{u, v} A).hom.naturality
    (X := (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J))
    (Y := (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj J))
    ((DerivedCategory.Q.map f).op, 𝟙 (DerivedCategory.Q.obj J))
  have h2 := (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).homIso_naturality f (𝟙 J)
  simp only [Functor.comp_map, Functor.prod_map, Functor.op_map, Quiver.Hom.unop_op,
    Prod.mkHom, CategoryTheory.Functor.map_id] at h1
  rw [CategoryTheory.Functor.map_id, Stacks.HomComplex.TensorHomMap.postcomp_id, Category.comp_id]
    at h2
  dsimp only [derivedHomModelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [reassoc_of% h1, ← CategoryTheory.Functor.map_comp, h2,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- The K-injective Hom model, as an isomorphism of functors of the source complex. -/
def derivedHomModelComparison (J : Model.Complex (ULift.{v} A)) [J.IsKInjective] :
    (scalarLocalization.{u, v} A).op ⋙
        Dualizing.dualizingDerivedHomFunctor.{u, v} A ((scalarLocalization.{u, v} A).obj J) ≅
      homComplexInto (ULift.{v} A) J ⋙ scalarLocalization.{u, v} A :=
  NatIso.ofComponents (fun F ↦ derivedHomModelIso.{u, v} A F.unop J) (by
    intro F F' f
    dsimp [homComplexInto, Model.homComplexFunctor]
    simp only [Stacks.HomComplex.TensorHomMap.postcomp_id, Category.comp_id]
    exact derivedHomModelIso_naturality A F.unop F'.unop J f.unop)

/-- The scalar transport of the derived category commutes with the shift. -/
@[instance_reducible]
def scalarEquivalenceCommShift : (derivedScalarEquivalence.{u, v} A).functor.CommShift ℤ :=
  inferInstanceAs
    ((uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategory.CommShift ℤ)

/-- Localization of complexes of `ULift A`-modules followed by restriction of scalars is a
localization of the category of cochain complexes at the quasi-isomorphisms. -/
theorem scalarLocalization_isLocalization : (scalarLocalization.{u, v} A).IsLocalization
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} A)) (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_equivalence_target DerivedCategory.Q _ _
    (derivedScalarEquivalence.{u, v} A) (Iso.refl _)

attribute [local instance] scalarEquivalenceCommShift scalarLocalization_isLocalization

/-- **Shifting a K-injective model shifts derived Hom into it**, as an isomorphism of functors
of the source object. The isomorphism is the localization lift of the cochain-level
identification `Hom^•(-, J)⟦a⟧ ≅ Hom^•(-, J⟦a⟧)`, transported through the K-injective Hom
model of `StacksDraft.DerivedHom.derivedHomModelIso`. -/
def derivedHomShiftIsoOfModel (J : Model.Complex (ULift.{v} A)) [J.IsKInjective] (a : ℤ) :
    Dualizing.dualizingDerivedHomFunctor.{u, v} A ((scalarLocalization.{u, v} A).obj (J⟦a⟧)) ≅
      Dualizing.dualizingDerivedHomFunctor.{u, v} A ((scalarLocalization.{u, v} A).obj J) ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) a := by
  letI : Localization.Lifting (scalarLocalization.{u, v} A).op
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} A)) (ComplexShape.up ℤ)).op
      (homComplexInto (ULift.{v} A) (J⟦a⟧) ⋙ scalarLocalization.{u, v} A)
      (Dualizing.dualizingDerivedHomFunctor.{u, v} A
        ((scalarLocalization.{u, v} A).obj (J⟦a⟧))) :=
    ⟨derivedHomModelComparison A (J⟦a⟧)⟩
  letI : Localization.Lifting (scalarLocalization.{u, v} A).op
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} A)) (ComplexShape.up ℤ)).op
      (homComplexInto (ULift.{v} A) J ⋙ scalarLocalization.{u, v} A)
      (Dualizing.dualizingDerivedHomFunctor.{u, v} A ((scalarLocalization.{u, v} A).obj J)) :=
    ⟨derivedHomModelComparison A J⟩
  exact Localization.liftNatIso (scalarLocalization.{u, v} A).op
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} A)) (ComplexShape.up ℤ)).op
    (homComplexInto (ULift.{v} A) (J⟦a⟧) ⋙ scalarLocalization.{u, v} A)
    ((homComplexInto (ULift.{v} A) J ⋙ scalarLocalization.{u, v} A) ⋙
      CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) a) _ _
    (Functor.isoWhiskerRight (homComplexIntoShiftIso (ULift.{v} A) J a).symm
        (scalarLocalization.{u, v} A) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homComplexInto (ULift.{v} A) J)
        ((scalarLocalization.{u, v} A).commShiftIso a) ≪≫
      (Functor.associator _ _ _).symm)

end StacksDraft.DerivedHom.HomShift

namespace Dualizing

open StacksDraft.DerivedHom StacksDraft.DerivedHom.HomShift

universe u v

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance] StacksDraft.DerivedHom.HomShift.scalarEquivalenceCommShift

variable (A : Type u) [CommRing A]

/-- **Derived Hom commutes with the shift in its target**, for an object presented as the
scalar transport of a K-injective cochain complex. -/
def dualizingDerivedHomShiftIsoOfModel (J : Model.Complex (ULift.{v} A)) [J.IsKInjective]
    (i : ℤ) {Ω : DerivedCategory (ModuleCat.{max u v} A)}
    (rho : Ω ≅ (scalarLocalization.{u, v} A).obj J) :
    dualizingDerivedHomFunctor.{u, v} A
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω) ≅
      dualizingDerivedHomFunctor.{u, v} A Ω ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i :=
  let Phi := (Functor.curry.obj (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom).flip
  Phi.mapIso
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).mapIso rho ≪≫
        (((scalarLocalization.{u, v} A).commShiftIso i).app J).symm) ≪≫
    derivedHomShiftIsoOfModel A J i ≪≫
    Functor.isoWhiskerRight (Phi.mapIso rho).symm
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i)

/-- **Derived Hom commutes with the shift in its target, naturally in its source:**
`RHom_A(K, Ω⟦i⟧) ≅ RHom_A(K, Ω)⟦i⟧`, as an isomorphism of contravariant functors of `K` on the
whole derived category. -/
def dualizingDerivedHomShiftIso (Ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    dualizingDerivedHomFunctor.{u, v} A
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω) ≅
      dualizingDerivedHomFunctor.{u, v} A Ω ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i := by
  have h := exists_isKInjective_model
    ((derivedScalarEquivalence.{u, v} A).inverse.obj Ω)
  have hJ : h.choose.IsKInjective := h.choose_spec.1
  exact dualizingDerivedHomShiftIsoOfModel A h.choose i
    (((derivedScalarEquivalence.{u, v} A).counitIso.app Ω).symm ≪≫
      (derivedScalarEquivalence.{u, v} A).functor.mapIso h.choose_spec.2.some.symm)

/-- The component of `Dualizing.dualizingDerivedHomShiftIso`:
`RHom_A(K, Ω⟦i⟧) ≅ RHom_A(K, Ω)⟦i⟧`. -/
def dualizingDerivedHomShift (Ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K,
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω) ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, Ω)) :=
  (dualizingDerivedHomShiftIso.{u, v} A Ω i).app (Opposite.op K)

/-- **The shift identification of `Dualizing.dualizingDerivedHomShift` is natural in the source
object**, written at the spelling the bifunctor itself uses. -/
theorem dualizingDerivedHomShift_naturality (Ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    {K K' : DerivedCategory (ModuleCat.{max u v} A)} (f : K ⟶ K') :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
          ((f.op, 𝟙 ((CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω)) :
            (Opposite.op K', (CategoryTheory.shiftFunctor
              (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω) ⟶
            (Opposite.op K, (CategoryTheory.shiftFunctor
              (DerivedCategory (ModuleCat.{max u v} A)) i).obj Ω)) ≫
        (dualizingDerivedHomShift.{u, v} A Ω i K).hom =
      (dualizingDerivedHomShift.{u, v} A Ω i K').hom ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).map
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
            ((f.op, 𝟙 Ω) : (Opposite.op K', Ω) ⟶ (Opposite.op K, Ω))) :=
  (dualizingDerivedHomShiftIso.{u, v} A Ω i).hom.naturality f.op

end Dualizing

end
