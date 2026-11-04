module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of dualizing complexes

Let `A` be a Noetherian commutative ring and let `K` and `K'` be dualizing complexes for `A`.
Then `K' ≅ K ⊗^L_A L` for an invertible object `L` of `D(A)`, namely `L = RHom_A(K, K')`.

## Main results

* `Dualizing.IsDualizingComplex.exists_iso_derivedTensorProduct_invertible`: two dualizing
  complexes differ by derived tensor product with an invertible object.
* `Dualizing.isInvertible_derivedHom`: for dualizing complexes `K` and `K'`, `RHom_A(K, K')` is
  invertible for the derived tensor product.

## References

* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- A dualizing complex is cohomologically bounded: it has a bounded representative by
injectives. -/
public theorem IsDualizingComplex.bounded
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{max u v} A)} (hK : IsDualizingComplex K) :
    (DerivedCategory.TStructure.t).bounded K := by
  obtain ⟨a, b, I, hGE, hLE, _, ⟨e⟩⟩ := hK.finiteInjectiveDimension
  exact ⟨⟨a, I, e, hGE⟩, ⟨b, I, e, hLE⟩⟩

/-- Over a Noetherian ring, a cohomologically bounded complex with finite cohomology is
pseudo-coherent. -/
public theorem isPseudoCoherent_of_bounded_of_finiteCohomology
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (X : DerivedCategory (ModuleCat.{max u v} R))
    (hFinite : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj X))
    (hBounded : (DerivedCategory.TStructure.t).bounded X) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent X := by
  obtain ⟨_, ⟨b, hb⟩⟩ := hBounded
  apply (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    X 0 (ULift.{v} R)).2.1.mpr
  exact ⟨⟨b, fun i hi ↦ DerivedCategory.isZero_of_isLE X b i hi⟩, hFinite⟩

/-- A cohomologically bounded complex is bounded below. -/
public theorem isBoundedBelow_of_bounded
    {R : Type u} [Ring R] (X : DerivedCategory (ModuleCat.{max u v} R))
    (hX : (DerivedCategory.TStructure.t).bounded X) :
    DerivedCategoryB.IsBoundedBelow X := by
  obtain ⟨⟨a, ha⟩, _⟩ := hX
  exact ⟨a, fun i hi ↦ (DerivedCategory.isGE_iff X a).mp ha i hi⟩

/-- A dualizing complex, as an object of the bounded coherent derived category. -/
public def IsDualizingComplex.boundedCoherentObject
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{max u v} A)} (hK : IsDualizingComplex K) :
    BoundedCoherentDerivedCategory.{u, v} A :=
  ⟨K, hK.finiteCohomology, hK.bounded⟩

/-- The composite `RHom_A(RHom_A(-, K), K')` of the two dualities attached to two dualizing
complexes. -/
public noncomputable def dualityComposite
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    BoundedCoherentDerivedCategory.{u, v} A ⥤ BoundedCoherentDerivedCategory.{u, v} A :=
  (boundedCoherentDualizingDerivedHomFunctor A K hK).rightOp ⋙
    boundedCoherentDualizingDerivedHomFunctor A K' hK'

/-- The composite of the two dualities is an autoequivalence of the bounded coherent derived
category. -/
public noncomputable instance dualityComposite_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    (dualityComposite A hK hK').IsEquivalence := by
  unfold dualityComposite
  let _ := boundedCoherentDualizingDerivedHom_isEquivalence A K hK
  let _ := boundedCoherentDualizingDerivedHom_isEquivalence A K' hK'
  infer_instance

/-- The ring, lifted to the larger module universe and placed in degree zero, as an object of
the bounded coherent derived category. It is the unit of the derived tensor product of
`CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure`. -/
public noncomputable def uliftRingObject
    (A : Type u) [CommRing A] :
    BoundedCoherentDerivedCategory.{u, v} A := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A (ULift.{v} A))
  refine ⟨X, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      let e : ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).obj X) ≃ₗ[A]
          ULift.{v} A :=
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} A) 0).app (ModuleCat.of A (ULift.{v} A))).toLinearEquiv
      exact Module.Finite.equiv e.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X) := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE X 0 i hi
        · exact DerivedCategory.isZero_of_isLE X 0 i hi
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  · exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

/-- Derived Hom out of the monoidal unit is the identity. -/
public noncomputable def derivedHomUnitIso
    (R : Type u) [CommRing R] (M : DerivedCategory (ModuleCat.{u} R)) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
    d.hom.obj
        (Opposite.op (DerivedCategory.Q.obj
          (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))), M) ≅ M := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))
  apply Yoneda.ext _ _
    (fun {Z} f ↦ (d.tensorRightUnitor.app Z).inv ≫ d.homEquiv Z U M f)
    (fun {Z} g ↦ (d.homEquiv Z U M).symm ((d.tensorRightUnitor.app Z).hom ≫ g))
  · intro Z f
    simp
  · intro Z f
    simp
  · intro Z Z' f g
    rw [d.homEquiv_naturality_left]
    have hn := (d.tensorRightUnitor.inv.naturality f).symm
    change (d.tensorRightUnitor.app Z').inv ≫ d.tensor.map (f, 𝟙 U) =
      f ≫ (d.tensorRightUnitor.app Z).inv at hn
    simpa only [Category.assoc] using
      congrArg (fun h ↦ h ≫ (d.homEquiv Z U M) g) hn

/-- Derived Hom out of the ring in degree zero is the identity. -/
public noncomputable def derivedHomRingIso
    (R : Type u) [CommRing R] (M : DerivedCategory (ModuleCat.{u} R)) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
    d.hom.obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R)), M) ≅ M :=
  derivedHomUnitIso R M

/-- Derived Hom out of the lifted ring in degree zero is the identity, in an independent module
universe. -/
public noncomputable def derivedHomULiftRingIso
    (A : Type u) [CommRing A] (M : DerivedCategory (ModuleCat.{max u v} A)) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    d.hom.obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))), M) ≅ M := by
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let U' := (DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} A)) 0).obj
    (ModuleCat.of (ULift.{v} A) (ULift.{v} A))
  let U := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A (ULift.{v} A))
  let hU : e.functor.obj U' ≅ U :=
    ((StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
      v} A).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).mapIso (Iso.refl _)
  exact (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.mapIso
      (hU.op.prod (e.counitIso.app M).symm) ≪≫
    (StacksDraft.DerivedHom.derivedHomULiftIso A).app (Opposite.op U', e.inverse.obj M) ≪≫
    e.functor.mapIso (derivedHomRingIso (ULift.{v} A) (e.inverse.obj M)) ≪≫
    e.counitIso.app M

/-- Derived Hom in an independent module universe, transported to the same-universe derived Hom
over the lifted ring. -/
public noncomputable def scalarDerivedHomIso
    (A : Type u) [CommRing A] (K L : DerivedCategory (ModuleCat.{max u v} A)) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    let d' := StacksDraft.DerivedHom.derivedHomAdjunctionULift (R := A)
    d.hom.obj (Opposite.op K, L) ≅
      E.functor.obj (d'.hom.obj (Opposite.op (E.inverse.obj K), E.inverse.obj L)) := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  exact d.hom.mapIso ((E.counitIso.app K).op.prod (E.counitIso.app L).symm) ≪≫
    (StacksDraft.DerivedHom.derivedHomULiftIso A).app
      (Opposite.op (E.inverse.obj K), E.inverse.obj L)

/-- Derived tensor product in an independent module universe, transported to the same-universe
derived tensor product over the lifted ring. -/
public noncomputable def scalarDerivedTensorIso
    (A : Type u) [CommRing A] (K L : DerivedCategory (ModuleCat.{max u v} A)) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    let d' := StacksDraft.DerivedHom.derivedHomAdjunctionULift (R := A)
    d.tensor.obj (K, L) ≅
      E.functor.obj (d'.tensor.obj (E.inverse.obj K, E.inverse.obj L)) := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  exact d.tensor.mapIso ((E.counitIso.app K).symm.prod (E.counitIso.app L).symm) ≪≫
    (StacksDraft.DerivedHom.derivedTensorULiftIso A).app
      (E.inverse.obj K, E.inverse.obj L)

/-- The canonical derived tensor product of [stacks 0FNQ] agrees with the tensor half of the
derived tensor--Hom adjunction. -/
public noncomputable def derivedHomAdjunctionTensorIso
    (R : Type u) [CommRing R] (P Q : DerivedCategory (ModuleCat.{u} R)) :
    ((canonicalDerivedTensorProduct R).tensor.obj P).obj Q ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.obj (P, Q) := by
  let D := canonicalDerivedTensorProduct R
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
  let q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let rP := CochainComplex.KFlat.exists_kFlat_resolution (q.objPreimage P)
  let K := rP.choose
  let f := rP.choose_spec.choose
  have hK : K.KFlat := rP.choose_spec.choose_spec.1
  have hf : QuasiIso f := rP.choose_spec.choose_spec.2.2.1
  let rQ := CochainComplex.KFlat.exists_kFlat_resolution (q.objPreimage Q)
  let L := rQ.choose
  let g := rQ.choose_spec.choose
  have hL : L.KFlat := rQ.choose_spec.choose_spec.1
  have hg : QuasiIso g := rQ.choose_spec.choose_spec.2.2.1
  let eK : q.obj K ≅ P := asIso (q.map f) ≪≫ q.objObjPreimageIso P
  let eL : q.obj L ≅ Q := asIso (q.map g) ≪≫ q.objObjPreimageIso Q
  exact ((D.tensor.mapIso eK.symm).app Q) ≪≫
    (D.tensor.obj (q.obj K)).mapIso eL.symm ≪≫
    D.comparison K L hK hL ≪≫ (d.tensorIso K L hL).symm ≪≫
    d.tensor.mapIso (eK.prod eL)

/-- The composite duality sends the lifted ring to `RHom_A(K, K')`. -/
public noncomputable def dualityCompositeRingIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    ((dualityComposite A hK hK').obj (uliftRingObject.{u, v} A)).obj ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
        (Opposite.op K, K') := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  change d.hom.obj
      (Opposite.op (d.hom.obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))), K)), K') ≅ d.hom.obj (Opposite.op K, K')
  exact (d.hom.mapIso ((derivedHomULiftRingIso A K).op.prod (Iso.refl K'))).symm

/-- The derived endomorphisms of a dualizing complex are the lifted ring in degree zero. -/
public noncomputable def dualizingDerivedHomSelfIsoRing
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{max u v} A)} (hK : IsDualizingComplex K) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
      (Opposite.op K, K) ≅ (uliftRingObject.{u, v} A).obj := by
  let U := uliftRingObject.{u, v} A
  let C : CoherentDerivedCategory.{u, v} A := ⟨U.obj, U.property.1⟩
  let e := (ObjectProperty.ι _).mapIso ((coherentDerivedBidualityIso A K hK).app C)
  exact (dualityCompositeRingIso A hK hK).symm ≪≫ e.symm

/-- Derived Hom out of the derived endomorphism complex of a dualizing complex is the
identity. -/
public noncomputable def iteratedDerivedHomSelfIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)} (hK : IsDualizingComplex K) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, K)), K') ≅ K' := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  exact d.hom.mapIso
      ((dualizingDerivedHomSelfIsoRing A hK).symm.op.prod (Iso.refl K')) ≪≫
    derivedHomULiftRingIso A K'

/-- An exact functor preserves vanishing of cohomology of a complex. -/
private theorem isZero_homology_mapDerivedCategory
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : DerivedCategory C} {i : ℤ} (h : IsZero ((DerivedCategory.homologyFunctor C i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K)) :=
  (F.map_isZero h).of_iso ((F.mapDerivedCategoryHomologyIso i).app K)

/-- An exact functor preserves upper cohomological bounds. -/
public theorem mapDerivedCategory_isLE
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n :=
  (DerivedCategory.isLE_iff _ _).2 fun i hi ↦
    isZero_homology_mapDerivedCategory (DerivedCategory.isZero_of_isLE K n i hi)

/-- An exact functor preserves lower cohomological bounds. -/
public theorem mapDerivedCategory_isGE
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n :=
  (DerivedCategory.isGE_iff _ _).2 fun i hi ↦
    isZero_homology_mapDerivedCategory (DerivedCategory.isZero_of_isGE K n i hi)

/-- An exact functor preserves cohomological boundedness. -/
public theorem mapDerivedCategory_bounded
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (hK : (DerivedCategory.TStructure.t).bounded K) :
    (DerivedCategory.TStructure.t).bounded (F.mapDerivedCategory.obj K) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  exact ⟨⟨a, mapDerivedCategory_isGE F K a⟩, ⟨b, mapDerivedCategory_isLE F K b⟩⟩

/-- An equivalence of abelian categories preserves finite injective dimension. -/
public theorem mapDerivedCategory_finiteInjectiveDimension
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ≌ D) [F.functor.Additive] (K : DerivedCategory C)
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (F.functor.mapDerivedCategory.obj K) := by
  obtain ⟨a, b, I, hGE, hLE, hInj, ⟨e⟩⟩ := hK
  let J : CochainComplex D ℤ := (F.functor.mapHomologicalComplex (.up ℤ)).obj I
  have hJGE : J.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun j hj ↦ F.functor.map_isZero ((I.isStrictlyGE_iff a).mp hGE j hj)
  have hJLE : J.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun j hj ↦ F.functor.map_isZero ((I.isStrictlyLE_iff b).mp hLE j hj)
  exact ⟨a, b, J, hJGE, hJLE, fun i ↦ F.functor.injective_obj_of_injective (hInj i),
    ⟨F.functor.mapDerivedCategory.mapIso e ≪≫ F.functor.mapDerivedCategoryFactors.app I⟩⟩

/-- The inverse of the scalar equivalence preserves finiteness of cohomology. -/
public theorem finiteCohomology_scalarEquivalence_inverse
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X)) :
    ∀ i : ℤ, Module.Finite (ULift.{v} A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) i).obj
        ((StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
          max u v + 1} A).inverse.obj X)) := by
  intro i
  let F := (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A).inverse
  have := hX i
  have : Module.Finite (ULift.{v} A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙ F).obj X) :=
    finite_restrictScalars_ringEquiv (ULift.ringEquiv.{u, v} (R := A))
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X)
  exact Module.Finite.equiv ((F.mapDerivedCategoryHomologyIso i).app X).symm.toLinearEquiv

/-- The inverse of the scalar equivalence preserves cohomological boundedness. -/
public theorem bounded_scalarEquivalence_inverse
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : (DerivedCategory.TStructure.t).bounded X) :
    (DerivedCategory.TStructure.t).bounded
      ((StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
        max u v + 1} A).inverse.obj X) :=
  mapDerivedCategory_bounded
    (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A).inverse X hX

/-- The inverse of the scalar equivalence preserves finite injective dimension. -/
public theorem finiteInjectiveDimension_scalarEquivalence_inverse
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension X) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
        max u v + 1} A).inverse.obj X) := by
  let _ : (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
      v} A).symm.functor.Additive :=
    inferInstanceAs (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
      v} A).inverse.Additive
  exact mapDerivedCategory_finiteInjectiveDimension
    (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A).symm X hX

/-- **Evaluation is an isomorphism on bounded coherent objects**: for dualizing complexes `K`
and `K'` and an object `X` of `D^b_{Coh}(A)`, the evaluation map
`RHom_A(K, K') ⊗^L_A X ⟶ RHom_A(RHom_A(X, K), K')` is invertible. -/
public noncomputable def evaluationIsoOfBoundedCoherent
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K')
    (X : BoundedCoherentDerivedCategory.{u, v} A) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    d.tensor.obj (d.hom.obj (Opposite.op K, K'), X.obj) ≅
      d.hom.obj (Opposite.op (d.hom.obj (Opposite.op X.obj, K)), K') := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  let d' := StacksDraft.DerivedHom.derivedHomAdjunctionULift (R := A)
  let Y := E.inverse.obj X.obj
  let L := E.inverse.obj K
  let M := E.inverse.obj K'
  let H := d.hom.obj (Opposite.op K, K')
  let H' := d'.hom.obj (Opposite.op L, M)
  let S := d.hom.obj (Opposite.op X.obj, K)
  let S' := d'.hom.obj (Opposite.op Y, L)
  let hH : E.inverse.obj H ≅ H' :=
    E.inverse.mapIso (scalarDerivedHomIso A K K') ≪≫ (E.unitIso.app H').symm
  let hS : E.inverse.obj S ≅ S' :=
    E.inverse.mapIso (scalarDerivedHomIso A X.obj K) ≪≫ (E.unitIso.app S').symm
  let ev := Classical.choose
    (StacksDraft.DerivedHom.exists_evaluationToIteratedDerivedHom (R := ULift.{v} A))
  let _ : IsNoetherianRing (ULift.{v} A) :=
    isNoetherianRing_of_ringEquiv A (ULift.ringEquiv.{u, v} (R := A)).symm
  have hPseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent Y :=
    isPseudoCoherent_of_bounded_of_finiteCohomology Y
      (finiteCohomology_scalarEquivalence_inverse A X.obj X.property.1)
      (bounded_scalarEquivalence_inverse A X.obj X.property.2)
  have hBelow : DerivedCategoryB.IsBoundedBelow L :=
    isBoundedBelow_of_bounded L (bounded_scalarEquivalence_inverse A K hK.bounded)
  have hInjective := finiteInjectiveDimension_scalarEquivalence_inverse A K'
    hK'.finiteInjectiveDimension
  let _ : IsIso (ev Y L M) :=
    StacksDraft.DerivedHom.evaluationToIteratedDerivedHom_isIso Y L M
      (Or.inr ⟨hPseudo, hBelow, hInjective⟩)
  exact scalarDerivedTensorIso A H X.obj ≪≫
    E.functor.mapIso (d'.tensor.mapIso (hH.prod (Iso.refl Y))) ≪≫
    E.functor.mapIso (asIso (ev Y L M)) ≪≫
    E.functor.mapIso (d'.hom.mapIso (hS.op.prod (Iso.refl M))) ≪≫
    (scalarDerivedHomIso A S K').symm

/-- Evaluation at a dualizing complex is an isomorphism. -/
public noncomputable def evaluationIsoOfDualizing
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    d.tensor.obj (d.hom.obj (Opposite.op K, K'), K) ≅
      d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, K)), K') :=
  evaluationIsoOfBoundedCoherent A hK hK' hK.boundedCoherentObject

/-- One dualizing complex is the derived tensor product of `RHom_A(K, K')` with the other. -/
public noncomputable def dualizingIsoDerivedHomTensor
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    K' ≅ d.tensor.obj (d.hom.obj (Opposite.op K, K'), K) :=
  (iteratedDerivedHomSelfIso A hK).symm ≪≫ (evaluationIsoOfDualizing A hK hK').symm

/-- One dualizing complex is the derived tensor product of the other with `RHom_A(K, K')`. -/
public noncomputable def dualizingIsoTensorDerivedHom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    K' ≅ d.tensor.obj (K, d.hom.obj (Opposite.op K, K')) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  exact dualizingIsoDerivedHomTensor A hK hK' ≪≫
    d.tensorSwap (d.hom.obj (Opposite.op K, K')) K

/-- The tensor product of the transported monoidal structure is the tensor half of the derived
tensor--Hom adjunction. -/
public noncomputable def monoidalTensorIso
    (A : Type u) [CommRing A] (P Q : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    P ⊗ Q ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).tensor.obj (P, Q) := by
  letI := canonicalDerivedMonoidalStructure.{u, v} A
  exact ((canonicalDerivedMonoidalTensorIso A).app P).app Q ≪≫
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A).functor.mapIso
      (derivedHomAdjunctionTensorIso (ULift.{v} A) _ _) ≪≫
    (scalarDerivedTensorIso A P Q).symm

/-- **`RHom_A(K, K')` is invertible** for the derived tensor product, when `K` and `K'` are
dualizing complexes. -/
public theorem isInvertible_derivedHom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    MonoidalCategory.IsInvertible
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
        (Opposite.op K, K')) := by
  let _ := canonicalDerivedMonoidalStructure.{u, v} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  let H := d.hom.obj (Opposite.op K, K')
  let F := dualityComposite A hK hK'
  let X := F.objPreimage (uliftRingObject.{u, v} A)
  have e : d.hom.obj (Opposite.op (d.hom.obj (Opposite.op X.obj, K)), K') ≅
      (uliftRingObject.{u, v} A).obj :=
    (ObjectProperty.ι _).mapIso (F.objObjPreimageIso (uliftRingObject.{u, v} A))
  have eHX : d.tensor.obj (H, X.obj) ≅ 𝟙_ _ :=
    evaluationIsoOfBoundedCoherent A hK hK' X ≪≫ e ≪≫
      (canonicalDerivedMonoidalUnitIso A).symm
  have eXH : d.tensor.obj (X.obj, H) ≅ 𝟙_ _ := d.tensorSwap X.obj H ≪≫ eHX
  exact ⟨{ inv := X.obj
           isoLeft := monoidalTensorIso A H X.obj ≪≫ eHX
           isoRight := monoidalTensorIso A X.obj H ≪≫ eXH }⟩

/-- Two dualizing complexes over a Noetherian ring differ by derived tensor product with an
invertible object. -/
@[stacks 0A7F, sga "5 I 2.1" "affine case"]
public theorem IsDualizingComplex.exists_iso_derivedTensorProduct_invertible
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    ∃ T : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, v} A,
      ∃ m : MonoidalCategory (DerivedCategory (ModuleCat.{max u v} A)),
        letI := m
        (Nonempty (MonoidalCategory.curriedTensor _ ≅ T.tensor) ∧
          Nonempty
          (𝟙_ (DerivedCategory (ModuleCat.{max u v} A)) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
              (ModuleCat.of A (ULift.{v} A)))) ∧
          ∃ L : DerivedCategory (ModuleCat.{max u v} A),
            MonoidalCategory.IsInvertible L ∧
              Nonempty (K' ≅ (T.tensor.obj K).obj L) := by
  let T := canonicalDerivedTensorProductGeneral.{u, v} A
  let m := canonicalDerivedMonoidalStructure.{u, v} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
  let L := d.hom.obj (Opposite.op K, K')
  exact ⟨T, m, ⟨⟨canonicalDerivedMonoidalTensorIso A⟩, ⟨canonicalDerivedMonoidalUnitIso A⟩⟩, L,
    isInvertible_derivedHom A hK hK', ⟨dualizingIsoTensorDerivedHom A hK hK' ≪≫
      (monoidalTensorIso A K L).symm ≪≫ ((canonicalDerivedMonoidalTensorIso A).app K).app L⟩⟩

end Dualizing

end
