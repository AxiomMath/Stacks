module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.DerivedShift

/-!
# Ext and the cohomology of derived Hom

Let `A` be a commutative ring and let `ω` be an object of the derived category of `A`-modules.
For a module `M` and an integer `i`, the `A`-module `Ext^i_A(M, ω)` is the group of morphisms
`M[0] ⟶ ω⟦i⟧` in `D(A)`, with its canonical `A`-module structure. This file identifies it with
the degree-`i` cohomology module of `RHom_A(M[0], ω)`, naturally in `M`, and more generally
identifies `Hom_{D(A)}(-, ω⟦i⟧)` with `H^i(RHom_A(-, ω))` on all of `D(A)`. Neither statement
needs `ω` to be dualizing.

The comparison is assembled from four identifications, all natural in the source object:

* morphisms into `ω⟦i⟧` are morphisms from the tensor unit into `RHom_A(-, ω⟦i⟧)`, by the
  tensor--Hom adjunction of [stacks 0A63] together with its left unitor;
* `RHom_A(-, ω⟦i⟧)` is `RHom_A(-, ω)⟦i⟧`, which is `Dualizing.dualizingDerivedHomShiftIso`;
* the tensor unit is the free rank-one module placed in degree zero, and that object
  corepresents degree-zero cohomology on the whole unbounded derived category, because it is
  projective ([stacks 06XS], in the form
  `DerivedCategory.homologyFromSingleLinearEquiv`);
* shifting by `i` and taking degree-zero cohomology is taking degree-`i` cohomology.

## Main definitions

* `StacksDraft.DerivedHom.ExtComparison.homZeroEquivOverRing` and
  `StacksDraft.DerivedHom.ExtComparison.homZeroLinearEquivOverRing` --- degree-zero derived Hom
  for the adjunction of [stacks 0A63], as an additive and then as an `A`-linear equivalence.
* `StacksDraft.DerivedHom.ExtComparison.unitIsoSingle` --- the tensor unit of that adjunction,
  identified with the free rank-one module in degree zero.
* `StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` --- the comparison on all of
  `D(A)`.
* `Dualizing.extIntoOmegaAtIso` --- its restriction to modules placed in degree zero, and
  `Dualizing.extIntoOmegaAtLinearEquiv` the same with the universe lift removed.

## Main results

* `StacksDraft.DerivedHom.ExtComparison.derivedHom_map_smul_id_left` --- the derived-Hom
  bifunctor of [stacks 0A63] is `A`-linear in its source variable.
* `Dualizing.nonempty_extIntoOmegaAtIso` --- the Ext--cohomology comparison of [stacks 0A7C].
* `Dualizing.extIntoOmegaAtLinearEquiv_naturality`.

## Implementation notes

`A`-linearity is the whole difficulty, and it is why this file is not a short composition of
existing isomorphisms. The structure `StacksDraft.DerivedHom.DerivedHomAdjunction` records the
tensor--Hom equivalence as an *additive* equivalence only, and no `CategoryTheory.Functor.Linear`
instance is available for its tensor or Hom bifunctor; but the statement being proved is an
isomorphism of `ModuleCat A`-valued functors, so every step has to be `A`-linear. The linearity
is obtained once, for the Hom bifunctor in its source variable, and everything else follows:
given it, the degree-zero identification is `A`-linear because `a • u` is `u` postcomposed with
`RHom_A(a • 𝟙, ω)`, which the adjunction's `homEquiv_dinaturality` converts into precomposition
by `a • 𝟙` on the other side.

That one linearity statement is proved on representatives. Multiplication by `a` on a complex of
`ULift A`-modules is multiplication by `ULift.up a`, and restriction of scalars along
`ULift.ringEquiv` turns one into the other; precomposition by a scalar multiple of the identity
on a Hom complex is that scalar multiple of the identity (`precomp_smul_id`); and the K-injective
Hom model of [stacks 0A63] is natural in the source complex
(`StacksDraft.DerivedHom.HomShift.derivedHomModelIso_naturality`). An arbitrary source and an
arbitrary target are then reached by conjugating with an isomorphism, in the source variable
directly and in the target variable through the isomorphism of functors it induces.

The derived category is taken at the standard model, as in
`StacksFrontier/RingTheory/Dualizing/DualizingDerivedHom.lean`: the model is baked into the type of
`Dualizing.dualizingDerivedHomFunctor`, so it is forced here rather than chosen. No statement in
this file mentions coproducts, and the standard model is a legitimate derived category of
`ModuleCat A`, so nothing is weakened by the pin.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CochainComplex
open CochainComplex.HomComplex

namespace StacksDraft.DerivedHom.ExtComparison

universe u v

/-- Precomposition on a Hom complex by a scalar multiple of the identity is that scalar
multiple of the identity. -/
theorem precomp_smul_id (R : Type*) [CommRing R] (L M : CochainComplex (ModuleCat R) ℤ) (a : R) :
    Stacks.HomComplex.TensorHomMap.precomp R L L M (a • 𝟙 L) = a • 𝟙 (CochainComplex.HomComplexR R L
      M) := by
  have hof : Cochain.ofHom (a • 𝟙 L) = a • Cochain.ofHom (𝟙 L) := by
    ext p q
    simp [Cochain.ofHom]
  have key : ∀ (n : ℤ) (z : Cochain L M n),
      (Cochain.ofHom (a • 𝟙 L)).comp z (zero_add n) = a • z := by
    intro n z
    rw [hof, Cochain.smul_comp]
    simp
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact key n z

/-- A linear functor sends a scalar multiple of an identity to the same multiple of the
identity. -/
private theorem functor_map_smul_id {R : Type*} [Ring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : C ⥤ D) [F.Linear R] (r : R)
    (X : C) : F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  rw [Functor.Linear.map_smul, F.map_id]

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along `ULift A ≃+* A` turns multiplication by `ULift.up a` into
multiplication by `a`, degreewise on cochain complexes. -/
theorem scalarComplex_map_smul_id
    (Z : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ) (b : ULift.{v} A) :
    ((uliftModuleEquivalence.{u, max u v, v} A).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).map (b • 𝟙 Z) =
      b.down • 𝟙 (((uliftModuleEquivalence.{u, max u v, v} A).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

/-- The derived restriction of scalars along `ULift A ≃+* A` turns multiplication by
`ULift.up a` into multiplication by `a`, at an object presented by a cochain complex. -/
theorem mapDerivedCategory_map_smul_id_Q
    (Z : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ) (b : ULift.{v} A) :
    (uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategory.map
        (b • 𝟙 (DerivedCategory.Q.obj Z)) =
      b.down • 𝟙 ((uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategory.obj
        (DerivedCategory.Q.obj Z)) := by
  have hnat :=
    (uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategoryFactors.hom.naturality
      (b • 𝟙 Z)
  simp only [Functor.comp_map] at hnat
  rw [functor_map_smul_id DerivedCategory.Q, scalarComplex_map_smul_id.{u, v} A Z b,
    functor_map_smul_id DerivedCategory.Q] at hnat
  have h2 : ((uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategoryFactors.hom.app
        Z) ≫ (b.down • 𝟙 _) ≫
      ((uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategoryFactors.inv.app Z) =
      (uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategory.map
        (b • 𝟙 (DerivedCategory.Q.obj Z)) := by
    rw [← Category.assoc]
    simp only [Functor.comp_obj]
    rw [← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← h2]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.hom_inv_id_app,
    Functor.comp_obj]

/-- The scalar equivalence of [stacks 0A63] turns multiplication by `ULift.up a` into
multiplication by `a`, at an object presented by a cochain complex. -/
theorem scalarEquivalence_functor_map_smul_id_Q
    (Z : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ) (b : ULift.{v} A) :
    (derivedScalarEquivalence.{u, v} A).functor.map (b • 𝟙 (DerivedCategory.Q.obj Z)) =
      b.down • 𝟙 ((derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj Z)) :=
  mapDerivedCategory_map_smul_id_Q.{u, v} A Z b

open StacksDraft.DerivedHom.HomShift

/-- **Derived Hom is `A`-linear in its source variable**, at a source presented by a cochain
complex of `ULift A`-modules and a K-injective target. -/
theorem derivedHom_map_smul_id_left_model (L J : Model.Complex (ULift.{v} A)) [J.IsKInjective]
    (a : A) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
        ((a • 𝟙 ((scalarLocalization.{u, v} A).obj L)).op,
          𝟙 ((scalarLocalization.{u, v} A).obj J)) =
      a • 𝟙 ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
        (Opposite.op ((scalarLocalization.{u, v} A).obj L),
          (scalarLocalization.{u, v} A).obj J)) := by
  have hnat := derivedHomModelIso_naturality.{u, v} A L L J ((ULift.up a) • 𝟙 L)
  rw [functor_map_smul_id DerivedCategory.Q,
    scalarEquivalence_functor_map_smul_id_Q.{u, v} A L (ULift.up a),
    precomp_smul_id (ULift.{v} A) L J (ULift.up a),
    functor_map_smul_id DerivedCategory.Q,
    scalarEquivalence_functor_map_smul_id_Q.{u, v} A
      (CochainComplex.HomComplexR (ULift.{v} A) L J) (ULift.up a)] at hnat
  dsimp only at hnat
  refine (cancel_mono (derivedHomModelIso.{u, v} A L J).hom).mp ?_
  dsimp only [scalarLocalization, Functor.comp_obj]
  rw [hnat]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]


/-- Every object of `D(A)` is the scalar transport of the localization of a cochain complex of
`ULift A`-modules. -/
theorem exists_scalarLocalization_iso (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ L : Model.Complex (ULift.{v} A), Nonempty (K ≅ (scalarLocalization.{u, v} A).obj L) :=
  ⟨DerivedCategory.Q.objPreimage ((derivedScalarEquivalence.{u, v} A).inverse.obj K),
    ⟨((derivedScalarEquivalence.{u, v} A).counitIso.app K).symm ≪≫
      (derivedScalarEquivalence.{u, v} A).functor.mapIso
        (DerivedCategory.Q.objObjPreimageIso
          ((derivedScalarEquivalence.{u, v} A).inverse.obj K)).symm⟩⟩

/-- Every object of `D(A)` is the scalar transport of the localization of a K-injective cochain
complex of `ULift A`-modules. -/
theorem exists_kInjective_scalarLocalization_iso
    (Ω : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ J : Model.Complex (ULift.{v} A), J.IsKInjective ∧
      Nonempty (Ω ≅ (scalarLocalization.{u, v} A).obj J) := by
  obtain ⟨J, hJ, ⟨iJ⟩⟩ :=
    exists_isKInjective_model ((derivedScalarEquivalence.{u, v} A).inverse.obj Ω)
  exact ⟨J, hJ, ⟨((derivedScalarEquivalence.{u, v} A).counitIso.app Ω).symm ≪≫
    (derivedScalarEquivalence.{u, v} A).functor.mapIso iJ.symm⟩⟩

/-- Transporting along an isomorphism of the source a statement that a contravariant functor
sends a scalar multiple of an identity to a scalar multiple of an identity. -/
theorem map_op_smul_id_of_iso {R S : Type*} [Ring R] [Ring S] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear S D] (G : Cᵒᵖ ⥤ D)
    {X X' : C} (φ : X ≅ X') (r : R) (s : S)
    (h : G.map (r • 𝟙 X').op = s • 𝟙 (G.obj (Opposite.op X'))) :
    G.map (r • 𝟙 X).op = s • 𝟙 (G.obj (Opposite.op X)) := by
  have hx : (r • 𝟙 X) = φ.hom ≫ (r • 𝟙 X') ≫ φ.inv := by
    simp [Linear.comp_smul, Linear.smul_comp]
  rw [hx, CategoryTheory.op_comp, CategoryTheory.op_comp, G.map_comp, G.map_comp, h]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, ← G.map_comp,
    ← CategoryTheory.op_comp, Iso.hom_inv_id, CategoryTheory.op_id,
    CategoryTheory.Functor.map_id]

/-- Transporting a scalar-identity statement along an isomorphism of functors. -/
theorem map_smul_id_of_natIso {S : Type*} [Ring S] {C D : Type*} [Category C] [Category D]
    [Preadditive D] [Linear S D] {G G' : C ⥤ D} (τ : G ≅ G') {X : C} (f : X ⟶ X) (s : S)
    (h : G'.map f = s • 𝟙 (G'.obj X)) : G.map f = s • 𝟙 (G.obj X) := by
  have hn := τ.hom.naturality f
  rw [h] at hn
  refine (cancel_mono ((τ.app X).hom)).mp ?_
  rw [show (τ.app X).hom = τ.hom.app X from rfl, hn]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id]

/-- **Derived Hom is `A`-linear in its source variable**, for a K-injective model of the
target. -/
theorem dualizingDerivedHomFunctor_map_smul_id_kInjective (J : Model.Complex (ULift.{v} A))
    [J.IsKInjective] (K : DerivedCategory (ModuleCat.{max u v} A)) (a : A) :
    (Dualizing.dualizingDerivedHomFunctor.{u, v} A ((scalarLocalization.{u, v} A).obj J)).map
        (a • 𝟙 K).op =
      a • 𝟙 ((Dualizing.dualizingDerivedHomFunctor.{u, v} A
        ((scalarLocalization.{u, v} A).obj J)).obj (Opposite.op K)) := by
  obtain ⟨L, ⟨φ⟩⟩ := exists_scalarLocalization_iso.{u, v} A K
  exact map_op_smul_id_of_iso _ φ a a (derivedHom_map_smul_id_left_model.{u, v} A L J a)

/-- **Derived Hom is `A`-linear in its source variable.** Multiplication by `a` on the source
induces multiplication by `a` on `RHom_A(-, Ω)`. -/
theorem dualizingDerivedHomFunctor_map_smul_id
    (K Ω : DerivedCategory (ModuleCat.{max u v} A)) (a : A) :
    (Dualizing.dualizingDerivedHomFunctor.{u, v} A Ω).map (a • 𝟙 K).op =
      a • 𝟙 ((Dualizing.dualizingDerivedHomFunctor.{u, v} A Ω).obj (Opposite.op K)) := by
  obtain ⟨J, hJ, ⟨ρ⟩⟩ := exists_kInjective_scalarLocalization_iso.{u, v} A Ω
  have := hJ
  exact map_smul_id_of_natIso
    ((Functor.curry.obj (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom).flip.mapIso ρ)
    ((a • 𝟙 K).op) a (dualizingDerivedHomFunctor_map_smul_id_kInjective.{u, v} A J K a)

/-- The derived-Hom bifunctor of [stacks 0A63] is `A`-linear in its source variable. -/
theorem derivedHom_map_smul_id_left (K Ω : DerivedCategory (ModuleCat.{max u v} A)) (a : A) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map ((a • 𝟙 K).op, 𝟙 Ω) =
      a • 𝟙 ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
        (Opposite.op K, Ω)) :=
  dualizingDerivedHomFunctor_map_smul_id.{u, v} A K Ω a

/-! ### Degree-zero derived Hom at the adjunction of [stacks 0A63] -/

/-- The tensor unit of the adjunction of [stacks 0A63] is the free rank-one `A`-module placed in
degree zero. -/
def unitIsoSingle :
    derivedTensorUnit.{u, v, max u v + 1} A ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A (ULift.{v} A)) :=
  (uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategoryFactors.app
      (𝟙_ (Model.Complex (ULift.{v} A))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (uliftModuleEquivalence.{u, max u v, v} A).functor (ComplexShape.up ℤ) 0).app
          (ModuleCat.of (ULift.{v} A) (ULift.{v} A))) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).app
      (ModuleCat.of A (ULift.{v} A))).symm

/-- **Degree-zero derived Hom for the adjunction of [stacks 0A63]**: morphisms from the tensor
unit into `RHom_A(K, M)` are morphisms `K ⟶ M`. -/
def homZeroEquivOverRing (K M : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedTensorUnit.{u, v, max u v + 1} A ⟶
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, M)) ≃+
      (K ⟶ M) where
  toFun u := (derivedTensorUnitLeft.{u, v, max u v + 1} A K).inv ≫
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv
      (derivedTensorUnit.{u, v, max u v + 1} A) K M u
  invFun g := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv
    (derivedTensorUnit.{u, v, max u v + 1} A) K M).symm
      ((derivedTensorUnitLeft.{u, v, max u v + 1} A K).hom ≫ g)
  left_inv u := by simp
  right_inv g := by simp
  map_add' u w := by simp [Preadditive.comp_add]

/-- The degree-zero identification is natural in the source object. -/
theorem homZeroEquivOverRing_naturality_left
    {K K' M : DerivedCategory (ModuleCat.{max u v} A)} (f : K' ⟶ K)
    (u : derivedTensorUnit.{u, v, max u v + 1} A ⟶
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, M)) :
    homZeroEquivOverRing.{u, v} A K' M
        (u ≫ (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map (f.op, 𝟙 M)) =
      f ≫ homZeroEquivOverRing.{u, v} A K M u := by
  dsimp only [homZeroEquivOverRing, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_dinaturality]
  have h := derivedTensorUnitLeft_natural.{u, v, max u v + 1} A f
  refine (cancel_epi (derivedTensorUnitLeft.{u, v, max u v + 1} A K').hom).mp ?_
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_assoc]

/-- The degree-zero identification is `A`-linear. -/
theorem homZeroEquivOverRing_map_smul (K M : DerivedCategory (ModuleCat.{max u v} A)) (a : A)
    (u : derivedTensorUnit.{u, v, max u v + 1} A ⟶
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, M)) :
    homZeroEquivOverRing.{u, v} A K M (a • u) =
      a • homZeroEquivOverRing.{u, v} A K M u := by
  have h1 : a • u = u ≫ (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
      ((a • 𝟙 K).op, 𝟙 M) := by
    rw [derivedHom_map_smul_id_left.{u, v} A K M a, Linear.comp_smul, Category.comp_id]
  rw [h1, homZeroEquivOverRing_naturality_left.{u, v} A (a • 𝟙 K) u, Linear.smul_comp,
    Category.id_comp]

/-- The degree-zero identification as an isomorphism of `A`-modules. -/
def homZeroLinearEquivOverRing (K M : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedTensorUnit.{u, v, max u v + 1} A ⟶
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, M)) ≃ₗ[A]
      (K ⟶ M) :=
  (homZeroEquivOverRing.{u, v} A K M).toLinearEquiv
    (homZeroEquivOverRing_map_smul.{u, v} A K M)


/-- **Degree-zero cohomology of `RHom_A(-, M)` is `Hom_{D(A)}(-, M)`**, as an isomorphism of
`ModuleCat A`-valued functors on `D(A)ᵒᵖ`. -/
def homZeroNatIso (M : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.dualizingDerivedHomFunctor.{u, v} A M ⋙
        (linearCoyoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj
          (Opposite.op (derivedTensorUnit.{u, v, max u v + 1} A)) ≅
      (linearYoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj M :=
  NatIso.ofComponents (fun K => (homZeroLinearEquivOverRing.{u, v} A K.unop M).toModuleIso) (by
    intro K K' g
    refine ModuleCat.hom_ext (LinearMap.ext fun u => ?_)
    exact homZeroEquivOverRing_naturality_left.{u, v} A g.unop u)

/-! ### Cohomology corepresented by the free rank-one module -/

/-- Evaluation at `ULift.up 1` identifies morphisms out of the free rank-one `A`-module with the
module itself, after a universe lift. -/
def evalUnitEquiv (N : ModuleCat.{max u v} A) :
    (ModuleCat.of A (ULift.{v} A) ⟶ N) ≃ₗ[A]
      ULift.{max u v + 1} (N : Type (max u v)) :=
  (ModuleCat.homLinearEquiv (S := A)).trans
    (((LinearEquiv.arrowCongr (ULift.moduleEquiv (R := A) (M := A))
        (LinearEquiv.refl A (N : Type (max u v)))).trans
      (LinearMap.ringLmapEquivSelf A A (N : Type (max u v)))).trans
        (ULift.moduleEquiv (R := A) (M := (N : Type (max u v)))).symm)

/-- `evalUnitEquiv` sends a morphism `f` to the lift of its value `f (ULift.up 1)`. -/
@[simp] theorem evalUnitEquiv_apply (N : ModuleCat.{max u v} A)
    (f : ModuleCat.of A (ULift.{v} A) ⟶ N) :
    evalUnitEquiv.{u, v} A N f = ULift.up (f.hom (ULift.up 1)) := rfl

/-- **The free rank-one module placed in degree zero corepresents degree-zero cohomology** on the
whole unbounded derived category. -/
def homologyZeroNatIso :
    (linearCoyoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A (ULift.{v} A)))) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 ⋙
        ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A :=
  NatIso.ofComponents
    (fun Y => ((DerivedCategory.homologyFromSingleLinearEquiv
        (ModuleCat.of A (ULift.{v} A)) Y 0 A).trans
      (evalUnitEquiv.{u, v} A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).obj Y))).toModuleIso) (by
    intro Y Y' g
    refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
    have h := DerivedCategory.homologyFromSingleLinearEquiv_comp
      (ModuleCat.of A (ULift.{v} A)) Y 0 A f g
    change ULift.up (((DerivedCategory.homologyFromSingleLinearEquiv
        (ModuleCat.of A (ULift.{v} A)) Y' 0 A) (f ≫ g)).hom (ULift.up 1)) = _
    rw [h]
    rfl)

/-- Shifting an object by `i` and taking degree-zero cohomology is taking degree-`i`
cohomology. -/
def homologyShiftNatIso (i : ℤ) :
    CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shiftIso i 0 i (add_zero i)

/-- **The Ext–cohomology comparison**, as an isomorphism of `ModuleCat A`-valued functors on the
whole derived category: morphisms into `ω⟦i⟧` are the degree-`i` cohomology of `RHom_A(-, ω)`,
universe-lifted. -/
def extCohomologyComparisonIso (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    (linearYoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω) ≅
      Dualizing.dualizingDerivedHomFunctor.{u, v} A ω ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙
          ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A :=
  (homZeroNatIso.{u, v} A
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω)).symm ≪≫
    Functor.isoWhiskerRight (Dualizing.dualizingDerivedHomShiftIso.{u, v} A ω i)
      ((linearCoyoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj
        (Opposite.op (derivedTensorUnit.{u, v, max u v + 1} A))) ≪≫
    Functor.isoWhiskerLeft
      (Dualizing.dualizingDerivedHomFunctor.{u, v} A ω ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i)
      ((linearCoyoneda A (DerivedCategory (ModuleCat.{max u v} A))).mapIso
          (unitIsoSingle.{u, v} A).symm.op ≪≫
        homologyZeroNatIso.{u, v} A) ≪≫
    Functor.isoWhiskerLeft (Dualizing.dualizingDerivedHomFunctor.{u, v} A ω)
      (Functor.isoWhiskerRight (homologyShiftNatIso.{u, v} A i)
        (ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A))

end StacksDraft.DerivedHom.ExtComparison

namespace Dualizing

universe u v

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- **The Ext--cohomology comparison for derived Hom**, natural in the source module.
The `ULift` is necessary because derived morphisms live in a larger universe than the modules in
the derived category. This comparison does not require `ω` to be dualizing. -/
@[stacks 0A7C "Ext–cohomology comparison"]
public theorem nonempty_extIntoOmegaAtIso
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Nonempty (extIntoOmegaAt.{u, v} A ω i ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op ⋙
        dualizingDerivedHomFunctor.{u, v} A ω ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙
            ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A) :=
  ⟨Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op
    (StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, v} A ω i)⟩

/-- A natural identification of `Ext^i_A(-, ω)` with the universe-lifted degree-`i` cohomology of
derived Hom. It is the canonical comparison
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso`, restricted along the functor
placing a module in degree zero. -/
public def extIntoOmegaAtIso (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    extIntoOmegaAt.{u, v} A ω i ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op ⋙
        dualizingDerivedHomFunctor.{u, v} A ω ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙
            ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op
    (StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, v} A ω i)

/-- The component of the Ext comparison, with the universe lift removed. In particular `Ext` is
linearly equivalent to a module in the universe of the derived category. -/
public def extIntoOmegaAtLinearEquiv (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (M : ModuleCat.{max u v} A) :
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((dualizingDerivedHomFunctor.{u, v} A ω).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))) :=
  ((extIntoOmegaAtIso.{u, v} A ω i).app (.op M)).toLinearEquiv.trans ULift.moduleEquiv

/-- Precomposition on `Ext` agrees with the map on cohomology induced by contravariant derived
Hom. -/
public theorem extIntoOmegaAtLinearEquiv_naturality
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (x : (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N ⟶
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω) :
    extIntoOmegaAtLinearEquiv.{u, v} A ω i M
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f ≫ x) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((dualizingDerivedHomFunctor.{u, v} A ω).map
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f).op)
        (extIntoOmegaAtLinearEquiv.{u, v} A ω i N x) := by
  have h := ConcreteCategory.congr_hom ((extIntoOmegaAtIso.{u, v} A ω i).hom.naturality f.op) x
  exact congrArg ULift.down h

end Dualizing

end
