module

public import StacksFrontier.Deformation.Artin.Obstruction.DerivedTensorOverRing
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.RingTheory.Dualizing.ScalarTransportComparisons

/-!
# Perfect duality in degree one for the canonical derived tensor product

Let `A` be a ring and let `K` be a perfect object of `D(A)`. [Stacks, Tag 07VI] identifies
`H⁰(X ⊗ᴸ Kᵛ)` with `Hom_{D(A)}(K, X)` functorially in `X`. Applying this to the dual `Kᵛ`,
whose own dual is `K` by biduality, and shifting by one, gives

`H¹(X ⊗ᴸ K) ≅ Hom_{D(A)}(Kᵛ[-1], X)`

functorially in `X`, with `Kᵛ[-1]` again perfect. This is the form in which the obstruction
theory of a dual deformation situation uses perfect duality: the left-hand side is the
first cohomology of the derived tensor product
`CochainComplex.DerivedTensor.derivedTensorProduct K`, the endofunctor `X ↦ X ⊗ᴸ K` of `D(A)`.

## Main results

* `Deformation.Artin.exists_perfect_homologyOneEquiv` — for perfect `K` there is a perfect `E`
  with `H¹(X ⊗ᴸ K) ≃+ Hom_{D(A)}(E, X)` naturally in `X`.
* `Deformation.Artin.exists_perfect_homologyZeroEquiv` — for perfect `P` there is a perfect `K`
  with `H⁰(X ⊗ᴸ K) ≃+ Hom_{D(A)}(P, X)` naturally in `X`, the represented object being `P`
  itself.

## Implementation notes

Three transports separate [stacks 07VI] from the statement proved here.

First, [stacks 07VI] is stated over `ULift A`, since Mathlib's monoidal category of modules
forces the ring and module universes to agree, while the obstruction theory works over `A`
itself. The scalar transport `StacksDraft.DerivedHom.derivedScalarEquivalence` carries the
degree-zero clause across; the argument is the one of
`StacksFrontier.RingTheory.Dualizing.RegularLocalFiniteLengthDuality`, whose helpers are private
and are therefore restated here.

Second, [stacks 07VI] uses the derived tensor product of the tensor--Hom adjunction
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, whereas the obstruction theory uses
`CochainComplex.DerivedTensor.derivedTensorProduct`. The two agree by
`Deformation.Artin.nonempty_derivedTensorProduct_iso_tensorOverRing`, every object of `D(A)`
having a K-flat representative.

Third, the degree is raised by one: `H¹(Y) ≅ H⁰(Y⟦1⟧)` by the shift sequence of the homology
functor, `(X ⊗ᴸ K)⟦1⟧ ≅ X⟦1⟧ ⊗ᴸ K` by the commutation of the derived tensor product with the
shift, and `Hom(Kᵛ, X⟦1⟧) ≅ Hom(Kᵛ[-1], X)` by the shift equivalence of the derived category.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedTensor StacksDraft.DerivedHom

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! ### Elementary transport lemmas -/

section Elementary

/-- Composition with isomorphisms, as an additive bijection of morphism groups. -/
private def homIsoAddEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y Y' : C}
    (α : X ≅ X') (β : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toFun g := α.inv ≫ g ≫ β.hom
  invFun g := α.hom ≫ g ≫ β.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := by
    simp only [Preadditive.add_comp, Preadditive.comp_add]

/-- The value of the morphism-group bijection attached to a pair of isomorphisms. -/
private theorem homIsoAddEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y') (g : X ⟶ Y) :
    homIsoAddEquiv α β g = α.inv ≫ g ≫ β.hom := rfl

-- The additive bijection of underlying groups attached to an isomorphism of modules, and its
-- value, stood here. MATHLIB REPLACES BOTH: `CategoryTheory.Iso.toLinearEquiv`
-- (Mathlib/Algebra/Category/ModuleCat/Basic.lean:289) with its `@[simp]` companion
-- `toLinearEquiv_apply` (:292); `α.toLinearEquiv.toAddEquiv` is the additive bijection.

end Elementary

/-! ### Perfectness along the scalar transport and the shift -/

section Perfectness

variable (A : Type u) [CommRing A]

/-- The identity map, as a semilinear equivalence from a module onto the same module with its
scalars restricted along the canonical isomorphism from the lifted ring. -/
private def identityRestrictScalarsUp (M : ModuleCat.{u} A) :
    LinearEquiv (R := A) (S := ULift.{0} A)
      (σ' := ↑(ULift.ringEquiv : ULift.{0} A ≃+* A))
      (↑(ULift.ringEquiv : ULift.{0} A ≃+* A).symm) M
      ((ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{0} A ≃+* A).toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity map, as a semilinear equivalence from a module over the lifted ring onto the
same module with its scalars restricted along the canonical isomorphism. -/
private def identityRestrictScalarsDown (M : ModuleCat.{u} (ULift.{0} A)) :
    LinearEquiv (R := ULift.{0} A) (S := A)
      (σ' := ↑(ULift.ringEquiv : ULift.{0} A ≃+* A).symm)
      (↑(ULift.ringEquiv : ULift.{0} A ≃+* A)) M
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{0} A ≃+* A).symm.toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Perfectness travels back along the scalar transport.** -/
private theorem isPerfect_inverse_scalarEquiv
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.Perfect.IsPerfect ((scalarEquiv A).inverse.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨j⟩⟩ := hK
  let F := (liftEquiv A).inverse
  let := ha
  let := hb
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b, inferInstance,
    inferInstance, ?_, ?_, ⟨?_⟩⟩
  · intro n
    let := hfin n
    exact Module.Finite.of_surjective (identityRestrictScalarsUp A (P.X n)).toLinearMap
      (identityRestrictScalarsUp A (P.X n)).surjective
  · intro n
    let := hproj n
    exact Module.Projective.of_equiv (identityRestrictScalarsUp A (P.X n))
  · exact (scalarEquiv A).inverse.mapIso j ≪≫ F.mapDerivedCategoryFactors.app P

/-- **Perfectness travels forward along the scalar transport.** -/
private theorem isPerfect_functor_scalarEquiv
    (K : DerivedCategory (ModuleCat.{u} (ULift.{0} A)))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.Perfect.IsPerfect ((scalarEquiv A).functor.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨j⟩⟩ := hK
  let F := (liftEquiv A).functor
  let := ha
  let := hb
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b, inferInstance,
    inferInstance, ?_, ?_, ⟨?_⟩⟩
  · intro n
    let := hfin n
    exact Module.Finite.of_surjective (identityRestrictScalarsDown A (P.X n)).toLinearMap
      (identityRestrictScalarsDown A (P.X n)).surjective
  · intro n
    let := hproj n
    exact Module.Projective.of_equiv (identityRestrictScalarsDown A (P.X n))
  · exact (scalarEquiv A).functor.mapIso j ≪≫ F.mapDerivedCategoryFactors.app P

variable {A}

/-- Perfectness is invariant under shift: shift a bounded finite projective representative. -/
private theorem isPerfect_shift (X : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : StacksDraft.Perfect.IsPerfect X) : StacksDraft.Perfect.IsPerfect (X⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := h
  refine ⟨(shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) n).obj P, a - n, b - n, ?_, ?_,
    fun i => hf _, fun i => hp _, ?_⟩
  · exact P.isStrictlyGE_shift a n (a - n) (by omega)
  · exact P.isStrictlyLE_shift b n (b - n) (by omega)
  · exact ⟨(shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app P⟩

end Perfectness

/-! ### Degree-zero perfect duality over the ring itself -/

section DegreeZero

/-- The derived dual `RHom_A(X, A)` of an object of `D(A)`, computed through the scalar
transport to the derived category of modules over the lifted ring. -/
private abbrev dualOverRing (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} A) :=
  (scalarEquiv A).functor.obj
    (StacksDraft.Perfect.derivedDual ((scalarEquiv A).inverse.obj X))

/-- The derived tensor product `L ⊗^L_A D` by a fixed object presented as the scalar transport
of an object `W`, identified with the scalar transport of `L ⊗^L W` over the lifted ring. -/
private def tensorScalarIso (A : Type u) [CommRing A]
    (W : DerivedCategory (ModuleCat.{u} (ULift.{0} A)))
    (D : DerivedCategory (ModuleCat.{u} A))
    (ψ : (scalarEquiv A).functor.obj W ≅ D)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (overRingData A).tensor.obj (L, D) ≅
      (scalarEquiv A).functor.obj
        ((liftedData A).tensor.obj ((scalarEquiv A).inverse.obj L, W)) :=
  (overRingData A).tensor.mapIso
      (((scalarEquiv A).counitIso.app L).symm.prod ψ.symm) ≪≫
    (derivedTensorULiftIso.{u, 0, u + 1} A).app ((scalarEquiv A).inverse.obj L, W)

/-- The identification of derived tensor products is natural in the first variable. -/
private theorem tensorScalarIso_naturality (A : Type u) [CommRing A]
    (W : DerivedCategory (ModuleCat.{u} (ULift.{0} A)))
    (D : DerivedCategory (ModuleCat.{u} A))
    (ψ : (scalarEquiv A).functor.obj W ≅ D)
    {L L' : DerivedCategory (ModuleCat.{u} A)} (f : L ⟶ L') :
    (overRingData A).tensor.map (f, 𝟙 D) ≫ (tensorScalarIso A W D ψ L').hom =
      (tensorScalarIso A W D ψ L).hom ≫
        (scalarEquiv A).functor.map
          ((liftedData A).tensor.map ((scalarEquiv A).inverse.map f, 𝟙 W)) := by
  have hprod :
      ((f, 𝟙 D) : ((L, D) : DerivedCategory (ModuleCat.{u} A) ×
          DerivedCategory (ModuleCat.{u} A)) ⟶ (L', D)) ≫
        (((scalarEquiv A).counitIso.app L').symm.prod ψ.symm).hom =
      (((scalarEquiv A).counitIso.app L).symm.prod ψ.symm).hom ≫
        (((scalarEquiv A).functor.map ((scalarEquiv A).inverse.map f),
            (scalarEquiv A).functor.map (𝟙 W)) :
          (((scalarEquiv A).functor.obj ((scalarEquiv A).inverse.obj L),
              (scalarEquiv A).functor.obj W) :
              DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
            ((scalarEquiv A).functor.obj ((scalarEquiv A).inverse.obj L'),
              (scalarEquiv A).functor.obj W)) := by
    refine Prod.ext ?_ ?_
    · exact (scalarEquiv A).counitIso.inv.naturality f
    · simp
  have hnat :
      (overRingData A).tensor.map
          (((scalarEquiv A).functor.map ((scalarEquiv A).inverse.map f),
              (scalarEquiv A).functor.map (𝟙 W)) :
            (((scalarEquiv A).functor.obj ((scalarEquiv A).inverse.obj L),
                (scalarEquiv A).functor.obj W) :
                DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              ((scalarEquiv A).functor.obj ((scalarEquiv A).inverse.obj L'),
                (scalarEquiv A).functor.obj W)) ≫
        ((derivedTensorULiftIso.{u, 0, u + 1} A).app
          ((scalarEquiv A).inverse.obj L', W)).hom =
      ((derivedTensorULiftIso.{u, 0, u + 1} A).app
          ((scalarEquiv A).inverse.obj L, W)).hom ≫
        (scalarEquiv A).functor.map
          ((liftedData A).tensor.map
            ((((scalarEquiv A).inverse.map f, 𝟙 W)) :
              (((scalarEquiv A).inverse.obj L, W) :
                  DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
                    DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶
                ((scalarEquiv A).inverse.obj L', W))) :=
    (derivedTensorULiftIso.{u, 0, u + 1} A).hom.naturality
      ((((scalarEquiv A).inverse.map f, 𝟙 W)) :
        (((scalarEquiv A).inverse.obj L, W) :
            DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
              DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶
          ((scalarEquiv A).inverse.obj L', W))
  dsimp only [tensorScalarIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hprod, Functor.map_comp, Category.assoc, hnat,
    Category.assoc]

/-- **Degree-zero perfect duality over the ring itself.** For a perfect object `X` of `D(A)`
and an object `D` isomorphic to its derived dual there are additive isomorphisms
`H⁰(L ⊗^L_A D) ≃+ Hom_{D(A)}(X, L)`, natural in `L`. -/
private theorem exists_addEquiv_homology_derivedTensor_dual (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : StacksDraft.Perfect.IsPerfect X)
    (D : DerivedCategory (ModuleCat.{u} A)) (ψ : dualOverRing A X ≅ D) :
    ∃ e : ∀ L : DerivedCategory (ModuleCat.{u} A),
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((overRingData A).tensor.obj (L, D))) : Type u) ≃+ (X ⟶ L),
      ∀ (L L' : DerivedCategory (ModuleCat.{u} A)) (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((overRingData A).tensor.obj (L, D))),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((overRingData A).tensor.map (f, 𝟙 D)) a) = e L a ≫ f := by
  set E := scalarEquiv A with hE
  set d' := liftedData A with hd'
  set H0A := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH0A
  set H0U := DerivedCategory.homologyFunctor (ModuleCat.{u} (ULift.{0} A)) 0 with hH0U
  set W := StacksDraft.Perfect.derivedDual (E.inverse.obj X) with hW
  obtain ⟨e, he⟩ := (StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos
    (E.inverse.obj X) (isPerfect_inverse_scalarEquiv A X hX)).exists_extZeroEquiv
  have he' : ∀ {M M' : DerivedCategory (ModuleCat.{u} (ULift.{0} A))} (g : M ⟶ M')
      (b : H0U.obj (d'.tensor.obj (M, W))),
      e M' (H0U.map (d'.tensor.map ((g, 𝟙 W) :
          ((M, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (M', W))) b) = e M b ≫ g :=
    fun g b => he g b
  refine ⟨fun L =>
    ((H0A.mapIso (tensorScalarIso A W D ψ L)).toLinearEquiv.toAddEquiv).trans
      ((scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0).trans
        ((e (E.inverse.obj L)).trans
          ((equivalenceHomAddEquiv E (E.inverse.obj X) (E.inverse.obj L)).trans
            (homIsoAddEquiv (E.counitIso.app X) (E.counitIso.app L))))), ?_⟩
  intro L L' f a
  have key : scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        ((H0A.mapIso (tensorScalarIso A W D ψ L')).toLinearEquiv.toAddEquiv
          (H0A.map ((overRingData A).tensor.map (f, 𝟙 D)) a)) =
      H0U.map (d'.tensor.map ((E.inverse.map f, 𝟙 W) :
          ((E.inverse.obj L, W) : DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
            DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶ (E.inverse.obj L', W)))
        (scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L, W)) 0
          ((H0A.mapIso (tensorScalarIso A W D ψ L)).toLinearEquiv.toAddEquiv a)) := by
    simp only [LinearEquiv.coe_toAddEquiv]
    show scalarHomologyAddEquiv.{u, 0} A (d'.tensor.obj (E.inverse.obj L', W)) 0
        (H0A.map (tensorScalarIso A W D ψ L').hom
          (H0A.map ((overRingData A).tensor.map (f, 𝟙 D)) a)) = _
    rw [← Functor.map_comp_apply, tensorScalarIso_naturality A W D ψ f,
      Functor.map_comp_apply]
    exact scalarHomologyAddEquiv_naturality.{u, 0} A _ 0 _
  have hcounit : E.functor.map (E.inverse.map f) ≫ (E.counitIso.app L').hom =
      (E.counitIso.app L).hom ≫ f := E.counitIso.hom.naturality f
  simp only [AddEquiv.trans_apply]
  rw [key, he' (E.inverse.map f), equivalenceHomAddEquiv_comp, homIsoAddEquiv_apply,
    homIsoAddEquiv_apply]
  simp only [Category.assoc]
  rw [hcounit]

end DegreeZero

/-! ### The comparison of the two derived tensor products, without a representative -/

section Bridge

variable {A : Type u} [CommRing A]

/-- **The two derived tensor products agree**, for any object of `D(A)`: every object of the
derived category of modules has a K-flat representative. -/
public theorem nonempty_derivedTensorProduct_iso_tensorOverRing'
    (M : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty (derivedTensorProduct M ≅
      (Functor.curry.obj (overRingData A).tensor).flip.obj M) := by
  obtain ⟨P, g, hP, -, hg, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage M)
  let : QuasiIso g := hg
  exact nonempty_derivedTensorProduct_iso_tensorOverRing P hP M
    (asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso M)

end Bridge

/-! ### Perfect duality in degree one -/

section DegreeOne

/-- Transport of the degree-zero duality from the tensor product `(overRingData A).tensor` to
`derivedTensorProduct D`, along any identification of the two. -/
private theorem exists_addEquiv_homology_derivedTensorProduct {A : Type u} [CommRing A]
    (X D : DerivedCategory (ModuleCat.{u} A))
    (h : ∃ e : ∀ L : DerivedCategory (ModuleCat.{u} A),
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((overRingData A).tensor.obj (L, D))) : Type u) ≃+ (X ⟶ L),
      ∀ (L L' : DerivedCategory (ModuleCat.{u} A)) (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((overRingData A).tensor.obj (L, D))),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((overRingData A).tensor.map (f, 𝟙 D)) a) = e L a ≫ f) :
    ∃ e : ∀ L : DerivedCategory (ModuleCat.{u} A),
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((derivedTensorProduct D).obj L)) : Type u) ≃+ (X ⟶ L),
      ∀ (L L' : DerivedCategory (ModuleCat.{u} A)) (f : L ⟶ L')
        (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedTensorProduct D).obj L)),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((derivedTensorProduct D).map f) c) = e L c ≫ f := by
  obtain ⟨e₁, he₁⟩ := h
  obtain ⟨β⟩ := nonempty_derivedTensorProduct_iso_tensorOverRing' D
  refine ⟨fun L => (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
    (β.app L)).toLinearEquiv.toAddEquiv).trans (e₁ L), fun L L' f c => ?_⟩
  have hβ : (derivedTensorProduct D).map f ≫ (β.app L').hom =
      (β.app L).hom ≫ (overRingData A).tensor.map (f, 𝟙 D) := β.hom.naturality f
  show e₁ L' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (β.app L').hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((derivedTensorProduct D).map f) c)) = _
  rw [← Functor.map_comp_apply, hβ, Functor.map_comp_apply]
  exact he₁ L L' f _

/-- Functoriality of the derived dual in its argument. -/
private def derivedDualMapIso {A : Type u} [CommRing A]
    {X Y : DerivedCategory (ModuleCat.{u} (ULift.{0} A))} (α : X ≅ Y) :
    StacksDraft.Perfect.derivedDual.{u, 0} (R := A) Y ≅
      StacksDraft.Perfect.derivedDual.{u, 0} (R := A) X :=
  (liftedData A).hom.mapIso
    (Iso.prod (Iso.op α) (Iso.refl (StacksDraft.Perfect.unitObject.{u, 0} (R := A))))

/-- **Stacks 07VI in degree one, over the ring itself.** -/
public theorem exists_perfect_homologyOneEquiv (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : StacksDraft.Perfect.IsPerfect K) :
    ∃ (E : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect E ∧
      ∃ Φ : ∀ X : DerivedCategory (ModuleCat.{u} A),
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X) : Type u) ≃+ (E ⟶ X),
        ∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y)
          (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X)),
          Φ Y ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
              ((CochainComplex.DerivedTensor.derivedTensorProduct K).map g) a) = Φ X a ≫ g := by
  have hK₀ : StacksDraft.Perfect.IsPerfect ((scalarEquiv A).inverse.obj K) :=
    isPerfect_inverse_scalarEquiv A K hK
  have hdual := StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos
    ((scalarEquiv A).inverse.obj K) hK₀
  have hKV : StacksDraft.Perfect.IsPerfect (dualOverRing A K) :=
    isPerfect_functor_scalarEquiv A _ hdual.dual_isPerfect
  have : IsIso (StacksDraft.Perfect.biduality ((scalarEquiv A).inverse.obj K)) :=
    hdual.biduality_isIso
  -- the dual of the dual is `K`
  let ψ : dualOverRing A (dualOverRing A K) ≅ K :=
    (scalarEquiv A).functor.mapIso
        (derivedDualMapIso
            ((scalarEquiv A).unitIso.app
              (StacksDraft.Perfect.derivedDual ((scalarEquiv A).inverse.obj K))) ≪≫
          (asIso (StacksDraft.Perfect.biduality ((scalarEquiv A).inverse.obj K))).symm) ≪≫
      (scalarEquiv A).counitIso.app K
  obtain ⟨e₂, he₂⟩ := exists_addEquiv_homology_derivedTensorProduct _ _
    (exists_addEquiv_homology_derivedTensor_dual A (dualOverRing A K) hKV K ψ)
  -- the shift equivalence of the derived category
  let 𝓢 : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{u} A) :=
    CategoryTheory.shiftEquiv' (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ) 1 (by omega)
  have : 𝓢.functor.Additive := by
    show (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ)).Additive
    infer_instance
  let e₄ : ∀ X : DerivedCategory (ModuleCat.{u} A),
      ((dualOverRing A K ⟶ X⟦(1 : ℤ)⟧) ≃+ ((dualOverRing A K)⟦(-1 : ℤ)⟧ ⟶ X)) := fun X =>
    (equivalenceHomAddEquiv 𝓢 (dualOverRing A K) (X⟦(1 : ℤ)⟧)).trans
      (homIsoAddEquiv (Iso.refl _) (𝓢.counitIso.app X))
  have he₄apply : ∀ (X : DerivedCategory (ModuleCat.{u} A))
      (k : dualOverRing A K ⟶ X⟦(1 : ℤ)⟧),
      e₄ X k = 𝓢.functor.map k ≫ (𝓢.counitIso.app X).hom := by
    intro X k
    show (Iso.refl (𝓢.functor.obj (dualOverRing A K))).inv ≫
      𝓢.functor.map k ≫ (𝓢.counitIso.app X).hom = _
    rw [Iso.refl_inv, Category.id_comp]
  have he₄ : ∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y)
      (h : dualOverRing A K ⟶ X⟦(1 : ℤ)⟧),
      e₄ Y (h ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g) =
        e₄ X h ≫ g := by
    intro X Y g h
    -- The counit of `𝓢` is a morphism out of `(𝓢.inverse ⋙ 𝓢.functor).obj Y`, while the
    -- composite below needs it out of `𝓢.functor.obj (Y⟦1⟧)`; the two agree only after
    -- `CategoryTheory.shiftEquiv'` is unfolded, so the three morphisms are named here with
    -- the spelling the composite uses and the square is pasted as a term.
    let mh : 𝓢.functor.obj (dualOverRing A K) ⟶
        𝓢.functor.obj ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).obj X) :=
      𝓢.functor.map h
    let sg : 𝓢.functor.obj ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).obj X) ⟶
        𝓢.functor.obj ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).obj Y) :=
      𝓢.functor.map ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g)
    let cX : 𝓢.functor.obj ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).obj X) ⟶
        X := (𝓢.counitIso.app X).hom
    let cY : 𝓢.functor.obj ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).obj Y) ⟶
        Y := (𝓢.counitIso.app Y).hom
    have hc : sg ≫ cY = cX ≫ g := 𝓢.counitIso.hom.naturality g
    rw [he₄apply, he₄apply, Functor.map_comp]
    show (mh ≫ sg) ≫ cY = (mh ≫ cX) ≫ g
    exact (Category.assoc _ _ _).trans ((mh ≫= hc).trans (Category.assoc _ _ _).symm)
  -- the commutation of the derived tensor product with the shift, with its naturality;
  -- both are abstracted so that later steps see one fixed spelling of the objects
  obtain ⟨ι, hι⟩ : ∃ ι : ∀ X : DerivedCategory (ModuleCat.{u} A),
      ((derivedTensorProduct K).obj X)⟦(1 : ℤ)⟧ ≅ (derivedTensorProduct K).obj (X⟦(1 : ℤ)⟧),
      ∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y),
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map
              ((derivedTensorProduct K).map g) ≫ (ι Y).hom =
          (ι X).hom ≫ (derivedTensorProduct K).map
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g) :=
    ⟨fun X => (((derivedTensorProduct K).commShiftIso (1 : ℤ)).app X).symm,
      fun _ _ g => ((derivedTensorProduct K).commShiftIso (1 : ℤ)).inv.naturality g⟩
  -- the shift sequence of the homology functor, likewise abstracted
  obtain ⟨sh, hsh⟩ : ∃ sh : ∀ Y : DerivedCategory (ModuleCat.{u} A),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj Y ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (Y⟦(1 : ℤ)⟧),
      ∀ (Y Y' : DerivedCategory (ModuleCat.{u} A)) (φ : Y ⟶ Y'),
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map φ ≫ (sh Y').hom =
          (sh Y).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map φ) :=
    ⟨fun Y => (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
        (1 : ℤ) 0 1 (by omega)).app Y).symm,
      fun _ _ φ => ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
        (1 : ℤ) 0 1 (by omega)).inv.naturality φ⟩
  -- the degree shift `H¹(X ⊗ᴸ K) ≅ H⁰(X⟦1⟧ ⊗ᴸ K)`
  let ν : ∀ X : DerivedCategory (ModuleCat.{u} A),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
          ((derivedTensorProduct K).obj X) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedTensorProduct K).obj (X⟦(1 : ℤ)⟧)) := fun X =>
    sh ((derivedTensorProduct K).obj X) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso (ι X)
  have hν : ∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
            ((derivedTensorProduct K).map g) ≫ (ν Y).hom =
        (ν X).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedTensorProduct K).map
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g)) := by
    intro X Y g
    have h1 : ∀ {Z : ModuleCat.{u} A}
        (k : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          (((derivedTensorProduct K).obj Y)⟦(1 : ℤ)⟧) ⟶ Z),
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
              ((derivedTensorProduct K).map g) ≫
            (sh ((derivedTensorProduct K).obj Y)).hom ≫ k =
          (sh ((derivedTensorProduct K).obj X)).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
              ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map
                ((derivedTensorProduct K).map g)) ≫ k :=
      fun k => by
        rw [← Category.assoc, hsh ((derivedTensorProduct K).obj X)
          ((derivedTensorProduct K).obj Y) ((derivedTensorProduct K).map g), Category.assoc]
    show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
          ((derivedTensorProduct K).map g) ≫
        (sh ((derivedTensorProduct K).obj Y)).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (ι Y).hom =
      ((sh ((derivedTensorProduct K).obj X)).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (ι X).hom) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedTensorProduct K).map
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g))
    rw [h1, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hι]
  refine ⟨(dualOverRing A K)⟦(-1 : ℤ)⟧, isPerfect_shift _ _ hKV, fun X =>
    ((ν X).toLinearEquiv.toAddEquiv).trans ((e₂ (X⟦(1 : ℤ)⟧)).trans (e₄ X)), ?_⟩
  intro X Y g a
  have hel : (ν Y).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
          ((derivedTensorProduct K).map g) a) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((derivedTensorProduct K).map
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g))
        ((ν X).hom a) := by
    have h := ConcreteCategory.congr_hom (hν X Y g) a
    simpa only [ConcreteCategory.comp_apply] using h
  show e₄ Y (e₂ (Y⟦(1 : ℤ)⟧) ((ν Y).hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
        ((derivedTensorProduct K).map g) a))) =
    e₄ X (e₂ (X⟦(1 : ℤ)⟧) ((ν X).hom a)) ≫ g
  rw [hel, he₂ _ _ ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map g), he₄]

end DegreeOne

/-! ### Perfect duality in degree zero, with the represented object named -/

section DegreeZeroNamed

/-- **Stacks 07VI in degree zero, over the ring itself, with the representing object named.**
For a perfect object `P` of `D(A)` there is a perfect `K` (the derived dual of `P`) with
`H⁰(X ⊗ᴸ K) ≃+ Hom_{D(A)}(P, X)` naturally in `X`, for the derived tensor product
`CochainComplex.DerivedTensor.derivedTensorProduct K`. -/
public theorem exists_perfect_homologyZeroEquiv (A : Type u) [CommRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) (hP : StacksDraft.Perfect.IsPerfect P) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ Φ : ∀ X : DerivedCategory (ModuleCat.{u} A),
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X) : Type u) ≃+ (P ⟶ X),
        ∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y)
          (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X)),
          Φ Y ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
              ((CochainComplex.DerivedTensor.derivedTensorProduct K).map g) a) = Φ X a ≫ g := by
  have hP₀ : StacksDraft.Perfect.IsPerfect ((scalarEquiv A).inverse.obj P) :=
    isPerfect_inverse_scalarEquiv A P hP
  have hdual := StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos
    ((scalarEquiv A).inverse.obj P) hP₀
  have hKV : StacksDraft.Perfect.IsPerfect (dualOverRing A P) :=
    isPerfect_functor_scalarEquiv A _ hdual.dual_isPerfect
  obtain ⟨e₂, he₂⟩ := exists_addEquiv_homology_derivedTensorProduct _ _
    (exists_addEquiv_homology_derivedTensor_dual A P hP (dualOverRing A P) (Iso.refl _))
  exact ⟨dualOverRing A P, hKV, e₂, he₂⟩

end DegreeZeroNamed

end Deformation.Artin

end
