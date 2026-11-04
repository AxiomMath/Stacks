module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeComponent
public import StacksFrontier.Homology.Tor.DerivedTensorInvertibleScalar

/-!
# Joining the K-flat and the K-injective description of one object

The descended change-of-rings comparison for derived Hom,
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`, is a natural isomorphism on all of
`D(R)ᵒᵖ × D(A)`, and `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app` computes its
component at a pair `(Q K, Q J)` with `K` K-flat over `R` and `J` K-injective over `A`, where the
representative comparison `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` is
defined. This file computes the components at an arbitrary pair by naturality, and in particular
at a pair whose covariant variable is given by its K-flat description `A ⊗_R X` for a K-flat
complex `X` of `R`-modules.

## Main definitions

* `Stacks.DerivedHom.BaseChange.kFlatKInjectiveJoin`: for a K-flat complex `X` of `R`-modules and
  a K-injective resolution `n : A ⊗_R X ⟶ J`, the isomorphism `F (Q X) ≅ Q J` of `D(A)` given by
  the comparison `α` of the model `F` of derived extension of scalars followed by `n`.

## Main results

* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app_of_iso`: the component of the
  descended comparison at a pair `(X, Y)` with `X ≅ Q K` for a K-flat `K` and `Y ≅ Q J` for a
  K-injective `J` is the representative comparison conjugated by these isomorphisms.
* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_of_iso`: the same statement for
  the inverse component.
* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app_kFlatKInjectiveJoin`: the
  component at `(X, F (Q P))` for a K-flat complex `P` is the representative comparison conjugated
  by `Stacks.DerivedHom.BaseChange.kFlatKInjectiveJoin`.
* `Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin`: every object of `D(R)` is isomorphic
  to the class of a K-flat complex and every object of `D(A)` to the class of a K-injective one
  whose restriction of scalars admits a K-injective resolution.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChange

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
  (α : DerivedCategory.Q ⋙ F ⟶
    CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- A natural transformation on `Cᵒᵖ × D` is recovered at `(X, Y)` from its component at `(X', Y')`
by conjugating with isomorphisms `X ≅ X'` and `Y ≅ Y'`. -/
private theorem app_eq_map_comp_app_comp_map_of_iso {C D E : Type*} [Category C] [Category D]
    [Category E] {G H : Cᵒᵖ × D ⥤ E} (τ : G ⟶ H) {X X' : C} {Y Y' : D} (eX : X ≅ X')
    (eY : Y ≅ Y') :
    τ.app (Opposite.op X, Y) = G.map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
      τ.app (Opposite.op X', Y') ≫ H.map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  have hid : (CategoryTheory.Prod.mkHom eX.inv.op eY.hom :
      (Opposite.op X, Y) ⟶ (Opposite.op X', Y')) ≫
      CategoryTheory.Prod.mkHom eX.hom.op eY.inv = 𝟙 _ := by
    apply Prod.ext
    · exact Quiver.Hom.unop_inj (by simp)
    · simp
  rw [← Category.assoc, τ.naturality, Category.assoc, ← Functor.map_comp, hid,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The component of the descended change-of-rings comparison at an arbitrary pair.**  Let `K`
be a K-flat complex of `R`-modules, `J` a K-injective complex of `A`-modules and
`q : J|_R ⟶ I` a K-injective resolution of its restriction, so that the representative comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` is defined. Then for *any* objects
`X` of `D(R)` and `Y` of `D(A)` with `eX : X ≅ Q K` and `eY : Y ≅ Q J` the component of
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` at `(X, Y)` is that representative
comparison conjugated by `eX` and `eY`. -/
theorem modelRestrictScalarsNatIso_hom_app_of_iso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    (hK : K.KFlat) {X : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (eX : X ≅ DerivedCategory.Q.obj K) (eY : Y ≅ DerivedCategory.Q.obj J) :
    (modelRestrictScalarsNatIso f F α).hom.app (Opposite.op X, Y) =
      (homRestrictSource f).map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
        (derivedHomChangeOfRingsModelIso f F α K J I q hK).hom ≫
          (homRestrictTarget f F).map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  rw [app_eq_map_comp_app_comp_map_of_iso _ eX eY,
    modelRestrictScalarsNatIso_hom_app f F α K J I q hK]

/-- **The inverse component of the descended change-of-rings comparison at an arbitrary pair.**
With the data of `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app_of_iso`, the
inverse component at `(X, Y)` is the inverse of the representative comparison, conjugated by the
same two isomorphisms in the opposite order. -/
theorem modelRestrictScalarsNatIso_inv_app_of_iso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    (hK : K.KFlat) {X : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (eX : X ≅ DerivedCategory.Q.obj K) (eY : Y ≅ DerivedCategory.Q.obj J) :
    (modelRestrictScalarsNatIso f F α).inv.app (Opposite.op X, Y) =
      (homRestrictTarget f F).map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
        (derivedHomChangeOfRingsModelIso f F α K J I q hK).inv ≫
          (homRestrictSource f).map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  have hrep : (modelRestrictScalarsNatIso f F α).inv.app
      (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj J) =
      (derivedHomChangeOfRingsModelIso f F α K J I q hK).inv :=
    (Iso.inv_eq_inv (Iso.app (modelRestrictScalarsNatIso f F α)
        (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj J))
      (derivedHomChangeOfRingsModelIso f F α K J I q hK)).2
      (modelRestrictScalarsNatIso_hom_app f F α K J I q hK)
  rw [app_eq_map_comp_app_comp_map_of_iso _ eX eY, hrep]

/-- **The join of the K-flat and the K-injective description.**  For a K-flat complex `X` of
`R`-modules the comparison `α` of a model `F` of derived extension of scalars is invertible at
`X`, so `F (Q X)` is the class of the complex `A ⊗_R X`; composing with a K-injective resolution
`n : A ⊗_R X ⟶ J` identifies it with the class of a K-injective complex. -/
noncomputable def kFlatKInjectiveJoin (X : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj X ⟶ J) [QuasiIso n] :
    F.obj (DerivedCategory.Q.obj X) ≅ DerivedCategory.Q.obj J :=
  letI : IsIso (α.app X) := isIso_extendScalarsCounit_app_of_kFlat f F α X hX
  asIso (α.app X) ≪≫ asIso (DerivedCategory.Q.map n)

/-- The forward map of `kFlatKInjectiveJoin` is the component `α.app X` followed by the class
of the K-injective resolution `n`. -/
@[simp]
theorem kFlatKInjectiveJoin_hom (X : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj X ⟶ J) [QuasiIso n] :
    (kFlatKInjectiveJoin f F α X hX J n).hom = α.app X ≫ DerivedCategory.Q.map n :=
  rfl

/-- **The component of the descended comparison read at a K-flat description.**  With the
covariant variable given as `F (Q P)` — the class of `A ⊗_R P` for a K-flat complex `P` of
`R`-modules — the component of
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` is the representative comparison at a
K-injective resolution `J` of `A ⊗_R P`, conjugated by the join
`Stacks.DerivedHom.BaseChange.kFlatKInjectiveJoin` and by an identification of the contravariant
variable with a K-flat complex. -/
theorem modelRestrictScalarsNatIso_hom_app_kFlatKInjectiveJoin
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (n : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj P ⟶ J) [QuasiIso n]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    {X : DerivedCategory (ModuleCat.{u} R)} (eX : X ≅ DerivedCategory.Q.obj K) :
    (modelRestrictScalarsNatIso f F α).hom.app
        (Opposite.op X, F.obj (DerivedCategory.Q.obj P)) =
      (homRestrictSource f).map (CategoryTheory.Prod.mkHom eX.inv.op
          (kFlatKInjectiveJoin f F α P hP J n).hom) ≫
        (derivedHomChangeOfRingsModelIso f F α K J I q hK).hom ≫
          (homRestrictTarget f F).map (CategoryTheory.Prod.mkHom eX.hom.op
            (kFlatKInjectiveJoin f F α P hP J n).inv) :=
  modelRestrictScalarsNatIso_hom_app_of_iso f F α K J I q hK eX
    (kFlatKInjectiveJoin f F α P hP J n)

/-- For objects `X` of `D(R)` and `Y` of `D(A)` there are a K-flat complex `K` with `X ≅ Q K`, a
K-injective complex `J` with `Y ≅ Q J`, and a K-injective resolution `q : J|_R ⟶ I` of the
restriction of scalars of `J`. -/
theorem exists_kFlatKInjectiveJoin (X : DerivedCategory (ModuleCat.{u} R))
    (Y : DerivedCategory (ModuleCat.{u} A)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
      (I : CochainComplex (ModuleCat.{u} R) ℤ) (_ : K.KFlat) (_ : J.IsKInjective)
      (_ : I.IsKInjective) (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
      (_ : QuasiIso q), Nonempty (X ≅ DerivedCategory.Q.obj K) ∧
        Nonempty (Y ≅ DerivedCategory.Q.obj J) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative X
  obtain ⟨J₀, j, hj, hJ₀⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage Y)
  obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J₀)
  exact ⟨K, J₀, I, hK, hJ₀, hI, q, hq, ⟨eK.symm⟩,
    ⟨(DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫ asIso (DerivedCategory.Q.map j)⟩⟩

end Stacks.DerivedHom.BaseChange

end
