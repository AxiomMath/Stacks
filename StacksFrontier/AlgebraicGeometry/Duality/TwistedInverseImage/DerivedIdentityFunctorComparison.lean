module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroCounitTransport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion

/-!
# A left derived functor of an exact endofunctor isomorphic to the identity

Let `C` be an abelian category with a derived category, let `F : C ⥤ C` be an exact additive
functor and let `e : F ≅ 𝟭 C`. Then `F` induces a functor `F.mapDerivedCategory` on derived
categories, and reading `e` there identifies it with the identity functor:

```
Functor.mapDerivedCategoryCongr e ≪≫ Functor.mapDerivedCategoryId C
```

If `LF` is *any* left derived functor of `F` followed by the localization — presented by a
functor on the derived category together with its comparison `ε : Qh ⋙ LF ⟶ K(F) ⋙ Qh` — then
`LF` is identified with `𝟭` through the same chain, by uniqueness of the left derived functor.
This file computes the *factorization* of that identification against `ε`: evaluated on the
image of `DerivedCategory.Qh`, the composite of the identification with the comparison is the
degreewise `e` read on the unbounded homotopy category.

## Main definitions

All in the namespace `CategoryTheory`.

* `mapHomotopyCategoryToId` — the transformation `K(F) ⟶ 𝟭` on the unbounded homotopy category
  attached to `e : F ≅ 𝟭 C`.
* `leftDerivedToIdIso` — the identification `LF ≅ 𝟭` of a left derived functor of `K(F) ⋙ Qh`
  with the identity, through `F.mapDerivedCategory`.

## Main results

* `CategoryTheory.leftDerivedToIdIso_hom_app_Qh` — **the factorization**: at an object `M` of
  the unbounded homotopy category,
  `ε.app M ≫ Qh.map ((mapHomotopyCategoryToId F e).app M)` is
  `(leftDerivedToIdIso F e LF ε).hom.app (Qh.obj M)`.
* `CategoryTheory.Functor.mapDerivedCategoryCongrId_hom_app_Qh` — the same factorization for
  `F.mapDerivedCategory`: on the image of `DerivedCategory.Qh`, its identification with `𝟭` is
  the factorization over the homotopy category followed by the class of the degreewise `e`.
* `CategoryTheory.Functor.mapDerivedCategoryId_hom_eq_mapDerivedCategoryIdIso` — the two
  constructions of `(𝟭 C).mapDerivedCategory ≅ 𝟭` agree: the one lifted through
  `DerivedCategory.Q` and the one lifted through `DerivedCategory.Qh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

/-! ### The identity functor on the homotopy category -/

section Additive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C)

/-- The transformation `K(F) ⟶ 𝟭` on the unbounded homotopy category of cochain complexes
attached to an isomorphism `e : F ≅ 𝟭 C`: the degreewise `e`, followed by the identification of
the functor induced by `𝟭 C` with the identity. -/
def mapHomotopyCategoryToId : F.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
    𝟭 (HomotopyCategory C (ComplexShape.up ℤ)) :=
  NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom

/-- `mapHomotopyCategoryToId` at the class of a cochain complex is the class of the degreewise
transformation. -/
theorem mapHomotopyCategoryToId_app_quotient (L : CochainComplex C ℤ) :
    (mapHomotopyCategoryToId F e).app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app L ≫
          (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app L) := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

end Additive

/-! ### The two constructions of the identity comparison on derived categories -/

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

omit [HasDerivedCategory C] in
/-- The identification of the functor induced on homotopy categories by `𝟭 C` with the identity
is, at the class of a cochain complex, the class of the degreewise identification. -/
theorem Functor.mapHomotopyCategoryIdIso_hom_app_quotient (K : CochainComplex C ℤ) :
    (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K) :=
  rfl

omit [HasDerivedCategory C] in
/-- The comparison `K(𝟭 C) ⟶ 𝟭` on the homotopy category, read through the factorization of
`(𝟭 C).mapHomotopyCategory` over the quotient functor, is the class of the degreewise
identification. -/
theorem Functor.mapHomotopyCategoryFactors_inv_app_comp_mapHomotopyCategoryIdIso
    (K : CochainComplex C ℤ) :
    ((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K ≫
        (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K) :=
  Category.id_comp _

/-- `CategoryTheory.Functor.mapDerivedCategoryId` on the image of `DerivedCategory.Q`. -/
theorem Functor.mapDerivedCategoryId_hom_app_Q (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryId C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K) := by
  rw [Functor.mapDerivedCategoryId, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp
  rfl

/-- **The crossing between `DerivedCategory.Q` and `DerivedCategory.Qh` for the identity
functor.** The value of `CategoryTheory.Functor.mapDerivedCategoryId` at `DerivedCategory.Q.obj
K`, transported along `CategoryTheory.DerivedCategory.quotientCompQhIso`, is the value computed
on the homotopy category through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
theorem Functor.mapDerivedCategoryId_hom_app_Q_comp_quotientCompQhIso (K : CochainComplex C ℤ) :
    (𝟭 C).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
        ((𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K)) =
      ((𝟭 C).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app
              ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc]
  have hmc : DerivedCategory.Qh.map
          (((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K)) :=
    Eq.trans (DerivedCategory.Qh.map_comp _ _).symm
      (CategoryTheory.Functor.congr_map DerivedCategory.Qh
        (Functor.mapHomotopyCategoryFactors_inv_app_comp_mapHomotopyCategoryIdIso K))
  rw [reassoc_of% hmc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Iso.inv_hom_id_app_assoc]

/-- **The two identifications of `(𝟭 C).mapDerivedCategory` with the identity agree**:
`CategoryTheory.Functor.mapDerivedCategoryId`, lifted through `DerivedCategory.Q`, and
`CategoryTheory.Functor.mapDerivedCategoryIdIso`, lifted through `DerivedCategory.Qh`. -/
theorem Functor.mapDerivedCategoryId_hom_eq_mapDerivedCategoryIdIso :
    (Functor.mapDerivedCategoryId C).hom = Functor.mapDerivedCategoryIdIso.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  refine (cancel_epi ((𝟭 C).mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso C).hom.app K))).mp ?_
  have hnat : (𝟭 C).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
        Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj K) =
      Functor.mapDerivedCategoryIdIso.hom.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app K :=
    Functor.mapDerivedCategoryIdIso.hom.naturality _
  refine Eq.trans ?_ hnat.symm
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh, Functor.mapDerivedCategoryId_hom_app_Q]
  exact Functor.mapDerivedCategoryId_hom_app_Q_comp_quotientCompQhIso K

end

/-! ### The factorization -/

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (e : F ≅ 𝟭 C)

/-- The isomorphism `Functor.mapDerivedCategoryCongr e` induced on derived categories by
`e : F ≅ 𝟭 C` is `CategoryTheory.NatTrans.mapDerivedCategory e.hom`. -/
theorem Functor.mapDerivedCategoryCongr_hom :
    (Functor.mapDerivedCategoryCongr e).hom = NatTrans.mapDerivedCategory e.hom := by
  refine NatTrans.mapDerivedCategory_eq e.hom _ fun K ↦ ?_
  rw [Functor.mapDerivedCategoryCongr, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  rfl

/-- **The identification of `F.mapDerivedCategory` with the identity, on the image of
`DerivedCategory.Qh`.** Reading `e : F ≅ 𝟭 C` on derived categories and then identifying the
functor induced by `𝟭 C` with the identity is, at `DerivedCategory.Qh.obj M`, the factorization
of `F.mapDerivedCategory` over the homotopy category followed by the class of the degreewise
`e`. -/
theorem Functor.mapDerivedCategoryCongrId_hom_app_Qh
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    (Functor.mapDerivedCategoryCongr e).hom.app (DerivedCategory.Qh.obj M) ≫
        (Functor.mapDerivedCategoryId C).hom.app (DerivedCategory.Qh.obj M) =
      F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryToId F e).app M) := by
  rw [Functor.mapDerivedCategoryCongr_hom,
    Functor.mapDerivedCategoryId_hom_eq_mapDerivedCategoryIdIso,
    Functor.mapDerivedCategoryIdIso_hom_app_Qh, ← Category.assoc,
    ← NatTrans.mapDerivedCategory_factorsh_hom e.hom M, Category.assoc, ← Functor.map_comp]
  rfl

variable (LF : DerivedCategory C ⥤ DerivedCategory C)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- **A left derived functor of an exact endofunctor isomorphic to the identity is the
identity.** `LF` is identified with `F.mapDerivedCategory` by uniqueness of the left derived
functor, and that with `𝟭` by reading `e` on derived categories. -/
def leftDerivedToIdIso : LF ≅ 𝟭 (DerivedCategory C) :=
  haveI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  Functor.leftDerivedUnique F.mapDerivedCategory LF ε F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ≪≫
    Functor.mapDerivedCategoryCongr e ≪≫ Functor.mapDerivedCategoryId C

/-- **The factorization of `leftDerivedToIdIso` against the comparison of the left derived
functor.** On the image of `DerivedCategory.Qh` the identification `LF ≅ 𝟭` is the comparison of
`LF` followed by the class of the degreewise `e`. -/
theorem leftDerivedToIdIso_hom_app_Qh (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    ε.app M ≫ DerivedCategory.Qh.map ((mapHomotopyCategoryToId F e).app M) =
      (leftDerivedToIdIso F e LF ε).hom.app (DerivedCategory.Qh.obj M) := by
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  have h1 : (Functor.leftDerivedUnique F.mapDerivedCategory LF ε
            F.mapDerivedCategoryFactorsh.hom
            (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).hom.app
          (DerivedCategory.Qh.obj M) ≫
        F.mapDerivedCategoryFactorsh.hom.app M = ε.app M :=
    Eq.trans (Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
      F.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (𝟙 _) M) (Category.comp_id _)
  rw [leftDerivedToIdIso]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryCongrId_hom_app_Qh F e M, ← Category.assoc, h1]

end

end CategoryTheory

end
