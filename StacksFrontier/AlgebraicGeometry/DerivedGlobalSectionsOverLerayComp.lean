module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyLevelsPseudoCoherent

/-!
# The linear Leray identification is compatible with composition

For a commutative square `i ≫ f = f' ≫ Spec φ` of schemes,
`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardRestrictScalarsIso` identifies
`RΓ_A(X, Ri_* M)` with `φ^* RΓ_{A'}(X', M)`. This file proves that these identifications compose:
for `X'' --j--> X' --i--> X` lying over `Spec A'' ⟶ Spec A' ⟶ Spec A`, the identification for
`j ≫ i` is the identification for `i` at `Rj_* M`, followed by `φ^*` of the identification for
`j`, read through a composition isomorphism `Rj_* ⋙ Ri_* ≅ R(j ≫ i)_*` and the comparison
`ψ^* ⋙ φ^* ≅ (ψ ∘ φ)^*` of restrictions of scalars.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardRestrictScalarsIso_comp` — the
  compatibility, for every model and every choice of the derived pushforwards and of the two
  composition isomorphisms, subject to the equations relating those isomorphisms to the units.
* `AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp` — the
  same for the derived pushforward of ringed spaces with
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` and
  `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp`, where those equations are
  discharged.

## Implementation notes

The proof is by the universal property of `R(j ≫ i)_* ⋙ RΓ_A(X, -)` as a right derived
functor: both sides agree after composition with its unit, which reduces to an identity of
underived comparisons whose components are identity maps.

The second statement is at the standard model, scoped to the declaration: the derived
pushforward of ringed spaces and `derivedRestrictScalarsComp` are defined only there.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ w₄ w₅ w₆ u

namespace AlgebraicGeometry

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {X X' X'' : Scheme.{u}} (j : X'' ⟶ X') (i : X' ⟶ X)
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (f'' : X'' ⟶ Spec (.of A''))
  (φ : A →+* A') (ψ : A' →+* A'') (χ : A →+* A'')

section Generic

variable [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} X'.Modules]
  [HasDerivedCategory.{w₃} X''.Modules]
  [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] [HasDerivedCategory.{w₅} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w₆} (ModuleCat.{u} A'')]
  (Ri : DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules)
  (αi : (Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
  (Rj : DerivedCategory X''.Modules ⥤ DerivedCategory X'.Modules)
  (αj : (Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
  (Rji : DerivedCategory X''.Modules ⥤ DerivedCategory X.Modules)
  (αji : (Scheme.Modules.pushforward (j ≫ i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rji)

/-- `derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac`, at an object. -/
theorem derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac_app
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))]
    (hi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (K : HomotopyCategory X'.Modules (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsOverPushforwardUnit i f Ri αi).app K ≫
        (derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi hi).hom.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (pushforwardGlobalSectionsOverRestrictScalarsIso i f f' φ hi).hom
            (ComplexShape.up ℤ)).app K) ≫
        (derivedGlobalSectionsOverRestrictScalarsUnit f' φ).app K :=
  NatTrans.congr_app
    (derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac i f f' φ Ri αi hi) K

/-- `derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac_app`, with the units unfolded. -/
private theorem derivedGlobalSectionsOverUnit_comp_pushforwardRestrictScalarsIso_hom_app
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))]
    (hi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (K : HomotopyCategory X'.Modules (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsOverUnit f).app
        (((Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (derivedGlobalSectionsOver f).map (αi.app K) ≫
      (derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi hi).hom.app
        (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Scheme.Modules.pushforward i ⋙ globalSectionsOver f))
          (ComplexShape.up ℤ)).hom.app K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (pushforwardGlobalSectionsOverRestrictScalarsIso i f f' φ hi).hom
            (ComplexShape.up ℤ)).app K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (globalSectionsOver f' ⋙ ModuleCat.restrictScalars φ))
            (ComplexShape.up ℤ)).inv.app K) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app
          (((globalSectionsOver f').mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map
          ((derivedGlobalSectionsOverUnit f').app K) := by
  have h := derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac_app i f f' φ Ri αi hi K
  simp only [derivedGlobalSectionsOverPushforwardUnit,
    derivedGlobalSectionsOverRestrictScalarsUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Functor.comp_obj] at h
  rw [← h, ← DerivedCategory.Qh.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The linear Leray identification is compatible with composition.** For
`X'' --j--> X' --i--> X` over `A'' ← A' ← A` with `χ = ψ ∘ φ`, right derived functors `Ri_*`,
`Rj_*`, `R(j ≫ i)_*` of the direct images, an isomorphism `c : Rj_* ⋙ Ri_* ≅ R(j ≫ i)_*`
compatible with the units (`hc`) and an isomorphism `r : ψ^* ⋙ φ^* ≅ χ^*` of derived
restrictions of scalars compatible with `ModuleCat.restrictScalarsComp'` (`hr`), the identification
for `j ≫ i` is `c⁻¹`, then the identification for `i`, then `φ^*` of the identification for `j`,
then `r`. -/
theorem derivedGlobalSectionsOverPushforwardRestrictScalarsIso_comp
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))]
    [Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso X''.Modules (ComplexShape.up ℤ))]
    [Rji.IsRightDerivedFunctor αji (HomotopyCategory.quasiIso X''.Modules (ComplexShape.up ℤ))]
    (c : Rj ⋙ Ri ≅ Rji)
    (hc : ∀ K : HomotopyCategory X''.Modules (ComplexShape.up ℤ),
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Scheme.Modules.pushforwardComp j i) (ComplexShape.up ℤ)).inv.app K) ≫
        αi.app (((Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          Ri.map (αj.app K) ≫ c.hom.app (DerivedCategory.Qh.obj K) = αji.app K)
    (w : χ = ψ.comp φ)
    (r : (ModuleCat.restrictScalars ψ).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars φ).mapDerivedCategory ≅
      (ModuleCat.restrictScalars χ).mapDerivedCategory)
    (hr : ∀ L : HomotopyCategory (ModuleCat.{u} A'') (ComplexShape.up ℤ),
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app
          (((ModuleCat.restrictScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map
          ((ModuleCat.restrictScalars ψ).mapDerivedCategoryFactorsh.inv.app L) ≫
          r.hom.app (DerivedCategory.Qh.obj L) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (ModuleCat.restrictScalarsComp' φ ψ χ w).symm (ComplexShape.up ℤ)).hom.app L) ≫
        (ModuleCat.restrictScalars χ).mapDerivedCategoryFactorsh.inv.app L)
    (hi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (hj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (hji : (j ≫ i) ≫ f = f'' ≫ Spec.map (CommRingCat.ofHom χ)) :
    (derivedGlobalSectionsOverPushforwardRestrictScalarsIso (j ≫ i) f f'' χ Rji αji hji).hom =
      Functor.whiskerRight c.inv (derivedGlobalSectionsOver f) ≫
        Functor.whiskerLeft Rj
          (derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi hi).hom ≫
        Functor.whiskerRight
          (derivedGlobalSectionsOverPushforwardRestrictScalarsIso j f' f'' ψ Rj αj hj).hom
          (ModuleCat.restrictScalars φ).mapDerivedCategory ≫
        Functor.whiskerLeft (derivedGlobalSectionsOver f'') r.hom := by
  subst w
  have := isRightDerivedFunctor_derivedGlobalSectionsOverPushforward (j ≫ i) f Rji αji
  refine Functor.rightDerived_ext (Rji ⋙ derivedGlobalSectionsOver f)
    (derivedGlobalSectionsOverPushforwardUnit (j ≫ i) f Rji αji)
    (HomotopyCategory.quasiIso X''.Modules (ComplexShape.up ℤ)) _ _ _ ?_
  rw [derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hni :=
    (derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi hi).hom.naturality
      (αj.app K)
  have hnr := r.hom.naturality ((derivedGlobalSectionsOverUnit f'').app K)
  simp only [derivedGlobalSectionsOverPushforwardUnit, derivedGlobalSectionsOverRestrictScalarsUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Functor.comp_map, Functor.comp_obj] at hni hnr ⊢
  rw [← hc K]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (derivedGlobalSectionsOver f) (c.hom.app _) (c.inv.app _),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat := (derivedGlobalSectionsOverUnit f).naturality
    ((Functor.mapHomotopyCategoryCompIso (Scheme.Modules.pushforwardComp j i)
      (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat, reassoc_of% hni]
  rw [reassoc_of% derivedGlobalSectionsOverUnit_comp_pushforwardRestrictScalarsIso_hom_app
    i f f' φ Ri αi hi
      (((Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)]
  have hfj' := derivedGlobalSectionsOverUnit_comp_pushforwardRestrictScalarsIso_hom_app
    j f' f'' ψ Rj αj hj K
  rw [← Functor.map_comp_assoc (ModuleCat.restrictScalars φ).mapDerivedCategory,
    ← Functor.map_comp_assoc (ModuleCat.restrictScalars φ).mapDerivedCategory,
    Category.assoc ((derivedGlobalSectionsOverUnit f').app _), hfj']
  simp only [Functor.map_comp, Category.assoc]
  rw [hnr]
  have hnatφ : ∀ {L L' : HomotopyCategory (ModuleCat.{u} A') (ComplexShape.up ℤ)} (x : L ⟶ L'),
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app L ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map (DerivedCategory.Qh.map x) =
      DerivedCategory.Qh.map (((ModuleCat.restrictScalars φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).map x) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app L' := fun x =>
    ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.naturality x).symm
  rw [reassoc_of% (hnatφ _), reassoc_of% (hnatφ _), reassoc_of% (hnatφ _)]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (hr _)]
  simp only [← Functor.map_comp_assoc]
  congr 2

end Generic

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` read through the homotopy
category: on `Qh(L)` it is induced by `ModuleCat.restrictScalarsComp'`. -/
theorem _root_.StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factorsh
    (w : χ = ψ.comp φ) (L : HomotopyCategory (ModuleCat.{u} A'') (ComplexShape.up ℤ)) :
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app
        (((ModuleCat.restrictScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((ModuleCat.restrictScalars ψ).mapDerivedCategoryFactorsh.inv.app L) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ ψ χ w).hom.app
          (DerivedCategory.Qh.obj L) =
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (ModuleCat.restrictScalarsComp' φ ψ χ w).symm (ComplexShape.up ℤ)).hom.app L) ≫
      (ModuleCat.restrictScalars χ).mapDerivedCategoryFactorsh.inv.app L := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  let Fg := ModuleCat.restrictScalars.{u} ψ
  let Ff := ModuleCat.restrictScalars.{u} φ
  let Fh := ModuleCat.restrictScalars.{u} χ
  let c := (NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp'.{u} φ ψ χ w).inv
    (ComplexShape.up ℤ)).app K
  have hn :=
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ ψ χ w).hom.naturality
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A'')).hom.app K)
  have hFg := Fg.mapDerivedCategoryFactorsh_inv_app_comp_map_quotientCompQhIso_hom K
  have hFf := Ff.mapDerivedCategoryFactorsh_inv_app_comp_map_quotientCompQhIso_hom
    ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hD := StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factors.{u, u} φ ψ χ w K
  have hU := Fh.quotientCompQhIso_inv_app_comp_Qh_map_comp_mapDerivedCategory_map c
  change Ff.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj
          ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      Ff.mapDerivedCategory.map
        (Fg.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ ψ χ w).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map c) ≫
        Fh.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K)
  refine (Iso.cancel_iso_inv_left ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
    ((Ff.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) _ _).1
    ((cancel_mono (Fh.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A'')).hom.app K))).1 ?_)
  refine Eq.trans ?_ (((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans hU).symm
  have hB := (Ff.mapDerivedCategory.map_comp _ _).symm.trans
    ((congrArg Ff.mapDerivedCategory.map hFg).trans (Ff.mapDerivedCategory.map_comp _ _))
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).trans ?_
  refine (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hn.symm).trans
    ((reassoc_of% hB) _))).trans ((reassoc_of% hFf) _))).trans ?_
  refine ((Iso.inv_hom_id_app_assoc
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) _ _).trans (hD.trans ?_))
  congr 2

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Compatibility of the linear Leray identification with composition, for the derived
pushforward of ringed spaces.** For `X'' --j--> X' --i--> X` over `A'' ← A' ← A`, with
`j ≫ i = k` and `χ = ψ ∘ φ`, the identification for `k` is the composite of the identifications
for `j` and for `i`, read through the composition isomorphism
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` of derived
pushforwards and `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` of restrictions of
scalars. All derived categories are at the standard model, the only one at which the derived
pushforward of ringed spaces and `derivedRestrictScalarsComp` are defined.

The composite is stated as `j ≫ i`; for a morphism `k` known to equal it, rewrite along that
equation first. -/
theorem derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp (w : χ = ψ.comp φ)
    (hi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (hj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (hk' : (j ≫ i) ≫ f = f'' ≫ Spec.map (CommRingCat.ofHom χ)) (M : DerivedCategory X''.Modules) :
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (j ≫ i) f f'' χ hk').hom.app M =
      (derivedGlobalSectionsOver f).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
              j.toLRSHom.toShHom i.toLRSHom.toShHom).inv.app M) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso i f f' φ hi).hom.app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            j.toLRSHom.toShHom).obj M) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map
          ((derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso j f' f'' ψ hj).hom.app
            M) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ ψ χ w).hom.app
          ((derivedGlobalSectionsOver f'').obj M) := by
  let Ri : DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom
  let αi : (Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit i.toLRSHom.toShHom
  let Rj : DerivedCategory X''.Modules ⥤ DerivedCategory X'.Modules :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward j.toLRSHom.toShHom
  let αj : (Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit j.toLRSHom.toShHom
  let Rji : DerivedCategory X''.Modules ⥤ DerivedCategory X.Modules :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward (j ≫ i).toLRSHom.toShHom
  let αji : (Scheme.Modules.pushforward (j ≫ i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rji :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
      (j ≫ i).toLRSHom.toShHom
  have : Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) :=
    open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
    isRightDerivedFunctor_of_isIso_app_isKInjective
      _ (Scheme.Modules.exists_quasiIso_isKInjective X') DerivedCategory.Qh _ _ fun I hI =>
        isIso_derivedPushforwardUnit_app_of_isKInjective i.toLRSHom.toShHom I hI
  have : Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso X''.Modules (ComplexShape.up ℤ)) :=
    open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
    isRightDerivedFunctor_of_isIso_app_isKInjective
      _ (Scheme.Modules.exists_quasiIso_isKInjective X'') DerivedCategory.Qh _ _ fun I hI =>
        isIso_derivedPushforwardUnit_app_of_isKInjective j.toLRSHom.toShHom I hI
  have : Rji.IsRightDerivedFunctor αji
      (HomotopyCategory.quasiIso X''.Modules (ComplexShape.up ℤ)) :=
    open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
    isRightDerivedFunctor_of_isIso_app_isKInjective
      _ (Scheme.Modules.exists_quasiIso_isKInjective X'') DerivedCategory.Qh _ _ fun I hI =>
        isIso_derivedPushforwardUnit_app_of_isKInjective (j ≫ i).toLRSHom.toShHom I hI
  have hc : ∀ K : HomotopyCategory X''.Modules (ComplexShape.up ℤ),
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Scheme.Modules.pushforwardComp j i) (ComplexShape.up ℤ)).inv.app K) ≫
        αi.app (((Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          Ri.map (αj.app K) ≫
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
              j.toLRSHom.toShHom i.toLRSHom.toShHom).hom.app (DerivedCategory.Qh.obj K) =
        αji.app K := fun K => by
    have h : (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Scheme.Modules.pushforwardComp j i) (ComplexShape.up ℤ)).inv.app K) ≫
        αi.app (((Scheme.Modules.pushforward j).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          Ri.map (αj.app K)) ≫
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
              j.toLRSHom.toShHom i.toLRSHom.toShHom).hom.app (DerivedCategory.Qh.obj K) =
        αji.app K :=
      open Stacks.Cohomology.DerivedPushforwardComposition in
      derivedPushforwardCompUnit_comp_derivedPushforwardCompIso
        j.toLRSHom.toShHom i.toLRSHom.toShHom K
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm.trans h
  have h := NatTrans.congr_app (derivedGlobalSectionsOverPushforwardRestrictScalarsIso_comp j i f f'
    f'' φ ψ χ Ri αi Rj αj Rji αji
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
      j.toLRSHom.toShHom i.toLRSHom.toShHom) hc w
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ ψ χ w)
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factorsh φ ψ χ w) hi hj hk') M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  exact h

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The linear Leray identification for the derived pushforward of ringed spaces depends on the
morphism only through its value: along an equation `k = k'` it changes by the transport of the
derived pushforward. -/
theorem derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_congr {k k' : X' ⟶ X}
    (hk : k = k') (h : k ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (h' : k' ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) (M : DerivedCategory X'.Modules) :
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso k' f f' φ h').hom.app M =
      (derivedGlobalSectionsOver f).map (eqToHom (by rw [hk])) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso k f f' φ h).hom.app M := by
  subst hk
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ _)
    (((derivedGlobalSectionsOver f).map_id _).symm.trans (congrArg _ (eqToHom_refl _ _).symm)))

end AlgebraicGeometry
