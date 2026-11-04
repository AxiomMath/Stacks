module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTwist

/-!
# Naturality of `Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ, (j_! K)|_{X̄_k̄})` in the sheaf

Let `k` be a field, `X` a `k`-scheme with a compactification `j : X ⟶ X̄`, `k̄` an extension of
`k` and `Y = X̄_k̄`. The identification `Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ_Y, (j_! K)|_Y)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt`, on which the canonical Frobenius is
`b ↦ θ(b ∘ τ)` (`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_canonical_apply`), is
natural in the sheaf `K`: a morphism `g : K ⟶ K'` acts on `Ext` by composition with
`(j_! g)|_Y`. Each of its three factors is natural: placing in degree zero commutes with `j_!` and
the restriction to `Y`, Leray for `Γ(Y, -) = Γ(Spec k̄, -) ∘ π_*` is a natural isomorphism of
derived functors, and global sections are corepresented by `Λ_Y`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusSingleIso_hom_naturality`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- Two naturality squares compose. -/
private theorem map_mapIso_trans_square {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (U : 𝒞 ⥤ 𝒟)
    {c c' d d' : 𝒞} {w w' : 𝒟} (e : c ≅ d) (e' : c' ≅ d') (r : U.obj d ≅ w) (r' : U.obj d' ≅ w')
    {a : c ⟶ c'} {b : d ⟶ d'} {t : w ⟶ w'} (h₁ : a ≫ e'.hom = e.hom ≫ b)
    (h₂ : U.map b ≫ r'.hom = r.hom ≫ t) :
    U.map a ≫ (U.mapIso e' ≪≫ r').hom = (U.mapIso e ≪≫ r).hom ≫ t := by
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, ← U.map_comp_assoc, h₁,
    U.map_comp_assoc, h₂, Category.assoc]

/-- Placing in degree zero commutes with two functors, naturally: the identification
`I(E(K[0])) ≅ (I(E K))[0]` is natural in `K`. -/
private theorem mapCochainComplexPlusSinglePlusIso_trans_naturality {A' A B : Type*} [Category* A']
    [Category* A] [Category* B] [Abelian A'] [Abelian A] [Abelian B] (E : A' ⥤ A) (I : A ⥤ B)
    [E.Additive] [I.Additive] {K K' : A'} (g : K ⟶ K') :
    I.mapCochainComplexPlus.map (E.mapCochainComplexPlus.map
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
        (I.mapCochainComplexPlus.mapIso (mapCochainComplexPlusSinglePlusIso E K') ≪≫
          mapCochainComplexPlusSinglePlusIso I (E.obj K')).hom =
      (I.mapCochainComplexPlus.mapIso (mapCochainComplexPlusSinglePlusIso E K) ≪≫
          mapCochainComplexPlusSinglePlusIso I (E.obj K)).hom ≫
        (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map (I.map (E.map g)) := by
  have n1 := (singlePlusFunctorCompMapCochainComplexPlusIso E).hom.naturality g
  have n2 := (singlePlusFunctorCompMapCochainComplexPlusIso I).hom.naturality (E.map g)
  dsimp only [Functor.comp_map, singlePlusFunctorCompMapCochainComplexPlusIso,
    NatIso.ofComponents_hom_app] at n1 n2
  exact map_mapIso_trans_square _ _ _ _ _ n1 n2

/-- A square of complexes, sent through `Q`, two functors `F₁, F₂`, an identification
`G ≅ F₁ ⋙ F₂` and a functor `H`, abstract in the categories. -/
private theorem map_mapIso_square {𝒜 ℬ ℬ' 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* ℬ'] [Category* 𝒞] [Category* 𝒟] (Q : 𝒜 ⥤ ℬ) (F₁ : ℬ ⥤ ℬ') (F₂ : ℬ' ⥤ 𝒞)
    (G : ℬ ⥤ 𝒞) (α : G ≅ F₁ ⋙ F₂) (H : 𝒞 ⥤ 𝒟) {a a' b b' : 𝒜} (e : a ≅ b) (e' : a' ≅ b')
    {x : a ⟶ a'} {s : b ⟶ b'} (h : x ≫ e'.hom = e.hom ≫ s) :
    H.map (F₂.map (F₁.map (Q.map x))) ≫
        (H.mapIso (F₂.mapIso (F₁.mapIso (Q.mapIso e')) ≪≫ α.symm.app (Q.obj b'))).hom =
      (H.mapIso (F₂.mapIso (F₁.mapIso (Q.mapIso e)) ≪≫ α.symm.app (Q.obj b))).hom ≫
        H.map (G.map (Q.map s)) := by
  have hα := α.inv.naturality (Q.map s)
  dsimp only [Functor.comp_map] at hα
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [← H.map_comp, ← H.map_comp]
  congr 1
  rw [Category.assoc, ← hα, ← F₂.map_comp_assoc, ← F₂.map_comp_assoc, ← F₁.map_comp,
    ← F₁.map_comp, ← Q.map_comp, ← Q.map_comp, h]

/-- `Hⁱ(Y, M) ≅ Ext^i(Λ, M)` is natural in the sheaf. -/
theorem etaleModuleRightDerivedPlusIsoExt_hom_naturality_of_commRing {Y : Scheme.{u}}
    {M M' : EtaleModules.{u, 0} Λ Y} (h : M ⟶ M') (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).map h) ≫
        (etaleModuleRightDerivedPlusIsoExt Λ Y M' i).hom =
      (etaleModuleRightDerivedPlusIsoExt Λ Y M i).hom ≫
        (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          Y.smallEtaleTopology) i).map h := by
  have n4 := (Stacks.DerivedIndexing.rightDerivedIso
    (etaleModuleGlobalSections.{u, 0} Λ Y) i).inv.naturality h
  have n5 := (Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived Λ
    Y.smallEtaleTopology i).inv.naturality h
  dsimp only [Functor.comp_map] at n5
  dsimp only [etaleModuleRightDerivedPlusIsoExt, Iso.trans, Iso.symm, Functor.mapIso, Iso.app]
  rw [← Functor.map_comp_assoc, n4, Functor.map_comp_assoc, n5, Category.assoc]

/-- The identification `(j_! K[0])|_{X̄_k̄} ≅ ((j_! K)|_{X̄_k̄})[0]` of
`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIso` is natural in the sheaf. -/
theorem compactSupportSingleRestriction_naturality (j : CompactificationOf (Over.mk f))
    {K K' : EtaleModules.{u, 0} Λ X} (g : K ⟶ K') :
    (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
        ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
            (mapCochainComplexPlusSinglePlusIso
              (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) K') ≪≫
          mapCochainComplexPlusSinglePlusIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K')).hom =
      ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
            (mapCochainComplexPlusSinglePlusIso
              (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) K) ≪≫
          mapCochainComplexPlusSinglePlusIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)).hom ≫
        (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)) :=
  mapCochainComplexPlusSinglePlusIso_trans_naturality _ _ g

/-- `Hⁱ_c(X_k̄, K) ≅ Hⁱ(X̄_k̄, (j_! K)|_{X̄_k̄})` is natural in the sheaf. -/
theorem compactSupportFrobeniusSingleIso_hom_naturality (j : CompactificationOf (Over.mk f))
    {K K' : EtaleModules.{u, 0} Λ X} (g : K ⟶ K') (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
        (compactSupportFrobeniusSingleIso Λ f j kbar K' i).hom =
      (compactSupportFrobeniusSingleIso Λ f j kbar K i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
            (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedPlus i).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)) :=
  map_mapIso_square DerivedCategory.Plus.Q
    (etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus
    (rightDerivedFunctorPlusCompIsoOfIso
      (etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
      (etaleModuleGlobalSectionsDirectImageIso
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ))
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i) _ _
    (compactSupportSingleRestriction_naturality Λ f kbar j g)

/-- **`Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ, (j_! K)|_{X̄_k̄})` is natural in the sheaf**: a morphism
`g : K ⟶ K'` acts on the `Ext` side by composition with `(j_! g)|_{X̄_k̄}`. -/
theorem compactSupportFrobeniusSingleIsoExt_hom_naturality (j : CompactificationOf (Over.mk f))
    {K K' : EtaleModules.{u, 0} Λ X} (g : K ⟶ K') (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g))) ≫
        (compactSupportFrobeniusSingleIsoExt Λ f j kbar K' i).hom =
      (compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).hom ≫
        (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) i).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)) :=
  map_mapIso_trans_square _ _ _ _ _
    (compactSupportFrobeniusSingleIso_hom_naturality Λ f kbar j g i)
    (etaleModuleRightDerivedPlusIsoExt_hom_naturality_of_commRing Λ _ i)

end Stacks.EtaleCohomology

end
