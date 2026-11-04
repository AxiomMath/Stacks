module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QA
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Resolution07Q9

/-!
# The bounds of [Stacks, Tag 07QA] for the module pullback

[Stacks, Tag 07QA] bounds the kernel and the cokernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_cris^*ℱ)`

by `q^{i + 1}`, where `f_cris^*` is the pullback of `𝒪_{X/S}`-modules.  This file builds that map
and carries the abstract bounds of `SmallSite/AlphaPCoverTriangle.lean` to it, for an arbitrary
annihilation of the cone of the first arrow `...SmallSite.moduleComparison07Q9` of the triangle of
[Stacks, Tag 07Q9].

## Main definitions

* `crisModuleCohomologyMap` — **`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_cris^*ℱ)`** for a
  sheaf of `𝒪_{X/S}`-modules: the pullback `...SmallSite.crisCohomologyMap` of the underlying
  abelian sheaf followed by `H^i` of the comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ`.
* `crisCohomologyIsoPushforwardHypercohomology` — `H^i(Cris(X'/S), 𝒢) ≅
  H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}𝒢)` for every abelian sheaf `𝒢` on `Cris(X'/S)`.

## Main results

* `crisModuleCohomologyMap_comp_crisCohomologyIsoPushforwardHypercohomology` — `f^*` is
  `H^i(X_Zar, -)` of `...SmallSite.moduleComparison07Q9`, conjugated by the Leray isomorphisms.
* `pow_smul_eq_zero_of_crisModuleCohomologyMap_eq_zero` — the kernel of `f^*` is annihilated by
  `q^{i + 1}` as soon as the cohomology sheaves of the cone of `moduleComparison07Q9` are
  annihilated by `q`.
* `exists_crisModuleCohomologyMap_eq_pow_smul` — the cokernel of `f^*` is annihilated by
  `q^{i + 1}` as soon as moreover `ℋ^0` of `moduleComparison07Q9` is a monomorphism.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The bounds on Zariski hypercohomology for an arbitrary comparison map -/

/-- A distinguished triangle in `D(Ab(X_Zar))` on `α`, with the cohomology sheaves of its third
term annihilated by `q`. -/
private theorem exists_distTriang_mapTriangle_of_annihilation (S' : GlobalCrystallineSituation.{u})
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})] (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})}
    [A.IsGE 0] [B.IsGE 0] (α : A ⟶ B) (hann : Annihilation07Q9 S' q α) :
    ∃ (E : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
      (v : B ⟶ E) (wE : E ⟶ A⟦(1 : ℤ)⟧),
      (DerivedCategory.Plus.ι.mapTriangle.obj (Triangle.mk α v wE)) ∈
        distTriang (DerivedCategory (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})) ∧
      (DerivedCategory.Plus.ι.mapTriangle.obj (Triangle.mk α v wE)).obj₁.IsGE 0 ∧
      (DerivedCategory.Plus.ι.mapTriangle.obj (Triangle.mk α v wE)).obj₂.IsGE 0 ∧
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj
          (DerivedCategory.Plus.ι.obj E)) = 0 := by
  obtain ⟨E, v, wE, hT⟩ := distinguished_cocone_triangle α
  exact ⟨E, v, wE, DerivedCategory.Plus.ι.map_distinguished _ hT,
    inferInstanceAs ((DerivedCategory.Plus.ι.obj A).IsGE 0),
    inferInstanceAs ((DerivedCategory.Plus.ι.obj B).IsGE 0),
    smul_id_homologyFunctor_ι_obj₃_eq_zero S' q hann v wE hT⟩

section Hypercohomology

variable (S' : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The kernel bound of [Stacks, Tag 07QA] on Zariski hypercohomology, for any morphism.**  Let
`α : A ⟶ B` be a morphism of `D⁺(Ab(X_Zar))` between objects concentrated in degrees `≥ 0` the
cohomology sheaves of whose cones are annihilated by `q`.  Then `q^{i + 1}` annihilates the kernel
of `H^i(X_Zar, A) ⟶ H^i(X_Zar, B)`. -/
theorem pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_of_annihilation (q i : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})}
    [A.IsGE 0] [B.IsGE 0] (α : A ⟶ B) (hann : Annihilation07Q9 S' q α)
    (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj A))
    (hx : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
      ((derivedZariskiGlobalSectionsFunctor S').map α) x = 0) :
    ((q : ℤ) ^ (i + 1)) • x = 0 := by
  obtain ⟨E, v, wE, hT₀, _, _, hE⟩ := exists_distTriang_mapTriangle_of_annihilation S' q α hann
  set T := (DerivedCategory.Plus.ι
    (C := Sheaf (opensTopology S') AddCommGrpCat.{u + 1})).mapTriangle.obj
      (Triangle.mk α v wE)
  have : T.obj₃.IsGE (-1) := by
    have h := Stacks.Triangulated.isGE_obj₃_sub_one T hT₀ 0
    rwa [zero_sub] at h
  have : (T.invRotate).obj₁.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_shift T.obj₃ (-1) (-1) 0 (by omega)
  have hW : ∀ j : ℤ, j ≤ (i : ℤ) →
      ((q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj (T.invRotate).obj₁) = 0) :=
    fun j _ => Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
      (((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).shiftIso (-1) j (j - 1)
          (by omega)).app T.obj₃)
      (hE (j - 1))
  have hkey : (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' A (i : ℤ)) x ≫
      DerivedCategory.Plus.ι.map α = 0 := by
    rw [← derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality S' α (i : ℤ) x, hx]
    exact map_zero _
  have hg := pow_smul_eq_zero_of_kernel_07QA q i (T.invRotate)
    (inv_rot_of_distTriang T hT₀) hW (zariskiUnitShift S' (i : ℤ))
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' A (i : ℤ)) x) hkey
  apply (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' A (i : ℤ)).injective
  rwa [map_zsmul, map_zero]

/-- **The cokernel bound of [Stacks, Tag 07QA] on Zariski hypercohomology, for any morphism.**
Let `α : A ⟶ B` be a morphism of `D⁺(Ab(X_Zar))` between objects concentrated in degrees `≥ 0`
the cohomology sheaves of whose cones are annihilated by `q`, and such that `ℋ^0(α)` is a
monomorphism.  Then `q^{i + 1}` times any class in `H^i(X_Zar, B)` comes from `H^i(X_Zar, A)`. -/
theorem exists_hypercohomologyMap_eq_pow_smul_of_annihilation (q i : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})}
    [A.IsGE 0] [B.IsGE 0] (α : A ⟶ B) (hann : Annihilation07Q9 S' q α)
    (hmono : Mono ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map α)))
    (y : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj B)) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
        ((derivedZariskiGlobalSectionsFunctor S').map α) x := by
  obtain ⟨E, v, wE, hT₀, _, _, hE⟩ := exists_distTriang_mapTriangle_of_annihilation S' q α hann
  set T := (DerivedCategory.Plus.ι
    (C := Sheaf (opensTopology S') AddCommGrpCat.{u + 1})).mapTriangle.obj
      (Triangle.mk α v wE)
  obtain ⟨h, hh⟩ := exists_comp_mor₁_eq_pow_smul_07QA_of_mono q i T hT₀ hmono (fun j _ => hE j)
    (zariskiUnitShift S' (i : ℤ)) ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' B
      (i : ℤ)) y)
  let h' : zariskiUnitShift S' (i : ℤ) ⟶ DerivedCategory.Plus.ι.obj A := h
  refine ⟨(derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' A (i : ℤ)).symm h', ?_⟩
  apply (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S' B (i : ℤ)).injective
  rwa [map_zsmul, derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality,
    AddEquiv.apply_symm_apply]

end Hypercohomology

/-! ### `H^i(Cris(X'/S), 𝒢)` as Zariski hypercohomology on `X` -/

section Transport

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **`H^i(Cris(X'/S), 𝒢) ≅ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}𝒢)`** for an abelian sheaf `𝒢` on
`Cris(X'/S)`: the Leray isomorphism for `u_{X'/S}` followed by the one for `f_{Zar}`.  At
`𝒢 = f_cris^{-1}ℱ` this is `...SmallSite.crisCohomologyIsoZariskiHypercohomologyPushforward`. -/
def crisCohomologyIsoPushforwardHypercohomology
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor S i).obj G ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((derivedZariskiGlobalSectionsFunctor S').obj
          ((derivedZariskiPushforwardFunctor S S' fX).obj
            ((derivedZariskiDirectImage S).obj G))) :=
  crisCohomologyIsoZariskiHypercohomology S G i ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      ((derivedZariskiGlobalSectionsIsoPushforward S S' fX).app
        ((derivedZariskiDirectImageFunctor S).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj G)))

/-- `crisCohomologyIsoZariskiHypercohomology` is natural in the sheaf. -/
theorem crisCohomologyIsoZariskiHypercohomology_hom_naturality
    {G G' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (g : G ⟶ G') (i : ℕ) :
    (cohomologyFunctor S i).map g ≫ (crisCohomologyIsoZariskiHypercohomology S G' i).hom =
      (crisCohomologyIsoZariskiHypercohomology S G i).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
          ((derivedZariskiGlobalSectionsFunctor S).map ((derivedZariskiDirectImage S).map g)) := by
  have h1 := (homologyDerivedGlobalSectionsIso S i).inv.naturality g
  have h2 : (derivedGlobalSectionsFunctor S).map
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).map
          g) ≫
      (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
          G') =
      (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
          G) ≫
        (derivedZariskiGlobalSectionsFunctor S).map ((derivedZariskiDirectImage S).map g) :=
    (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.naturality _
  simp only [crisCohomologyIsoZariskiHypercohomology, homologyDerivedGlobalSectionsIsoObj,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% h1]
  congr 1
  simp only [Functor.comp_map, derivedGlobalSections]
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map h2).trans
      (Functor.map_comp _ _ _))

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})] in
/-- `crisCohomologyIsoPushforwardHypercohomology` is natural in the sheaf. -/
theorem crisCohomologyIsoPushforwardHypercohomology_hom_naturality
    {G G' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (g : G ⟶ G') (i : ℕ) :
    (cohomologyFunctor S i).map g ≫
        (crisCohomologyIsoPushforwardHypercohomology S S' fX G' i).hom =
      (crisCohomologyIsoPushforwardHypercohomology S S' fX G i).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
          ((derivedZariskiGlobalSectionsFunctor S').map
            ((derivedZariskiPushforwardFunctor S S' fX).map
              ((derivedZariskiDirectImage S).map g))) := by
  have h2 : (derivedZariskiGlobalSectionsFunctor S).map ((derivedZariskiDirectImage S).map g) ≫
      (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom.app
        ((derivedZariskiDirectImage S).obj G') =
      (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom.app
        ((derivedZariskiDirectImage S).obj G) ≫
        (derivedZariskiGlobalSectionsFunctor S').map
          ((derivedZariskiPushforwardFunctor S S' fX).map
            ((derivedZariskiDirectImage S).map g)) :=
    (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom.naturality _
  simp only [crisCohomologyIsoPushforwardHypercohomology, Iso.trans_hom]
  rw [← Category.assoc, crisCohomologyIsoZariskiHypercohomology_hom_naturality, Category.assoc,
    Category.assoc]
  congr 1
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map h2).trans
      (Functor.map_comp _ _ _))

include hf

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})] in
/-- At `𝒢 = f_cris^{-1}ℱ`, `crisCohomologyIsoPushforwardHypercohomology` is
`...SmallSite.crisCohomologyIsoZariskiHypercohomologyPushforward`. -/
theorem crisCohomologyIsoZariskiHypercohomologyPushforward_eq
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    crisCohomologyIsoZariskiHypercohomologyPushforward S S' fS fX hf F i =
      crisCohomologyIsoPushforwardHypercohomology S S' fX (crisPullback S S' fS fX hf F) i :=
  rfl

/-- **`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_cris^*ℱ)`** for a sheaf `ℱ` of
`𝒪_{X/S}`-modules, the map of [Stacks, Tag 07QA]: the pullback
`...SmallSite.crisCohomologyMap` of the underlying abelian sheaf, followed by `H^i` of the
comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ` of the abelian inverse image with the module pullback. -/
def crisModuleCohomologyMap (F : ModuleSheaf S') (i : ℕ) :
    (cohomologyFunctor S' i).obj ((toAbelianSheaf S').obj F) ⟶
      (cohomologyFunctor S i).obj
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) :=
  crisCohomologyMap S S' fS fX hf ((toAbelianSheaf S').obj F) i ≫
    (cohomologyFunctor S i).map (crisModuleComparison S S' fS fX hf F)

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})] in
/-- **`f^*` on crystalline cohomology is `H^i` of `RΓ(Cris(X/S), ℱ) ⟶ RΓ(Cris(X'/S), f_cris^*ℱ)`**,
the map `...SmallSite.derivedModulePullbackMap`, read through the identifications
`...SmallSite.homologyDerivedGlobalSectionsIsoObj` of the graded cohomology with the cohomology of
`RΓ`. -/
theorem crisModuleCohomologyMap_eq_derivedModulePullbackMap (F : ModuleSheaf S') (i : ℕ) :
    crisModuleCohomologyMap S S' fS fX hf F i =
      (homologyDerivedGlobalSectionsIsoObj S' ((toAbelianSheaf S').obj F) i).inv ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
          (derivedModulePullbackMap S S' fS fX hf F) ≫
        (homologyDerivedGlobalSectionsIsoObj S
          ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) i).hom := by
  have h := (homologyDerivedGlobalSectionsIso S i).hom.naturality
    (crisModuleComparison S S' fS fX hf F)
  simp only [Functor.comp_map] at h
  rw [crisModuleCohomologyMap, crisCohomologyMap, derivedModulePullbackMap, Functor.map_comp]
  simp only [homologyDerivedGlobalSectionsIsoObj, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← h]

/-- **`f^*` on crystalline cohomology is `H^i(X_Zar, -)` of the comparison map of
[Stacks, Tag 07Q9]**, conjugated by the Leray isomorphisms. -/
theorem crisModuleCohomologyMap_comp_crisCohomologyIsoPushforwardHypercohomology
    (F : ModuleSheaf S') (i : ℕ) :
    crisModuleCohomologyMap S S' fS fX hf F i ≫
        (crisCohomologyIsoPushforwardHypercohomology S S' fX
          ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) i).hom =
      (crisCohomologyIsoZariskiHypercohomology S' ((toAbelianSheaf S').obj F) i).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
          ((derivedZariskiGlobalSectionsFunctor S').map
            (moduleComparison07Q9 S S' fS fX hf F)) := by
  rw [crisModuleCohomologyMap, Category.assoc,
    crisCohomologyIsoPushforwardHypercohomology_hom_naturality]
  have h := crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward
    S S' fS fX hf ((toAbelianSheaf S').obj F) i
  rw [crisCohomologyIsoZariskiHypercohomologyPushforward_eq] at h
  rw [← Category.assoc, h, Category.assoc, zariskiHypercohomologyComparisonMap,
    ← Functor.map_comp, ← Functor.map_comp, moduleComparison07Q9]

/-- The element-level form of
`crisModuleCohomologyMap_comp_crisCohomologyIsoPushforwardHypercohomology`. -/
theorem crisModuleCohomologyMap_apply (F : ModuleSheaf S') (i : ℕ)
    (x : (cohomologyFunctor S' i).obj ((toAbelianSheaf S').obj F)) :
    (crisCohomologyIsoPushforwardHypercohomology S S' fX
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) i).hom
          (crisModuleCohomologyMap S S' fS fX hf F i x) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
        ((derivedZariskiGlobalSectionsFunctor S').map (moduleComparison07Q9 S S' fS fX hf F))
          ((crisCohomologyIsoZariskiHypercohomology S' ((toAbelianSheaf S').obj F) i).hom x) := by
  have h := crisModuleCohomologyMap_comp_crisCohomologyIsoPushforwardHypercohomology
    S S' fS fX hf F i
  exact congrArg (fun φ => φ x) (congrArg (fun φ => ConcreteCategory.hom φ) h)

/-- **The kernel bound of [Stacks, Tag 07QA] for the module pullback.**  If the cohomology sheaves
of the cones of the comparison map `...SmallSite.moduleComparison07Q9` of [Stacks, Tag 07Q9] are
annihilated by `q`, the kernel of `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_cris^*ℱ)` is
annihilated by `q^{i + 1}`. -/
theorem pow_smul_eq_zero_of_crisModuleCohomologyMap_eq_zero (q i : ℕ) (F : ModuleSheaf S')
    (hann : Annihilation07Q9 S' q (moduleComparison07Q9 S S' fS fX hf F))
    (x : (cohomologyFunctor S' i).obj ((toAbelianSheaf S').obj F))
    (hx : crisModuleCohomologyMap S S' fS fX hf F i x = 0) :
    ((q : ℤ) ^ (i + 1)) • x = 0 := by
  have := isGE_derivedZariskiDirectImage_obj S' ((toAbelianSheaf S').obj F)
  have := isGE_derivedZariskiPushforward_obj S S' fX
    ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))
  have hz := crisModuleCohomologyMap_apply S S' fS fX hf F i x
  rw [hx, map_zero] at hz
  have h := pow_smul_eq_zero_of_hypercohomologyMap_eq_zero_of_annihilation S' q i
    (moduleComparison07Q9 S S' fS fX hf F) hann _ hz.symm
  apply (crisCohomologyZariskiHypercohomologyAddEquiv S' ((toAbelianSheaf S').obj F) i).injective
  rwa [map_zsmul, map_zero]

/-- **The cokernel bound of [Stacks, Tag 07QA] for the module pullback.**  If the cohomology
sheaves of the cones of the comparison map `...SmallSite.moduleComparison07Q9` of
[Stacks, Tag 07Q9] are annihilated by `q` and `ℋ^0` of that map is a monomorphism, then
`q^{i + 1}` times any class of `H^i(Cris(X'/S), f_cris^*ℱ)` is in the image of `f^*`. -/
theorem exists_crisModuleCohomologyMap_eq_pow_smul (q i : ℕ) (F : ModuleSheaf S')
    (hann : Annihilation07Q9 S' q (moduleComparison07Q9 S S' fS fX hf F))
    (hmono : Mono ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
        (DerivedCategory.Plus.ι.map (moduleComparison07Q9 S S' fS fX hf F))))
    (y : (cohomologyFunctor S i).obj
      ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y = crisModuleCohomologyMap S S' fS fX hf F i x := by
  have := isGE_derivedZariskiDirectImage_obj S' ((toAbelianSheaf S').obj F)
  have := isGE_derivedZariskiPushforward_obj S S' fX
    ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))
  set e := crisCohomologyZariskiHypercohomologyAddEquiv S' ((toAbelianSheaf S').obj F) i
  set e' := (crisCohomologyIsoPushforwardHypercohomology S S' fX
    ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) i).addCommGroupIsoToAddEquiv
  obtain ⟨z, hz⟩ := exists_hypercohomologyMap_eq_pow_smul_of_annihilation S' q i
    (moduleComparison07Q9 S S' fS fX hf F) hann hmono (e' y)
  refine ⟨e.symm z, e'.injective ?_⟩
  have hb := crisModuleCohomologyMap_apply S S' fS fX hf F i (e.symm z)
  have he : (crisCohomologyIsoZariskiHypercohomology S' ((toAbelianSheaf S').obj F) i).hom
      (e.symm z) = z := e.apply_symm_apply z
  rw [he] at hb
  rw [map_zsmul]
  exact hz.trans hb.symm

end Transport

/-! ### The monomorphism of the cokernel half, reduced to the module unit -/

section Mono

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

include hf

/-- **`ℋ^0` of the comparison map of [Stacks, Tag 07Q9] is a monomorphism exactly when
`u_{X/S, *}` of the module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` is one.**  The comparison map is
`Ru_{X/S, *}` of the derived unit followed by a component of the isomorphism
`...SmallSite.derivedZariskiSquare` (`...SmallSite.moduleComparison07Q9_eq`); the derived unit is
the module unit followed by the canonical `f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]`
(`...SmallSite.derivedModuleCrisUnit_eq`), an isomorphism on `ℋ^0`; and `ℋ^0 ∘ Ru_{X/S, *}` on a
sheaf in degree zero is `u_{X/S, *}`. -/
theorem mono_homologyMap_moduleComparison07Q9_iff (F : ModuleSheaf S') :
    Mono ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
          (DerivedCategory.Plus.ι.map (moduleComparison07Q9 S S' fS fX hf F))) ↔
      Mono ((zariskiDirectImage S').map (crisModuleUnit S S' fS fX hf F)) := by
  have hunit : IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
        ((derivedZariskiDirectImageFunctor S').map
          ((singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))))) :=
    isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app
      (crisDirectImage S S' fS fX hf) (zariskiDirectImage S')
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))
  have heq : moduleComparison07Q9 S S' fS fX hf F =
      (derivedZariskiDirectImage S').map (crisModuleUnit S S' fS fX hf F) ≫
        (derivedZariskiDirectImageFunctor S').map
          ((singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) ≫
        (derivedZariskiSquare S S' fS fX hf (crisZariskiSquare S S' fS fX hf)).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) := by
    rw [moduleComparison07Q9_eq, derivedModuleCrisUnit_eq]
    exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)
  have hmap : (DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
          (DerivedCategory.Plus.ι.map (moduleComparison07Q9 S S' fS fX hf F)) =
      ((DerivedCategory.Plus.homologyFunctor _ 0).map
          ((derivedZariskiDirectImage S').map (crisModuleUnit S S' fS fX hf F)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map ((derivedZariskiDirectImageFunctor S').map
          ((singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))))) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map ((derivedZariskiSquare S S' fS fX hf
          (crisZariskiSquare S S' fS fX hf)).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))) := by
    rw [heq]
    exact (Functor.map_comp _ _ _).trans
      ((congrArg ((DerivedCategory.Plus.homologyFunctor _ 0).map _ ≫ ·)
        (Functor.map_comp _ _ _)).trans
      (Category.assoc _ _ _).symm)
  rw [hmap]
  refine ((mono_comp_iff_of_isIso_snd _ _ (Iso.isIso_hom ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).mapIso ((derivedZariskiSquare S S' fS fX
        hf (crisZariskiSquare S S' fS fX hf)).app _)))).trans
    (mono_comp_iff_of_isIso_snd _ _ hunit)).trans ?_
  exact mono_homologyFunctor_derivedZariskiDirectImage_map_iff S' (crisModuleUnit S S' fS fX hf F)

end Mono

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
