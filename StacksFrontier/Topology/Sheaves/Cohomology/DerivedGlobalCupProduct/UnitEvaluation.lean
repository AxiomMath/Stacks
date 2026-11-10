module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductOnSections

/-!
# Evaluation at the unit: cohomology classes as morphisms out of the shifted structure sheaf

Let `(X, 𝒪_X)` be a ringed space, `m ∈ ℤ` and write `𝒪_X[-m]` for the structure sheaf placed in
degree `m` (`unitComplex X m`).  The global section `1` of `𝒪_X` is a global cocycle of
`Γ(X, 𝒪_X[-m])` in degree `m`, with class `unitCycleClass X m ∈ Hᵐ(X, 𝒪_X[-m])`.  Evaluation at
that class,

`evalUnit K m : Hom_{D(𝒪_X)}(𝒪_X[-m], K) ⟶ Hᵐ(X, K)`, `φ ↦ Hᵐ(RΓ φ)(unitCycleClass X m)`,

is a bijection (`evalUnit_bijective`, `evalUnitEquiv`).  On a K-injective model `I` of `K`
morphisms out of `𝒪_X[-m]` are chain maps up to homotopy, a chain map out of `𝒪_X[-m]` is the
global cocycle it sends `1` to, `RΓ(X, I)` is computed by `Γ(X, I)`, and a cocycle whose class
vanishes is a boundary, which makes the chain map null-homotopic.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.globalClass`: the class in `Hⁿ(X, N)` of a global
  cocycle of a complex `N` of `𝒪_X`-modules.
* `Stacks.Cohomology.DerivedGlobalCupProduct.unitComplex`, `unitCycle`, `unitCycleClass`: the
  structure sheaf in degree `m`, the cocycle `1` and its class.
* `Stacks.Cohomology.DerivedGlobalCupProduct.homOfCycle`: the chain map `𝒪_X[-m] ⟶ I` attached to
  a global cocycle of `I`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit`: evaluation at the class of `1`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map`: classes of global cocycles are
  natural along chain maps.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isIso_sectionsUnitQ_of_isKInjective`: a K-injective
  complex computes `RΓ`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.exists_globalClass_of_isKInjective`: every class of a
  K-injective complex is the class of a global cocycle.
* `Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_surjective`,
  `Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_injective` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_bijective`: **evaluation at the unit is a
  bijection** `Hom_{D(𝒪_X)}(𝒪_X[-m], K) ≃ Hᵐ(X, K)`, packaged as `evalUnitEquiv`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedSectionsLeray

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- The class in `Hⁿ(X, N)` of a global cocycle of a complex `N` of `𝒪_X`-modules. -/
def globalClass (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ)
    (s : (sectionsComplex X N).cycles n) : cohomologyModule (DerivedCategory.Q.obj N) n :=
  ((sectionsComplex X N).homologyπ n ≫
    (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex X N) ≫
      (DerivedCategory.homologyFunctor _ n).map (sectionsUnitQ X ⊤ N)).hom s

/-- The class of a family of global cocycles, at an element, is the class of the cocycle. -/
theorem globalCycleClass_apply {M : ModuleCat.{u} (baseRing X)}
    {N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {n : ℤ}
    (z : M ⟶ (sectionsComplex X N).cycles n) (a : M) :
    (globalCycleClass z).hom a = globalClass N n (z.hom a) :=
  rfl

/-! ### Every class is the image of the class of `1` -/

section Unit

variable (X)

/-- The class of a global cocycle is natural along chain maps, on elements. -/
theorem globalClass_map {N N' : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (g : N ⟶ N') (n : ℤ) (s : (sectionsComplex X N).cycles n) :
    ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map (DerivedCategory.Q.map g))).hom
        (globalClass N n s) =
      globalClass N' n ((HomologicalComplex.cyclesMap
        (((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map g) n).hom s) :=
  ConcreteCategory.congr_hom
    (globalCycleClass_map (𝟙 ((sectionsComplex X N).cycles n)) g) s

/-- The structure sheaf placed in degree `n`. -/
abbrev unitComplex (n : ℤ) : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
    (_root_.SheafOfModules.unit (structureSheafRing X))

/-- The global section `1` of `𝒪_X`, in degree `n` of `Γ(X, 𝒪_X[-n])`. -/
def unitSection (n : ℤ) : (sectionsComplex X (unitComplex X n)).X n :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
    (_root_.SheafOfModules.unit (structureSheafRing X))).inv.val.app (op ⊤)).hom
      (1 : (structureSheafRing X).obj.obj (op ⊤))

/-- The differential of `Γ(X, 𝒪_X[-n])` out of degree `n` vanishes on the section `1`. -/
theorem d_unitSection (n : ℤ) :
    ((sectionsComplex X (unitComplex X n)).d n (n + 1)).hom (unitSection X n) = 0 := by
  have : (sectionsComplex X (unitComplex X n)).d n (n + 1) = 0 := by
    simp [sectionsComplex, unitComplex]
  rw [this]
  rfl

/-- The global section `1` of `𝒪_X` is a cocycle of `Γ(X, 𝒪_X[-n])`. -/
def unitCycle (n : ℤ) : (sectionsComplex X (unitComplex X n)).cycles n :=
  ((sectionsComplex X (unitComplex X n)).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _ (unitSection X n))) (n + 1)
    (by simp) (by
      ext
      change ((sectionsComplex X (unitComplex X n)).d n (n + 1)).hom
        ((LinearMap.toSpanSingleton (baseRing X) _ (unitSection X n)) 1) = 0
      rw [LinearMap.toSpanSingleton_apply, one_smul]
      exact d_unitSection X n)).hom 1

/-- The cocycle `unitCycle X n` is the section `1` in degree `n` of `Γ(X, 𝒪_X[-n])`. -/
theorem iCycles_unitCycle (n : ℤ) :
    ((sectionsComplex X (unitComplex X n)).iCycles n).hom (unitCycle X n) = unitSection X n := by
  have := ConcreteCategory.congr_hom ((sectionsComplex X (unitComplex X n)).liftCycles_i
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _ (unitSection X n))) (n + 1)
    (by simp) (by
      ext
      change ((sectionsComplex X (unitComplex X n)).d n (n + 1)).hom
        ((LinearMap.toSpanSingleton (baseRing X) _ (unitSection X n)) 1) = 0
      rw [LinearMap.toSpanSingleton_apply, one_smul]
      exact d_unitSection X n)) (1 : baseRing X)
  exact this.trans (by
    change (LinearMap.toSpanSingleton (baseRing X) _ (unitSection X n)) 1 = _
    rw [LinearMap.toSpanSingleton_apply, one_smul])

variable {X}

/-- A chain map out of `𝒪_X[-m]` sends the cocycle `1` to the image of the section `1`. -/
private theorem iCycles_cyclesMap_unitCycle
    {N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {m : ℤ}
    (ψ : unitComplex X m ⟶ N) :
    ((sectionsComplex X N).iCycles m).hom ((HomologicalComplex.cyclesMap
      (((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) m).hom
        (unitCycle X m)) = ((ψ.f m).val.app (op ⊤)).hom (unitSection X m) := by
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) m)
      (unitCycle X m)).trans ?_
  exact congrArg _ (iCycles_unitCycle X m)

/-- The morphism `𝒪_X ⟶ F` sending `1` to a global section `x` of `F`. -/
def homOfGlobalSection (F : SheafOfModules.{u} (structureSheafRing X)) (x : F.val.obj (op ⊤)) :
    _root_.SheafOfModules.unit (structureSheafRing X) ⟶ F :=
  F.unitHomEquiv.symm (F.val.sectionsMk
    (fun V => F.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op x) (by
      intro V W g
      exact (F.val.map_comp_apply (homOfLE (show V.unop ≤ ⊤ from le_top)).op g x).symm))

/-- The morphism attached to a global section sends `1` to it, over an open `V`, up to
restriction. -/
theorem homOfGlobalSection_app_one (F : SheafOfModules.{u} (structureSheafRing X))
    (x : F.val.obj (op ⊤)) (V : (Opens X.carrier)ᵒᵖ) :
    ((homOfGlobalSection F x).val.app V).hom (1 : (structureSheafRing X).obj.obj V) =
      (F.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom x := by
  have h1 := _root_.SheafOfModules.unitHomEquiv_apply_coe F (homOfGlobalSection F x) V
  rw [homOfGlobalSection, Equiv.apply_symm_apply] at h1
  exact h1.symm

/-- The morphism attached to a global section sends `1` to it. -/
theorem homOfGlobalSection_app_top_one (F : SheafOfModules.{u} (structureSheafRing X))
    (x : F.val.obj (op ⊤)) :
    ((homOfGlobalSection F x).val.app (op ⊤)).hom (1 : (structureSheafRing X).obj.obj (op ⊤)) =
      x := by
  rw [homOfGlobalSection_app_one,
    show (homOfLE (le_top : (⊤ : Opens X.carrier) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl,
    PresheafOfModules.map_id]
  rfl

/-- The section `1` in degree `m` of `Γ(X, 𝒪_X[-m])` is `1` under the identification of the
degree-`m` term with `𝒪_X`. -/
theorem singleObjXSelf_hom_unitSection (m : ℤ) :
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
      (_root_.SheafOfModules.unit (structureSheafRing X))).hom.val.app (op ⊤)).hom
        (unitSection X m)) = (1 : (structureSheafRing X).obj.obj (op ⊤)) := by
  have h0 := congrArg (fun g : _ ⟶ _ => (g.val.app (op ⊤)).hom)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
      (_root_.SheafOfModules.unit (structureSheafRing X))).inv_hom_id
  exact LinearMap.congr_fun h0 (1 : (structureSheafRing X).obj.obj (op ⊤))

/-- The chain map `𝒪_X[-m] ⟶ I` attached to a global cocycle of `I` in degree `m`. -/
def homOfCycle (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ)
    (x : (I.X n).val.obj (op ⊤)) (hx : ((I.d n (n + 1)).val.app (op ⊤)).hom x = 0) :
    unitComplex X n ⟶ I :=
  HomologicalComplex.mkHomFromSingle (homOfGlobalSection (I.X n) x)
    (by
      rintro k hk
      obtain rfl : n + 1 = k := hk
      apply (I.X (n + 1)).unitHomEquiv.injective
      apply Subtype.ext
      funext V
      rw [_root_.SheafOfModules.unitHomEquiv_comp_apply, homOfGlobalSection,
        Equiv.apply_symm_apply]
      refine (PresheafOfModules.naturality_apply (I.d n (n + 1)).val
        (homOfLE (le_top : V.unop ≤ ⊤)).op x).trans ?_
      rw [hx, map_zero]
      rfl)

/-- The chain map attached to a global cocycle sends the section `1` to the cocycle. -/
theorem homOfCycle_unitSection (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (n : ℤ) (x : (I.X n).val.obj (op ⊤)) (hx : ((I.d n (n + 1)).val.app (op ⊤)).hom x = 0) :
    ((((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (homOfCycle I n x hx)).f n).hom (unitSection X n) = x := by
  change (((homOfCycle I n x hx).f n).val.app (op ⊤)).hom (unitSection X n) = x
  rw [homOfCycle, HomologicalComplex.mkHomFromSingle_f]
  change ((homOfGlobalSection (I.X n) x).val.app (op ⊤)).hom
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
      (_root_.SheafOfModules.unit (structureSheafRing X))).hom.val.app (op ⊤)).hom
        (unitSection X n)) = x
  rw [singleObjXSelf_hom_unitSection]
  exact homOfGlobalSection_app_top_one _ x

/-- At a K-injective complex the unit `Γ ⟶ RΓ` is invertible. -/
theorem isIso_sectionsUnitQ_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso (sectionsUnitQ X ⊤ I) := by
  have h :=
    Stacks.Cohomology.DerivedSectionsModels.isIso_derivedSectionsOverOpenUnit_app_of_isKInjective
      X ⊤ I hI
  have h2 : IsIso ((derivedSectionsOverOpen X ⊤).map
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).hom.app I)) :=
    Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ h h2)

/-- Every class in `Hⁿ(X, I)` of a K-injective complex `I` is the class of a global cocycle. -/
theorem exists_globalClass_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (n : ℤ) (ξ : cohomologyModule (DerivedCategory.Q.obj I) n) :
    ∃ c : (sectionsComplex X I).cycles n, globalClass I n c = ξ := by
  have hu := isIso_sectionsUnitQ_of_isKInjective I hI
  have h3 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map
      (sectionsUnitQ X ⊤ I)) := Functor.map_isIso _ _
  have h4 : Epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing X)) n).inv.app
      (sectionsComplex X I) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map (sectionsUnitQ X ⊤ I)) :=
    @epi_comp _ _ _ _ _ _ inferInstance _ (@IsIso.epi_of_iso _ _ _ _ _ h3)
  have h5 : Epi ((sectionsComplex X I).homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing X)) n).inv.app
        (sectionsComplex X I) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map (sectionsUnitQ X ⊤ I)) :=
    @epi_comp _ _ _ _ _ _ inferInstance _ h4
  exact (ModuleCat.epi_iff_surjective _).1 h5 ξ

/-- `exists_unitComplex_hom` at an object presented by a K-injective complex. -/
theorem exists_unitComplex_hom_of_iso
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ K) (n : ℤ) (ξ : cohomologyModule K n) :
    ∃ φ : DerivedCategory.Q.obj (unitComplex X n) ⟶ K,
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map φ)).hom
        (globalClass (unitComplex X n) n (unitCycle X n)) = ξ := by
  obtain ⟨c, hc⟩ := exists_globalClass_of_isKInjective I hI n
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map e.inv)).hom ξ)
  obtain ⟨x, hxdef⟩ : ∃ x, x = ((sectionsComplex X I).iCycles n).hom c := ⟨_, rfl⟩
  have hx : ((I.d n (n + 1)).val.app (op ⊤)).hom x = 0 := by
    rw [hxdef]
    exact ConcreteCategory.congr_hom ((sectionsComplex X I).iCycles_d n (n + 1)) c
  refine ⟨DerivedCategory.Q.map (homOfCycle I n x hx) ≫ e.hom, ?_⟩
  have hcyc : (HomologicalComplex.cyclesMap (((globalSections X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homOfCycle I n x hx)) n).hom (unitCycle X n) = c := by
    apply (ModuleCat.mono_iff_injective ((sectionsComplex X I).iCycles n)).1 inferInstance
    refine (iCycles_cyclesMap_unitCycle (homOfCycle I n x hx)).trans ?_
    exact (homOfCycle_unitSection I n x hx).trans hxdef
  have h1 := globalClass_map X (homOfCycle I n x hx) n (unitCycle X n)
  rw [hcyc, hc] at h1
  have h3 := ConcreteCategory.congr_hom
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map
      ((congrArg (baseSections X).map e.inv_hom_id).trans ((baseSections X).map_id _))).trans
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map_id _)) ξ
  rw [Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply, h1,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact h3

/-- Every object of `D(𝒪_X)` is isomorphic to a K-injective complex. -/
private theorem exists_isKInjective_iso
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ,
      I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ K) := by
  have := Localization.essSurj (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X)))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  obtain ⟨I, i, hI, _⟩ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X
      (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- **Every cohomology class is the image of the class of `1`**: for `K ∈ D(𝒪_X)` and
`ξ ∈ Hⁿ(X, K)` there is a morphism `φ : 𝒪_X[-n] ⟶ K` carrying the class of the global section
`1` to `ξ`. -/
theorem exists_unitComplex_hom (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (n : ℤ) (ξ : cohomologyModule K n) :
    ∃ φ : DerivedCategory.Q.obj (unitComplex X n) ⟶ K,
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map φ)).hom
        (globalClass (unitComplex X n) n (unitCycle X n)) = ξ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso K
  exact exists_unitComplex_hom_of_iso I hI e n ξ

/-- **Chain maps out of `𝒪_X[-m]` are determined by the image of `1`**: two chain maps
`𝒪_X[-m] ⟶ N` agreeing on the global section `1` in degree `m` are equal. -/
theorem unitComplex_hom_ext {N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {m : ℤ} (φ₁ φ₂ : unitComplex X m ⟶ N)
    (h : ((φ₁.f m).val.app (op ⊤)).hom (unitSection X m) =
      ((φ₂.f m).val.app (op ⊤)).hom (unitSection X m)) : φ₁ = φ₂ := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  by_cases hk : k = m
  · subst hk
    let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k
      (_root_.SheafOfModules.unit (structureSheafRing X))
    rw [← cancel_epi ι.inv]
    apply (N.X k).unitHomEquiv.injective
    apply Subtype.ext
    funext V
    have key : ∀ (φ : unitComplex X k ⟶ N),
        (((N.X k).unitHomEquiv (ι.inv ≫ φ.f k)).val V) =
          ((N.X k).val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom
            (((φ.f k).val.app (op ⊤)).hom (unitSection X k)) := by
      intro φ
      rw [_root_.SheafOfModules.unitHomEquiv_apply_coe]
      change ((φ.f k).val.app V).hom ((ι.inv.val.app V).hom
        (1 : (structureSheafRing X).obj.obj V)) = _
      have h1 : (ι.inv.val.app V).hom (1 : (structureSheafRing X).obj.obj V) =
          (((unitComplex X k).X k).val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom
            ((ι.inv.val.app (op ⊤)).hom (1 : (structureSheafRing X).obj.obj (op ⊤))) := by
        have := PresheafOfModules.naturality_apply ι.inv.val (homOfLE (le_top : V.unop ≤ ⊤)).op
          (1 : (structureSheafRing X).obj.obj (op ⊤))
        refine Eq.trans ?_ this
        congr 1
        exact (PresheafOfModules.unit_map_one _ _).symm
      rw [h1]
      exact PresheafOfModules.naturality_apply (φ.f k).val (homOfLE (le_top : V.unop ≤ ⊤)).op _
    rw [key, key, h]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).eq_of_src _ _

/-- **Morphisms into a K-injective complex are chain maps**: for `I` K-injective every morphism
`QP ⟶ QI` of `D(𝒪_X)` is the image of a chain map. -/
theorem exists_Q_map_eq_of_isKInjective
    {P I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} [I.IsKInjective]
    (φ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    ∃ ψ : P ⟶ I, DerivedCategory.Q.map ψ = φ := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) I).2
      ((DerivedCategory.quotientCompQhIso _).hom.app P ≫ φ ≫
        (DerivedCategory.quotientCompQhIso _).inv.app I)
  obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective g
  refine ⟨ψ, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (structureSheafRing X))).hom.naturality ψ
  dsimp only [Functor.comp_map] at hn
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app P), ← hn, hg]
  simp

/-- The class of a global cocycle of a K-injective complex vanishes only on boundaries. -/
theorem exists_d_eq_of_globalClass_eq_zero_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (n : ℤ) (c : (sectionsComplex X I).cycles n) (hc : globalClass I n c = 0) :
    ∃ b : (sectionsComplex X I).X (n - 1),
      ((sectionsComplex X I).d (n - 1) n).hom b = ((sectionsComplex X I).iCycles n).hom c := by
  have hu := isIso_sectionsUnitQ_of_isKInjective I hI
  have h3 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map
      (sectionsUnitQ X ⊤ I)) := Functor.map_isIso _ _
  have hπ : ((sectionsComplex X I).homologyπ n).hom c = 0 := by
    apply (ModuleCat.mono_iff_injective ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} (baseRing X)) n).inv.app (sectionsComplex X I) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map
        (sectionsUnitQ X ⊤ I))).1 inferInstance
    exact hc.trans (map_zero _).symm
  let S := ShortComplex.mk ((sectionsComplex X I).toCycles (n - 1) n)
    ((sectionsComplex X I).homologyπ n) ((sectionsComplex X I).toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    ((sectionsComplex X I).homologyIsCokernel (n - 1) n (by simp))
  obtain ⟨b, hb⟩ : c ∈ LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    exact hπ
  refine ⟨b, ?_⟩
  rw [← hb]
  exact (ConcreteCategory.congr_hom ((sectionsComplex X I).toCycles_i (n - 1) n) b).symm

variable (X) in
/-- The class of the global section `1` in `Hᵐ(X, 𝒪_X[-m])`. -/
abbrev unitCycleClass (m : ℤ) : cohomologyModule (DerivedCategory.Q.obj (unitComplex X m)) m :=
  globalClass (unitComplex X m) m (unitCycle X m)

/-- **Evaluation at the unit**: a morphism `φ : 𝒪_X[-m] ⟶ K` of `D(𝒪_X)` is sent to the image
of the class of `1` under `Hᵐ(RΓ φ)`. -/
def evalUnit (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (m : ℤ)
    (φ : DerivedCategory.Q.obj (unitComplex X m) ⟶ K) : cohomologyModule K m :=
  ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map φ)).hom (unitCycleClass X m)

/-- **Evaluation at the unit is surjective**: every class in `Hᵐ(X, K)` is the image of the class
of `1` under a morphism `𝒪_X[-m] ⟶ K`. -/
theorem evalUnit_surjective (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (m : ℤ) : Function.Surjective (evalUnit K m) := fun ξ =>
  exists_unitComplex_hom K m ξ

/-- Two chain maps out of `𝒪_X[-m]` whose values on `1` differ by a global boundary are
identified in the derived category. -/
private theorem Q_map_eq_of_d_eq_sub
    {I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {m : ℤ}
    (ψ₁ ψ₂ : unitComplex X m ⟶ I) (b : (sectionsComplex X I).X (m - 1))
    (hb : ((sectionsComplex X I).d (m - 1) m).hom b =
      ((ψ₁.f m).val.app (op ⊤)).hom (unitSection X m) -
        ((ψ₂.f m).val.app (op ⊤)).hom (unitSection X m)) :
    DerivedCategory.Q.map ψ₁ = DerivedCategory.Q.map ψ₂ := by
  let β := homOfGlobalSection (I.X (m - 1)) b
  let hh : ∀ i j, (ComplexShape.up ℤ).Rel j i → ((unitComplex X m).X i ⟶ I.X j) :=
    fun i j hij => if hi : i = m then
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) m
        (_root_.SheafOfModules.unit (structureSheafRing X)) i hi).hom ≫ β ≫
          (I.XIsoOfEq (show m - 1 = j by
            have : j + 1 = i := hij
            omega)).hom
      else 0
  have heq : ψ₁ - ψ₂ = Homotopy.nullHomotopicMap' hh := by
    apply unitComplex_hom_ext
    rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (m - 1) m by simp)
      (show (ComplexShape.up ℤ).Rel m (m + 1) by simp)]
    have hd : (unitComplex X m).d m (m + 1) = 0 := by simp [unitComplex]
    rw [hd, zero_comp, zero_add]
    have hhm : hh m (m - 1) (by simp) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
          (_root_.SheafOfModules.unit (structureSheafRing X))).hom ≫ β := by
      simp only [hh, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        Category.comp_id]
      rfl
    rw [hhm]
    change ((ψ₁.f m - ψ₂.f m).val.app (op ⊤)).hom (unitSection X m) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
          (_root_.SheafOfModules.unit (structureSheafRing X))).hom ≫ β ≫
            I.d (m - 1) m).val.app (op ⊤)).hom (unitSection X m)
    change _ = ((I.d (m - 1) m).val.app (op ⊤)).hom ((β.val.app (op ⊤)).hom
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
        (_root_.SheafOfModules.unit (structureSheafRing X))).hom.val.app (op ⊤)).hom
          (unitSection X m)))
    rw [singleObjXSelf_hom_unitSection]
    refine Eq.trans ?_ (congrArg ((I.d (m - 1) m).val.app (op ⊤)).hom
      (homOfGlobalSection_app_top_one (I.X (m - 1)) b).symm)
    refine Eq.trans ?_ hb.symm
    rfl
  exact DerivedCategory.Q_map_eq_of_homotopy (C := SheafOfModules.{u} (structureSheafRing X))
    (Homotopy.equivSubZero.symm ((Homotopy.ofEq heq).trans (Homotopy.nullHomotopy' hh)))

/-- **Evaluation at the unit is injective on a K-injective complex.** -/
theorem evalUnit_injective_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (m : ℤ) : Function.Injective (evalUnit (DerivedCategory.Q.obj I) m) := by
  intro φ₁ φ₂ h
  obtain ⟨ψ₁, rfl⟩ := exists_Q_map_eq_of_isKInjective φ₁
  obtain ⟨ψ₂, rfl⟩ := exists_Q_map_eq_of_isKInjective φ₂
  let Γψ := fun ψ : unitComplex X m ⟶ I =>
    (HomologicalComplex.cyclesMap (((globalSections X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ψ) m).hom (unitCycle X m)
  have h' : globalClass I m (Γψ ψ₁ - Γψ ψ₂) = 0 := by
    unfold evalUnit unitCycleClass at h
    rw [globalClass_map X ψ₁ m (unitCycle X m), globalClass_map X ψ₂ m (unitCycle X m)] at h
    rw [globalClass, map_sub]
    exact sub_eq_zero.2 h
  obtain ⟨b, hb⟩ := exists_d_eq_of_globalClass_eq_zero_of_isKInjective I hI m _ h'
  have hiC : ∀ ψ : unitComplex X m ⟶ I, ((sectionsComplex X I).iCycles m).hom (Γψ ψ) =
      ((ψ.f m).val.app (op ⊤)).hom (unitSection X m) := fun ψ => iCycles_cyclesMap_unitCycle ψ
  rw [map_sub, hiC, hiC] at hb
  exact Q_map_eq_of_d_eq_sub ψ₁ ψ₂ b hb

/-- Evaluation at the unit is natural along morphisms of the target. -/
theorem evalUnit_comp {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (m : ℤ) (φ : DerivedCategory.Q.obj (unitComplex X m) ⟶ K) (g : K ⟶ L) :
    evalUnit L m (φ ≫ g) =
      ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map g)).hom
        (evalUnit K m φ) := by
  unfold evalUnit
  rw [Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **Evaluation at the unit is injective**: a morphism `𝒪_X[-m] ⟶ K` of `D(𝒪_X)` is determined
by the image of the class of `1`. -/
theorem evalUnit_injective (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (m : ℤ) : Function.Injective (evalUnit K m) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso K
  intro φ₁ φ₂ h
  have h' : evalUnit (DerivedCategory.Q.obj I) m (φ₁ ≫ e.inv) =
      evalUnit (DerivedCategory.Q.obj I) m (φ₂ ≫ e.inv) := by
    rw [evalUnit_comp, evalUnit_comp, h]
  simpa using congrArg (· ≫ e.hom) (evalUnit_injective_of_isKInjective I hI m h')

/-- **Evaluation at the unit is a bijection** `Hom_{D(𝒪_X)}(𝒪_X[-m], K) ≃ Hᵐ(X, K)`. -/
theorem evalUnit_bijective (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (m : ℤ) : Function.Bijective (evalUnit K m) :=
  ⟨evalUnit_injective K m, evalUnit_surjective K m⟩

/-- **Evaluation at the unit**, as an equivalence `Hom_{D(𝒪_X)}(𝒪_X[-m], K) ≃ Hᵐ(X, K)`. -/
noncomputable def evalUnitEquiv (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (m : ℤ) : (DerivedCategory.Q.obj (unitComplex X m) ⟶ K) ≃ cohomologyModule K m :=
  Equiv.ofBijective _ (evalUnit_bijective K m)

end Unit

end Stacks.Cohomology.DerivedGlobalCupProduct

end
