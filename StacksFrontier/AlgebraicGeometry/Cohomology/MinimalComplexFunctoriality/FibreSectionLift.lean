module

public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.AffineFibreBridge
public import
  StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.BaseChangePullbackMap
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PushforwardGenerator
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.CategoryTheory.Nondegeneracy.NotIsZero
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# Lifting a section of a trivial fibre to an affine neighbourhood

This file carries out the cohomological half of the proof of
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2) in the case where every `ℒ_i` is
trivial, over an affine base `Spec R`. Let `p : P ⟶ Spec R` and the `i k ≫ p : X k ⟶ Spec R`
(`k` in a finite type) be flat, proper and of finite presentation, let `ℒ` be an invertible
`𝒪_P`-module whose pullbacks `(i k)^*ℒ` are trivial, and let

```
F --tF--> P        FX k --tX k--> X k
|ps       |p        |              |i k ≫ p
Spec K ---> Spec R  Spec K -------> Spec R
```

be the base changes along `t = Spec χ` for a homomorphism `χ : R ⟶ K` to a field, with
`isk k : FX k ⟶ F` the base change of `i k`. If `ℒ` is trivial on `F`, if
`𝒪_{Spec K} ⟶ ps_* 𝒪_F` and `𝒪_{Spec K} ⟶ (isk k ≫ ps)_* 𝒪_{FX k}` are isomorphisms, and if
`H¹(F, 𝒪_F) ⟶ ⊕_k H¹(FX k, 𝒪_{FX k})` is injective, then some morphism `σ : 𝒪_P ⟶ ℒ` has
nonzero pullback `tF^*σ` to the fibre.

The proof is the source's. [Stacks, Tag 0B91] (from [Stacks, Tag 0A1H])
makes `E = Rp_*ℒ` and `E_k = R(i k ≫ p)_* L(i k)^*ℒ` perfect and their formation commute with
the base change to `Spec K`; the pullback maps `E ⟶ E_k` commute with that base change
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_pullbackMap`); the fibre cohomology of
`E` and the `E_k` is that of `𝒪_F` and of the `𝒪_{FX k}`, so the injectivity hypothesis, the
dimension bound `dim H⁰(FX k, 𝒪) ≤ 1`, the nonvanishing of `H⁰(F, 𝒪)` and the derived unit of
`𝒪_{X k} ≅ (i k)^*ℒ` feed the matrix argument
`AlgebraicGeometry.MinimalComplexFunctoriality.exists_map_derivedPullback_ne_zero` (built on
[Stacks, Tag 0BCC] minimal models), which returns `𝒪_{Spec R}[0] ⟶ E` with nonzero derived
pullback to `Spec K`. Its transpose is a morphism `σ : 𝒪_P ⟶ ℒ`, and by the mate identity of the
derived base change map (`PushforwardGenerator.derivedPullback_map_derivedAdjoint_eq_zero`)
`tF^*σ ≠ 0`.

## Main results

* `MinimalComplexFunctoriality.exists_unit_hom_modulePullback_ne_zero_of_injective_H1`:
  the statement above.
* `AlgebraicGeometry.MinimalComplexFunctoriality.homologyZeroSectionsOverBaseSingleIso`: the degree
  zero cohomology of `RΓ(V, P[0])` over the base `T` of `c : V ⟶ T` is `Γ(V, P)`, with scalars
  restricted along `c^♯`.

## Implementation notes

Every chase is stated as a lemma with its functors and morphisms as variables
(`sectionsPullbackMap_chase`, `comp_eq_comp_comp_inv`, `eq_zero_of_forall_map_eq_zero_of_isIso`)
and then instantiated: unfolding the concrete derived functors inside one proof exhausts the
elaborator.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction derivedPushforwardCompIso)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.GlobalKunneth (sectionsOverBase baseRing sectionsPullbackMap lerayIso)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open AlgebraicGeometry.ProperFlatBaseChange
open AlgebraicGeometry.SheafOfModules (IsTrivial IsInvertible)

universe u

namespace Stacks.Cohomology.DerivedSectionsLeray

/-- Sections over the inverse image of an open, as a module over the functions on the open, are
left exact: evaluation of sheaves of modules and restriction of scalars both are. -/
instance preimageSections_preservesFiniteLimits
    {V T : RingedSpace.{u, u}} (c : V ⟶ T) (U : Opens T.carrier) :
    PreservesFiniteLimits (Stacks.Cohomology.DerivedSectionsLeray.preimageSections c U) := by
  have h2 : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u} ((structureSheafHom c).hom.app (op U)).hom) := by
    constructor
    intro J _ _
    constructor
    intro K
    infer_instance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (SheafOfModules.Finite.evaluationPreservesFiniteLimits (structureSheafRing V)
      (op ((opensMap c).obj U))) h2

end Stacks.Cohomology.DerivedSectionsLeray

namespace AlgebraicGeometry.MinimalComplexFunctoriality

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Degree zero cohomology of sections over a base -/

/-- **`H⁰(RΓ(V, P[0])) = Γ(V, P)` over the base.** For `c : V ⟶ T` and an `𝒪_V`-module `P`, the
degree zero cohomology of the `Γ(T, 𝒪_T)`-linear derived sections of `P[0]` is the module of
global sections of `P`, with scalars restricted along `c^♯`: sections over the inverse image of an
open are left exact, and complexes of `𝒪_V`-modules have K-injective resolutions. -/
def homologyZeroSectionsOverBaseSingleIso {V T : RingedSpace.{u, u}} (c : V ⟶ T)
    (P : _root_.SheafOfModules.{u} (structureSheafRing V)) :
    (DerivedCategory.homologyFunctor _ 0).obj ((sectionsOverBase c).obj
      ((DerivedCategory.singleFunctor _ 0).obj P)) ≅
      (Stacks.Cohomology.DerivedSectionsLeray.preimageSections c ⊤).obj P :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso _ _
    (Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit c ⊤)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective V) P 0

/-- An isomorphism `𝒪_Y ⟶ f_*𝒪_X` of sheaves of rings is bijective on the sections over every
open. -/
theorem bijective_structureSheafHom_app {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [IsIso (structureSheafHom f)] (U : (Opens Y.carrier)ᵒᵖ) :
    Function.Bijective ((structureSheafHom f).hom.app U) := by
  have : IsIso (structureSheafHom f).hom :=
    Functor.map_isIso (ObjectProperty.ι _) (structureSheafHom f)
  exact ConcreteCategory.bijective_of_isIso _

/-- A module obtained from a ring `B` by restricting scalars twice, along ring maps whose composite
`K ⟶ B` from a field is bijective, is one-dimensional over `K`. -/
theorem finrank_restrictScalars_restrictScalars_self {K : Type u} [Field K] {A B : RingCat.{u}}
    (φ₁ : K →+* A) (φ₂ : A →+* B) (h : Function.Bijective (φ₂.comp φ₁)) :
    Module.finrank K ((ModuleCat.restrictScalars φ₁).obj
      ((ModuleCat.restrictScalars φ₂).obj (ModuleCat.of B B))) = 1 := by
  let f : K →ₗ[K] ((ModuleCat.restrictScalars φ₁).obj
      ((ModuleCat.restrictScalars φ₂).obj (ModuleCat.of B B))) :=
    { toFun := fun a => φ₂ (φ₁ a)
      map_add' := fun a b => by
        show φ₂ (φ₁ (a + b)) = φ₂ (φ₁ a) + φ₂ (φ₁ b)
        simp
      map_smul' := fun a b => by
        show φ₂ (φ₁ (a * b)) = φ₂ (φ₁ a) * φ₂ (φ₁ b)
        simp }
  rw [← (LinearEquiv.ofBijective f h).finrank_eq, Module.finrank_self]

/-- If `𝒪_{Spec K} ⟶ c_*𝒪_F` is an isomorphism for a field `K`, the functions on `F` form a
nontrivial ring. -/
theorem nontrivial_structureSheafRing_of_isIso {K : Type u} [Field K] {F : RingedSpace.{u, u}}
    (c : F ⟶ (Spec (CommRingCat.of K)).toRingedSpace) [IsIso (structureSheafHom c)] :
    Nontrivial ((structureSheafRing F).obj.obj (op ((opensMap c).obj ⊤))) := by
  have h1 : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have : Nontrivial ((structureSheafRing (Spec (CommRingCat.of K)).toRingedSpace).obj.obj
      (op ⊤)) := h1.1.nontrivial
  exact (bijective_structureSheafHom_app c (op ⊤)).1.nontrivial

/-- If `Y` is isomorphic to the derived sections of `𝒪_F` over `Spec K`, with `𝒪_{Spec K} ⟶ c_*𝒪_F`
an isomorphism, then `H⁰(Y)`, as a `K`-module, is one-dimensional. -/
private theorem finrank_restrictScalars_homology_zero_eq_one {K : Type u} [Field K]
    {F : RingedSpace.{u, u}} (c : F ⟶ (Spec (CommRingCat.of K)).toRingedSpace)
    [IsIso (structureSheafHom c)]
    {Y : DerivedCategory (ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace))}
    (A : Y ⟶ (sectionsOverBase c).obj ((DerivedCategory.singleFunctor _ 0).obj
      (_root_.SheafOfModules.unit (structureSheafRing F)))) [IsIso A] :
    Module.finrank K ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).obj
      ((DerivedCategory.homologyFunctor _ 0).obj Y)) = 1 := by
  let e := (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).mapIso
    ((DerivedCategory.homologyFunctor _ 0).mapIso (asIso A) ≪≫
      homologyZeroSectionsOverBaseSingleIso c
        (_root_.SheafOfModules.unit (structureSheafRing F)))
  exact e.toLinearEquiv.finrank_eq.trans (finrank_restrictScalars_restrictScalars_self _ _
    ((bijective_structureSheafHom_app c (op ⊤)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)))

/-! ### Chases with the functors as variables -/

/-- **The chase behind the comparison of pullback maps.** A base change map `β` followed by the
pullback map `ψ₁ ≫ ψ₂` is `φL ≫ βk ≫ ρ`; the pullback map on sections is the Leray conjugate
`le⁻¹ ≫ bS(ψ₁) ≫ bS(ψ₂) ≫ le'` and is natural along `γ`. Then the base change of the sections of
`φL`, read through `le` and `γ`, is the pullback map on sections up to a morphism on the right. -/
theorem sectionsPullbackMap_chase {C D : Type*} [Category C] [Category D] (bS : C ⥤ D)
    {A B B₁ B₂ A₂ A₃ : C}
    (β : A ⟶ B) (ψ₁ : B ⟶ B₁) (ψ₂ : B₁ ⟶ B₂) (φL : A ⟶ A₂) (βk : A₂ ⟶ A₃) (ρ : A₃ ⟶ B₂)
    (hβφ : β ≫ ψ₁ ≫ ψ₂ = φL ≫ βk ≫ ρ) {S₀ S₀' S₁ S₁' : D} (le : bS.obj B ≅ S₀)
    (le' : bS.obj B₂ ⟶ S₁) (γ : S₀ ⟶ S₀') (pmQ : S₀' ⟶ S₁') (m : S₁ ⟶ S₁')
    (hnat : γ ≫ pmQ = (le.inv ≫ bS.map ψ₁ ≫ bS.map ψ₂ ≫ le') ≫ m) :
    (bS.map β ≫ le.hom ≫ γ) ≫ pmQ = bS.map φL ≫ bS.map βk ≫ bS.map ρ ≫ le' ≫ m := by
  rw [Category.assoc, Category.assoc, hnat]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc]
  rw [hβφ]

/-- Moving an isomorphism across an equation `φL ≫ βk = β ≫ (ψ₁ ≫ ψ₂) ≫ c`. -/
theorem comp_eq_comp_comp_inv {C : Type*} [Category C] {A B B₁ B₂ A₂ A₃ : C}
    (β : A ⟶ B) (ψ₁ : B ⟶ B₁) (ψ₂ : B₁ ⟶ B₂) (φL : A ⟶ A₂) (βk : A₂ ⟶ A₃) (c : B₂ ⟶ A₃)
    [IsIso c] (h : φL ≫ βk = β ≫ (ψ₁ ≫ ψ₂) ≫ c) : β ≫ ψ₁ ≫ ψ₂ = φL ≫ βk ≫ inv c := by
  rw [reassoc_of% h]
  simp

/-- **Joint injectivity transported along an isomorphism.** If the maps `H(s k)` out of `H(P')` are
jointly injective and `a ≫ s k = f k ≫ Y k` for an isomorphism `a : P ⟶ P'`, then the maps
`H(f k)` out of `H(P)` are jointly injective. -/
theorem eq_zero_of_forall_map_eq_zero_of_isIso {D : Type*} [Category D] {R : Type u} [Ring R]
    (H : D ⥤ ModuleCat.{u} R) {ι : Type*} {P P' : D} (a : P ⟶ P') [IsIso a]
    {Q Q' : ι → D} (f : ∀ k, P ⟶ Q k) (s : ∀ k, P' ⟶ Q' k) (Y : ∀ k, Q k ⟶ Q' k)
    (key : ∀ k, a ≫ s k = f k ≫ Y k)
    (hinj : ∀ c : H.obj P', (∀ k, (H.map (s k)).hom c = 0) → c = 0)
    (c : H.obj P) (hc : ∀ k, (H.map (f k)).hom c = 0) : c = 0 := by
  have h0 : (H.map a).hom c = 0 := hinj _ fun k => by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, key k, Functor.map_comp,
      ModuleCat.comp_apply, hc k, map_zero]
  have := congrArg (H.map (inv a)).hom h0
  rwa [← ModuleCat.comp_apply, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    ModuleCat.id_apply, map_zero] at this

/-- A morphism stays zero after cancelling isomorphisms on both sides of its image under a
functor. -/
theorem map_eq_zero_of_iso_comp_comp_iso {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms D] (G : C ⥤ D) {X Y Z W : C} (a : X ⟶ Y) (f : Y ⟶ Z) (b : Z ⟶ W)
    [IsIso a] [IsIso b] (h : G.map (a ≫ f ≫ b) = 0) : G.map f = 0 := by
  rw [G.map_comp, G.map_comp] at h
  simpa using congrArg (fun x => inv (G.map a) ≫ x ≫ inv (G.map b)) h

/-- A morphism stays zero after cancelling an isomorphism on the left of its image under a
functor. -/
theorem map_eq_zero_of_iso_comp {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms D] (G : C ⥤ D) {X Y Z : C} (a : X ⟶ Y) (f : Y ⟶ Z)
    [IsIso a] (h : G.map (a ≫ f) = 0) : G.map f = 0 := by
  rw [G.map_comp] at h
  simpa using congrArg (fun x => inv (G.map a) ≫ x) h

/-- If `(a⁻¹ ≫ f) ≫ e` vanishes for isomorphisms `a` and `e`, then `f` vanishes. -/
theorem eq_zero_of_inv_comp_comp_hom_eq_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B M D : C} (a : A ≅ B) (f : A ⟶ M) (e : M ≅ D) (h : (a.inv ≫ f) ≫ e.hom = 0) : f = 0 := by
  simpa using congrArg (fun x => a.hom ≫ x ≫ e.inv) h

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-! ### The section of the fibre lifted to the affine neighbourhood -/

/-- **[Stacks, Tag 0BF2], the cohomological half, over an affine base.** Let
`p : P ⟶ Spec R` and the `i k ≫ p` be flat, proper and of finite presentation, let `ℒ` be
invertible on `P` with every `(i k)^*ℒ` trivial, and let `tF : F ⟶ P`, `tX k : FX k ⟶ X k` be the
base changes along `Spec χ` for a homomorphism `χ : R ⟶ K` to a field, with
`isk k : FX k ⟶ F` the base change of `i k`. If `ℒ` is trivial on `F`, if
`𝒪_{Spec K} ⟶ ps_* 𝒪_F` and every `𝒪_{Spec K} ⟶ (isk k ≫ ps)_* 𝒪_{FX k}` are isomorphisms, and
if the pullback maps `H¹(F, 𝒪_F) ⟶ H¹(FX k, 𝒪_{FX k})` are jointly injective, then there is
`σ : 𝒪_P ⟶ ℒ` whose pullback to `F` is nonzero. -/
theorem exists_unit_hom_modulePullback_ne_zero_of_injective_H1
    {R : CommRingCat.{u}} {K : Type u} [Field K] (χ : R ⟶ CommRingCat.of K)
    {P : Scheme.{u}} (p : P ⟶ Spec R) [Flat p] [IsProper p] (hpfp : FinitePresentation p)
    {ι : Type u} [Finite ι] (X : ι → Scheme.{u}) (i : ∀ k, X k ⟶ P)
    (hflat : ∀ k, Flat (i k ≫ p)) (hprop : ∀ k, IsProper (i k ≫ p))
    (hfp : ∀ k, FinitePresentation (i k ≫ p))
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    [IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L]
    (htriv : ∀ k, IsTrivial (X k).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (X k).IsSheaf)
      ((modulePullback (i k).toLRSHom.toShHom).obj L))
    {F : Scheme.{u}} (tF : F ⟶ P) (ps : F ⟶ Spec (CommRingCat.of K))
    (hF : IsPullback tF ps p (Spec.map χ))
    (hFO : IsIso (structureSheafHom ps.toLRSHom.toShHom))
    (hFtriv : IsTrivial F.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) F.IsSheaf)
      ((modulePullback tF.toLRSHom.toShHom).obj L))
    (FX : ι → Scheme.{u}) (isk : ∀ k, FX k ⟶ F) (tX : ∀ k, FX k ⟶ X k)
    (hX : ∀ k, IsPullback (tX k) (isk k ≫ ps) (i k ≫ p) (Spec.map χ))
    (hXF : ∀ k, tX k ≫ i k = isk k ≫ tF)
    (hXO : ∀ k, IsIso (structureSheafHom (isk k ≫ ps).toLRSHom.toShHom))
    (hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace)) 1).obj
        ((sectionsOverBase ps.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap ps.toLRSHom.toShHom (isk k).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace)))))).hom c = 0) →
        c = 0) :
    ∃ σ : _root_.SheafOfModules.unit (structureSheafRing P.toRingedSpace) ⟶ L,
      (modulePullback tF.toLRSHom.toShHom).map σ ≠ 0 := by
  classical
  -- notation
  let g := (Spec.map χ).toLRSHom.toShHom
  let p₀ := p.toLRSHom.toShHom
  let gP := tF.toLRSHom.toShHom
  let ps₀ := ps.toLRSHom.toShHom
  have sqA : gP ≫ p₀ = ps₀ ≫ g := comp_toShHom_of_comm hF.w
  let 𝓛 := (DerivedCategory.singleFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) 0).obj L
  let E := (derivedPushforward p₀).obj 𝓛
  let EX : ι → _ := fun k => (derivedPushforward ((i k).toLRSHom.toShHom ≫ p₀)).obj
    ((derivedPullback (i k).toLRSHom.toShHom).obj 𝓛)
  let φ : ∀ k, E ⟶ EX k := fun k =>
    (derivedPushforward p₀).map ((derivedAdjunction (i k).toLRSHom.toShHom).unit.app 𝓛) ≫
      (derivedPushforwardCompIso (i k).toLRSHom.toShHom p₀).hom.app
        ((derivedPullback (i k).toLRSHom.toShHom).obj 𝓛)
  have := hpfp.1
  have := hpfp.2.1
  have := hpfp.2.2
  have hLinv : IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L := ‹_›
  have hLflat :
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := P.toRingedSpace.sheaf) L :=
    Stacks.SheafOfModules.isFlat_of_isInvertible (X := P.toRingedSpace) L hLinv
  have hLq : L.IsQuasicoherent := @AlgebraicGeometry.isQuasicoherent_of_isInvertible _ L hLinv
  have h𝓛 : RingedSpace.IsPerfect (X := P.toRingedSpace) 𝓛 :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L).symm
      (@Stacks.Chow.isPerfect_singleZero P L hLinv)
  have hB := isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat p hpfp
    inferInstance inferInstance 𝓛 h𝓛
  have hEq : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent :=
    fun n => isQuasicoherent_homology_derivedPushforward_single_zero p L hLq n
  -- the faces
  let M : ∀ k, _root_.SheafOfModules.{u} (structureSheafRing (X k).toRingedSpace) :=
    fun k => (modulePullback (i k).toLRSHom.toShHom).obj L
  have hMinv : ∀ k, IsInvertible (X k).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (X k).IsSheaf) (M k) :=
    fun k => Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ L hLinv
  let ρ : ∀ k, (derivedPullback (i k).toLRSHom.toShHom).obj 𝓛 ≅
      (DerivedCategory.singleFunctor _ 0).obj (M k) := fun k =>
    Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso _ L hLflat
  have hBX : ∀ k, _ := fun k =>
    isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat (i k ≫ p) (hfp k)
      (hprop k) (hflat k) ((derivedPullback (i k).toLRSHom.toShHom).obj 𝓛)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ 𝓛 h𝓛)
  have hEXq : ∀ k (n : ℤ),
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj (EX k)).IsQuasicoherent := by
    intro k n
    have := (hfp k).2.1
    have := (hfp k).2.2
    exact isQuasicoherent_of_iso _ _ _
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
        ((derivedPushforward ((i k).toLRSHom.toShHom ≫ p₀)).mapIso (ρ k)).symm)
      (isQuasicoherent_homology_derivedPushforward_single_zero (i k ≫ p) (M k)
        (@AlgebraicGeometry.isQuasicoherent_of_isInvertible _ (M k) (hMinv k)) n)
  -- the base change isomorphisms
  have hβE : IsIso (derivedBaseChangeMap gP ps₀ p₀ g sqA 𝓛) := hB.2 (Spec.map χ) ps tF hF
  let gX : ∀ k, (FX k).toRingedSpace ⟶ (X k).toRingedSpace := fun k => (tX k).toLRSHom.toShHom
  let i₀ : ∀ k, (X k).toRingedSpace ⟶ P.toRingedSpace := fun k => (i k).toLRSHom.toShHom
  let is₀ : ∀ k, (FX k).toRingedSpace ⟶ F.toRingedSpace := fun k => (isk k).toLRSHom.toShHom
  have sqC : ∀ k, gX k ≫ i₀ k = is₀ k ≫ gP := fun k => comp_toShHom_of_comm (hXF k)
  have hβX : ∀ k, IsIso (derivedBaseChangeMap (gX k) (is₀ k ≫ ps₀) (i₀ k ≫ p₀) g
      (Stacks.Cohomology.DerivedBaseChange.comp_square (gX k) (is₀ k) (i₀ k) gP ps₀ p₀ g
        (sqC k) sqA) ((derivedPullback (i₀ k)).obj 𝓛)) :=
    fun k => (hBX k).2 (Spec.map χ) (isk k ≫ ps) (tX k) (hX k)
  -- the fibre of `ℒ` and of its restrictions are trivial
  let γ : (derivedPullback gP).obj 𝓛 ≅ (DerivedCategory.singleFunctor _ 0).obj
      (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace)) :=
    Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso gP L hLflat ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso hFtriv.some
  let γQ := γ ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).app
      (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace))
  let δ : ∀ k, (derivedPullback (gX k)).obj ((derivedPullback (i₀ k)).obj 𝓛) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing (FX k).toRingedSpace)) := fun k =>
    (derivedPullback (gX k)).mapIso (ρ k ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
      (htriv k).some) ≪≫ Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso (gX k)
  -- the fibre cohomology of `E`, read on `F`
  let A₀ :
      (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).obj
      ((derivedPullback g).obj E) ⟶
      (sectionsOverBase ps₀).obj ((DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace))) :=
    (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).map
      (derivedBaseChangeMap gP ps₀ p₀ g sqA 𝓛) ≫
    (lerayIso ps₀).hom.app ((derivedPullback gP).obj 𝓛) ≫ (sectionsOverBase ps₀).map γ.hom
  have hA₀ : IsIso A₀ := by dsimp only [A₀]; infer_instance
  let Aq :
      (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).obj
      ((derivedPullback g).obj E) ⟶
      (sectionsOverBase ps₀).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace)))) :=
    (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).map
      (derivedBaseChangeMap gP ps₀ p₀ g sqA 𝓛) ≫
    (lerayIso ps₀).hom.app ((derivedPullback gP).obj 𝓛) ≫ (sectionsOverBase ps₀).map γQ.hom
  have hAq : IsIso Aq := by dsimp only [Aq]; infer_instance
  let AX : ∀ k,
      (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).obj
      ((derivedPullback g).obj (EX k)) ⟶
      (sectionsOverBase (is₀ k ≫ ps₀)).obj ((DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing (FX k).toRingedSpace))) := fun k =>
    (Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace).map
      (derivedBaseChangeMap (gX k) (is₀ k ≫ ps₀) (i₀ k ≫ p₀) g
        (Stacks.Cohomology.DerivedBaseChange.comp_square (gX k) (is₀ k) (i₀ k) gP ps₀ p₀ g
          (sqC k) sqA) ((derivedPullback (i₀ k)).obj 𝓛)) ≫
      (lerayIso (is₀ k ≫ ps₀)).hom.app
        ((derivedPullback (gX k)).obj ((derivedPullback (i₀ k)).obj 𝓛)) ≫
      (sectionsOverBase (is₀ k ≫ ps₀)).map (δ k).hom
  have hAX : ∀ k, IsIso (AX k) := fun k => by dsimp only [AX]; infer_instance
  have h1 : ∀ c : (MinimalComplexFunctoriality.fibreHomology χ 1).obj E,
      (∀ k, (MinimalComplexFunctoriality.fibreHomology χ 1).map (φ k) c = 0) → c = 0 := by
    intro c hc
    let Q₀ := DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace)))
    let bS := Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace
    let H₁ := DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace)) 1
    have key : ∀ k, ∃ Y, Aq ≫ sectionsPullbackMap ps₀ (is₀ k) Q₀ =
        bS.map ((derivedPullback g).map (φ k)) ≫ Y := by
      intro k
      let α := (Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare (gX k) (is₀ k) (i₀ k) gP
        (sqC k)).natTrans.app 𝓛
      have hα : IsIso α := by
        dsimp only [α, Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare,
          Stacks.Cohomology.DerivedBaseChange.Mate.derivedPullbackSquare]
        infer_instance
      have hpb := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_pullbackMap (i₀ k) p₀
        (is₀ k) ps₀ (gX k) gP g (sqC k) sqA 𝓛
      refine ⟨bS.map (derivedBaseChangeMap (gX k) (is₀ k ≫ ps₀) (i₀ k ≫ p₀) g
          (Stacks.Cohomology.DerivedBaseChange.comp_square (gX k) (is₀ k) (i₀ k) gP ps₀ p₀ g
            (sqC k) sqA) ((derivedPullback (i₀ k)).obj 𝓛)) ≫
        bS.map (inv ((derivedPushforward (is₀ k ≫ ps₀)).map α)) ≫
        (lerayIso (is₀ k ≫ ps₀)).hom.app _ ≫
        (sectionsOverBase (is₀ k ≫ ps₀)).map ((derivedPullback (is₀ k)).map γQ.hom), ?_⟩
      exact sectionsPullbackMap_chase bS _ _ _ _ _ _ (comp_eq_comp_comp_inv _ _ _ _ _ _ hpb)
        ((lerayIso ps₀).app _) _ _ _ _
        (Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap_naturality ps₀ (is₀ k) γQ.hom)
    exact eq_zero_of_forall_map_eq_zero_of_isIso H₁ Aq
      (fun k => bS.map ((derivedPullback g).map (φ k)))
      (fun k => sectionsPullbackMap ps₀ (is₀ k) Q₀) _ (fun k => (key k).choose_spec) hinj c hc
  have hdim : ∀ k, Module.finrank K
      ((MinimalComplexFunctoriality.fibreHomology χ 0).obj (EX k)) ≤ 1 := fun k =>
    haveI : IsIso (structureSheafHom (is₀ k ≫ ps₀)) := hXO k
    haveI := hAX k
    (finrank_restrictScalars_homology_zero_eq_one (is₀ k ≫ ps₀) (AX k)).le
  let ε : (tilde.functor R).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.unitComplex R)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing (Spec R).toRingedSpace)) :=
    (tilde.functor R).mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app (ModuleCat.of R R)).symm ≪≫
      ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of R R)
  have hz : ∀ k, ∃ z : (tilde.functor R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.unitComplex R)) ⟶ EX k,
      (StandardModel.specDerivedPullback χ).map z ≠ 0 := by
    intro k
    let tr := (htriv k).some
    let sk : _root_.SheafOfModules.unit (structureSheafRing (X k).toRingedSpace) ⟶ M k := tr.inv
    have : IsIso sk := Iso.isIso_inv tr
    refine ⟨ε.hom ≫ PushforwardGenerator.derivedAdjoint (i₀ k ≫ p₀) (M k) sk ≫
      (derivedPushforward (i₀ k ≫ p₀)).map (ρ k).inv, fun h0 => ?_⟩
    have hne' :
        ¬ IsZero (_root_.SheafOfModules.unit (structureSheafRing (FX k).toRingedSpace)) := by
      have := @nontrivial_structureSheafRing_of_isIso K _ _ (is₀ k ≫ ps₀) (hXO k)
      exact Stacks.Nondegeneracy.not_isZero_unit_of_nontrivial _
        (op ((opensMap (is₀ k ≫ ps₀)).obj ⊤))
    exact PushforwardGenerator.derivedPullback_map_derivedAdjoint_ne_zero (i₀ k ≫ p₀) (M k)
      (gX k) (is₀ k ≫ ps₀) g
      (Stacks.Cohomology.DerivedBaseChange.comp_square (gX k) (is₀ k) (i₀ k) gP ps₀ p₀ g
        (sqC k) sqA) sk hne'
        (@map_eq_zero_of_iso_comp_comp_iso _ _ _ _ _ _ _ _ _ _ _ _ _ (Iso.isIso_hom ε)
          inferInstance h0)
  have hne : Nontrivial ((MinimalComplexFunctoriality.fibreHomology χ 0).obj E) :=
    haveI : IsIso (structureSheafHom ps₀) := hFO
    haveI := hA₀
    Module.nontrivial_of_finrank_pos (R := K)
      ((finrank_restrictScalars_homology_zero_eq_one ps₀ A₀).symm ▸ one_pos)
  obtain ⟨y, hy⟩ := MinimalComplexFunctoriality.exists_map_derivedPullback_ne_zero χ
    (Field.toIsField K) E hB.1 hEq EX (fun k => (hBX k).1) hEXq φ h1 hdim hz hne
  let y' := ε.inv ≫ y
  let σ := (DerivedCategory.singleFunctor _ 0).preimage
    ((Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso p₀).inv ≫
      ((derivedAdjunction p₀).homEquiv _ _).symm y')
  have hσ : PushforwardGenerator.derivedAdjoint p₀ L σ = y' := by
    rw [PushforwardGenerator.derivedAdjoint, Functor.map_preimage, Iso.hom_inv_id_assoc]
    exact Equiv.apply_symm_apply _ _
  refine ⟨σ, fun h0 => hy ?_⟩
  have h2 := PushforwardGenerator.derivedPullback_map_derivedAdjoint_eq_zero p₀ L gP ps₀ g sqA
    hLflat hβE σ h0
  rw [hσ] at h2
  exact @map_eq_zero_of_iso_comp _ _ _ _ _ _ _ _ _ _ _ (Iso.isIso_inv ε) h2

end AlgebraicGeometry.MinimalComplexFunctoriality

end
