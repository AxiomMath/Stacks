module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies

/-!
# The décalage of an invertible ideal as a functor

In Situation 0GT4 — a ringed space `(X, O_X)` together with a sheaf of ideals `ι : I ⟶ O_X`
which is invertible and a subsheaf — the Berthelot–Ogus operator `η_I` of `EtaSheaf.lean` is
defined on complexes of `I`-torsion-free `O_X`-modules, one complex at a time.  This file
organises the `I`-torsion-free modules into a full additive subcategory and promotes `η_I` to
a genuine functor on complexes over it.

## Main definitions

* `torsionFreeProperty`: being `I`-torsion-free, as an object property of `O_X`-modules, and
  `TorsionFreeModule`, the full subcategory it cuts out.
* `torsionFreeComplex`: the inclusion of complexes of `I`-torsion-free modules into complexes
  of `O_X`-modules.
* `etaFunctor`: the décalage `η_I`, as a functor from complexes of `I`-torsion-free
  `O_X`-modules to complexes of `O_X`-modules.

## Main results

* `isIdealTorsionFree_of_isZero`, `isIdealTorsionFree_biprod` and
  `isIdealTorsionFree_of_mono`: a zero module is `I`-torsion-free, a binary biproduct of
  `I`-torsion-free modules is `I`-torsion-free, and a submodule of an `I`-torsion-free module
  is `I`-torsion-free.  The first two are what makes `TorsionFreeModule` an additive category
  with a zero object and binary biproducts, recorded as the instances
  `torsionFreeProperty_containsZero` and `torsionFreeModule_hasBinaryBiproducts`.
* `etaMap_id` and `etaMap_comp`: the décalage of the identity is the identity and the décalage
  of a composite is the composite of the décalages; these are the functor laws of `etaFunctor`.

## Implementation notes

`IsIdealTorsionFree` is the vanishing of the degree-one ideal-power annihilator subsheaf of
Tag 0GT5, a supremum of subsheaves; the hypotheses available here are `Mono ι` together with
invertibility of `I`, that is condition (2) of Tag 0GT3 rather than condition (1) demanded by
Situation 0GT4, exactly as in `EtaSheaf.lean` and `EtaSheafQuasiIso.lean`.  Under those
hypotheses the equivalent criteria of Tag 0GT5 are unavailable — that tag is stated for an
ideal which is finite locally free of rank one — so the three closure statements are proved
from the definition.  Each runs the same way: a member of the family the annihilator is the
supremum of is a subsheaf whose sections are annihilated by the ideal, its inclusion is a
monomorphism, the image of a monomorphism is a subsheaf again (`monoRange`), and a subsheaf
of an `I`-torsion-free module with annihilated sections lies in the zero subsheaf.  For a
biproduct the two components are treated in turn: the kernel of one component maps
monomorphically to the other factor, hence vanishes, which makes the component itself a
monomorphism and so zero.  That half of the argument is about an arbitrary abelian category
and is stated there (`eq_zero_of_biprod_components`), which also keeps it inside the
elaboration budget.

The degree-`n` term of `η_I F` is a categorical fibre product whose definition this module may
not unfold, so a composite mixing `(η_I F).X n` with the projections of that fibre product is
type-correct only at `default` transparency and no rewrite can act on it.  The functor laws
are therefore proved at the `etaTerm` spelling, where every object is a fibre product, and
crossed to `η_I F` by `exact`, which elaborates at that transparency; this is the discipline
of `EtaSheafCohomology.lean` and `EtaSheafQuasiIso.lean`.

## References

* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 0GT3](https://stacks.math.columbia.edu/tag/0GT3)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0F8P](https://stacks.math.columbia.edu/tag/0F8P)
-/
@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open scoped ZeroObject

universe u v w

namespace Stacks.IdealTorsion.Eta

/-! ## Subsheaves cut out by a monomorphism -/

section Subsheaves

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A section in the image of a monomorphism lies in the subsheaf it cuts out. -/
private lemma mem_monoRange {N M : SheafOfModules.{w} R} (f : N ⟶ M) [Mono f] (U : Cᵒᵖ)
    (t : N.val.obj U) :
    (f.val.app U).hom t ∈ (monoRange f).toSubmodule.obj U :=
  ⟨t, rfl⟩

/-- A section of the zero subsheaf is zero. -/
private lemma eq_zero_of_mem_bot_submodule {M : SheafOfModules.{w} R} {U : Cᵒᵖ}
    {s : M.val.obj U} (hs : s ∈ (⊥ : M.Submodule).toSubmodule.obj U) : s = 0 := by
  rw [bot_submodule_obj] at hs
  exact (Submodule.mem_bot _).mp hs

/-- A section is in the zero subsheaf as soon as it is zero. -/
private lemma mem_bot_submodule {M : SheafOfModules.{w} R} {U : Cᵒᵖ}
    {s : M.val.obj U} (hs : s = 0) : s ∈ (⊥ : M.Submodule).toSubmodule.obj U := by
  rw [bot_submodule_obj]
  exact (Submodule.mem_bot _).mpr hs

/-- The zero morphism is zero on sections. -/
private lemma zero_app_hom {N M : SheafOfModules.{w} R} (U : Cᵒᵖ) (t : N.val.obj U) :
    ((0 : N ⟶ M).val.app U).hom t = 0 := by
  rw [show (0 : N ⟶ M).val = 0 from (SheafOfModules.forget R).map_zero _ _]
  rfl

end Subsheaves

/-- A monomorphism `j` has vanishing composite with `q` as soon as `q` kills every monomorphic
factorization through `j`, and every monomorphic piece with `q`-trivial image is killed by `j`. -/
private lemma comp_eq_zero_of_mono_factors {A : Type u} [Category.{v} A] [Preadditive A]
    [HasKernels A] {B Z P : A} (j : B ⟶ Z)
    [Mono j] (q : Z ⟶ P)
    (hq : ∀ {T : A} (p : T ⟶ B), Mono ((p ≫ j) ≫ q) → (p ≫ j) ≫ q = 0)
    (hk : ∀ {T : A} (p : T ⟶ B) [Mono p], (p ≫ j) ≫ q = 0 → p ≫ j = 0) : j ≫ q = 0 := by
  have h₂ : kernel.ι (j ≫ q) = 0 :=
    (cancel_mono j).mp
      ((hk _ ((Category.assoc _ _ _).trans (kernel.condition _))).trans zero_comp.symm)
  simpa using hq (𝟙 B) (by simpa using Preadditive.mono_of_kernel_zero h₂)

/-! ## Monomorphisms into a biproduct -/

section Biprod

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]

/-- A monomorphism into a biproduct whose second component vanishes is, on first components,
again a monomorphism. -/
private lemma mono_comp_fst {T M N : A} (g : T ⟶ M ⊞ N) [Mono g]
    (h : g ≫ biprod.snd = 0) : Mono (g ≫ biprod.fst) := by
  refine mono_of_mono_fac (show (g ≫ biprod.fst) ≫ biprod.inl = g from ?_)
  apply biprod.hom_ext <;> simp [h]

/-- A monomorphism into a biproduct whose first component vanishes is, on second components,
again a monomorphism. -/
private lemma mono_comp_snd {T M N : A} (g : T ⟶ M ⊞ N) [Mono g]
    (h : g ≫ biprod.fst = 0) : Mono (g ≫ biprod.snd) := by
  refine mono_of_mono_fac (show (g ≫ biprod.snd) ≫ biprod.inr = g from ?_)
  apply biprod.hom_ext <;> simp [h]

/-- A monomorphism into a biproduct both of whose components vanish on every monomorphic
factorization is zero. -/
private lemma eq_zero_of_biprod_components [HasKernels A] {B M N : A} (j : B ⟶ M ⊞ N) [Mono j]
    (hfst : ∀ {T : A} (p : T ⟶ B), Mono ((p ≫ j) ≫ biprod.fst) → (p ≫ j) ≫ biprod.fst = 0)
    (hsnd : ∀ {T : A} (p : T ⟶ B), Mono ((p ≫ j) ≫ biprod.snd) → (p ≫ j) ≫ biprod.snd = 0) :
    j = 0 := by
  have htot : ∀ {T : A} (g : T ⟶ M ⊞ N),
      g = (g ≫ biprod.fst) ≫ biprod.inl + (g ≫ biprod.snd) ≫ biprod.inr := by
    intro T g
    apply biprod.hom_ext <;> simp
  have hzsnd : j ≫ biprod.snd = 0 :=
    comp_eq_zero_of_mono_factors j biprod.snd hsnd fun p _ hz => by
      rw [htot (p ≫ j), hfst p (mono_comp_fst _ hz), hz, zero_comp, zero_comp, add_zero]
  have hzfst : j ≫ biprod.fst = 0 :=
    comp_eq_zero_of_mono_factors j biprod.fst hfst fun p _ hz => by
      rw [htot (p ≫ j), hsnd p (mono_comp_snd _ hz), hz, zero_comp, zero_comp, add_zero]
  rw [htot j, hzfst, hzsnd, zero_comp, zero_comp, add_zero]

end Biprod

/-! ## Torsion-freeness is inherited by submodules and biproducts -/

section Closure

variable (X : RingedSpace.{u})

local notation "Oₛ" => structureSheafRing X
local notation "𝒪ₛ" => SheafOfModules.unit Oₛ

/-- The condition cutting out the degree-one ideal-power annihilator, read on sections: every
restriction of the section is annihilated by every local section of the ideal. -/
private def IdealAnnihilates {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    (F : SheafOfModules.{u} Oₛ) {U : (Opens X)ᵒᵖ} (s : F.val.obj U) : Prop :=
  ∀ (V : Opens X) (hVU : V ≤ unop U) (a : I.val.obj (op V)),
    idealSection X i (op V) a • (F.val.map (homOfLE hVU).op).hom s = 0

/-- A submodule of `F` all of whose sections are annihilated by the ideal is one of the
submodules the degree-one annihilator subsheaf is the supremum of. -/
private lemma le_annihilatorSubsheaf {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    (F : SheafOfModules.{u} Oₛ) (N : F.Submodule)
    (hN : ∀ (U : (Opens X)ᵒᵖ) (s : F.val.obj U), s ∈ N.toSubmodule.obj U →
      IdealAnnihilates X i F s) :
    N ≤ idealPowerAnnihilatorSubsheaf X i F 1 := by
  refine le_sSup ?_
  intro U s hs V hVU a
  simpa only [Fin.prod_univ_one] using hN U s hs V hVU (a 0)

/-- A member of the family the degree-one annihilator subsheaf is the supremum of has
annihilated sections. -/
private lemma annihilates_of_mem {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    (F : SheafOfModules.{u} Oₛ) {N : F.Submodule}
    (hN : ∀ (U : (Opens X)ᵒᵖ) (s : F.val.obj U), s ∈ N.toSubmodule.obj U →
      ∀ (V : Opens X) (hVU : V ≤ unop U) (a : Fin 1 → I.val.obj (op V)),
        (∏ k, idealSection X i (op V) (a k)) •
          (F.val.map (homOfLE hVU).op).hom s = 0)
    (U : (Opens X)ᵒᵖ) (s : F.val.obj U) (hs : s ∈ N.toSubmodule.obj U) :
    IdealAnnihilates X i F s := by
  intro V hVU a
  simpa only [Fin.prod_univ_one] using hN U s hs V hVU (fun _ => a)

/-- Annihilation by the ideal is carried along a morphism of sheaves of modules. -/
private lemma idealAnnihilates_map {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {A M : SheafOfModules.{u} Oₛ} (f : A ⟶ M) {U : (Opens X)ᵒᵖ} {s : A.val.obj U}
    (hs : IdealAnnihilates X i A s) :
    IdealAnnihilates X i M ((f.val.app U).hom s) := by
  intro V hVU a
  have hnat : (M.val.map (homOfLE hVU).op).hom ((f.val.app U).hom s) =
      (f.val.app (op V)).hom ((A.val.map (homOfLE hVU).op).hom s) :=
    (PresheafOfModules.naturality_apply f.val (homOfLE hVU).op s).symm
  rw [hnat]
  have hsm := map_smul (f.val.app (op V)).hom (idealSection X i (op V) a)
    ((A.val.map (homOfLE hVU).op).hom s)
  exact hsm.symm.trans ((congrArg (f.val.app (op V)).hom (hs V hVU a)).trans (map_zero _))

/-- A monomorphism into an `I`-torsion-free module whose sections are annihilated by the ideal
is zero on sections. -/
private lemma apply_eq_zero_of_annihilated {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {A M : SheafOfModules.{u} Oₛ} (f : A ⟶ M) [Mono f]
    (hM : IsIdealTorsionFree X i M)
    (hA : ∀ (U : (Opens X)ᵒᵖ) (s : A.val.obj U),
      IdealAnnihilates X i M ((f.val.app U).hom s))
    (U : (Opens X)ᵒᵖ) (s : A.val.obj U) :
    (f.val.app U).hom s = 0 := by
  have hle : monoRange f ≤ idealPowerAnnihilatorSubsheaf X i M 1 := by
    refine le_annihilatorSubsheaf X i M _ ?_
    rintro V _ ⟨r, rfl⟩
    exact hA V r
  change idealPowerAnnihilatorSubsheaf X i M 1 = ⊥ at hM
  rw [hM] at hle
  exact eq_zero_of_mem_bot_submodule
    (SheafOfModules.Submodule.le_iff.mp hle U (mem_monoRange f U s))

/-- A monomorphism into an `I`-torsion-free module whose sections are annihilated by the ideal
is zero. -/
private lemma eq_zero_of_annihilated {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {A M : SheafOfModules.{u} Oₛ} (f : A ⟶ M) [Mono f]
    (hM : IsIdealTorsionFree X i M)
    (hA : ∀ (U : (Opens X)ᵒᵖ) (s : A.val.obj U),
      IdealAnnihilates X i M ((f.val.app U).hom s)) :
    f = 0 :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext <|
    LinearMap.ext fun s => apply_eq_zero_of_annihilated X i f hM hA U s

/-- **Torsion-freeness passes to submodules.**  A sheaf of modules admitting a monomorphism
into an `I`-torsion-free one is itself `I`-torsion-free. -/
private lemma isIdealTorsionFree_of_mono {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {A M : SheafOfModules.{u} Oₛ} (f : A ⟶ M) [Mono f]
    (hM : IsIdealTorsionFree X i M) :
    IsIdealTorsionFree X i A := by
  change idealPowerAnnihilatorSubsheaf X i A 1 = ⊥
  refine le_antisymm (sSup_le ?_) bot_le
  intro N hN U s hs
  refine mem_bot_submodule (Stacks.SheafOfModules.injective_app_of_mono f U ?_)
  rw [map_zero]
  refine apply_eq_zero_of_annihilated X i (A := N.toSheafOfModules) (N.ι ≫ f) hM ?_ U ⟨s, hs⟩
  intro V t
  exact idealAnnihilates_map X i f (annihilates_of_mem X i A hN V t.val t.property)

/-- **A zero sheaf of modules is `I`-torsion-free.** -/
private lemma isIdealTorsionFree_of_isZero {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {A : SheafOfModules.{u} Oₛ} (hA : IsZero A) :
    IsIdealTorsionFree X i A := by
  change idealPowerAnnihilatorSubsheaf X i A 1 = ⊥
  refine le_antisymm (sSup_le ?_) bot_le
  intro N hN U s hs
  exact mem_bot_submodule (Stacks.SheafOfModules.eq_zero_of_isZero hA U s)

/-- Annihilation by the ideal is inherited by a component of a morphism factoring through a
subsheaf with annihilated sections. -/
private lemma idealAnnihilates_comp {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {T B D P : SheafOfModules.{u} Oₛ} (p : T ⟶ B) (j : B ⟶ D) (q : D ⟶ P)
    (hann : ∀ (U : (Opens X)ᵒᵖ) (t : B.val.obj U), IdealAnnihilates X i D ((j.val.app U).hom t))
    (U : (Opens X)ᵒᵖ) (t : T.val.obj U) :
    IdealAnnihilates X i P ((((p ≫ j) ≫ q).val.app U).hom t) := by
  exact idealAnnihilates_map X i q (hann U ((p.val.app U).hom t))

/-- A monomorphism into a biproduct of `I`-torsion-free modules whose sections are annihilated
by the ideal vanishes. -/
private lemma eq_zero_of_annihilated_biprod {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    {B M N : SheafOfModules.{u} Oₛ} (j : B ⟶ M ⊞ N) [Mono j]
    (hM : IsIdealTorsionFree X i M) (hN : IsIdealTorsionFree X i N)
    (hann : ∀ (U : (Opens X)ᵒᵖ) (t : B.val.obj U),
      IdealAnnihilates X i (M ⊞ N) ((j.val.app U).hom t)) :
    j = 0 :=
  eq_zero_of_biprod_components j
    (fun p _ => eq_zero_of_annihilated X i _ hM (idealAnnihilates_comp X i p j biprod.fst hann))
    (fun p _ => eq_zero_of_annihilated X i _ hN (idealAnnihilates_comp X i p j biprod.snd hann))

/-- **Torsion-freeness passes to binary biproducts.** -/
private lemma isIdealTorsionFree_biprod {I : SheafOfModules.{u} Oₛ} (i : I ⟶ 𝒪ₛ)
    (M N : SheafOfModules.{u} Oₛ)
    (hM : IsIdealTorsionFree X i M) (hN : IsIdealTorsionFree X i N) :
    IsIdealTorsionFree X i (M ⊞ N) := by
  change idealPowerAnnihilatorSubsheaf X i (M ⊞ N) 1 = ⊥
  refine le_antisymm (sSup_le ?_) bot_le
  intro K hK U s hs
  have hj : K.ι = 0 :=
    eq_zero_of_annihilated_biprod X i K.ι hM hN
      (fun V t => annihilates_of_mem X i (M ⊞ N) hK V t.val t.property)
  refine mem_bot_submodule ?_
  have hv : ((K.ι.val.app U).hom (⟨s, hs⟩ : K.toSheafOfModules.val.obj U)) = s := rfl
  rw [← hv, hj]
  exact zero_app_hom U _

end Closure

/-! ## The subcategory of `I`-torsion-free modules -/

section Subcategory

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- Being `I`-torsion-free, as a property of sheaves of `O_X`-modules. -/
public def torsionFreeProperty {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) :
    ObjectProperty (SheafOfModules.{u} Oₓ) :=
  fun F => IsIdealTorsionFree X ι F

/-- The full subcategory of `I`-torsion-free sheaves of `O_X`-modules. -/
public abbrev TorsionFreeModule {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) : Type (u + 1) :=
  (torsionFreeProperty X ι).FullSubcategory

/-- The zero sheaf of modules is `I`-torsion-free. -/
public instance torsionFreeProperty_containsZero {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) :
    (torsionFreeProperty X ι).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isIdealTorsionFree_of_isZero X ι (isZero_zero _)⟩

/-- Binary biproducts of `I`-torsion-free sheaves of modules are `I`-torsion-free, so they are
computed in the full subcategory. -/
public instance torsionFreeModule_hasBinaryBiproducts {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) :
    HasBinaryBiproducts (TorsionFreeModule X ι) := by
  refine ⟨fun Y Z => ?_⟩
  let P : TorsionFreeModule X ι :=
    ⟨Y.obj ⊞ Z.obj, isIdealTorsionFree_biprod X ι Y.obj Z.obj Y.property Z.property⟩
  let b : BinaryBicone Y Z :=
    { pt := P
      fst := ObjectProperty.homMk biprod.fst
      snd := ObjectProperty.homMk biprod.snd
      inl := ObjectProperty.homMk biprod.inl
      inr := ObjectProperty.homMk biprod.inr
      inl_fst := ObjectProperty.hom_ext _ biprod.inl_fst
      inl_snd := ObjectProperty.hom_ext _ biprod.inl_snd
      inr_fst := ObjectProperty.hom_ext _ biprod.inr_fst
      inr_snd := ObjectProperty.hom_ext _ biprod.inr_snd }
  exact hasBinaryBiproduct_of_total b (ObjectProperty.hom_ext _ biprod.total)

/-- The inclusion of complexes of `I`-torsion-free modules into complexes of `O_X`-modules. -/
public noncomputable def torsionFreeComplex {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) :
    CochainComplex (TorsionFreeModule X ι) ℤ ⥤ CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  (torsionFreeProperty X ι).ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Every term of a complex of `I`-torsion-free modules is `I`-torsion-free. -/
public theorem torsionFreeComplex_torsionFree {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪)
    (F : CochainComplex (TorsionFreeModule X ι) ℤ) (n : ℤ) :
    IsIdealTorsionFree X ι (((torsionFreeComplex X ι).obj F).X n) :=
  (F.X n).property

end Subcategory

/-! ## The décalage as a functor on complexes of torsion-free modules -/

section Functoriality

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- Twisting by an ideal power is an equivalence, hence preserves binary biproducts, hence is
additive. -/
private instance tensorPowerFunctor_additive (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) :
    (Stacks.SheafOfModules.Invertible.tensorPowerEquivalence X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I n).functor.Additive :=
  have _h : Limits.PreservesBinaryBiproducts
      (Stacks.SheafOfModules.Invertible.tensorPowerEquivalence X.sheaf.obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I n).functor :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  Functor.additive_of_preservesBinaryBiproducts _

private lemma pmAdd (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (n : ℤ) {M N : SheafOfModules.{u} Oₓ} (a b : M ⟶ N) :
    idealPowerMap X I n (a + b) = idealPowerMap X I n a + idealPowerMap X I n b :=
  CategoryTheory.Functor.map_add
    (F := (Stacks.SheafOfModules.Invertible.tensorPowerEquivalence X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I n).functor)

/-! The degree-`n` term of `η_I F` is a categorical fibre product whose definition this module
may not unfold, so a composite mixing `(η_I F).X n` with the projections of that fibre product
is type-correct only at `default` transparency.  The functoriality of the décalage is therefore
proved one degree at a time at the `etaTerm` spelling, where every object is a fibre product,
and crossed to `η_I F` by `exact`, which elaborates at that transparency. -/

/-- On the first projection, the degreewise induced map is the twisted map in the same
degree. -/
private lemma etaTermMap_fst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (n : ℤ) :
    etaTermMap X I ι a n ≫ etaFst X I ι G n =
      etaFst X I ι F n ≫ idealPowerMap X I n (a.f n) :=
  pullback.lift_fst _ _ _

/-- On the second projection, the degreewise induced map is the twisted map in the next
degree. -/
private lemma etaTermMap_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (n : ℤ) :
    etaTermMap X I ι a n ≫ etaSnd X I ι G n =
      etaSnd X I ι F n ≫ idealPowerMap X I (n + 1) (a.f (n + 1)) :=
  pullback.lift_snd _ _ _

private lemma etaTermMap_id (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTermMap X I ι (𝟙 F) n = 𝟙 (etaTerm X I ι F n) := by
  refine pullback.hom_ext ?_ ?_
  · rw [etaTermMap_fst, HomologicalComplex.id_f, idealPowerMap_id, Category.comp_id,
      Category.id_comp]
  · rw [etaTermMap_snd, HomologicalComplex.id_f, idealPowerMap_id, Category.comp_id,
      Category.id_comp]

private lemma etaTermMap_comp (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G H : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (b : G ⟶ H) (n : ℤ) :
    etaTermMap X I ι (a ≫ b) n = etaTermMap X I ι a n ≫ etaTermMap X I ι b n := by
  refine pullback.hom_ext ?_ ?_
  · rw [etaTermMap_fst, HomologicalComplex.comp_f a b n, idealPowerMap_comp, Category.assoc,
      etaTermMap_fst,
      ← Category.assoc (etaTermMap X I ι a n) (etaFst X I ι G n)
        (idealPowerMap X I n (b.f n)),
      etaTermMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [etaTermMap_snd, HomologicalComplex.comp_f a b (n + 1), idealPowerMap_comp, Category.assoc,
      etaTermMap_snd,
      ← Category.assoc (etaTermMap X I ι a n) (etaSnd X I ι G n)
        (idealPowerMap X I (n + 1) (b.f (n + 1))),
      etaTermMap_snd]
    exact (Category.assoc _ _ _).symm

private lemma etaTermMap_add (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a b : F ⟶ G) (n : ℤ) :
    etaTermMap X I ι (a + b) n = etaTermMap X I ι a n + etaTermMap X I ι b n := by
  refine pullback.hom_ext ?_ ?_
  · rw [etaTermMap_fst, HomologicalComplex.add_f_apply a b n, pmAdd,
      Preadditive.comp_add, Preadditive.add_comp, etaTermMap_fst, etaTermMap_fst]
  · rw [etaTermMap_snd, HomologicalComplex.add_f_apply a b (n + 1), pmAdd,
      Preadditive.comp_add, Preadditive.add_comp, etaTermMap_snd, etaTermMap_snd]

/-- **The décalage of the identity is the identity.** -/
public theorem etaMap_id (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) :
    etaMap X I ι (𝟙 F) hF hF = 𝟙 (etaObj X I ι F hF) := by
  exact HomologicalComplex.hom_ext _ _ fun n => etaTermMap_id X I ι F n

/-- **The décalage of a composite is the composite of the décalages.** -/
public theorem etaMap_comp (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G H : CochainComplex (SheafOfModules.{u} Oₓ) ℤ}
    (a : F ⟶ G) (b : G ⟶ H)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n))
    (hH : ∀ n : ℤ, IsIdealTorsionFree X ι (H.X n)) :
    etaMap X I ι (a ≫ b) hF hH = etaMap X I ι a hF hG ≫ etaMap X I ι b hG hH := by
  exact HomologicalComplex.hom_ext _ _ fun n => etaTermMap_comp X I ι a b n

/-- **The décalage is additive on morphisms.** -/
public theorem etaMap_add (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ}
    (a b : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) :
    etaMap X I ι (a + b) hF hG = etaMap X I ι a hF hG + etaMap X I ι b hF hG := by
  exact HomologicalComplex.hom_ext _ _ fun n => etaTermMap_add X I ι a b n

/-- **The Berthelot–Ogus décalage as a functor** from complexes of `I`-torsion-free
`O_X`-modules to complexes of `O_X`-modules. -/
public noncomputable def etaFunctor (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I] :
    CochainComplex (TorsionFreeModule X ι) ℤ ⥤ CochainComplex (SheafOfModules.{u} Oₓ) ℤ where
  obj F := etaObj X I ι ((torsionFreeComplex X ι).obj F) (torsionFreeComplex_torsionFree X ι F)
  map {F G} a := etaMap X I ι ((torsionFreeComplex X ι).map a)
    (torsionFreeComplex_torsionFree X ι F) (torsionFreeComplex_torsionFree X ι G)
  map_id F := by
    rw [CategoryTheory.Functor.map_id]
    exact etaMap_id X I ι _ _
  map_comp {F G H} a b := by
    rw [CategoryTheory.Functor.map_comp]
    exact etaMap_comp X I ι _ _ _ _ _

/-- The inclusion of `I`-torsion-free modules is additive, hence so is its action on
complexes. -/
private instance torsionFreeComplex_additive (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) :
    (torsionFreeComplex X ι).Additive := by
  dsimp only [torsionFreeComplex]
  infer_instance

/-- **The décalage functor is additive.** -/
public instance etaFunctor_additive (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I] :
    (etaFunctor X I ι).Additive where
  map_add := by
    intro F G a b
    change etaMap X I ι ((torsionFreeComplex X ι).map (a + b)) _ _ = _
    rw [CategoryTheory.Functor.map_add]
    exact etaMap_add X I ι _ _ _ _

end Functoriality

end Stacks.IdealTorsion.Eta

end
