module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.RingTheory.Cech.IdealCechComplexRestriction
public import StacksFrontier.RingTheory.Cech.SemilinearBaseChange

/-!
# The presheaf of extended alternating Čech complexes of a family of sections

Let `R` be a presheaf of commutative rings on a category `𝒞` and let `f₁, …, f_r` be a family of
sections of `R`, one over each object, compatible with restriction. This file assembles the
sectionwise extended alternating Čech complexes

`V ↦ K(R(V), (f₁|_V, …, f_r|_V))`

into a single complex of **presheaves of modules** over `R`, together with its augmentation onto
`R` and, for a subfamily, the restriction map between two such complexes.

This is the complex of presheaves `K_{U, I}^\bullet : U'/U ↦ K(𝒪(U'), I𝒪(U'))` of
[Stacks, Tag 099E], before sheafification, with the finitely generated ideal `I` of
[Stacks, Tag 099D] replaced by a generating family transported along the restriction maps of `R`.

## Main definitions

* `Stacks.CechPresheaf.cechAddPresheaf`: the degree-`p` term as a presheaf of abelian groups.
* `Stacks.CechPresheaf.cechPresheafTerm`: the same as a presheaf of `R`-modules.
* `Stacks.CechPresheaf.cechPresheafComplexNat`: **the presheaf of Čech complexes**, as a cochain
  complex of presheaves of modules indexed by `ℕ`.
* `Stacks.CechPresheaf.cechPresheafAugmentationNat`: its augmentation onto `R` placed in degree
  zero.
* `Stacks.CechPresheaf.cechPresheafRestrictNat`: **the restriction map** of the presheaf
  complexes of a family and of a subfamily of it.
* `Stacks.CechPresheaf.cechPresheafComplex`, `Stacks.CechPresheaf.cechPresheafAugmentation`,
  `Stacks.CechPresheaf.cechPresheafRestrict`: the same three, indexed by `ℤ` rather than by `ℕ`.

## Main results

* `Stacks.CechPresheaf.cechComplexIsoEvaluation`: **the sections over an object are the Čech
  complex of the ring of sections** at the restricted family.
* `Stacks.CechPresheaf.evaluation_map_cechPresheafRestrictNat`: the restriction map evaluates to
  `Cech.cechRestrict`, the restriction map of complexes of modules.
* `Stacks.CechPresheaf.cechPresheafRestrictNat_comp_augmentation`: **the restriction map is a map
  over `R`.**

## Implementation notes

The datum is a generating family rather than an ideal because a functorial choice of generators
of an ideal does not exist (`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`).

The complex is indexed by `ℕ` first, as `Cech.cechComplex` is, and then extended by zero along
`ComplexShape.embeddingUpNat`. Both indexings use the spelling `R ⋙ forget₂ CommRingCat RingCat`
of the presheaf of rings; the underlying presheaf of rings of a sheaf of commutative rings is that
composite only after `CategoryTheory.sheafCompose` is unfolded, which `rw` does not do.

`Stacks.CechPresheaf.cechComplexIsoEvaluation` is stated out of the Čech complex of `R(V)`, so
that the ring of the target `ModuleCat` is matched by unification rather than by synthesising a
`CommRing` instance on the image of `R(V)` under the forgetful functor.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.CechPresheaf

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w}) {r s : ℕ}
  (f : ∀ V : Cᵒᵖ, Fin r → R.obj V)
  (hf : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (i : Fin r), (R.map a).hom (f V i) = f W i)

/-- The degree-`p` term of the sectionwise Čech complex, as a presheaf of abelian groups: over
`V` it is `C^p(f₁|_V, …, f_r|_V; R(V))`, and restriction is the semilinear change of rings
`Stacks.CechSemilinear.termMap`. -/
def cechAddPresheaf (p : ℕ) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := AddCommGrpCat.of (Cech.cechTerm (f V) (R.obj V) p)
  map {V W} a := AddCommGrpCat.ofHom
    (CechSemilinear.termMap (R.map a).hom (f V) (f W) (hf a) p).toAddMonoidHom
  map_id V := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    change CechSemilinear.termMap (R.map (𝟙 V)).hom (f V) (f V) (hf (𝟙 V)) p x = x
    exact (CechSemilinear.termMap_congr (congrArg CommRingCat.Hom.hom (R.map_id V))
      (f V) (f V) (hf (𝟙 V)) (fun _ => rfl) p x).trans
      (CechSemilinear.termMap_id (f V) (fun _ => rfl) p x)
  map_comp {V W Z} a b := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    change CechSemilinear.termMap (R.map (a ≫ b)).hom (f V) (f Z) (hf (a ≫ b)) p x =
      CechSemilinear.termMap (R.map b).hom (f W) (f Z) (hf b) p
        (CechSemilinear.termMap (R.map a).hom (f V) (f W) (hf a) p x)
    have hcomp (i : Fin r) : ((R.map b).hom.comp (R.map a).hom) (f V i) = f Z i :=
      (congrArg (R.map b).hom (hf a i)).trans (hf b i)
    exact (CechSemilinear.termMap_congr (congrArg CommRingCat.Hom.hom (R.map_comp a b))
      (f V) (f Z) (hf (a ≫ b)) hcomp p x).trans
      (CechSemilinear.termMap_comp (R.map a).hom (R.map b).hom (f V) (f W) (f Z)
        (hf a) (hf b) hcomp p x).symm

/-- The degree-`p` term of the sectionwise Čech complex, as a presheaf of `R`-modules. -/
def cechPresheafTerm (p : ℕ) :
    PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) := by
  letI : ∀ V, Module ((R ⋙ forget₂ CommRingCat RingCat).obj V)
      ((cechAddPresheaf R f hf p).obj V) := fun V =>
    inferInstanceAs (Module (R.obj V) (Cech.cechTerm (f V) (R.obj V) p))
  exact PresheafOfModules.ofPresheaf (cechAddPresheaf R f hf p)
    (fun {_V _W} a c x =>
      (CechSemilinear.termMap (R.map a).hom (f _) (f _) (hf a) p).map_smulₛₗ c x)

/-- The Čech differential, as a map of presheaves of modules. -/
def cechPresheafDifferential (p : ℕ) :
    cechPresheafTerm R f hf p ⟶ cechPresheafTerm R f hf (p + 1) where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) p) ⟶
      ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) (p + 1))
    exact ModuleCat.ofHom (Cech.cechD (f V) (R.obj V) p)
  naturality {_V _W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (CechSemilinear.termMap_cechD (R.map a).hom _ _ (hf a) p x).symm

/-- **The presheaf of extended alternating Čech complexes.** Over each object it is the extended
alternating Čech complex of the ring of sections at the restricted family. -/
def cechPresheafComplexNat :
    CochainComplex (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) ℕ :=
  CochainComplex.of (cechPresheafTerm R f hf) (cechPresheafDifferential R f hf) fun p => by
    refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change Cech.cechD (f V) (R.obj V) (p + 1) (Cech.cechD (f V) (R.obj V) p x) = 0
    exact LinearMap.congr_fun (Cech.cechD_comp_cechD (f V) (R.obj V) p) x

/-- **The sections of the presheaf of Čech complexes over an object are the Čech complex of its
ring of sections**, at the restricted family. -/
def cechComplexIsoEvaluation (V : Cᵒᵖ) :
    Cech.cechComplex (f V) (R.obj V) ≅
      ((PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechPresheafComplexNat R f hf) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j h => by
    obtain rfl : i + 1 = j := h
    simp only [cechPresheafComplexNat, Cech.cechComplex, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.of_d]
    rfl

/-- The augmentation of the degree-zero term onto `R`: over each object it is the identification
of the degree-zero Čech term with the ring of sections. -/
def cechPresheafAugmentationZero :
    cechPresheafTerm R f hf 0 ⟶ PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat) where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) 0) ⟶
      ModuleCat.of (R.obj V) (R.obj V)
    exact ModuleCat.ofHom (Stacks.LocalCohomology.cechTermZeroEquiv (f V)
      (ModuleCat.of (R.obj V) (R.obj V))).toLinearMap
  naturality {_V _W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact CechSemilinear.cechTermZeroEquiv_termMap (R.map a).hom _ _ (hf a) x

/-- **The augmentation of the presheaf of Čech complexes onto `R`** placed in degree zero. -/
def cechPresheafAugmentationNat :
    cechPresheafComplexNat R f hf ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (cechPresheafAugmentationZero R f hf)

section Restrict

variable (g : ∀ V : Cᵒᵖ, Fin s → R.obj V)
  (hg : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (j : Fin s), (R.map a).hom (g V j) = g W j)
  (e : Fin r ↪o Fin s) (he : ∀ (V : Cᵒᵖ) (i : Fin r), g V (e i) = f V i)

/-- The degreewise restriction map onto a subfamily, as a map of presheaves of modules. -/
def cechPresheafTermRestrict (p : ℕ) :
    cechPresheafTerm R g hg p ⟶ cechPresheafTerm R f hf p where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechTerm (g V) (R.obj V) p) ⟶
      ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) p)
    exact ModuleCat.ofHom (Cech.cechTermRestrict (f V) (R.obj V) (g V) e (he V) p)
  naturality {V W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (CechSemilinear.termMap_cechTermRestrict (R.map a).hom (f V) (g V) (f W) (g W) e
      (hf a) (hg a) (he V) (he W) p x).symm

/-- **The restriction map of the presheaf of Čech complexes of a family onto that of a
subfamily.** -/
def cechPresheafRestrictNat :
    cechPresheafComplexNat R g hg ⟶ cechPresheafComplexNat R f hf where
  f p := cechPresheafTermRestrict R f hf g hg e he p
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    simp only [cechPresheafComplexNat, CochainComplex.of_d]
    refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (Cech.cechTermRestrict_comm (f V) (R.obj V) (g V) e (he V) p x).symm

/-- **The restriction map evaluates to the restriction map of complexes of modules.** -/
theorem evaluation_map_cechPresheafRestrictNat (V : Cᵒᵖ) :
    ((PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (cechPresheafRestrictNat R f hf g hg e he) =
        (cechComplexIsoEvaluation R g hg V).inv ≫
          Cech.cechRestrict (f V) (R.obj V) (g V) e (he V) ≫
            (cechComplexIsoEvaluation R f hf V).hom := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

/-- **The restriction map is a map over `R`**: it is compatible with the two augmentations. -/
theorem cechPresheafRestrictNat_comp_augmentation :
    cechPresheafRestrictNat R f hf g hg e he ≫ cechPresheafAugmentationNat R f hf =
      cechPresheafAugmentationNat R g hg := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show Stacks.LocalCohomology.cechTermZeroEquiv (f V) (ModuleCat.of (R.obj V) (R.obj V))
      (Cech.cechTermRestrict (f V) (R.obj V) (g V) e (he V) 0 x) =
    Stacks.LocalCohomology.cechTermZeroEquiv (g V) (ModuleCat.of (R.obj V) (R.obj V)) x
  exact congrArg (fun m : (Cech.cechComplex (g V) (R.obj V)).X 0 ⟶
      ModuleCat.of (R.obj V) (R.obj V) => m.hom x)
    (Stacks.IdealCechComplex.cechZeroIso_cechRestrict (f V) (g V) e (he V)
      (ModuleCat.of (R.obj V) (R.obj V)))

end Restrict

section Extend

/-- **The presheaf of Čech complexes, indexed by `ℤ`**: the `ℕ`-indexed complex extended by zero
along `ComplexShape.embeddingUpNat`. -/
abbrev cechPresheafComplex :
    CochainComplex (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) ℤ :=
  (cechPresheafComplexNat R f hf).extend ComplexShape.embeddingUpNat

/-- **The augmentation of the `ℤ`-indexed presheaf of Čech complexes onto `R`.** -/
def cechPresheafAugmentation :
    cechPresheafComplex R f hf ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) :=
  HomologicalComplex.extendMap (cechPresheafAugmentationNat R f hf)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) 0 0 rfl).hom

variable (g : ∀ V : Cᵒᵖ, Fin s → R.obj V)
  (hg : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (j : Fin s), (R.map a).hom (g V j) = g W j)
  (e : Fin r ↪o Fin s) (he : ∀ (V : Cᵒᵖ) (i : Fin r), g V (e i) = f V i)

/-- **The restriction map onto a subfamily, indexed by `ℤ`.** -/
abbrev cechPresheafRestrict : cechPresheafComplex R g hg ⟶ cechPresheafComplex R f hf :=
  HomologicalComplex.extendMap (cechPresheafRestrictNat R f hf g hg e he)
    ComplexShape.embeddingUpNat

/-- **The restriction map is a map over `R`**, in the `ℤ`-indexed form. -/
theorem cechPresheafRestrict_comp_augmentation :
    cechPresheafRestrict R f hf g hg e he ≫ cechPresheafAugmentation R f hf =
      cechPresheafAugmentation R g hg := by
  rw [cechPresheafAugmentation, cechPresheafAugmentation, ← Category.assoc,
    ← HomologicalComplex.extendMap_comp, cechPresheafRestrictNat_comp_augmentation]

end Extend

end Stacks.CechPresheaf

end
