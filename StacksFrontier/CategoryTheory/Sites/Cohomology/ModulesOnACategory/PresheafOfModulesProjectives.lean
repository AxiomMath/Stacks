module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Presheaves of modules have enough projectives, at independent universes

Let `C'` be a category and let `R` be a presheaf of rings on it. The category of presheaves of
`R`-modules has enough projectives, and its colimits indexed by `ℕ` are exact. The point of this
file is that the site universes, the ring universe and the module universe are **independent**:
for `C' : Type u'` with `Category.{v'} C'` and `R` valued in `RingCat.{r}`, both conclusions are
obtained for `PresheafOfModules.{max w u' v' r}` with `w` arbitrary.

A projective generator is the free `R`-module `R ⊗_ℤ ℤ[Hom(-, U)]` on a representable, with the
representable lifted into the module universe. Maps out of it into `M` are the sections of `M`
over `U`, and an epimorphism of presheaves of modules is surjective on sections, so it is
projective; the coproduct of these over the elements of `M` then covers `M`.

Mathlib's free presheaf of modules `PresheafOfModules.free` cannot be used here: its output
module universe is pinned to the ring universe, so it produces objects of
`PresheafOfModules.{r} R` only, and no lifting of its input repairs this, since a module with
sections in `max w u' v' r` needs that many generators. The generator used instead is built from
extension of scalars `Stacks.SheafOfModules.tensorPresheaf`, whose ring and module universes are
already separated.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.gen` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.genMk`: the free `R`-module on a
  representable presheaf, and its canonical section over the representing object.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.fromGen`: the morphism out of that
  free module determined by a section.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.genCoproduct` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.fromGenCoproduct`: the coproduct,
  indexed by the elements of `M`, of the free modules on representables, and its map to `M`.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.gen_hom_ext`: a morphism out of the
  free module on a representable is determined by the image of the canonical section.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.gen_projective`: the free module on a
  representable is projective.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.enoughProjectives`: presheaves of
  modules have enough projectives.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.hasExactColimitsOfShapeNat`:
  colimits of presheaves of modules indexed by `ℕ` are exact.

## Implementation notes

The module universe is written `max w u' v' r` with a single free universe `w`, rather than
`max u v u' v' r` with two, because two universes occurring only inside one `max` are not
determined by the type of a declaration. Instantiating `w := max u v` recovers the latter.

The free abelian group on the lifted representable is only definitionally, not syntactically, the
sections of `Stacks.SheafOfModules.freeRepresentable`, and the restriction maps of a presheaf of
modules are semilinear, so the goals below are not type-correct at the transparency at which
`rewrite` and `simp` re-check their rewrites. The steps crossing that identification are
therefore written as explicit terms, built from `congrArg` and
`PresheafOfModules.naturality_apply`, rather than as rewrites; `gen_hom_ext` reduces to the
generators through the additive map `genUnitHom` so that only one such crossing is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.SheafOfModules

universe r w v' u'

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

variable {C' : Type u'} [Category.{v'} C'] (R : C'ᵒᵖ ⥤ RingCat.{r})

/-! ### The free module on a representable -/

/-- The free `R`-module `R ⊗_ℤ ℤ[Hom(-, U)]` on the representable presheaf of `U`, with the
representable lifted into the module universe. -/
abbrev gen (U : C') : PresheafOfModules.{max w u' v' r} R :=
  tensorPresheaf.{u', v', max w u' v', r} R (freeRepresentable.{u', v', max r w} U)

/-- The canonical section of `gen R U` over `U`: the generator indexed by the identity of `U`,
tensored with `1`. -/
abbrev genMk (U : C') : (gen.{r, w, v', u'} R U).obj (op U) :=
  (1 : R.obj (op U)) ⊗ₜ[ℤ]
    (FreeAbelianGroup.of (ULift.up (𝟙 U)) :
      (freeRepresentable.{u', v', max r w} U).obj (op U))

/-- Restricting the canonical section of `gen R U` along `f : X.unop ⟶ U` gives the generator
indexed by `f`, tensored with `1`. -/
lemma gen_map_genMk (U : C') (X : C'ᵒᵖ) (f : X.unop ⟶ U) :
    (gen.{r, w, v', u'} R U).map f.op (genMk.{r, w, v', u'} R U) =
      (1 : R.obj X) ⊗ₜ[ℤ]
        (FreeAbelianGroup.of (ULift.up f) : (freeRepresentable.{u', v', max r w} U).obj X) := by
  have hfree : (freeRepresentable.{u', v', max r w} U).map f.op
      (FreeAbelianGroup.of (ULift.up (𝟙 U))) = FreeAbelianGroup.of (ULift.up f) := by
    change FreeAbelianGroup.map
      (fun a : ULift.{max u' v' r w} (U ⟶ U) => ULift.up (f ≫ a.down))
      (FreeAbelianGroup.of (ULift.up (𝟙 U))) = _
    rw [FreeAbelianGroup.map_of_apply]
    simp only [Category.comp_id]
  refine Eq.trans (tensorPresheafRestrict_tmul.{u', v', max w u' v', r} R
    (freeRepresentable.{u', v', max r w} U) f.op (1 : R.obj (op U)) _) ?_
  rw [hfree, map_one]
  rfl

/-- A morphism out of `gen R U` sends the generator indexed by `f` to the restriction along `f`
of the image of the canonical section. -/
lemma app_tmul_of (U : C') {M : PresheafOfModules.{max w u' v' r} R}
    (φ : gen.{r, w, v', u'} R U ⟶ M) (X : C'ᵒᵖ) (f : X.unop ⟶ U) :
    φ.app X ((1 : R.obj X) ⊗ₜ[ℤ]
        (FreeAbelianGroup.of (ULift.up f) : (freeRepresentable.{u', v', max r w} U).obj X)) =
      M.map f.op (φ.app (op U) (genMk.{r, w, v', u'} R U)) :=
  (congrArg (fun z => φ.app X z) (gen_map_genMk.{r, w, v', u'} R U X f).symm).trans
    (PresheafOfModules.naturality_apply φ f.op (genMk.{r, w, v', u'} R U))

/-- The additive map on sections `z ↦ φ (1 ⊗ z)` attached to a morphism `φ` out of `gen R U`.
Since `1 ⊗ (-)` generates the sections of `gen R U` over the ring, `φ` is determined by it. -/
def genUnitHom (U : C') {M : PresheafOfModules.{max w u' v' r} R}
    (φ : gen.{r, w, v', u'} R U ⟶ M) (X : C'ᵒᵖ) :
    (freeRepresentable.{u', v', max r w} U).obj X →+ M.obj X where
  toFun z := φ.app X ((1 : R.obj X) ⊗ₜ[ℤ] z)
  map_zero' := by
    have h0 : ((1 : R.obj X) ⊗ₜ[ℤ]
        (0 : (freeRepresentable.{u', v', max r w} U).obj X)) = 0 :=
      TensorProduct.tmul_zero _ _
    exact (congrArg (fun z => φ.app X z) h0).trans (map_zero _)
  map_add' z₁ z₂ := by
    have hadd : ((1 : R.obj X) ⊗ₜ[ℤ] (z₁ + z₂)) =
        (1 : R.obj X) ⊗ₜ[ℤ] z₁ + (1 : R.obj X) ⊗ₜ[ℤ] z₂ :=
      TensorProduct.tmul_add _ _ _
    exact (congrArg (fun z => φ.app X z) hadd).trans (map_add _ _ _)

/-- **A morphism out of `gen R U` is determined by the image of the canonical section.** Two such
morphisms agreeing there agree on every generator, hence on every section. -/
lemma gen_hom_ext (U : C') {M : PresheafOfModules.{max w u' v' r} R}
    (φ ψ : gen.{r, w, v', u'} R U ⟶ M)
    (h : φ.app (op U) (genMk.{r, w, v', u'} R U) = ψ.app (op U) (genMk.{r, w, v', u'} R U)) :
    φ = ψ := by
  refine PresheafOfModules.hom_ext fun X => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  have key : genUnitHom.{r, w, v', u'} R U φ X = genUnitHom.{r, w, v', u'} R U ψ X :=
    FreeAbelianGroup.lift_ext _ _ fun x =>
      (app_tmul_of.{r, w, v', u'} R U φ X x.down).trans
        ((congrArg (fun s => M.map x.down.op s) h).trans
          (app_tmul_of.{r, w, v', u'} R U ψ X x.down).symm)
  have hsm : a • ((1 : R.obj X) ⊗ₜ[ℤ] y) = a ⊗ₜ[ℤ] y := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hχ (χ : gen.{r, w, v', u'} R U ⟶ M) :
      χ.app X (a ⊗ₜ[ℤ] y) = a • genUnitHom.{r, w, v', u'} R U χ X y :=
    (congrArg (fun z => χ.app X z) hsm.symm).trans (map_smul _ _ _)
  exact (hχ φ).trans ((congrArg (fun s => a • s) (DFunLike.congr_fun key y)).trans (hχ ψ).symm)

/-- The morphism `gen R U ⟶ M` determined by a section `m` of `M` over `U`. -/
def fromGen (U : C') {M : PresheafOfModules.{max w u' v' r} R} (m : M.obj (op U)) :
    gen.{r, w, v', u'} R U ⟶ M :=
  (exists_tensorPresheafLift_eval.{u', v', r, w} R U M m).choose

/-- `fromGen R U m` carries the canonical section of `gen R U` to `m`. -/
lemma fromGen_app_genMk (U : C') {M : PresheafOfModules.{max w u' v' r} R} (m : M.obj (op U)) :
    (fromGen.{r, w, v', u'} R U m).app (op U) (genMk.{r, w, v', u'} R U) = m :=
  (exists_tensorPresheafLift_eval.{u', v', r, w} R U M m).choose_spec

/-- **The free module on a representable is projective.** A morphism out of it is the image of
the canonical section, and an epimorphism of presheaves of modules is surjective on sections. -/
@[sga "4 V 2.3.1" "more general"]
instance gen_projective (U : C') : Projective (gen.{r, w, v', u'} R U) where
  factors {E N} g e he := by
    have := he
    obtain ⟨m, hm⟩ := PresheafOfModules.surjective_of_epi e (op U)
      (g.app (op U) (genMk.{r, w, v', u'} R U))
    refine ⟨fromGen.{r, w, v', u'} R U m, gen_hom_ext.{r, w, v', u'} R U _ _ ?_⟩
    change e.app (op U) ((fromGen.{r, w, v', u'} R U m).app (op U)
      (genMk.{r, w, v', u'} R U)) = _
    rw [fromGen_app_genMk.{r, w, v', u'} R U m]
    exact hm

/-! ### Enough projectives and exactness of countable colimits -/

variable (M : PresheafOfModules.{max w u' v' r} R)

/-- The coproduct, indexed by the elements of `M`, of the free modules on the representables of
the objects over which those elements are sections. -/
abbrev genCoproduct : PresheafOfModules.{max w u' v' r} R :=
  ∐ fun m : M.Elements => gen.{r, w, v', u'} R m.1.unop

/-- The morphism `genCoproduct R M ⟶ M` whose component at an element `m` of `M` carries the
canonical section to `m`. -/
abbrev fromGenCoproduct : genCoproduct.{r, w, v', u'} R M ⟶ M :=
  Sigma.desc fun m => fromGen.{r, w, v', u'} R m.1.unop m.2

/-- **Every section of `M` is in the image of `fromGenCoproduct R M`**, namely of the canonical
section of the summand indexed by that element of `M`. -/
lemma fromGenCoproduct_app_ι (m : M.Elements) :
    (fromGenCoproduct.{r, w, v', u'} R M).app m.1
      ((Sigma.ι (fun m : M.Elements => gen.{r, w, v', u'} R m.1.unop) m).app m.1
        (genMk.{r, w, v', u'} R m.1.unop)) = m.2 :=
  (ConcreteCategory.congr_hom
    ((PresheafOfModules.evaluation R m.1 ⋙ forget _).congr_map
      (Sigma.ι_comp_desc (fun m : M.Elements => fromGen.{r, w, v', u'} R m.1.unop m.2) m))
    (genMk.{r, w, v', u'} R m.1.unop)).trans
    (fromGen_app_genMk.{r, w, v', u'} R m.1.unop m.2)

/-- `fromGenCoproduct R M` is an epimorphism, being surjective on sections. -/
lemma epi_fromGenCoproduct : Epi (fromGenCoproduct.{r, w, v', u'} R M) :=
  PresheafOfModules.epi_of_surjective fun {X} x =>
    ⟨_, fromGenCoproduct_app_ι.{r, w, v', u'} R M (M.elementsMk X x)⟩

/-- **Presheaves of modules have enough projectives, at independent universes.** Every presheaf
of modules receives an epimorphism from the coproduct, indexed by its elements, of the free
modules on representables, and that coproduct is projective. -/
instance enoughProjectives : EnoughProjectives (PresheafOfModules.{max w u' v' r} R) :=
  ⟨fun M => ⟨{ p := genCoproduct.{r, w, v', u'} R M
               f := fromGenCoproduct.{r, w, v', u'} R M
               epi := epi_fromGenCoproduct.{r, w, v', u'} R M }⟩⟩

/-- **Colimits of presheaves of modules indexed by `ℕ` are exact**, since they are computed on
the underlying presheaves of abelian groups, where this is Grothendieck's AB5. -/
instance hasExactColimitsOfShapeNat :
    HasExactColimitsOfShape ℕ (PresheafOfModules.{max w u' v' r} R) :=
  letI : AB5OfSize.{0, 0, max w u' v' r, max w u' v' r + 1} AddCommGrpCat.{max w u' v' r} :=
    AB5OfSize_of_univLE.{0, 0, max w u' v' r, max w u' v' r} AddCommGrpCat.{max w u' v' r}
  HasExactColimitsOfShape.domain_of_functor ℕ (PresheafOfModules.toPresheaf R)

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
