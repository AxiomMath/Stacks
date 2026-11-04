module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.CochainReplacement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExtCochainComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PresheafOfModulesProjectives
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# The cochain complex computes the Ext groups of modules on a category

Let `C` be a small category carrying the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat` be a sheaf of
rings on it and let `G`, `F` be `O`-modules. The cochain complex `K^•(G, F)` of
`Stacks.CategoryExt.extCochainComplex` computes the extension groups,
`Ext^n_O(G, F) = H^n(K^•(G, F))` for all `n ≥ 0`, provided either

1. `G(U)` is a projective `O(U)`-module for every object `U` of `C`, or
2. for every arrow `U ⟶ V` of `C` the module `F(U)` is injective over `O(V)` through the
   restriction map `O(V) ⟶ O(U)`.

The hypothesis of (2) cannot be weakened to `F(U)` being an injective `O(U)`-module for every
object `U`: `Stacks.CategoryExt.ArrowCounterexample.injective_obj_and_not_nonempty_extAddEquiv_two`
gives, on the category with one non-identity arrow, an objectwise injective `F` and a `G` with
`Ext²_O(G, F)` not isomorphic to `H²(K^•(G, F))`.

## Main definitions

* `Stacks.CategoryExt.coinducedModule`: the product over the objects `U` of `C` of the modules
  coinduced from the sections over `U`, together with the embedding
  `Stacks.CategoryExt.toCoinducedModule` of a module into it.
* `Stacks.CategoryExt.extCochainFixedSourceDeltaFunctor` and
  `Stacks.CategoryExt.extCochainFixedTargetDeltaFunctor`: the cohomology of the cochain complex
  as a δ-functor of the target, respectively of the source.
* `Stacks.CategoryExt.extSourceDeltaFunctor` and `Stacks.CategoryExt.extTargetDeltaFunctor`: the
  `Ext` groups as a δ-functor of the target, respectively of the source.

## Main results

* `Stacks.CategoryExt.extAddEquivCohomology_of_objectwiseProjective` and
  `Stacks.CategoryExt.extAddEquivCohomology_of_arrowwiseInjective`: the two cases of the
  identification `Ext^n_O(G, F) = H^n(K^•(G, F))`, in every degree `n`.
* `Stacks.CategoryExt.extAddEquivCohomology_of_objectwiseProjective_zero` and
  `Stacks.CategoryExt.extAddEquivCohomology_of_arrowwiseInjective_zero`: both identifications
  are the canonical one in degree zero, where they carry the class of a morphism of modules to
  the class of its family of components.
* `Stacks.CategoryExt.extAddEquivCohomology_of_objectwiseProjective_delta` and
  `Stacks.CategoryExt.extAddEquivCohomology_of_arrowwiseInjective_delta`: both identifications
  intertwine the connecting map of a short exact sequence of modules with the cohomological
  connecting map of the corresponding short exact sequence of cochain complexes, which pins them
  down in every positive degree as well.
* `Stacks.CategoryExt.shortExact_extCochainComplexShortComplexRight` and
  `Stacks.CategoryExt.shortExact_extCochainComplexShortComplexLeft`: the exactness of the
  cochain construction in each variable, under the corresponding hypothesis.
* `Stacks.CategoryExt.isZero_coinducedModule_homology`: the cochain complex with coinduced
  target is acyclic in positive degrees.

## Implementation notes

The coinduced module is formed as one presheaf of modules whose sections over `V` are the
families of sections of `F` indexed by the arrows into `V`, rather than as a categorical product
of the modules coinduced from single objects.

The `Ext` groups are taken in the universe of the modules, which is required to contain the
universes of the objects and of the arrows of `C` and the universe of the rings, so that the
category of modules is Grothendieck abelian with `Ext` groups in that universe and the free
modules on representables exist there. The module universe is therefore written `max u v m`, and
the declarations about it are applied with explicit universe arguments, since a universe
occurring only inside a `max` is not determined by the type of a declaration.

The degree-`n` cochains are `Hom_{O(Uₙ)}(G(Uₙ), F(U₀))`, the `Hom` being taken over the ring at
the *far* end of the string, so exactness of `K^•(-, F)` asks that `F(U₀)` be injective over
`O(Uₙ)`, and not merely over `O(U₀)`; hence the arrowwise hypothesis of (2).

## References

* [Stacks Project, Tag 08S0](https://stacks.math.columbia.edu/tag/08S0)
* [Stacks Project, Tag 08RZ](https://stacks.math.columbia.edu/tag/08RZ)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v m t

namespace Stacks.CategoryExt

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ RingCat.{v}}

section Functoriality

variable {G G' F F' : PresheafOfModules.{m} O}

/-- The map of cochain complexes induced by a morphism of modules in each variable. -/
abbrev extCochainComplexMap (g : G' ⟶ G) (f : F ⟶ F') :
    extCochainComplex G F ⟶ extCochainComplex G' F' :=
  (extCochainComplexBifunctor C O).map (X := (op G, F)) (Y := (op G', F')) (g.op, f)

/-- The component of `extCochainComplexMap g f` in degree `n` sends a cochain `φ` to
`x ↦ f ∘ φ x ∘ g`, with `g` taken at the last object and `f` at the first object of `x`. -/
lemma extCochainComplexMap_f_apply (g : G' ⟶ G) (f : F ⟶ F') (n : ℕ)
    (φ : extCochain G F n) (x : ComposableArrows C n)
    (s : G'.obj (op (x.obj (Fin.last n)))) :
    ((extCochainComplexMap g f).f n φ : extCochain G' F' n) x s =
      f.app (op (x.obj 0)) (φ x (g.app (op (x.obj (Fin.last n))) s)) :=
  rfl

end Functoriality

section ZeroNaturality

variable {G G' F F' : PresheafOfModules.{m} O}

/-- Pre- and postcomposition with fixed morphisms of modules, on homomorphism groups. -/
def homCompHom (g : G' ⟶ G) (f : F ⟶ F') :
    AddCommGrpCat.of (G ⟶ F) ⟶ AddCommGrpCat.of (G' ⟶ F') :=
  AddCommGrpCat.ofHom
    { toFun := fun α ↦ g ≫ α ≫ f
      map_zero' := by rw [zero_comp, comp_zero]
      map_add' := fun α β ↦ by
        rw [Preadditive.add_comp, Preadditive.comp_add] }

/-- The identification of the degree-zero cycles with the homomorphism group is natural. -/
lemma extCochainComplexCyclesZeroIso_naturality (g : G' ⟶ G) (f : F ⟶ F') :
    HomologicalComplex.cyclesMap (extCochainComplexMap g f) 0 ≫
        (extCochainComplexCyclesZeroIso G' F').hom =
      (extCochainComplexCyclesZeroIso G F).hom ≫ homCompHom g f := by
  apply ConcreteCategory.hom_ext
  intro c
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  have hk : (extCochainComplex G' F').iCycles 0
        (HomologicalComplex.cyclesMap (extCochainComplexMap g f) 0 c) =
      (extCochainComplexMap g f).f 0 ((extCochainComplex G F).iCycles 0 c) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ _) c
  show ((extCochainComplex G' F').iCycles 0
      (HomologicalComplex.cyclesMap (extCochainComplexMap g f) 0 c) : extCochain G' F' 0)
      (ComposableArrows.mk₀ U.unop) s = _
  rw [hk]
  rfl

/-- The degree-zero comparison is natural in both modules. -/
lemma extCochainComplexHomologyZeroIso_naturality (g : G' ⟶ G) (f : F ⟶ F') :
    HomologicalComplex.homologyMap (extCochainComplexMap g f) 0 ≫
        (extCochainComplexHomologyZeroIso G' F').hom =
      (extCochainComplexHomologyZeroIso G F).hom ≫ homCompHom g f := by
  dsimp only [extCochainComplexHomologyZeroIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality, Category.assoc,
    extCochainComplexCyclesZeroIso_naturality, Category.assoc]

end ZeroNaturality

section Exactness

/-- Evaluating a short exact sequence of modules at an object and restricting scalars along an
arrow of the category gives a short exact sequence of modules. -/
lemma shortExact_evaluation_restrictScalars {S : ShortComplex (PresheafOfModules.{m} O)}
    (hS : S.ShortExact) {X Y : C} (u : X ⟶ Y) :
    ((S.map (PresheafOfModules.evaluation O (op X))).map
      (ModuleCat.restrictScalars (O.map u.op).hom)).ShortExact := by
  have hE : (S.map (PresheafOfModules.evaluation O (op X))).ShortExact := hS.map_of_exact _
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S.map (PresheafOfModules.evaluation O (op X)))).mp hE.exact))
    ((ModuleCat.mono_iff_injective _).mpr hE.moduleCat_injective_f)
    ((ModuleCat.epi_iff_surjective _).mpr hE.moduleCat_surjective_g)

variable (G F : PresheafOfModules.{m} O) (S : ShortComplex (PresheafOfModules.{m} O))

/-- A cochain component with values in the quotient of a short exact sequence of targets lifts
to the middle term, when the source module is projective at the relevant object. -/
lemma exists_extCochainComponent_lift_right (hG : ∀ U : C, Projective (G.obj (op U)))
    (hS : S.ShortExact) {X Y : C} (u : X ⟶ Y)
    (χ : G.obj (op Y) →ₛₗ[(O.map u.op).hom] S.X₃.obj (op X)) :
    ∃ χ' : G.obj (op Y) →ₛₗ[(O.map u.op).hom] S.X₂.obj (op X),
      ∀ s, S.g.app (op X) (χ' s) = χ s := by
  let T := (S.map (PresheafOfModules.evaluation O (op X))).map
    (ModuleCat.restrictScalars (O.map u.op).hom)
  have hT : T.ShortExact := shortExact_evaluation_restrictScalars hS u
  let : Projective (G.obj (op Y)) := hG Y
  let : Epi T.g := hT.epi_g
  let χ₀ : G.obj (op Y) ⟶ T.X₃ :=
    (ModuleCat.semilinearMapAddEquiv (O.map u.op).hom (G.obj (op Y)) (S.X₃.obj (op X))) χ
  let ψ₀ : G.obj (op Y) ⟶ T.X₂ := Projective.factorThru χ₀ T.g
  have hψ₀ : ψ₀ ≫ T.g = χ₀ := Projective.factorThru_comp χ₀ T.g
  exact ⟨(ModuleCat.semilinearMapAddEquiv (O.map u.op).hom _ _).symm ψ₀,
    fun s ↦ ConcreteCategory.congr_hom hψ₀ s⟩

/-- A cochain component killed by the second map of a short exact sequence of targets comes
from the first, when the source module is projective at the relevant object. -/
lemma exists_extCochainComponent_desc_right (hG : ∀ U : C, Projective (G.obj (op U)))
    (hS : S.ShortExact) {X Y : C} (u : X ⟶ Y)
    (χ : G.obj (op Y) →ₛₗ[(O.map u.op).hom] S.X₂.obj (op X))
    (hχ : ∀ s, S.g.app (op X) (χ s) = 0) :
    ∃ χ' : G.obj (op Y) →ₛₗ[(O.map u.op).hom] S.X₁.obj (op X),
      ∀ s, S.f.app (op X) (χ' s) = χ s := by
  let T := (S.map (PresheafOfModules.evaluation O (op X))).map
    (ModuleCat.restrictScalars (O.map u.op).hom)
  have hT : T.ShortExact := shortExact_evaluation_restrictScalars hS u
  let : Projective (G.obj (op Y)) := hG Y
  let χ₀ : G.obj (op Y) ⟶ T.X₂ :=
    (ModuleCat.semilinearMapAddEquiv (O.map u.op).hom (G.obj (op Y)) (S.X₂.obj (op X))) χ
  have hz : χ₀ ≫ T.g = 0 := ModuleCat.hom_ext (LinearMap.ext hχ)
  let ψ₀ : G.obj (op Y) ⟶ T.X₁ := hT.exact.liftFromProjective χ₀ hz
  have hψ₀ : ψ₀ ≫ T.f = χ₀ := hT.exact.liftFromProjective_comp χ₀ hz
  exact ⟨(ModuleCat.semilinearMapAddEquiv (O.map u.op).hom _ _).symm ψ₀,
    fun s ↦ ConcreteCategory.congr_hom hψ₀ s⟩

/-- A cochain component on the first term of a short exact sequence of sources extends to the
middle term, when the target module stays injective after restriction of scalars. -/
lemma exists_extCochainComponent_lift_left
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (hS : S.ShortExact) {X Y : C} (u : X ⟶ Y)
    (χ : S.X₁.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X)) :
    ∃ χ' : S.X₂.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X),
      ∀ s, χ' (S.f.app (op Y) s) = χ s := by
  let E := S.map (PresheafOfModules.evaluation O (op Y))
  have hE : E.ShortExact := hS.map_of_exact _
  let : Injective ((ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X))) := hF u
  let : Mono E.f := hE.mono_f
  let χ₀ : E.X₁ ⟶ (ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X)) :=
    (ModuleCat.semilinearMapAddEquiv (O.map u.op).hom (S.X₁.obj (op Y)) (F.obj (op X))) χ
  let ψ₀ : E.X₂ ⟶ (ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X)) :=
    Injective.factorThru χ₀ E.f
  have hψ₀ : E.f ≫ ψ₀ = χ₀ := Injective.comp_factorThru χ₀ E.f
  exact ⟨(ModuleCat.semilinearMapAddEquiv (O.map u.op).hom _ _).symm ψ₀,
    fun s ↦ ConcreteCategory.congr_hom hψ₀ s⟩

/-- A cochain component vanishing on the first term of a short exact sequence of sources comes
from the quotient, when the target module stays injective after restriction of scalars. -/
lemma exists_extCochainComponent_desc_left
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (hS : S.ShortExact) {X Y : C} (u : X ⟶ Y)
    (χ : S.X₂.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X))
    (hχ : ∀ s, χ (S.f.app (op Y) s) = 0) :
    ∃ χ' : S.X₃.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X),
      ∀ s, χ' (S.g.app (op Y) s) = χ s := by
  let E := S.map (PresheafOfModules.evaluation O (op Y))
  have hE : E.ShortExact := hS.map_of_exact _
  let : Injective ((ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X))) := hF u
  let χ₀ : E.X₂ ⟶ (ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X)) :=
    (ModuleCat.semilinearMapAddEquiv (O.map u.op).hom (S.X₂.obj (op Y)) (F.obj (op X))) χ
  have hz : E.f ≫ χ₀ = 0 := ModuleCat.hom_ext (LinearMap.ext hχ)
  let ψ₀ : E.X₃ ⟶ (ModuleCat.restrictScalars (O.map u.op).hom).obj (F.obj (op X)) :=
    hE.exact.descToInjective χ₀ hz
  have hψ₀ : E.g ≫ ψ₀ = χ₀ := hE.exact.comp_descToInjective χ₀ hz
  exact ⟨(ModuleCat.semilinearMapAddEquiv (O.map u.op).hom _ _).symm ψ₀,
    fun s ↦ ConcreteCategory.congr_hom hψ₀ s⟩

/-- The cochain complexes of a short complex of targets form a short complex. -/
lemma extCochainComplexMap_right_comp_zero :
    extCochainComplexMap (𝟙 G) S.f ≫ extCochainComplexMap (𝟙 G) S.g = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  funext x
  refine LinearMap.ext fun s ↦ ?_
  have hz := congrArg (fun q : S.X₁ ⟶ S.X₃ ↦ q.app (op (x.obj 0))) S.zero
  change (S.f.app (op (x.obj 0)) ≫ S.g.app (op (x.obj 0))) = 0 at hz
  show (S.f.app (op (x.obj 0)) ≫ S.g.app (op (x.obj 0))) (φ x s) = 0
  rw [hz]
  rfl

/-- The cochain complexes of a short complex of sources form a short complex. -/
lemma extCochainComplexMap_left_comp_zero :
    extCochainComplexMap S.g (𝟙 F) ≫ extCochainComplexMap S.f (𝟙 F) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  funext x
  refine LinearMap.ext fun s ↦ ?_
  have hz := congrArg (fun q : S.X₁ ⟶ S.X₃ ↦ q.app (op (x.obj (Fin.last n)))) S.zero
  change (S.f.app (op (x.obj (Fin.last n))) ≫ S.g.app (op (x.obj (Fin.last n)))) = 0 at hz
  show φ x ((S.f.app (op (x.obj (Fin.last n))) ≫
    S.g.app (op (x.obj (Fin.last n)))) s) = 0
  rw [hz]
  show φ x 0 = 0
  rw [map_zero]

/-- The short complex of cochain complexes attached to a short complex of targets. -/
abbrev extCochainComplexShortComplexRight :
    ShortComplex (CochainComplex AddCommGrpCat.{max u m} ℕ) :=
  ShortComplex.mk (extCochainComplexMap (𝟙 G) S.f) (extCochainComplexMap (𝟙 G) S.g)
    (extCochainComplexMap_right_comp_zero G S)

/-- The short complex of cochain complexes attached to a short complex of sources. -/
abbrev extCochainComplexShortComplexLeft :
    ShortComplex (CochainComplex AddCommGrpCat.{max u m} ℕ) :=
  ShortComplex.mk (extCochainComplexMap S.g (𝟙 F)) (extCochainComplexMap S.f (𝟙 F))
    (extCochainComplexMap_left_comp_zero F S)

/-- Exactness in the second variable, degreewise: if `G` is projective at every object, the
degree-`n` cochains carry a short exact sequence of targets to a short exact sequence. -/
lemma shortExact_extCochainComplexShortComplexRight_map_eval
    (hG : ∀ U : C, Projective (G.obj (op U))) (hS : S.ShortExact) (n : ℕ) :
    ((extCochainComplexShortComplexRight G S).map
      (HomologicalComplex.eval AddCommGrpCat.{max u m} (ComplexShape.up ℕ) n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.ab_exact_iff _).mpr fun φ hφ ↦ ?_
    choose ψ hψ using fun x : ComposableArrows C n ↦
      exists_extCochainComponent_desc_right G S hG hS (stringSpine x) (φ x)
        (fun s ↦ congrArg (fun q : extCochain G S.X₃ n ↦ q x s) hφ)
    exact ⟨ψ, funext fun x ↦ LinearMap.ext (hψ x)⟩
  · refine (AddCommGrpCat.mono_iff_injective _).mpr fun φ ψ h ↦ ?_
    funext x
    refine LinearMap.ext fun s ↦ ?_
    exact (hS.map_of_exact (PresheafOfModules.evaluation O
      (op (x.obj 0)))).moduleCat_injective_f
      (congrArg (fun q : extCochain G S.X₂ n ↦ q x s) h)
  · refine (AddCommGrpCat.epi_iff_surjective _).mpr fun φ ↦ ?_
    choose ψ hψ using fun x : ComposableArrows C n ↦
      exists_extCochainComponent_lift_right G S hG hS (stringSpine x) (φ x)
    exact ⟨ψ, funext fun x ↦ LinearMap.ext (hψ x)⟩

/-- Exactness in the first variable, degreewise: if the target stays injective after
restriction of scalars along every arrow, the degree-`n` cochains carry a short exact sequence
of sources to a short exact sequence. -/
lemma shortExact_extCochainComplexShortComplexLeft_map_eval
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (hS : S.ShortExact) (n : ℕ) :
    ((extCochainComplexShortComplexLeft F S).map
      (HomologicalComplex.eval AddCommGrpCat.{max u m} (ComplexShape.up ℕ) n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.ab_exact_iff _).mpr fun φ hφ ↦ ?_
    choose ψ hψ using fun x : ComposableArrows C n ↦
      exists_extCochainComponent_desc_left F S hF hS (stringSpine x) (φ x)
        (fun s ↦ congrArg (fun q : extCochain S.X₁ F n ↦ q x s) hφ)
    exact ⟨ψ, funext fun x ↦ LinearMap.ext (hψ x)⟩
  · refine (AddCommGrpCat.mono_iff_injective _).mpr fun φ ψ h ↦ ?_
    funext x
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨t, rfl⟩ := (hS.map_of_exact (PresheafOfModules.evaluation O
      (op (x.obj (Fin.last n))))).moduleCat_surjective_g s
    exact congrArg (fun q : extCochain S.X₂ F n ↦ q x t) h
  · refine (AddCommGrpCat.epi_iff_surjective _).mpr fun φ ↦ ?_
    choose ψ hψ using fun x : ComposableArrows C n ↦
      exists_extCochainComponent_lift_left F S hF hS (stringSpine x) (φ x)
    exact ⟨ψ, funext fun x ↦ LinearMap.ext (hψ x)⟩

/-- Exactness in the second variable: if `G` is projective at every object, the
cochain complex carries a short exact sequence of targets to a short exact sequence of
complexes. -/
@[stacks 08S0 "exactness in the second variable"]
lemma shortExact_extCochainComplexShortComplexRight
    (hG : ∀ U : C, Projective (G.obj (op U))) (hS : S.ShortExact) :
    (extCochainComplexShortComplexRight G S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (shortExact_extCochainComplexShortComplexRight_map_eval G S hG hS)

/-- Exactness in the first variable: if the target stays injective after
restriction of scalars along every arrow, the cochain complex carries a short exact sequence of
sources to a short exact sequence of complexes. -/
@[stacks 08S0 "exactness in the first variable, when F(U) is injective over O(V) for every
arrow U ⟶ V"]
lemma shortExact_extCochainComplexShortComplexLeft
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (hS : S.ShortExact) :
    (extCochainComplexShortComplexLeft F S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (shortExact_extCochainComplexShortComplexLeft_map_eval F S hF hS)

end Exactness

/-- Prepending an arrow to a string of arrows precomposes its composite. -/
lemma stringSpine_precomp {n : ℕ} (x : ComposableArrows C n) {U : C} (f : U ⟶ x.obj 0) :
    stringSpine (x.precomp f) = f ≫ stringSpine x := by
  cases n with
  | zero =>
    show f = f ≫ x.map (𝟙 (0 : Fin 1))
    rw [x.map_id, Category.comp_id]
  | succ n => rfl

section Coinduced

/-- The sections over `V` of the coinduced module of `F`: families, indexed by the arrows
`U ⟶ V` of `C`, of sections of `F` over `U`, each read as an `O(V)`-module through the
restriction map along its index. -/
abbrev coinducedSections (F : PresheafOfModules.{max u m} O) (V : C) :
    ModuleCat.{max u m} (O.obj (op V)) :=
  ModuleCat.of (O.obj (op V))
    (∀ (U : C) (f : U ⟶ V), (ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))

/-- The coinduced module of a module `F`: the product, over the objects `U` of `C`, of the
modules coinduced along the points `p_U` from the sections of `F` over `U`. -/
def coinducedModule (F : PresheafOfModules.{max u m} O) : PresheafOfModules.{max u m} O where
  obj V := coinducedSections F V.unop
  map {V W} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (O.map g).hom).obj (coinducedSections F W.unop))
    { toFun := fun s U f ↦ s U (f ≫ g.unop)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ by
        funext U f
        change (O.map (f ≫ g.unop).op).hom r • s U (f ≫ g.unop) =
          (O.map f.op).hom ((O.map g).hom r) • s U (f ≫ g.unop)
        congr 1
        rw [op_comp, O.map_comp]
        rfl }
  map_id V := by
    ext s
    funext U f
    exact congrArg (s U) (Category.comp_id f)
  map_comp g h := by
    ext s
    funext U f
    exact congrArg (s U) (Category.assoc f h.unop g.unop).symm

/-- Restriction along `g : V ⟶ W` in the coinduced module precomposes the index arrow with
`g.unop`. -/
lemma coinducedModule_map_apply (F : PresheafOfModules.{max u m} O) {V W : Cᵒᵖ} (g : V ⟶ W)
    (s : (coinducedModule F).obj V) (U : C) (f : U ⟶ W.unop) :
    (coinducedModule F).map g s U f = s U (f ≫ g.unop) :=
  rfl

/-- The canonical map from a module into its coinduced module: a section goes to the family of
its restrictions. -/
def toCoinducedModule (F : PresheafOfModules.{max u m} O) : F ⟶ coinducedModule F where
  app V := ModuleCat.ofHom
    { toFun := fun s U f ↦ F.map f.op s
      map_add' := fun _ _ ↦ by funext U f; exact map_add _ _ _
      map_smul' := fun r s ↦ by
        funext U f
        exact F.map_smul f.op r s }
  naturality {V W} g := by
    ext s
    funext U f
    change F.map f.op (F.map g s) = F.map (f ≫ g.unop).op s
    rw [op_comp, F.map_comp_apply]
    rfl

/-- The canonical map from a module into its coinduced module is a monomorphism. -/
instance toCoinducedModule_mono (F : PresheafOfModules.{max u m} O) :
    Mono (toCoinducedModule F) := by
  apply PresheafOfModules.mono_of_injective
  intro V s t h
  have hst : F.map (𝟙 V.unop).op s = F.map (𝟙 V.unop).op t :=
    congrArg (fun z : (coinducedModule F).obj V ↦ z V.unop (𝟙 V.unop)) h
  exact (restrictₛₗ_eq_id_apply F _ rfl s).symm.trans
    (hst.trans (restrictₛₗ_eq_id_apply F _ rfl t))

/-- The contracting homotopy of the cochain complex with coinduced target: prepend the point of
the index of a section to the string of arrows. -/
@[sga "3 I 5.2.2"]
def extCochainCoinducedContraction (G F : PresheafOfModules.{max u m} O) (n : ℕ) :
    extCochain G (coinducedModule F) (n + 1) →+ extCochain G (coinducedModule F) n where
  toFun φ x :=
    { toFun := fun s U f ↦ φ (x.precomp f) s U (𝟙 U)
      map_add' := fun s t ↦ by
        funext U f
        exact congrFun (congrFun (map_add (φ (x.precomp f)) s t) U) (𝟙 U)
      map_smul' := fun r s ↦ by
        funext U f
        have key : (O.map (stringSpine (x.precomp f)).op).hom r =
            (O.map f.op).hom ((O.map (stringSpine x).op).hom r) := by
          have h : O.map (stringSpine (x.precomp f)).op =
              O.map (stringSpine x).op ≫ O.map f.op := by
            rw [stringSpine_precomp, ← O.map_comp]
            rfl
          rw [h]
          rfl
        change φ (x.precomp f) (r • s) U (𝟙 U) =
          (O.map f.op).hom ((O.map (stringSpine x).op).hom r) • (φ (x.precomp f) s U (𝟙 U))
        refine (congrFun (congrFun (map_smulₛₗ (φ (x.precomp f)) r s) U) (𝟙 U)).trans ?_
        change (O.map (𝟙 U).op).hom ((O.map (stringSpine (x.precomp f)).op).hom r) •
          (φ (x.precomp f) s U (𝟙 U)) = _
        exact congrArg (fun z ↦ z • (φ (x.precomp f) s U (𝟙 U)))
          ((ring_map_op_eq_id_apply (𝟙 U) rfl _).trans key) }
  map_zero' := rfl
  map_add' φ ψ := rfl

/-- Two values of a cochain with coinduced target at equal data agree. -/
lemma extCochainCoinduced_apply_eq {G F : PresheafOfModules.{max u m} O} {n : ℕ}
    (φ : extCochain G (coinducedModule F) n)
    (x y : ComposableArrows C n) (hxy : x = y)
    (s : G.obj (op (x.obj (Fin.last n)))) (t : G.obj (op (y.obj (Fin.last n)))) (hst : HEq s t)
    (U : C) (f : U ⟶ x.obj 0) (g : U ⟶ y.obj 0) (hfg : HEq f g) :
    (show F.obj (op U) from φ x s U f) = (show F.obj (op U) from φ y t U g) := by
  subst hxy
  cases hst
  cases hfg
  rfl

/-- Omitting a vertex other than the first from a prepended string is prepending to the string
with that vertex omitted. -/
lemma nerve_precomp_face {n : ℕ} (x : ComposableArrows C (n + 1)) {U : C} (f : U ⟶ x.obj 0)
    (i : Fin (n + 2)) :
    (nerve C).δ i.succ (x.precomp f) =
      ((nerve C).δ i x).precomp (f ≫ x.map (homOfLE (Fin.zero_le (i.succAbove 0)))) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · show ComposableArrows.Precomp.obj x U (i.succ.succAbove 0) = U
    simp
  · refine CategoryTheory.Functor.ext (h_obj := ?_) (h_map := ?_)
    · intro j
      show ComposableArrows.Precomp.obj x U (i.succ.succAbove j.succ) =
        x.obj (i.succAbove j)
      simp only [Fin.succ_succAbove_succ]
      rfl
    · intro j k g
      apply (conj_eqToHom_iff_heq' _ _ _ _).mpr
      exact Stacks.CategoryCohomology.precomp_map_heq x f
        (Fin.succ_succAbove_succ i j) (Fin.succ_succAbove_succ i k)
        ((SimplexCategory.toCat.map (SimplexCategory.δ i.succ)).toFunctor.map
          ((Fin.succFunctor _).map g))
        ((SimplexCategory.toCat.map (SimplexCategory.δ i)).toFunctor.map g)
  · refine (conj_eqToHom_iff_heq' _ _ _ _).mpr ?_
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      refine heq_of_eq ?_
      show f = f ≫ x.map (𝟙 (0 : Fin (n + 2)))
      rw [x.map_id, Category.comp_id]

/-- Restricting along the last vertex of a prepended string. -/
lemma restrict_precomp_heq (G : PresheafOfModules.{m} O)
    {n : ℕ} (x : ComposableArrows C n) {U : C} (f : U ⟶ x.obj 0)
    (a : Fin (n + 2)) (j : Fin (n + 1)) (ha : a = j.succ)
    (s : G.obj (op (x.obj (Fin.last n)))) :
    HEq (G.restrictₛₗ ((x.precomp f).map (homOfLE (Fin.le_last a))).op s)
      (G.restrictₛₗ (x.map (homOfLE (Fin.le_last j))).op s) := by
  subst ha
  rfl

/-- The first vertex of a prepended string is the prepended object. -/
lemma precomp_first_heq {n : ℕ} (x : ComposableArrows C n) {U : C} (f : U ⟶ x.obj 0)
    (a : Fin (n + 2)) (ha : a = 0) :
    HEq ((𝟙 U) ≫ (x.precomp f).map (homOfLE (Fin.zero_le a))) (𝟙 U) := by
  subst ha
  show HEq ((𝟙 U) ≫ 𝟙 U) (𝟙 U)
  rw [Category.id_comp]

/-- The contraction undoes the zeroth coface map. -/
lemma extCochainCoinducedContraction_coface_zero (G F : PresheafOfModules.{max u m} O) (n : ℕ)
    (φ : extCochain G (coinducedModule F) n) :
    extCochainCoinducedContraction G F n
      (extCochainSimplexMap G (coinducedModule F) (SimplexCategory.δ 0) φ) = φ := by
  funext x
  refine LinearMap.ext fun s ↦ ?_
  funext U f
  show (show F.obj (op U) from
    φ x (G.restrictₛₗ (x.map (𝟙 (Fin.last n))).op s) U (𝟙 U ≫ f)) = φ x s U f
  rw [restrictₛₗ_eq_id_apply G _ (x.map_id _), Category.id_comp]

/-- The contraction commutes with the remaining coface maps. -/
lemma extCochainCoinducedContraction_coface_succ (G F : PresheafOfModules.{max u m} O) (n : ℕ)
    (i : Fin (n + 2)) (φ : extCochain G (coinducedModule F) (n + 1)) :
    extCochainCoinducedContraction G F (n + 1)
      (extCochainSimplexMap G (coinducedModule F) (SimplexCategory.δ i.succ) φ) =
    extCochainSimplexMap G (coinducedModule F) (SimplexCategory.δ i)
      (extCochainCoinducedContraction G F n φ) := by
  funext x
  refine LinearMap.ext fun s ↦ ?_
  funext U f
  show (show F.obj (op U) from
    extCochainSimplexMap G (coinducedModule F) (SimplexCategory.δ i.succ) φ
      (x.precomp f) s U (𝟙 U)) = _
  rw [extCochainSimplexMap_apply]
  show _ = (show F.obj (op U) from
    extCochainSimplexMap G (coinducedModule F) (SimplexCategory.δ i)
      (extCochainCoinducedContraction G F n φ) x s U f)
  rw [extCochainSimplexMap_apply]
  exact extCochainCoinduced_apply_eq φ _ _ (nerve_precomp_face x f i) _ _
    (restrict_precomp_heq G x f _ _ (Fin.succ_succAbove_succ i (Fin.last n)) s)
    U _ _ (precomp_first_heq x f _ (Fin.succ_succAbove_zero i))

/-- A family of maps contracting a cosimplicial object gives a homotopy between the identity and
zero on its alternating-coface complex in positive degrees. -/
lemma cosimplicialContraction {B : Type*} [Category B] [Preadditive B]
    (X : CosimplicialObject B)
    (s : ∀ n : ℕ, X.obj (SimplexCategory.mk (n + 1)) ⟶ X.obj (SimplexCategory.mk n))
    (hzero : ∀ n : ℕ, X.δ 0 ≫ s n = 𝟙 _)
    (hsucc : ∀ (n : ℕ) (i : Fin (n + 2)),
      X.δ i.succ ≫ s (n + 1) = s n ≫ X.δ i) (n : ℕ) :
    s n ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD X n +
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X (n + 1) ≫ s (n + 1) = 𝟙 _ := by
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ (fun i : Fin (n + 3) ↦
    (-1 : ℤ) ^ i.val • (X.δ i ≫ s (n + 1)))]
  simp only [Fin.val_zero, pow_zero, one_zsmul, hzero, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, hsucc, Finset.sum_neg_distrib]
  abel

/-- A cochain complex of abelian groups with a contracting family of maps has no cohomology in
positive degrees. -/
lemma isZero_homology_succ_of_contracting_maps (K : CochainComplex AddCommGrpCat.{t} ℕ)
    (s : ∀ n : ℕ, K.X (n + 1) ⟶ K.X n)
    (hs : ∀ n : ℕ,
      s n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ s (n + 1) = 𝟙 (K.X (n + 1))) (n : ℕ) :
    IsZero (K.homology (n + 1)) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (K.exactAt_iff' n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
    (by simp [CochainComplex.next])).2
  apply (K.sc' n (n + 1) (n + 2)).ab_exact_iff.mpr
  intro z hz
  refine ⟨s n z, ?_⟩
  have he := congrArg
    (fun q : K.X (n + 1) ⟶ K.X (n + 1) ↦ q z) (hs n)
  change K.d n (n + 1) (s n z) + s (n + 1) (K.d (n + 1) (n + 2) z) = z at he
  change K.d (n + 1) (n + 2) z = 0 at hz
  rw [hz, map_zero, add_zero] at he
  exact he

/-- The cochain complex with coinduced target is acyclic in positive degrees. -/
@[sga "3 I 5.2.2" "special case"]
theorem isZero_coinducedModule_homology (G F : PresheafOfModules.{max u m} O) (n : ℕ) :
    IsZero ((extCochainComplex G (coinducedModule F)).homology (n + 1)) := by
  let s := fun k ↦ AddCommGrpCat.ofHom (extCochainCoinducedContraction G F k)
  refine isZero_homology_succ_of_contracting_maps _ s ?_ n
  intro k
  have hz : ∀ j : ℕ, (extCochainCosimplicialObject G (coinducedModule F)).δ 0 ≫ s j = 𝟙 _ :=
    fun j ↦ AddCommGrpCat.hom_ext
      (AddMonoidHom.ext (extCochainCoinducedContraction_coface_zero G F j))
  have hsucc : ∀ (j : ℕ) (i : Fin (j + 2)),
      (extCochainCosimplicialObject G (coinducedModule F)).δ i.succ ≫ s (j + 1) =
        s j ≫ (extCochainCosimplicialObject G (coinducedModule F)).δ i := fun j i ↦
    AddCommGrpCat.hom_ext (AddMonoidHom.ext (extCochainCoinducedContraction_coface_succ G F j i))
  simp only [extCochainComplex, extCochainComplexBifunctor, extCochainCosimplicialBifunctor,
    Functor.comp_obj, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of.d,
    dite_eq_left (show (k + 1) + 1 = k + 2 from rfl), dite_true, eqToHom_refl,
    Category.comp_id]
  exact cosimplicialContraction (extCochainCosimplicialObject G (coinducedModule F)) s hz hsucc k

end Coinduced

section SourceDeltaFunctor

/-- The pair of modules with the source fixed, as a functor of the target. -/
def fixedSourcePair (G : PresheafOfModules.{m} O) :
    PresheafOfModules.{m} O ⥤ (PresheafOfModules.{m} O)ᵒᵖ × PresheafOfModules.{m} O where
  obj F := (op G, F)
  map f := (𝟙 (op G), f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cochain complex `K^•(G, -)` as a functor of the target module. -/
def extCochainFixedSourceFunctor (G : PresheafOfModules.{m} O) :
    PresheafOfModules.{m} O ⥤ CochainComplex AddCommGrpCat.{max u m} ℕ :=
  fixedSourcePair G ⋙ extCochainComplexBifunctor C O

/-- The functor `K^•(G, -)` is additive. -/
instance extCochainFixedSourceFunctor_additive (G : PresheafOfModules.{m} O) :
    (extCochainFixedSourceFunctor G).Additive where
  map_add := HomologicalComplex.hom_ext _ _ fun _ ↦ AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun _ ↦ funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)

/-- If every section module `G(U)` is projective, then the functor `K^•(G, -)` is exact. -/
lemma extCochainFixedSourceFunctor_exact (G : PresheafOfModules.{m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) :
    exactFunctor _ _ (extCochainFixedSourceFunctor G) := by
  rw [exactFunctor_iff]
  exact ((Functor.exact_tfae (extCochainFixedSourceFunctor G)).out 4 1).mpr fun S hS ↦
    shortExact_extCochainComplexShortComplexRight G S hG hS

/-- The δ-functor of the cohomology of `K^•(G, -)`, for `G` projective at every object. -/
def extCochainFixedSourceDeltaFunctor (G : PresheafOfModules.{m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) :
    DeltaFunctor (PresheafOfModules.{m} O) AddCommGrpCat.{max u m} := by
  let K := extCochainFixedSourceFunctor G
  have hK := extCochainFixedSourceFunctor_exact G hG
  letI : PreservesFiniteLimits K := ((exactFunctor_iff K).mp hK).1
  letI : PreservesFiniteColimits K := ((exactFunctor_iff K).mp hK).2
  letI : K.Additive := extCochainFixedSourceFunctor_additive G
  exact
    { functor := fun n ↦ K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
      additive := fun _ ↦ inferInstance
      δ := fun {S} hS n ↦
        (hS.map_of_exact K).δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      map_g_δ := fun hS n ↦
        (hS.map_of_exact K).comp_δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      δ_map_f := fun hS n ↦
        (hS.map_of_exact K).δ_comp n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      mono_map_f := by
        intro S hS
        let : Mono ((S.map K).f) := (hS.map_of_exact K).mono_f
        apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (S.map K).f 0
        intro i
        simp only [ComplexShape.up_Rel]
        omega
      exact_map := fun hS n ↦ (hS.map_of_exact K).homology_exact₂ n
      exact_δ₁ := fun hS n ↦ (hS.map_of_exact K).homology_exact₃ n (n + 1)
        (ComplexShape.up_mk n (n + 1) (by omega))
      exact_δ₂ := fun hS n ↦ (hS.map_of_exact K).homology_exact₁ n (n + 1)
        (ComplexShape.up_mk n (n + 1) (by omega))
      δ_naturality := by
        intro S T hS hT φ n
        let ψ : S.map K ⟶ T.map K :=
          { τ₁ := K.map φ.τ₁
            τ₂ := K.map φ.τ₂
            τ₃ := K.map φ.τ₃
            comm₁₂ := by simpa using congrArg K.map φ.comm₁₂
            comm₂₃ := by simpa using congrArg K.map φ.comm₂₃ }
        change HomologicalComplex.homologyMap (K.map φ.τ₃) n ≫ _ =
          _ ≫ HomologicalComplex.homologyMap (K.map φ.τ₁) (n + 1)
        exact (HomologicalComplex.HomologySequence.δ_naturality ψ
          (hS.map_of_exact K) (hT.map_of_exact K) n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))).symm }

/-- The cochain δ-functor in the target variable is universal, for `G` projective at every
object. -/
lemma extCochainFixedSourceDeltaFunctor_isUniversal (G : PresheafOfModules.{max u m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) :
    (extCochainFixedSourceDeltaFunctor G hG).IsUniversal := by
  exact DeltaFunctor.isUniversal_of_forall_exists_mono _ fun n F ↦ ⟨coinducedModule F,
    toCoinducedModule F, inferInstance, (isZero_coinducedModule_homology G F n).eq_of_tgt _ _⟩

end SourceDeltaFunctor

section ExtComparison

attribute [local instance] HasDerivedCategory.standard

/-- Presheaves of modules in a universe containing the site and the ring form a Grothendieck
abelian category. -/
@[sga "3 I 3.1.1" "partial, special case"]
lemma isGrothendieckAbelian_presheafOfModules :
    IsGrothendieckAbelian.{max u v m} (PresheafOfModules.{max u v m} O) :=
  Stacks.SheafOfModules.presheafModulesGrothendieck.{u, u, v, m} O

/-- The `Ext` groups of presheaves of modules live in the universe of the modules, as soon as it
contains the universes of the site and of the ring. -/
lemma hasExt_presheafOfModules :
    HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
  let : IsGrothendieckAbelian.{max u v m} (PresheafOfModules.{max u v m} O) :=
    isGrothendieckAbelian_presheafOfModules.{u, v, m}
  IsGrothendieckAbelian.hasExt _

/-- The δ-functor `Ext^•(G, -)` out of a fixed source module. -/
@[sga "4 V 6.2" "special case"]
abbrev extSourceDeltaFunctor (G : PresheafOfModules.{max u v m} O) :
    DeltaFunctor (PresheafOfModules.{max u v m} O) AddCommGrpCat.{max u v m} :=
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  ModuleSheafCohomology.extDeltaFunctor (𝟭 _) G

/-- `Ext^•(G, -)` is a universal δ-functor. -/
lemma extSourceDeltaFunctor_isUniversal (G : PresheafOfModules.{max u v m} O) :
    (extSourceDeltaFunctor.{u, v, m} G).IsUniversal := by
  let : IsGrothendieckAbelian.{max u v m} (PresheafOfModules.{max u v m} O) :=
    isGrothendieckAbelian_presheafOfModules.{u, v, m}
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  refine ModuleSheafCohomology.extDeltaFunctor_isUniversal (𝟭 _) G (fun I hI n e ↦ ?_)
  let : Injective ((𝟭 (PresheafOfModules.{max u v m} O)).obj I) := hI
  exact Abelian.Ext.eq_zero_of_injective e

/-- The components of an isomorphism of δ-functors. -/
def deltaComponentIso {A B : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    {D E : DeltaFunctor A B} (e : D ≅ E) (n : ℕ) (X : A) :
    (D.functor n).obj X ≅ (E.functor n).obj X where
  hom := (e.hom.app n).app X
  inv := (e.inv.app n).app X
  hom_inv_id := congrArg (fun f : D ⟶ D ↦ (f.app n).app X) e.hom_inv_id
  inv_hom_id := congrArg (fun f : E ⟶ E ↦ (f.app n).app X) e.inv_hom_id

/-- The inverse degree-zero comparison is natural in both modules. -/
lemma extCochainComplexHomologyZeroIso_inv_naturality {G G' F F' : PresheafOfModules.{m} O}
    (g : G' ⟶ G) (f : F ⟶ F') :
    (extCochainComplexHomologyZeroIso G F).inv ≫
        HomologicalComplex.homologyMap (extCochainComplexMap g f) 0 =
      homCompHom g f ≫ (extCochainComplexHomologyZeroIso G' F').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact extCochainComplexHomologyZeroIso_naturality g f

/-- The degree-zero cohomology of `K^•(G, F)` is the group of homomorphisms
`G ⟶ F`, as an isomorphism of additive groups. -/
def homAddEquivExtCochainHomologyZero (G F : PresheafOfModules.{m} O) :
    (G ⟶ F) ≃+ (extCochainComplex G F).homology 0 :=
  (extCochainComplexHomologyZeroIso G F).symm.addCommGroupIsoToAddEquiv

/-- The degree-zero comparison is natural in both modules, as a statement about homomorphisms. -/
private lemma homAddEquivExtCochainHomologyZero_natural {G G' F F' : PresheafOfModules.{m} O}
    (g : G' ⟶ G) (f : F ⟶ F') (α : G ⟶ F) :
    homAddEquivExtCochainHomologyZero G' F' (g ≫ α ≫ f) =
      HomologicalComplex.homologyMap (extCochainComplexMap g f) 0
        (homAddEquivExtCochainHomologyZero G F α) :=
  (ConcreteCategory.congr_hom (extCochainComplexHomologyZeroIso_inv_naturality g f) α).symm

/-- The degree-zero comparison commutes with postcomposition in the target. -/
lemma homAddEquivExtCochainHomologyZero_natural_right (G F F' : PresheafOfModules.{m} O)
    (f : F ⟶ F') (α : G ⟶ F) :
    homAddEquivExtCochainHomologyZero G F' (α ≫ f) =
      HomologicalComplex.homologyMap (extCochainComplexMap (𝟙 G) f) 0
        (homAddEquivExtCochainHomologyZero G F α) := by
  simpa using homAddEquivExtCochainHomologyZero_natural (𝟙 G) f α

/-- The degree-zero comparison commutes with precomposition in the source. -/
lemma homAddEquivExtCochainHomologyZero_natural_left (G G' F : PresheafOfModules.{m} O)
    (g : G' ⟶ G) (α : G ⟶ F) :
    homAddEquivExtCochainHomologyZero G' F (g ≫ α) =
      HomologicalComplex.homologyMap (extCochainComplexMap g (𝟙 F)) 0
        (homAddEquivExtCochainHomologyZero G F α) := by
  simpa using homAddEquivExtCochainHomologyZero_natural g (𝟙 F) α

/-- The comparison in degree zero, in the target variable: degree-zero `Ext` and the
degree-zero cohomology of the cochain complex are isomorphic, naturally in the target. -/
def extSourceComparisonZero (G : PresheafOfModules.{max u v m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) :
    (extSourceDeltaFunctor.{u, v, m} G).functor 0 ≅
      (extCochainFixedSourceDeltaFunctor G hG).functor 0 := by
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  refine NatIso.ofComponents (fun F ↦ (Abelian.Ext.addEquiv₀.trans
    (homAddEquivExtCochainHomologyZero G F)).toAddCommGrpIso) ?_
  intro F F' f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro e
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective.{max u v m} G F).2 e
  change homAddEquivExtCochainHomologyZero G F'
      (Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ a).comp (Abelian.Ext.mk₀ f) (add_zero 0))) =
    HomologicalComplex.homologyMap (extCochainComplexMap (𝟙 G) f) 0
      (homAddEquivExtCochainHomologyZero G F (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ a)))
  rw [Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.addEquiv₀_symm_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact homAddEquivExtCochainHomologyZero_natural_right G F F' f a

/-- The comparison of the δ-functors `Ext^•(G, -)` and `H^•(K^•(G, -))`, for `G` projective at
every object. -/
def extSourceComparison (G : PresheafOfModules.{max u v m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) :
    extSourceDeltaFunctor.{u, v, m} G ≅ extCochainFixedSourceDeltaFunctor G hG := by
  letI := extSourceDeltaFunctor_isUniversal.{u, v, m} G
  letI := extCochainFixedSourceDeltaFunctor_isUniversal.{u, v, max v m} G hG
  exact DeltaFunctor.IsUniversal.isoOfIso (extSourceComparisonZero.{u, v, m} G hG)

/-- Case (1): if the first module is projective at every object, the cochain
complex computes all its `Ext` groups: `Ext^n_O(G, F) ≅ H^n(K^•(G, F))` for every `n`. -/
@[stacks 08S0 "objectwise-projective case, every degree"]
def extAddEquivCohomology_of_objectwiseProjective (G F : PresheafOfModules.{max u v m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) (n : ℕ) :
    Abelian.zExt G F (n : ℤ) ≃+ (extCochainComplex G F).homology n := by
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  exact (Abelian.Ext.homAddEquiv.{_, max u v m}).symm.trans
    (deltaComponentIso (extSourceComparison.{u, v, m} G hG) n F).addCommGroupIsoToAddEquiv

/-! ### Free covers -/

open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent in
/-- The sections of the free module on a representable form a free, hence projective, module. -/
lemma projective_gen_obj (U V : C) :
    Projective ((gen.{v, m, u, u} O U).obj (op V)) := by
  show Projective (ModuleCat.of (O.obj (op V))
    (O.obj (op V) ⊗[ℤ] FreeAbelianGroup (ULift.{max u v m} (V ⟶ U))))
  exact ModuleCat.projective_of_free
    ((Module.Free.chooseBasis ℤ (FreeAbelianGroup (ULift.{max u v m} (V ⟶ U)))).baseChange
      (O.obj (op V)))

open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent in
/-- The free cover of a module is projective at every object. -/
lemma projective_genCoproduct_obj (G : PresheafOfModules.{max u v m} O) (V : C) :
    Projective ((genCoproduct.{v, m, u, u} O G).obj (op V)) := by
  let (j : G.Elements) : Projective ((gen.{v, m, u, u} O j.1.unop).obj (op V)) :=
    projective_gen_obj.{u, v, m} j.1.unop V
  refine Projective.of_iso
    (PreservesCoproduct.iso (PresheafOfModules.evaluation O (op V))
      (fun j : G.Elements ↦ gen.{v, m, u, u} O j.1.unop)).symm ?_
  show Projective (∐ fun j : G.Elements ↦ (gen.{v, m, u, u} O j.1.unop).obj (op V))
  infer_instance

open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent in
/-- The cochain complex of a free cover is acyclic in positive degrees. -/
lemma isZero_homology_genCoproduct (G F : PresheafOfModules.{max u v m} O) (n : ℕ) :
    IsZero ((extCochainComplex (genCoproduct.{v, m, u, u} O G) F).homology (n + 1)) := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  have e := extAddEquivCohomology_of_objectwiseProjective.{u, v, m}
    (genCoproduct.{v, m, u, u} O G) F (fun V ↦ projective_genCoproduct_obj.{u, v, m} G V) (n + 1)
  have hzero : ∀ z : Abelian.zExt (genCoproduct.{v, m, u, u} O G) F ((n + 1 : ℕ) : ℤ), z = 0 :=
    fun z ↦ Abelian.Ext.homAddEquiv.{_, max u v m}.symm.map_eq_zero_iff.1
      (Abelian.Ext.eq_zero_of_projective _)
  have : Subsingleton ((extCochainComplex (genCoproduct.{v, m, u, u} O G) F).homology (n + 1)) := by
    let := subsingleton_of_forall_eq 0 hzero
    exact e.symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-! ### The cochain δ-functor in the source variable -/

/-- The pair of modules with the target fixed, as a functor of the source. -/
def fixedTargetPair (F : PresheafOfModules.{m} O) :
    (PresheafOfModules.{m} O)ᵒᵖ ⥤ (PresheafOfModules.{m} O)ᵒᵖ × PresheafOfModules.{m} O where
  obj G := (G, F)
  map g := (g, 𝟙 F)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cochain complex `K^•(-, F)` as a functor of the source module. -/
def extCochainFixedTargetFunctor (F : PresheafOfModules.{m} O) :
    (PresheafOfModules.{m} O)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max u m} ℕ :=
  fixedTargetPair F ⋙ extCochainComplexBifunctor C O

/-- The functor `K^•(-, F)` is additive. -/
instance extCochainFixedTargetFunctor_additive (F : PresheafOfModules.{m} O) :
    (extCochainFixedTargetFunctor F).Additive where
  map_add {G G' f g} := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    funext x
    refine LinearMap.ext fun s ↦ ?_
    have h : ((f + g).unop.app (op (x.obj (Fin.last n)))) s =
        f.unop.app (op (x.obj (Fin.last n))) s +
          g.unop.app (op (x.obj (Fin.last n))) s := by
      rw [CategoryTheory.unop_add]
      rfl
    change φ x ((f + g).unop.app (op (x.obj (Fin.last n))) s) =
      φ x (f.unop.app (op (x.obj (Fin.last n))) s) +
        φ x (g.unop.app (op (x.obj (Fin.last n))) s)
    rw [h]
    exact map_add (φ x) _ _

/-- If for every arrow `f : U ⟶ V` the module `F(U)`, with scalars restricted along `O(f)`, is
injective, then the functor `K^•(-, F)` is exact. -/
lemma extCochainFixedTargetFunctor_exact (F : PresheafOfModules.{m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))) :
    exactFunctor _ _ (extCochainFixedTargetFunctor F) := by
  rw [exactFunctor_iff]
  apply ((Functor.exact_tfae (extCochainFixedTargetFunctor F)).out 4 1).mpr
  intro S hS
  exact shortExact_extCochainComplexShortComplexLeft F S.unop (hF := hF) hS.unop

/-- The δ-functor of the cohomology of `K^•(-, F)`, for a target which stays injective after
restriction of scalars along every arrow. -/
def extCochainFixedTargetDeltaFunctor (F : PresheafOfModules.{m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))) :
    DeltaFunctor (PresheafOfModules.{m} O)ᵒᵖ AddCommGrpCat.{max u m} := by
  let K := extCochainFixedTargetFunctor F
  have hK := extCochainFixedTargetFunctor_exact F hF
  letI : PreservesFiniteLimits K := ((exactFunctor_iff K).mp hK).1
  letI : PreservesFiniteColimits K := ((exactFunctor_iff K).mp hK).2
  letI : K.Additive := extCochainFixedTargetFunctor_additive F
  exact
    { functor := fun n ↦ K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
      additive := fun _ ↦ inferInstance
      δ := fun {S} hS n ↦
        (hS.map_of_exact K).δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      map_g_δ := fun hS n ↦
        (hS.map_of_exact K).comp_δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      δ_map_f := fun hS n ↦
        (hS.map_of_exact K).δ_comp n (n + 1) (ComplexShape.up_mk n (n + 1) (by omega))
      mono_map_f := by
        intro S hS
        let : Mono ((S.map K).f) := (hS.map_of_exact K).mono_f
        apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (S.map K).f 0
        intro i
        simp only [ComplexShape.up_Rel]
        omega
      exact_map := fun hS n ↦ (hS.map_of_exact K).homology_exact₂ n
      exact_δ₁ := fun hS n ↦ (hS.map_of_exact K).homology_exact₃ n (n + 1)
        (ComplexShape.up_mk n (n + 1) (by omega))
      exact_δ₂ := fun hS n ↦ (hS.map_of_exact K).homology_exact₁ n (n + 1)
        (ComplexShape.up_mk n (n + 1) (by omega))
      δ_naturality := by
        intro S T hS hT φ n
        let ψ : S.map K ⟶ T.map K :=
          { τ₁ := K.map φ.τ₁
            τ₂ := K.map φ.τ₂
            τ₃ := K.map φ.τ₃
            comm₁₂ := by simpa using congrArg K.map φ.comm₁₂
            comm₂₃ := by simpa using congrArg K.map φ.comm₂₃ }
        change HomologicalComplex.homologyMap (K.map φ.τ₃) n ≫ _ =
          _ ≫ HomologicalComplex.homologyMap (K.map φ.τ₁) (n + 1)
        exact (HomologicalComplex.HomologySequence.δ_naturality ψ
          (hS.map_of_exact K) (hT.map_of_exact K) n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))).symm }

open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent in
/-- The cochain δ-functor in the source variable is universal, for a target which stays
injective after restriction of scalars along every arrow. -/
lemma extCochainFixedTargetDeltaFunctor_isUniversal (F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))) :
    (extCochainFixedTargetDeltaFunctor F hF).IsUniversal := by
  apply DeltaFunctor.isUniversal_of_forall_exists_mono
  intro n G
  have := epi_fromGenCoproduct.{v, m, u, u} O G.unop
  exact ⟨op (genCoproduct.{v, m, u, u} O G.unop), (fromGenCoproduct.{v, m, u, u} O G.unop).op,
    inferInstance, (isZero_homology_genCoproduct.{u, v, m} G.unop F n).eq_of_tgt _ _⟩

/-! ### The Ext δ-functor in the source variable -/

/-- The δ-functor `Ext^•(-, F)` into a fixed target module. -/
def extTargetDeltaFunctor (F : PresheafOfModules.{max u v m} O) :
    DeltaFunctor (PresheafOfModules.{max u v m} O)ᵒᵖ AddCommGrpCat.{max u v m} := by
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  exact
    { functor := fun n ↦ (Abelian.extFunctor.{max u v m} n).flip.obj F
      additive := fun n ↦ ⟨by
        intro X Y f g
        ext e
        change (Abelian.Ext.mk₀ (f + g).unop).comp e (zero_add n) = _
        rw [CategoryTheory.unop_add, Abelian.Ext.mk₀_add]
        exact Abelian.Ext.add_comp _ _ _ _⟩
      δ := fun {S} hS n ↦
        AddCommGrpCat.ofHom (hS.unop.extClass.precomp F (by omega : 1 + n = n + 1))
      map_g_δ := by
        intro S hS n
        ext e
        change hS.unop.extClass.comp
          ((Abelian.Ext.mk₀ S.g.unop).comp e (zero_add n)) (by omega) = 0
        exact hS.unop.extClass_comp_assoc e
      δ_map_f := by
        intro S hS n
        ext e
        change (Abelian.Ext.mk₀ S.f.unop).comp
          (hS.unop.extClass.comp e (by omega)) (zero_add (n + 1)) = 0
        exact hS.unop.comp_extClass_assoc e (by omega)
      mono_map_f := by
        intro S hS
        have : Epi S.f.unop := hS.unop.epi_g
        exact Abelian.Ext.mono_precomp_mk₀_of_epi F S.f.unop
      exact_map := fun hS n ↦ Abelian.Ext.contravariant_sequence_exact₂' hS.unop F n
      exact_δ₁ := fun hS n ↦
        Abelian.Ext.contravariant_sequence_exact₁' hS.unop F n (n + 1) (by omega)
      exact_δ₂ := fun hS n ↦
        Abelian.Ext.contravariant_sequence_exact₃' hS.unop F n (n + 1) (by omega)
      δ_naturality := by
        intro S T hS hT φ n
        ext e
        change hT.unop.extClass.comp
          ((Abelian.Ext.mk₀ φ.τ₃.unop).comp e (zero_add n)) (by omega) =
          (Abelian.Ext.mk₀ φ.τ₁.unop).comp
            (hS.unop.extClass.comp e (by omega)) (zero_add (n + 1))
        have hn := hT.unop.extClass_naturality hS.unop (ShortComplex.unopMap φ)
        change hT.unop.extClass.comp (Abelian.Ext.mk₀ φ.τ₃.unop) (add_zero 1) =
          (Abelian.Ext.mk₀ φ.τ₁.unop).comp hS.unop.extClass (zero_add 1) at hn
        refine ((Abelian.Ext.comp_assoc_of_second_deg_zero
          hT.unop.extClass (Abelian.Ext.mk₀ φ.τ₃.unop) e (by omega)).symm).trans ?_
        refine (congrArg (fun z ↦ z.comp e (by omega : 1 + n = n + 1)) hn).trans ?_
        exact Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (by omega) (by omega) }

open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent in
/-- `Ext^•(-, F)` is a universal δ-functor. -/
lemma extTargetDeltaFunctor_isUniversal (F : PresheafOfModules.{max u v m} O) :
    (extTargetDeltaFunctor.{u, v, m} F).IsUniversal := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  apply DeltaFunctor.isUniversal_of_forall_exists_mono
  intro n G
  have := epi_fromGenCoproduct.{v, m, u, u} O G.unop
  refine ⟨op (genCoproduct.{v, m, u, u} O G.unop), (fromGenCoproduct.{v, m, u, u} O G.unop).op,
    inferInstance, ?_⟩
  ext e
  apply Abelian.Ext.eq_zero_of_projective

/-! ### The comparison in the source variable -/

/-- The comparison in degree zero, in the source variable: degree-zero `Ext` and the degree-zero
cohomology of the cochain complex are isomorphic, naturally in the source. -/
def extTargetComparisonZero (F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))) :
    (extTargetDeltaFunctor.{u, v, m} F).functor 0 ≅
      (extCochainFixedTargetDeltaFunctor F hF).functor 0 := by
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  refine NatIso.ofComponents (fun G ↦ (Abelian.Ext.addEquiv₀.trans
    (homAddEquivExtCochainHomologyZero G.unop F)).toAddCommGrpIso) ?_
  intro G G' g
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro e
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective.{max u v m} G.unop F).2 e
  change homAddEquivExtCochainHomologyZero G'.unop F
      (Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ g.unop).comp (Abelian.Ext.mk₀ a) (zero_add 0))) =
    HomologicalComplex.homologyMap (extCochainComplexMap g.unop (𝟙 F)) 0
      (homAddEquivExtCochainHomologyZero G.unop F (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ a)))
  rw [Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.addEquiv₀_symm_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact homAddEquivExtCochainHomologyZero_natural_left G.unop G'.unop F g.unop a

/-- The comparison of the δ-functors `Ext^•(-, F)` and `H^•(K^•(-, F))`, for a target which stays
injective after restriction of scalars along every arrow. -/
def extTargetComparison (F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U)))) :
    extTargetDeltaFunctor.{u, v, m} F ≅ extCochainFixedTargetDeltaFunctor F hF := by
  letI := extTargetDeltaFunctor_isUniversal.{u, v, m} F
  letI := extCochainFixedTargetDeltaFunctor_isUniversal.{u, v, m} F hF
  exact DeltaFunctor.IsUniversal.isoOfIso (extTargetComparisonZero.{u, v, m} F hF)

/-- Case (2): if each section of the second module remains injective after
restriction of scalars along every arrow, the cochain complex computes all `Ext` groups into it:
`Ext^n_O(G, F) ≅ H^n(K^•(G, F))` for every `n`.

Injectivity of each `F(U)` over `O(U)` alone does not suffice:
`Stacks.CategoryExt.ArrowCounterexample.injective_obj_and_not_nonempty_extAddEquiv_two` is a
counterexample in degree two. -/
@[stacks 08S0 "case (2), every degree, F(U) injective over O(V) for every arrow U ⟶ V;
objectwise injectivity does not suffice, see
Stacks.CategoryExt.ArrowCounterexample.injective_obj_and_not_nonempty_extAddEquiv_two"]
def extAddEquivCohomology_of_arrowwiseInjective (G F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (n : ℕ) :
    Abelian.zExt G F (n : ℤ) ≃+ (extCochainComplex G F).homology n := by
  letI : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  exact (Abelian.Ext.homAddEquiv.{_, max u v m}).symm.trans
    (deltaComponentIso (extTargetComparison.{u, v, m} F hF) n (op G)).addCommGroupIsoToAddEquiv

/-! ### Normalization of the comparisons in degree zero -/

/-- The degree-zero comparison sends the `Ext` class of a morphism, read through the derived
category, to the morphism. -/
private lemma homAddEquivExtCochainHomologyZero_addEquiv₀_homAddEquiv_symm_mk₀
    [HasExt.{max u v m} (PresheafOfModules.{max u v m} O)]
    (G F : PresheafOfModules.{max u v m} O) (α : G ⟶ F) :
    homAddEquivExtCochainHomologyZero G F (Abelian.Ext.addEquiv₀
      (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((DerivedCategory.singleFunctor _ 0).map α)))) =
      homAddEquivExtCochainHomologyZero G F α := by
  have hh : ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor (PresheafOfModules.{max u v m} O) 0).map α) =
      (Abelian.Ext.homAddEquiv (Abelian.Ext.mk₀ α) : Abelian.zExt G F 0) :=
    (Abelian.Ext.mk₀_hom α).symm
  show homAddEquivExtCochainHomologyZero G F (Abelian.Ext.addEquiv₀
    (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor _ 0).map α)))) = _
  rw [hh, AddEquiv.symm_apply_apply]
  exact congrArg (homAddEquivExtCochainHomologyZero G F)
    (Abelian.Ext.addEquiv₀.apply_symm_apply α)

/-- The projective comparison is the canonical identification in degree zero: it carries the
class of a morphism of modules to the class of its family of components. -/
theorem extAddEquivCohomology_of_objectwiseProjective_zero
    (G F : PresheafOfModules.{max u v m} O)
    (hG : ∀ U : C, Projective (G.obj (op U))) (α : G ⟶ F) :
    extAddEquivCohomology_of_objectwiseProjective.{u, v, m} G F hG 0
        (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor (PresheafOfModules.{max u v m} O) 0).map α)) =
      homAddEquivExtCochainHomologyZero G F α := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  show ((extSourceComparison.{u, v, m} G hG).hom.app 0).app F
    (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor _ 0).map α))) = _
  simp only [extSourceComparison, DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero]
  exact homAddEquivExtCochainHomologyZero_addEquiv₀_homAddEquiv_symm_mk₀.{u, v, m} G F α

/-- The injective comparison has the same normalization in degree zero. -/
theorem extAddEquivCohomology_of_arrowwiseInjective_zero
    (G F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (α : G ⟶ F) :
    extAddEquivCohomology_of_arrowwiseInjective.{u, v, m} G F hF 0
        (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor (PresheafOfModules.{max u v m} O) 0).map α)) =
      homAddEquivExtCochainHomologyZero G F α := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  show ((extTargetComparison.{u, v, m} F hF).hom.app 0).app (op G)
    (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor _ 0).map α))) = _
  simp only [extTargetComparison, DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero]
  exact homAddEquivExtCochainHomologyZero_addEquiv₀_homAddEquiv_symm_mk₀.{u, v, m} G F α

/-! ### Compatibility of the comparisons with the connecting maps -/

/-- The projective comparison intertwines the connecting map of a short exact sequence of targets
with the cohomological connecting map of its image under the cochain functor. -/
theorem extAddEquivCohomology_of_objectwiseProjective_delta
    (G : PresheafOfModules.{max u v m} O)
    (hG : ∀ U : C, Projective (G.obj (op U)))
    (S : ShortComplex (PresheafOfModules.{max u v m} O)) (hS : S.ShortExact)
    (n : ℕ) (e : Abelian.zExt G S.X₃ (n : ℤ)) :
    extAddEquivCohomology_of_objectwiseProjective.{u, v, m} G S.X₁ hG (n + 1)
        (e.comp hS.singleδ (by omega)) =
      (shortExact_extCochainComplexShortComplexRight G S hG hS).δ n (n + 1) rfl
        (extAddEquivCohomology_of_objectwiseProjective.{u, v, m} G S.X₃ hG n e) := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  obtain ⟨ξ, rfl⟩ := (Abelian.Ext.homAddEquiv.{_, max u v m}
    (X := G) (Y := S.X₃) (n := n)).surjective e
  have hn : (extCochainFixedSourceDeltaFunctor G hG).δ hS n
        (((extSourceComparison.{u, v, m} G hG).hom.app n).app S.X₃ ξ) =
      ((extSourceComparison.{u, v, m} G hG).hom.app (n + 1)).app S.X₁
        ((extSourceDeltaFunctor.{u, v, m} G).δ hS n ξ) :=
    ConcreteCategory.congr_hom ((extSourceComparison.{u, v, m} G hG).hom.comm hS n) ξ
  have hc : (Abelian.Ext.homAddEquiv ξ : Abelian.zExt G S.X₃ (n : ℤ)).comp
      hS.singleδ (by omega) =
      (Abelian.Ext.homAddEquiv (ξ.comp hS.extClass rfl) :
        Abelian.zExt G S.X₁ ((n + 1 : ℕ) : ℤ)) := by
    simp only [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom, hS.extClass_hom]
  rw [hc]
  show ((extSourceComparison.{u, v, m} G hG).hom.app (n + 1)).app S.X₁
      (Abelian.Ext.homAddEquiv.{_, max u v m}.symm
        (Abelian.Ext.homAddEquiv (ξ.comp hS.extClass rfl))) =
    (shortExact_extCochainComplexShortComplexRight G S hG hS).δ n (n + 1) rfl
      (((extSourceComparison.{u, v, m} G hG).hom.app n).app S.X₃
        (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (Abelian.Ext.homAddEquiv ξ)))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact hn.symm

/-- The injective comparison intertwines the connecting map of a short exact sequence of sources
with the cohomological connecting map of the reversed sequence of cochain complexes. -/
theorem extAddEquivCohomology_of_arrowwiseInjective_delta
    (F : PresheafOfModules.{max u v m} O)
    (hF : ∀ {U V : C} (f : U ⟶ V),
      Injective ((ModuleCat.restrictScalars (O.map f.op).hom).obj (F.obj (op U))))
    (S : ShortComplex (PresheafOfModules.{max u v m} O)) (hS : S.ShortExact)
    (n : ℕ) (e : Abelian.zExt S.X₁ F (n : ℤ)) :
    extAddEquivCohomology_of_arrowwiseInjective.{u, v, m} S.X₃ F hF (n + 1)
        (ShiftedHom.comp hS.singleδ e (by omega)) =
      (shortExact_extCochainComplexShortComplexLeft F S hF hS).δ n (n + 1) rfl
        (extAddEquivCohomology_of_arrowwiseInjective.{u, v, m} S.X₁ F hF n e) := by
  let : HasExt.{max u v m} (PresheafOfModules.{max u v m} O) :=
    hasExt_presheafOfModules.{u, v, m}
  obtain ⟨ξ, rfl⟩ := (Abelian.Ext.homAddEquiv.{_, max u v m}
    (X := S.X₁) (Y := F) (n := n)).surjective e
  have hn : (extCochainFixedTargetDeltaFunctor F hF).δ hS.op n
        (((extTargetComparison.{u, v, m} F hF).hom.app n).app (op S.X₁) ξ) =
      ((extTargetComparison.{u, v, m} F hF).hom.app (n + 1)).app (op S.X₃)
        ((extTargetDeltaFunctor.{u, v, m} F).δ hS.op n ξ) :=
    ConcreteCategory.congr_hom ((extTargetComparison.{u, v, m} F hF).hom.comm hS.op n) ξ
  have hc : ShiftedHom.comp hS.singleδ
      (Abelian.Ext.homAddEquiv ξ : Abelian.zExt S.X₁ F (n : ℤ)) (by omega) =
      (Abelian.Ext.homAddEquiv (hS.extClass.comp ξ (by omega)) :
        Abelian.zExt S.X₃ F ((n + 1 : ℕ) : ℤ)) := by
    simp only [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom, hS.extClass_hom]
  rw [hc]
  show ((extTargetComparison.{u, v, m} F hF).hom.app (n + 1)).app (op S.X₃)
      (Abelian.Ext.homAddEquiv.{_, max u v m}.symm
        (Abelian.Ext.homAddEquiv (hS.extClass.comp ξ (by omega)))) =
    (shortExact_extCochainComplexShortComplexLeft F S hF hS).δ n (n + 1) rfl
      (((extTargetComparison.{u, v, m} F hF).hom.app n).app (op S.X₁)
        (Abelian.Ext.homAddEquiv.{_, max u v m}.symm (Abelian.Ext.homAddEquiv ξ)))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact hn.symm

end ExtComparison

end Stacks.CategoryExt

end
