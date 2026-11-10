module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of an injective sheaf of modules along a monomorphism

Let `𝒪` be a sheaf of rings on a site and let `a : U' ⟶ U` be a monomorphism of objects of
the site. If `ℐ` is an injective object of the category of sheaves of `𝒪`-modules, then the
restriction map `ℐ(U) ⟶ ℐ(U')` is surjective: every section over `U'` extends to a section over
`U`.

## Main results

* `Stacks.Injectives.surjective_presheaf_map_of_injective`: the restriction map of an
  injective sheaf of modules along a monomorphism of objects of the site is surjective.
* `Stacks.Injectives.injective_restriction_surjective`: the same statement for the structure
  sheaf of a ringed site.

## Implementation notes

The sheaf of rings of a ringed site is `AlgebraicGeometry.RingedSite.ringSheaf`, the structure
sheaf with commutativity forgotten. The restriction map is the map of the underlying presheaf of
modules induced by `a.op`.

## References

* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.Injectives

universe u u'

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Corepresenting

variable (R : Sheaf J RingCat.{u})

/-- The sheaf of `R`-modules corepresenting the sections over `U`: the sheafification of the
free presheaf of modules on `yoneda.obj U`. -/
private def sectionsCorepresenting (U : C) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

/-- Maps out of `sectionsCorepresenting R U` are the sections over `U`. -/
private def sectionsCorepresentingHomEquiv (U : C) (I : SheafOfModules.{u} R) :
    (sectionsCorepresenting R U ⟶ I) ≃ I.val.presheaf.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
    (PresheafOfModules.freeHomEquiv.trans yonedaEquiv)

/-- The map of corepresenting objects induced by a morphism of the site. -/
private def sectionsCorepresentingMap {U' U : C} (a : U' ⟶ U) :
    sectionsCorepresenting R U' ⟶ sectionsCorepresenting R U :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map a))

/-- A monomorphism of the site induces a monomorphism of corepresenting objects. -/
private lemma mono_sectionsCorepresentingMap {U' U : C} (a : U' ⟶ U) [Mono a] :
    Mono (sectionsCorepresentingMap R a) := by
  have hfree : Mono ((PresheafOfModules.free R.obj).map (yoneda.map a)) := by
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective
      ((ModuleCat.free (R.obj.obj V)).map ((yoneda.map a).app V))
    intro x y hxy
    apply Finsupp.mapDomain_injective (f := fun f : V.unop ⟶ U' => f ≫ a)
      fun _ _ h => (cancel_mono a).1 h
    simp only [ModuleCat.free, ModuleCat.hom_ofHom] at hxy
    exact hxy
  exact Functor.map_mono _ _

end Corepresenting

/-- Yoneda naturality for the free presheaf of modules: restricting the section
corresponding to `f` along `a` corresponds to precomposing `f` with the free presheaf of
modules on `yoneda.map a`. -/
private lemma forget_map_yonedaEquiv_freeHomEquiv {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {U' U : C}
    (a : U' ⟶ U) (M : PresheafOfModules.{u} R₀)
    (f : (PresheafOfModules.free R₀).obj (yoneda.obj U) ⟶ M) :
    (M.presheaf ⋙ forget AddCommGrpCat).map a.op
        (yonedaEquiv (PresheafOfModules.freeHomEquiv f)) =
      yonedaEquiv (PresheafOfModules.freeHomEquiv
        ((PresheafOfModules.free R₀).map (yoneda.map a) ≫ f)) := by
  rw [yonedaEquiv_naturality]
  congr 1
  exact ((PresheafOfModules.freeAdjunction R₀).homEquiv_naturality_left (yoneda.map a) f).symm

/-- The equivalence of `sectionsCorepresentingHomEquiv` is compatible with restriction:
restricting a section along `a` corresponds to precomposing with
`sectionsCorepresentingMap`. -/
private lemma sectionsCorepresentingHomEquiv_restrict {R : Sheaf J RingCat.{u}} {U' U : C}
    (a : U' ⟶ U) (I : SheafOfModules.{u} R) (f : sectionsCorepresenting R U ⟶ I) :
    I.val.presheaf.map a.op (sectionsCorepresentingHomEquiv R U I f) =
      sectionsCorepresentingHomEquiv R U' I (sectionsCorepresentingMap R a ≫ f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
    ((SheafOfModules.forget R).obj I)
  change (M.presheaf ⋙ forget AddCommGrpCat).map a.op
      (yonedaEquiv (PresheafOfModules.freeHomEquiv (adj.homEquiv _ _ f))) =
    yonedaEquiv (PresheafOfModules.freeHomEquiv
      (adj.homEquiv _ _ (sectionsCorepresentingMap R a ≫ f)))
  refine (forget_map_yonedaEquiv_freeHomEquiv a M (adj.homEquiv _ _ f)).trans
    (congrArg (fun z => yonedaEquiv (PresheafOfModules.freeHomEquiv z)) ?_)
  exact (adj.homEquiv_naturality_left
    ((PresheafOfModules.free R.obj).map (yoneda.map a)) f).symm

/-- Restriction of an injective sheaf of modules along a monomorphism of objects of the site
is surjective. -/
public theorem surjective_presheaf_map_of_injective {R : Sheaf J RingCat.{u}} {U' U : C}
    (a : U' ⟶ U) [Mono a] (I : SheafOfModules.{u} R) [Injective I] :
    Function.Surjective (I.val.presheaf.map a.op) := by
  intro y
  let _ : Mono (sectionsCorepresentingMap R a) := mono_sectionsCorepresentingMap R a
  let f := (sectionsCorepresentingHomEquiv R U' I).symm y
  refine ⟨sectionsCorepresentingHomEquiv R U I
    (Injective.factorThru f (sectionsCorepresentingMap R a)), ?_⟩
  rw [sectionsCorepresentingHomEquiv_restrict, Injective.comp_factorThru]
  exact (sectionsCorepresentingHomEquiv R U' I).apply_symm_apply y

/-- On a ringed site, restriction of an injective sheaf of modules over the
structure sheaf along a monomorphism of objects of the site is surjective. -/
@[stacks 093X]
public theorem injective_restriction_surjective (X : AlgebraicGeometry.RingedSite.{u, u, u})
    {U' U : X.C} (a : U' ⟶ U)
    [Mono a]
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [Injective I] :
    Function.Surjective (I.val.presheaf.map a.op) :=
  surjective_presheaf_map_of_injective a I

end Stacks.Injectives

end
