module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The internal hom for presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C`. Mathlib equips the category
`PresheafOfModulesOfCommRing R` of presheaves of `R`-modules with a symmetric monoidal structure
whose tensor product is computed sectionwise, but provides no internal hom for it: there is no
`MonoidalClosed` instance, and hence no dual `M ⟶[R] R` of a presheaf of modules. This file
supplies both. It is the theory under Stacks Tag 0B8K (the sheaf `Hom` of two modules) and the
construction that the dual of an invertible module needs.

The internal hom is obtained as an adjoint, not by hand. The input is the special adjoint functor
theorem together with two facts already in Mathlib: that `PresheafOfModules R` is a Grothendieck
abelian category, and that `tensorLeft M` preserves colimits. Those two facts are the only
properties of presheaves of modules used, so the argument is isolated here as a statement about
an arbitrary Grothendieck abelian monoidal category,
`Stacks.InternalHom.monoidalClosedOfGrothendieckAbelian`. That factoring is deliberate: it is
exactly the form in which the same conclusion will apply to sheaves of modules, see the
implementation notes.

## Main definitions

* `Stacks.InternalHom.monoidalClosedOfGrothendieckAbelian`: a Grothendieck abelian monoidal
  category in which every `tensorLeft M` preserves colimits is monoidal closed.
* `Stacks.InternalHom.dual`: in a monoidal category, the dual `(ihom A).obj (𝟙_ C)` of a closed
  object, i.e. the internal hom into the unit.
* `Stacks.InternalHom.dualEv`: the evaluation map `A ⊗ dual A ⟶ 𝟙_ C`.
* `Stacks.InternalHom.dualIso` and `Stacks.InternalHom.dualIsoLeft`: the evaluation read as an
  isomorphism `A ⊗ dual A ≅ 𝟙_ D`, when `tensorLeft A` is an equivalence, and its braided form
  `dual A ⊗ A ≅ 𝟙_ D`.
* `Stacks.InternalHom.sectionsEquiv`: the sections of the internal hom of presheaves of modules
  over an object `X` of `C`, described as maps out of a tensor product with a free presheaf of
  modules on a Yoneda presheaf.
* `Stacks.InternalHom.sheafOfModulesMonoidalClosed`: the sheaf-level internal hom, reduced to the
  one input that is missing at this Mathlib pin.
* `Stacks.InternalHom.schemeMonoidalCategory` and `Stacks.InternalHom.schemeMonoidalClosed`: the
  monoidal structure and the internal hom on presheaves of modules over a scheme, in Mathlib's
  own `AlgebraicGeometry.Scheme.PresheafOfModules` spelling.

## Main results

* `Stacks.InternalHom.instMonoidalClosed`: the instance
  `MonoidalClosed (PresheafOfModulesOfCommRing R)` for a presheaf of commutative rings `R` on a
  small category. This is the main content of the file.
* `Stacks.InternalHom.isIso_ev_app` and `Stacks.InternalHom.isIso_coev_app`: if `tensorLeft A` is
  an equivalence, then every component of the evaluation and of the coevaluation is an
  isomorphism. Together with `dualIso` this is the step that an invertible module needs: for `L`
  invertible, the evaluation `L ⊗ dual L ⟶ 𝟙_` is an isomorphism.
* `Stacks.InternalHom.sectionsEquiv_naturality`: `sectionsEquiv` is natural in the target.

## Implementation notes

The adjoint functor theorem is applied at the universe of the module sections. Concretely, for
`C : Type u` a small category and `R : Cᵒᵖ ⥤ CommRingCat.{u}`, the internal hom is built on
`PresheafOfModulesOfCommRing.{u} R`; the three side conditions of
`isLeftAdjoint_of_preservesColimits_of_isSeparating` — cocompleteness, local smallness and
well-copoweredness — all come from `IsGrothendieckAbelian.{u}`, the last through
`CategoryTheory.wellPowered_opposite`, which needs the category to be abelian. The separating
family is the single separator supplied by `HasSeparator`; for presheaves of modules that
separator is a coproduct of the free modules on Yoneda presheaves,
`PresheafOfModules.hasSeparator`.

Three reducibility and transparency gotchas were hit. All are worked around with ordinary
tactics and attributes, with no compiler option switched anywhere in this file:

* `ihom.ev A` is a `def` unfolding to `(ihom.adjunction A).counit`, and `IsIso` of a component of
  the counit of an adjunction with fully faithful right adjoint is found by instance search only
  in the latter spelling. The two are definitionally equal at default transparency but not at
  instance transparency, so `isIso_ev_app` is proved by `change` to the counit spelling followed
  by `infer_instance`, rather than by a direct `inferInstance`.
* `monoidalClosedOfGrothendieckAbelian` is a definition of class type, so it carries
  `@[instance_reducible]`; without it Lean warns that the definition is semireducible and the
  build is not warning-free.
* `AlgebraicGeometry.Scheme.PresheafOfModules X` is `PresheafOfModules X.ringCatSheaf.obj`, and
  `X.ringCatSheaf` is a `TopCat.Sheaf`, so it is not syntactically a composition with `forget₂`.
  Neither the monoidal structure nor the internal hom is therefore found for it by instance
  search, even though both hold definitionally. `schemeMonoidalCategory` and
  `schemeMonoidalClosed` bridge this with `inferInstanceAs`, and the latter carries the former as
  a `letI` in its type rather than relying on an attribute.

The internal hom produced here is an abstract right adjoint: it has no chosen formula. What pins
it down is `sectionsEquiv`, which identifies its sections over `X : C` with
`M ⊗ (free R).obj (yoneda.obj X) ⟶ N`, using
`PresheafOfModules.freeYonedaEquiv` and the adjunction. Unwinding that further to the end
description of Stacks Tag 0B8K — a restriction-compatible family of `R`-linear maps
`M.obj Y ⟶ N.obj Y` indexed by maps `Y ⟶ X` — is not carried out here.

## What is not done

The sheaf-level internal hom is not constructed, and the mathematical question of whether
sheafification is needed is not settled here. What is established is the exact shape of the
remaining gap, in `sheafOfModulesMonoidalClosed`: `SheafOfModules R` is already known to Mathlib
to be Grothendieck abelian, so by `monoidalClosedOfGrothendieckAbelian` an internal hom for
sheaves of modules follows from a monoidal structure on `SheafOfModules R` whose `tensorLeft`
preserves colimits — and nothing else. Mathlib at this pin has no monoidal structure on
`SheafOfModules R` at all, which is why `sheafOfModulesMonoidalClosed` must take it as a
hypothesis.

On the mathematical question, the expected answer is that no sheafification is needed: the
internal hom of two presheaves of modules whose target is a sheaf should already be a sheaf,
because its sections are cut out by a limit. The reduction of that statement to a single
remaining input, carried out on paper and not in Lean, runs as follows. By `sectionsEquiv` the
sections of `(ihom M).obj N` over `X` are `M ⊗ F X ⟶ N`, with `F X` the free presheaf of modules
on `yoneda.obj X`. A sieve `S` on `X` is a colimit of representables, and both `free` and
`M ⊗ -` preserve colimits, so descent data for `(ihom M).obj N` along `S` is exactly
`M ⊗ F S ⟶ N`. The sheaf condition for `(ihom M).obj N` is therefore the assertion that
restriction along `M ⊗ (free _).map ι` is bijective on maps into `N`, for `ι : S ⟶ yoneda.obj X`
the sieve inclusion. Since `N` is a sheaf, maps into `N` invert local isomorphisms, and
`(free _).map ι` is one; so the whole statement reduces to: tensoring a local isomorphism of
presheaves of modules by a fixed `M` again gives a local isomorphism. That last step is
equivalent to monoidality of sheafification, and is the only thing missing. It is also precisely
what Mathlib proves for presheaves valued in a closed monoidal category, in
`CategoryTheory.GrothendieckTopology.W.whiskerLeft` — and that proof goes through
`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`, which needs the internal hom in its
explicit end form rather than as an abstract adjoint. Supplying that end form for presheaves of
modules is where further work should start; the abstract adjoint built here cannot
substitute for it, because the argument above is circular without it.

No Stacks attribute is attached to anything in this file: it is general library infrastructure.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits MonoidalCategory Opposite

namespace Stacks.InternalHom

section GrothendieckAbelian

variable (D : Type u) [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{w} D]
  [MonoidalCategory D] [∀ M : D, PreservesColimitsOfSize.{w, w} (tensorLeft M)]

/-- A Grothendieck abelian monoidal category in which tensoring on the left by any object
preserves colimits is monoidal closed: the special adjoint functor theorem produces the right
adjoint of `tensorLeft M`, and a Grothendieck abelian category supplies every one of its side
conditions — cocompleteness, local smallness, well-copoweredness and a separator. -/
@[instance_reducible]
noncomputable def monoidalClosedOfGrothendieckAbelian : MonoidalClosed D :=
  MonoidalClosed.mk fun M ↦
    have : (tensorLeft M).IsLeftAdjoint :=
      isLeftAdjoint_of_preservesColimits_of_isSeparating.{w} (isSeparator_separator D) _
    Closed.mk _ (Adjunction.ofIsLeftAdjoint (tensorLeft M))

end GrothendieckAbelian

section Dual

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] (A : D) [Closed A]

/-- The dual of a closed object of a monoidal category: the internal hom into the unit. -/
noncomputable abbrev dual : D := (ihom A).obj (𝟙_ D)

/-- The evaluation map `A ⊗ dual A ⟶ 𝟙_ D`, the component at the unit of the evaluation of the
internal hom adjunction. -/
noncomputable abbrev dualEv : A ⊗ dual A ⟶ 𝟙_ D := (ihom.ev A).app (𝟙_ D)

variable [(tensorLeft A).IsEquivalence]

/-- The right adjoint of `tensorLeft A` is an equivalence as soon as `tensorLeft A` is. -/
theorem ihom_isEquivalence : (ihom A).IsEquivalence :=
  (ihom.adjunction A).isEquivalence_right_of_isEquivalence_left

/-- If tensoring on the left by `A` is an equivalence, every component of the evaluation of the
internal hom adjunction is an isomorphism. -/
theorem isIso_ev_app (X : D) : IsIso ((ihom.ev A).app X) := by
  have := ihom_isEquivalence A
  show IsIso ((ihom.adjunction A).counit.app X)
  infer_instance

/-- If tensoring on the left by `A` is an equivalence, every component of the coevaluation of the
internal hom adjunction is an isomorphism. -/
theorem isIso_coev_app (X : D) : IsIso ((ihom.coev A).app X) := by
  have := ihom_isEquivalence A
  show IsIso ((ihom.adjunction A).unit.app X)
  infer_instance

/-- The evaluation `A ⊗ dual A ⟶ 𝟙_ D` read as an isomorphism, when tensoring on the left by `A`
is an equivalence. This is the statement that an invertible object is invertible with inverse its
dual, with the inverse map being the evaluation. -/
noncomputable def dualIso : A ⊗ dual A ≅ 𝟙_ D :=
  have := isIso_ev_app A (𝟙_ D)
  asIso (dualEv A)

/-- The forward map of `dualIso A` is the evaluation `dualEv A`. -/
@[simp]
theorem dualIso_hom : (dualIso A).hom = dualEv A := rfl

/-- The braided form of `dualIso`: in a braided monoidal category, an object whose left tensoring
is an equivalence satisfies `dual A ⊗ A ≅ 𝟙_ D`. This is the side on which Stacks Tag 01CS states
invertibility. -/
noncomputable def dualIsoLeft [BraidedCategory D] : dual A ⊗ A ≅ 𝟙_ D :=
  BraidedCategory.braiding (dual A) A ≪≫ dualIso A

end Dual

section PresheafOfModules

variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ CommRingCat.{u})

/-- **The internal hom for presheaves of modules.** For a presheaf of commutative rings `R` on a
small category, the symmetric monoidal category of presheaves of `R`-modules is closed. -/
noncomputable instance instMonoidalClosed :
    MonoidalClosed (PresheafOfModulesOfCommRing.{u} R) :=
  monoidalClosedOfGrothendieckAbelian.{u} _

variable {R}

/-- The sections of the internal hom of presheaves of modules over an object `X` of `C`,
identified with the maps `M ⊗ (free R).obj (yoneda.obj X) ⟶ N`. This is what pins down the
internal hom, which on its own is only an abstract right adjoint. -/
noncomputable def sectionsEquiv (M N : PresheafOfModulesOfCommRing.{u} R) (X : C) :
    ((ihom M).obj N).obj (op X) ≃
      (M ⊗ (PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X) ⟶ N) :=
  PresheafOfModules.freeYonedaEquiv.symm.trans ((ihom.adjunction M).homEquiv _ _).symm

/-- `sectionsEquiv` is the inverse of `freeYonedaEquiv` followed by the inverse of the
hom-equivalence of the internal hom adjunction. -/
theorem sectionsEquiv_apply (M N : PresheafOfModulesOfCommRing.{u} R) (X : C)
    (s : ((ihom M).obj N).obj (op X)) :
    sectionsEquiv M N X s =
      ((ihom.adjunction M).homEquiv _ _).symm (PresheafOfModules.freeYonedaEquiv.symm s) :=
  rfl

/-- `sectionsEquiv` is natural in the target: transporting a section of the internal hom along
`g : N ⟶ N'` corresponds to postcomposition with `g`. -/
theorem sectionsEquiv_naturality {M N N' : PresheafOfModulesOfCommRing.{u} R} (g : N ⟶ N')
    (X : C) (s : ((ihom M).obj N).obj (op X)) :
    sectionsEquiv M N' X (((ihom M).map g).app (op X) s) = sectionsEquiv M N X s ≫ g := by
  have h : PresheafOfModules.freeYonedaEquiv.symm (((ihom M).map g).app (op X) s) =
      PresheafOfModules.freeYonedaEquiv.symm s ≫ (ihom M).map g := by
    refine PresheafOfModules.freeYonedaEquiv.symm_apply_eq.mpr ?_
    rw [PresheafOfModules.freeYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [sectionsEquiv_apply, sectionsEquiv_apply, h,
    Adjunction.homEquiv_naturality_right_symm]

end PresheafOfModules

section SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- **The internal hom for sheaves of modules, reduced to its one missing input.** Mathlib knows
that `SheafOfModules R` is Grothendieck abelian, so the construction used for presheaves of
modules applies verbatim and produces an internal hom for sheaves of modules — as soon as there
is a monoidal structure on `SheafOfModules R` whose `tensorLeft` preserves colimits. At this
Mathlib pin there is no monoidal structure on `SheafOfModules R`, so that structure is a
hypothesis here; constructing it is the remaining work, and it is the whole of the remaining
work. -/
@[instance_reducible]
noncomputable def sheafOfModulesMonoidalClosed [MonoidalCategory (SheafOfModules.{u} R)]
    [∀ M : SheafOfModules.{u} R, PreservesColimitsOfSize.{u, u} (tensorLeft M)] :
    MonoidalClosed (SheafOfModules.{u} R) :=
  monoidalClosedOfGrothendieckAbelian.{u} _

end SheafOfModules

section Scheme

open AlgebraicGeometry

/-- The sectionwise monoidal structure on presheaves of modules over a scheme. This is not found
by instance search from Mathlib's `AlgebraicGeometry.Scheme.PresheafOfModules`, which is phrased
through `X.ringCatSheaf.obj` rather than through a composition with `forget₂`: the two agree at
default transparency but not at instance transparency. -/
@[instance_reducible]
noncomputable def schemeMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

/-- **The internal hom for presheaves of modules over a scheme.** The instance for a general
small site, transported across the identification of `X.PresheafOfModules` with presheaves of
modules over the presheaf of commutative rings `X.presheaf`. -/
@[instance_reducible]
noncomputable def schemeMonoidalClosed (X : Scheme.{u}) :
    letI := schemeMonoidalCategory X
    MonoidalClosed X.PresheafOfModules :=
  inferInstanceAs (MonoidalClosed (PresheafOfModulesOfCommRing.{u} X.presheaf))

end Scheme

end Stacks.InternalHom

end
