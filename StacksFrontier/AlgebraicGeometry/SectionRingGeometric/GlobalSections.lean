module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.TransferInstance
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.Basic

/-!
# Honest global sections as the carrier of the section ring

`StacksFrontier/AlgebraicGeometry/GradedSections/Monoidal.lean` builds the graded ring
`Γ_*(L) = ⨁_{n ≥ 0} (𝟙_ C ⟶ L ^⊗ n)` on morphisms out of the monoidal unit, which is the right
carrier for an arbitrary monoidal category but not the one Stacks Tag 01CV and its consumers use:
they work with the module of global sections `Γ(L ^⊗ n, ⊤)`. This file identifies the two for
sheaves of modules, additively, and transports the commutative ring structure to the honest
global sections.

**Why they agree, and why it is not a triviality.** The monoidal unit of `SheafOfModules` is the
sheafification of the presheaf unit and so is the structure sheaf
(`AlgebraicGeometry.SheafOfModules.unitIso`), and Mathlib's
`SheafOfModules.unitHomEquiv` identifies morphisms out of the free rank-one sheaf with the type of
*sections* of `F`, that is, with the restriction-compatible families `(s_U)_{U}`. That type is not
`Γ(F, ⊤)` for a general site: it is the limit of `F` over the whole site. The two agree exactly
because the site of opens has a terminal object, and `sectionsEquivObj` is that step, stated for
an arbitrary terminal object of an arbitrary site.

## Main definitions

* `Stacks.SectionRingGeometric.homAddEquivOfIso`: precomposition with an isomorphism, as an
  additive isomorphism of hom groups.
* `Stacks.SectionRingGeometric.sectionsEquivObj`: for a presheaf of modules on a site with a
  terminal object, the type of sections is the module of sections over that object.
* `Stacks.SectionRingGeometric.unitHomAddEquiv`: `(unit 𝒪 ⟶ F) ≃+ Γ(F, ⊤)`.
* `Stacks.SectionRingGeometric.tensorUnitHomAddEquiv`: **`(𝟙_ ⟶ F) ≃+ Γ(F, ⊤)`**, the carrier
  comparison.
* `Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv`: the comparison in every degree at
  once, `Γ_*(L) ≃+ ⨁_{n ≥ 0} Γ(L ^⊗ n, ⊤)`.
* `Stacks.SectionRingGeometric.gradedGlobalSectionsCommRing`: **`⨁_{n ≥ 0} Γ(L ^⊗ n, ⊤)` is a
  commutative ring**, for an invertible module on a scheme.

## Implementation notes

**The additivity is definitional.** Every one of the three bijections composed here is additive by
`rfl`: the hom groups of `SheafOfModules` are the hom groups of the underlying presheaves of
modules (`SheafOfModules.add_val`), those are sectionwise (`PresheafOfModules.add_app`), and
Mathlib's unit correspondence is evaluation at `1`, which is additive on the nose. So no
compatibility has to be checked by hand, and the `map_add'` fields below are `rfl`.

**Why the transported ring structure is stated and not unfolded.** The multiplication on
`⨁ Γ(L ^⊗ n, ⊤)` is the transport of the one on `Γ_*(L)` along the comparison, so by
construction it is the product of Stacks Tag 01CV read on honest sections; it is *not* given here
by a formula on sections. Supplying such a formula would mean computing the monoidality
isomorphism of sheafification on sections, which this repository does not have (see the "what is
not done" of `StacksFrontier/AlgebraicGeometry/SheafInternalHom/Basic.lean`).

**Universes and local instances.** As in the sibling file: polymorphic in the site universes and
the module universe where it can be, monomorphic in `u` for schemes, and the monoidal and braided
structures on `SheafOfModules` are reintroduced with a local-instance attribute in every section
whose statement mentions `𝟙_`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)

## What is not done

**The one clause of Stacks Tag 01CV that is still open, precisely.** The carrier produced here is
the direct sum of the honest global sections of the nonnegative tensor powers, which is the
carrier the source and this repository's consumers ask for, and it carries a commutative graded
ring structure. What is *not* produced is the identification of that product with the explicit
one: the composite that tensors two global sections pointwise, pushes the result through the
sheafification unit, and applies the addition isomorphism of Stacks Tag 01CU. That identification
needs the monoidality isomorphism of sheafification evaluated on sections, and this repository has
it only abstractly. At this Mathlib pin that isomorphism *is*
`CategoryTheory.Localization.Monoidal.μ`, a component of a `Lifting₂.iso`, and its entire API is
naturality in each argument plus three structural coherences — there is no component formula
anywhere in `Mathlib/CategoryTheory/`, `Mathlib/CategoryTheory/Sites/Monoidal.lean` has nothing
section-level, and `SheafOfModules` has no monoidal structure in Mathlib at all.

**Computing with a product of sections does not need that clause first.** In particular the
multiplicativity of the nonvanishing loci, `X_{st} = X_s ∩ X_t`, does not.
Surjectivity of a stalk map is stable under composition with isomorphisms, so the geometric
statement needs only that the comparison *is* invertible, never its value on sections — and
`X_{st} = X_s ∩ X_t` is proved on exactly that observation, as
`Stacks.SectionProduct.nonvanishingLocus_mul`
(`StacksFrontier/AlgebraicGeometry/SectionProduct/Basic.lean`). What remains open is the
identification of the transported product with the explicit composite, and nothing else.

No Stacks attribute is attached to anything here.

Nothing is said about negative degrees, and the graded module `Γ_*(X, L, F)` of Stacks Tag 01CV
is still not constructed.
-/

@[expose] public section

universe v₁ u₁ v u w

open CategoryTheory Category MonoidalCategory Limits Stacks.SheafOfModules.TensorSheafification
  Opposite
open TopologicalSpace

open scoped DirectSum

namespace Stacks.SectionRingGeometric

/-- Precomposition with an isomorphism, as an additive isomorphism of hom groups. -/
def homAddEquivOfIso {D : Type u₁} [Category.{v₁} D] [Preadditive D] {A B : D} (e : A ≅ B)
    (F : D) : (A ⟶ F) ≃+ (B ⟶ F) where
  toFun f := e.inv ≫ f
  invFun g := e.hom ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

section Sections

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- **On a site with a terminal object, the sections of a presheaf of modules are the sections
over that object.** A restriction-compatible family is determined by its value at the terminal
object, because every object receives a unique morphism to it. Without a terminal object the type
of sections is the limit over the whole site and there is nothing to compare it to. -/
noncomputable def sectionsEquivObj {T : C} (hT : IsTerminal T) (M : PresheafOfModules.{w} R) :
    M.sections ≃ M.obj (op T) where
  toFun s := s.val (op T)
  invFun m := PresheafOfModules.sectionsMk (fun U ↦ M.map (hT.from U.unop).op m) (by
    intro U V f
    rw [← PresheafOfModules.map_comp_apply]
    exact M.congr_map_apply (Quiver.Hom.unop_inj (hT.hom_ext _ _)) m)
  left_inv s := by
    refine PresheafOfModules.sections_ext _ _ fun U ↦ ?_
    exact PresheafOfModules.sections_property s _
  right_inv m := by
    have h : (hT.from (op T).unop).op = 𝟙 (op T) := Quiver.Hom.unop_inj (hT.hom_ext _ _)
    refine (M.congr_map_apply h m).trans ?_
    simp
    rfl

end Sections

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Morphisms out of the free rank-one sheaf of modules are global sections**, additively, on a
site with a terminal object. -/
noncomputable def unitHomAddEquiv {T : C} (hT : IsTerminal T) (F : SheafOfModules.{w} R) :
    (SheafOfModules.unit R ⟶ F) ≃+ F.val.obj (op T) where
  toEquiv := F.unitHomEquiv.trans (sectionsEquivObj hT F.val)
  map_add' _ _ := rfl

end Unit

section TensorUnit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory

/-- **The carrier comparison.** Morphisms out of the monoidal unit of `SheafOfModules` are the
honest global sections. The monoidal unit is the structure sheaf by
`AlgebraicGeometry.SheafOfModules.unitIso`, and morphisms out of the structure sheaf are global
sections by `unitHomAddEquiv`. -/
noncomputable def tensorUnitHomAddEquiv {T : C} (hT : IsTerminal T)
    (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) ≃+ F.val.obj (op T) :=
  (homAddEquivOfIso (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪) F).trans
    (unitHomAddEquiv hT F)

end TensorUnit

/-! ### Schemes -/

section Scheme

open AlgebraicGeometry

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory presheafMonoidalPreadditiveStructure
  sheafifyAdditive tensorLeftAdditive tensorRightAdditive

variable (X : Scheme.{u})

/-- **`Γ(F, ⊤)` is the group of morphisms out of the monoidal unit**, for an `𝒪_X`-module on a
scheme: the site of opens has `⊤` as a terminal object. This is the carrier comparison in the
vocabulary of the tagged statements. -/
noncomputable def schemeGlobalSectionsAddEquiv (F : X.Modules) :
    (𝟙_ X.Modules ⟶ F) ≃+ Γ(F, ⊤) :=
  tensorUnitHomAddEquiv X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    isTerminalTop F

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The graded carrier comparison**: the section ring of Stacks Tag 01CV, built on morphisms out
of the monoidal unit, is additively the direct sum of the honest global sections of the tensor
powers. -/
noncomputable def gradedGlobalSectionsAddEquiv :
    Stacks.GradedSections.sectionRing L ≃+
      ⨁ n : ℕ, Γ(Stacks.TensorPowers.natTensorPow L n, ⊤) :=
  DirectSum.congrAddEquiv fun n ↦
    schemeGlobalSectionsAddEquiv X (Stacks.TensorPowers.natTensorPow L n)

/-- **`⨁_{n ≥ 0} Γ(L ^⊗ n, ⊤)` is a commutative ring**, for an invertible `𝒪_X`-module on a
scheme. The multiplication is the transport of the one of Stacks Tag 01CV along
`gradedGlobalSectionsAddEquiv`; see the module docstring on why no sectionwise formula is given
for it.

**A defect to know about before using this instance.** It is built with `Equiv.commRing`, which
transports the *addition* as well, so its `Add` is propositionally but **not definitionally** the
direct sum's own. With this instance in scope, a term mentioning `gradedGlobalSectionsAddEquiv`
can fail to elaborate with "synthesized type class instance is not definitionally equal". The
workaround, used by
`Stacks.SectionProduct.equiv_symm_mul_of`, is to state what you need outside this instance's
scope in terms of the underlying `Equiv`. The proper repair is to transport only the
multiplication and take the additive axioms from the existing `AddCommGroup` — Mathlib's
`Function.Injective.commRing` is the tool (see its use at
`Mathlib/Algebra/DirectSum/Ring.lean:507`), but it requires `Mul`, `One`, `Pow`, `NatCast` and
`IntCast` instances on the target to be supplied first, so it is a restructure rather than a
one-line change and has not been done. -/
@[instance_reducible]
noncomputable def gradedGlobalSectionsCommRing :
    CommRing (⨁ n : ℕ, Γ(Stacks.TensorPowers.natTensorPow L n, ⊤)) :=
  letI := schemeSectionCommRing X L
  (gradedGlobalSectionsAddEquiv X L).toEquiv.symm.commRing

end Scheme

end Stacks.SectionRingGeometric
