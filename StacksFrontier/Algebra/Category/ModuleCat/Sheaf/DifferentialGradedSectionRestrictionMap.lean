module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionDerived
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction

/-!
# The derived restriction map of a morphism of a chaotic site

Let `(A, d)` be a sheaf of differential graded algebras on a site, let `a : V ⟶ U` be a morphism
of `Cᵒᵖ` and let `M` be a right differential graded `A`-module. Restricting local sections along
`a` is a homomorphism `M(V) ⟶ M(U)` of differential graded `A(V)`-modules, the target being read
through restriction of scalars along the restriction homomorphism `A(V) ⟶ A(U)` of section
algebras. This file assembles those homomorphisms into a single natural transformation, first on
the homotopy categories and then — on a chaotic site, where taking sections already inverts the
quasi-isomorphisms — on the derived categories:

`RΓ(V, -) ⟶ RΓ(U, -)_{A(V)}`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.sectionModuleRestrictionNatTrans`: restriction of
  sections as a natural transformation `M(V) ⟶ M(U)_{A(V)}` of functors on right differential
  graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.sectionHomotopyRestriction`: **restriction of sections
  on the homotopy categories**, `K(A(V)) ∋ M(V) ⟶ M(U)_{A(V)}`.
* `SheafOfModules.DifferentialGradedModule.sectionHomotopyRestrictionLocalized`: the same
  transformation read in the derived category of `A(V)`, through the factorization of derived
  restriction of scalars.
* `SheafOfModules.DifferentialGradedModule.derivedRestrictionMap`: **the derived restriction map
  `RΓ(V, -) ⟶ RΓ(U, -)_{A(V)}`** of a morphism `a : V ⟶ U` of a chaotic site.
* `SheafOfModules.DifferentialGradedModule.derivedSectionsIso`: the identification of the derived
  sections of the class of a right differential graded module with the class of its sections, as
  an isomorphism of functors on right differential graded `A`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionHomotopyRestriction_app_quotient`: the value of
  the transformation on homotopy categories at the homotopy class of `M` is the homotopy class of
  restriction of sections.
* `SheafOfModules.DifferentialGradedModule.derivedRestrictionMap_app_toDerivedCategory`: **on the
  image of a right differential graded module the derived restriction map is restriction of
  sections**, read through the identifications of the derived sections and the factorization of
  derived restriction of scalars.

## Implementation notes

The transformation on the homotopy categories is `CategoryTheory.Quotient.natTransLift` applied
to the family of homotopy classes of the restriction homomorphisms: both the section functor on
homotopy categories and restriction of scalars on homotopy categories are `Quotient.lift`s, so
the two ends of a component are the homotopy classes of the differential graded modules
themselves, and the naturality square is the naturality of restriction of sections,
`SheafOfModules.DifferentialGradedModule.sectionRestrictAdd_sectionMapAdd`, pushed into the
homotopy category.

Passing to the derived categories is `CategoryTheory.Localization.liftNatTrans`. Its two lifting
data are the one that `CategoryTheory.Localization.lift` produces for the derived sections — which
is the content of `liftingDerivedSections`, since derived sections are opaque to instance search —
and `CategoryTheory.Localization.Lifting.compRight` for the composite with derived restriction of
scalars. Because both lifting data are the canonical ones, `Localization.liftNatTrans_app`
evaluates the derived restriction map on the image of a homotopy class as the factorization
isomorphism of the derived sections, the transformation on homotopy categories, and the
factorization isomorphism of derived restriction of scalars.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

/-! ### Restriction of sections on the homotopy categories -/

section Homotopy

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R) {U V : Cᵒᵖ}

/-- **Restriction of sections along `a : V ⟶ U`, as a natural transformation of functors on right
differential graded `A`-modules**: it sends `M` to the homomorphism `M(V) ⟶ M(U)` of differential
graded `A(V)`-modules, the target being read through restriction of scalars along the restriction
homomorphism `A(V) ⟶ A(U)`. Its naturality is the naturality of restriction of sections in the
differential graded module. -/
@[implicit_reducible]
def sectionModuleRestrictionNatTrans (a : V ⟶ U) :
    sectionModuleFunctor A V ⟶
      sectionModuleFunctor A U ⋙
        _root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction a) where
  app M := M.sectionModuleRestriction a
  naturality _ _ f :=
    _root_.DifferentialGradedModule.Hom.ext
      (LinearMap.ext fun x ↦ sectionRestrictAdd_sectionMapAdd f a x)

/-- The component of `sectionModuleRestrictionNatTrans` at `M` is restriction of sections of
`M` along `a`. -/
@[simp] theorem sectionModuleRestrictionNatTrans_app (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (sectionModuleRestrictionNatTrans A a).app M = M.sectionModuleRestriction a :=
  rfl

/-- **Restriction of sections along `a : V ⟶ U` on the homotopy categories**: the natural
transformation `K(A) ⥤ K(A(V))` from taking sections over `V` to taking sections over `U` and
restricting scalars along `A(V) ⟶ A(U)`. Both functors are descents through the homotopy quotient
of right differential graded `A`-modules, so the transformation is determined by the homotopy
classes of the restriction homomorphisms. -/
def sectionHomotopyRestriction (a : V ⟶ U) :
    sectionHomotopyFunctor A V ⟶
      sectionHomotopyFunctor A U ⋙
        _root_.DifferentialGradedModule.restrictScalarsHomotopyFunctor
          (A.sectionRestriction a) :=
  CategoryTheory.Quotient.natTransLift _
    { app := fun M ↦ (_root_.DifferentialGradedModule.toHomotopyCategory
        (A.sectionAlgebra V)).map (M.sectionModuleRestriction a)
      naturality := fun M N f ↦ by
        change (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
              (sectionMap f V) ≫
            (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
              (N.sectionModuleRestriction a) =
          (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
              (M.sectionModuleRestriction a) ≫
            (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
              (_root_.DifferentialGradedModule.restrictScalarsHom (A.sectionRestriction a)
                (sectionMap f U))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg
          (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
          ((sectionModuleRestrictionNatTrans A a).naturality f) }

/-- The transformation on homotopy categories, at the homotopy class of a right differential
graded module, is the homotopy class of restriction of sections. -/
theorem sectionHomotopyRestriction_app_quotient (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (sectionHomotopyRestriction A a).app ((HomotopyCategory.quotient A).obj M) =
      (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
        (M.sectionModuleRestriction a) :=
  rfl

end Homotopy

/-! ### The derived restriction map on a chaotic site -/

section Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R) {U V : Cᵒᵖ}

/-- The lifting datum exhibiting the derived sections over `U` as the descent of taking sections
on the homotopy categories. It is the datum that `CategoryTheory.Localization.lift` produces,
stated so that instance search can find it: the derived sections functor is defined by that
lift. -/
instance liftingDerivedSections (U : Cᵒᵖ) :
    Localization.Lifting (quasiIsomorphisms.{t, a, a} A).Q (quasiIsomorphisms.{t, a, a} A)
      (sectionHomotopyFunctor A U ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q)
      (derivedSections A U) :=
  Localization.liftingLift _ (quasiIsomorphisms_isInvertedBy_sectionHomotopyFunctor A U) _

/-- **The identification of derived sections with sections**, as an isomorphism of functors on
right differential graded `A`-modules: the derived sections over `U` of the class of `M` are the
class of the differential graded `A(U)`-module `M(U)` of its sections. -/
def derivedSectionsIso (U : Cᵒᵖ) :
    HomotopyCategory.quotient.{t, a, a} A ⋙ toDerivedCategory.{t, a, a} A ⋙
        derivedSections A U ≅
      sectionModuleFunctor A U ⋙
        _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) ⋙
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q :=
  Functor.isoWhiskerLeft (HomotopyCategory.quotient.{t, a, a} A)
      (derivedSectionsFactorization A U) ≪≫
    Functor.isoWhiskerRight (sectionHomotopyFunctorIso A U)
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q

/-- Restriction of sections on the homotopy categories, read in the derived category of `A(V)`:
the transformation on homotopy categories followed by localization, composed with the
factorization of derived restriction of scalars along `A(V) ⟶ A(U)`. This is the transformation
that the derived restriction map descends from. -/
def sectionHomotopyRestrictionLocalized (a : V ⟶ U) :
    sectionHomotopyFunctor A V ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q ⟶
      (sectionHomotopyFunctor A U ⋙
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q) ⋙
        _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) :=
  Functor.whiskerRight (sectionHomotopyRestriction A a)
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q ≫
    Functor.whiskerLeft (sectionHomotopyFunctor A U)
      (_root_.DifferentialGradedModule.derivedRestrictionFactorization
        (A.sectionRestriction a)).inv

/-- **The derived restriction map `RΓ(V, -) ⟶ RΓ(U, -)_{A(V)}`** of a morphism `a : V ⟶ U` of a
chaotic site: the descent through the localization at the quasi-isomorphisms of restriction of
sections on the homotopy categories, the target being read through derived restriction of scalars
along the restriction homomorphism `A(V) ⟶ A(U)` of section algebras. -/
def derivedRestrictionMap (a : V ⟶ U) :
    derivedSections A V ⟶
      derivedSections A U ⋙
        _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) :=
  Localization.liftNatTrans (quasiIsomorphisms.{t, a, a} A).Q (quasiIsomorphisms.{t, a, a} A)
    _ _ _ _ (sectionHomotopyRestrictionLocalized A a)

/-- The localized transformation, at the homotopy class of a right differential graded module:
the class of restriction of sections, localized, followed by the factorization of derived
restriction of scalars. -/
theorem sectionHomotopyRestrictionLocalized_app_quotient (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (sectionHomotopyRestrictionLocalized A a).app ((HomotopyCategory.quotient A).obj M) =
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
            (M.sectionModuleRestriction a)) ≫
        (_root_.DifferentialGradedModule.derivedRestrictionFactorization
            (A.sectionRestriction a)).inv.app
          ((sectionHomotopyFunctor A U).obj ((HomotopyCategory.quotient A).obj M)) :=
  rfl

/-- The lifting datum of the derived sections is their factorization through the localization:
the derived sections functor is defined by the lift that carries this datum. -/
theorem liftingIso_derivedSections_hom_app (U : Cᵒᵖ)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (Localization.Lifting.iso (quasiIsomorphisms.{t, a, a} A).Q (quasiIsomorphisms.{t, a, a} A)
        (sectionHomotopyFunctor A U ⋙
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q)
        (derivedSections A U)).hom.app ((HomotopyCategory.quotient A).obj M) =
      (derivedSectionsFactorization A U).hom.app ((HomotopyCategory.quotient A).obj M) :=
  rfl

/-- The lifting datum of the derived sections followed by derived restriction of scalars is the
factorization of the derived sections, carried through derived restriction of scalars. -/
theorem liftingIso_derivedSections_comp_inv_app (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (Localization.Lifting.iso (quasiIsomorphisms.{t, a, a} A).Q (quasiIsomorphisms.{t, a, a} A)
        ((sectionHomotopyFunctor A U ⋙
            (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q) ⋙
          _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a))
        (derivedSections A U ⋙
          _root_.DifferentialGradedModule.derivedRestriction
            (A.sectionRestriction a))).inv.app ((HomotopyCategory.quotient A).obj M) =
      (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
        ((derivedSectionsFactorization A U).inv.app ((HomotopyCategory.quotient A).obj M)) :=
  rfl

/-- The identification of derived sections with sections, at a right differential graded module,
is the factorization of the derived sections at its homotopy class: the descent of the section
functor to the homotopy categories is the identity on objects and on homotopy classes. -/
theorem derivedSectionsIso_hom_app (U : Cᵒᵖ) (M : DifferentialGradedModule.{t, a, a} A) :
    (derivedSectionsIso A U).hom.app M =
      (derivedSectionsFactorization A U).hom.app ((HomotopyCategory.quotient A).obj M) := by
  simp only [derivedSectionsIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The derived restriction map on the image of a homotopy class, read through the factorizations
of the derived sections: localizing the restriction of sections. This is the computation rule of
the lift, with both factorizations in the types they are stated in. -/
theorem derivedRestrictionMap_app_derivedSectionsFactorization (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (derivedSectionsFactorization A V).hom.app ((HomotopyCategory.quotient A).obj M) ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
            (M.sectionModuleRestriction a)) =
      (derivedRestrictionMap A a).app
          ((quasiIsomorphisms.{t, a, a} A).Q.obj ((HomotopyCategory.quotient A).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
          ((derivedSectionsFactorization A U).hom.app ((HomotopyCategory.quotient A).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestrictionFactorization
            (A.sectionRestriction a)).hom.app
          ((sectionHomotopyFunctor A U).obj ((HomotopyCategory.quotient A).obj M)) := by
  have hmap :
      (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
            ((derivedSectionsFactorization A U).inv.app
              ((HomotopyCategory.quotient A).obj M)) ≫
          (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
            ((derivedSectionsFactorization A U).hom.app
              ((HomotopyCategory.quotient A).obj M)) =
        𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have cancel : ∀ {Z₀ Z₁ Z₂ Z₃ Z₄ :
        _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra V)}
      (p : Z₀ ⟶ Z₁) (q : Z₁ ⟶ Z₂) (α : Z₂ ⟶ Z₃) (α' : Z₃ ⟶ Z₂) (β : Z₃ ⟶ Z₄) (β' : Z₄ ⟶ Z₃),
      β ≫ β' = 𝟙 Z₃ → α ≫ α' = 𝟙 Z₂ → p ≫ q = (p ≫ (q ≫ α) ≫ β) ≫ β' ≫ α' := by
    intro _ _ _ _ _ p q α α' β β' hβ hα
    simp only [Category.assoc]
    rw [← Category.assoc β, hβ, Category.id_comp, hα, Category.comp_id]
  dsimp only [derivedRestrictionMap]
  rw [Localization.liftNatTrans_app, liftingIso_derivedSections_hom_app,
    liftingIso_derivedSections_comp_inv_app, sectionHomotopyRestrictionLocalized_app_quotient]
  exact cancel _ _ _ _ _ _ hmap (Iso.inv_hom_id_app _ _)

/-- **On the image of a right differential graded module the derived restriction map is
restriction of sections**, read through the identification of the derived sections with the
sections and the factorization of derived restriction of scalars. -/
theorem derivedRestrictionMap_app_toDerivedCategory (a : V ⟶ U)
    (M : DifferentialGradedModule.{t, a, a} A) :
    (derivedSectionsIso A V).hom.app M ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
            (M.sectionModuleRestriction a)) =
      (derivedRestrictionMap A a).app
          ((toDerivedCategory.{t, a, a} A).obj ((HomotopyCategory.quotient A).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
          ((derivedSectionsIso A U).hom.app M) ≫
        (_root_.DifferentialGradedModule.derivedRestrictionFactorization
            (A.sectionRestriction a)).hom.app
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
            ((sectionModuleFunctor A U).obj M)) := by
  rw [derivedSectionsIso_hom_app, derivedSectionsIso_hom_app]
  exact derivedRestrictionMap_app_derivedSectionsFactorization A a M

end Chaotic

end DifferentialGradedModule

end SheafOfModules

end
