module

public import StacksFrontier.CategoryTheory.Sites.DerivedPushforwardSheafify
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExactLargeCoefficients
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived presheaf direct image at an object is the cohomology of the fibre site

Let `F : C ⥤ D` be a functor from a site `(C, J)` to a category `D`, and let `y` be an object of
`D`. The *fibre* of `F` over `y` is the site of elements of the presheaf of sets
`x ↦ Hom_D(F x, y)` on `C`, that is, the category whose objects are the pairs `(x, φ)` of an
object `x` of `C` and a morphism `φ : F x ⟶ y`, with the topology of Stacks 0791: a family is a
covering exactly when its image in `C` is. Its projection `pr` to `C` is continuous and
cocontinuous, and restriction along it is the inverse image `pr⁻¹` of the localization morphism
of topoi.

The direct image of an abelian sheaf `ℋ` along `F`, taken as a presheaf, is the right Kan
extension of `ℋ` along `F.op`; its value at `y` is the limit of `ℋ` over the pairs `(x, φ)`,
which is the module of global sections `Γ(fibre, pr⁻¹ℋ)`. This file proves the derived form of
that formula: the value at `y` of the `p`-th right derived presheaf direct image is the `p`-th
cohomology group of the fibre site,

`(Rᵖ(F_*^{PSh}) ℋ)(y) ≅ Hᵖ(fibre of F over y, pr⁻¹ ℋ)`,

naturally in `ℋ`. This is the identification in the proof of Stacks 0GR2, where the fibre is
the category `(V ×_{y, 𝒴} 𝒳)'`.

## Main definitions

* `CategoryTheory.Functor.DirectImageFibre.fibre`: the fibre of `F` over `y`.
* `CategoryTheory.Functor.DirectImageFibre.fibreTopology`: its topology.
* `CategoryTheory.Functor.DirectImageFibre.fibreProjection` and
  `CategoryTheory.Functor.DirectImageFibre.fibreRestriction`: the projection `pr` and the
  restriction `pr⁻¹` of abelian sheaves along it.

## Main results

* `CategoryTheory.Functor.DirectImageFibre.ranEvaluationIso`: the presheaf direct image at `y` is
  the limit over the fibre.
* `CategoryTheory.Functor.DirectImageFibre.presheafDirectImageEvaluationIso`: in degree zero,
  `(F_*^{PSh} ℋ)(y) ≅ Γ(fibre, pr⁻¹ ℋ)`.
* `CategoryTheory.Functor.DirectImageFibre.derivedPresheafDirectImageEvaluationIso`: in every
  degree, `(Rᵖ(F_*^{PSh}) ℋ)(y) ≅ Hᵖ(fibre, pr⁻¹ ℋ)`.

## Implementation notes

The proof is the one of the source. Evaluation at `y` is exact, so it comes out of the right
derived functor; in degree zero the two functors agree; and `pr⁻¹` is exact and preserves
injective abelian sheaves (Stacks 07A0, in the form
`preservesInjectiveObjects_sheafPushforwardContinuous` in
`Stacks.Sites.LocalizationShriek.LargeCoefficients`), so it carries an injective resolution of
`ℋ` to one of `pr⁻¹ ℋ` (`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`).
Finally the right derived functors of global sections are Mathlib's sheaf cohomology
`Sheaf.functorH` (`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`).

The two categories share their morphism universe `v`, which is what makes the presheaf
`x ↦ Hom_D(F x, y)` a presheaf of sets on `C` in the universe of its morphisms. The coefficient
universe is `max u₁ u₂ v a`, as for `CategoryTheory.Functor.derivedPresheafDirectImage`.

## References

* [Stacks Project, Tag 0GR2](https://stacks.math.columbia.edu/tag/0GR2)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Functor.DirectImageFibre

universe u₁ u₂ v a

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (J : GrothendieckTopology C) (F : C ⥤ D) (y : D)

/-- The presheaf of sets `x ↦ Hom_D(F x, y)` on `C`, the inverse image of the presheaf represented
by `y`. -/
abbrev fibrePresheaf : Cᵒᵖ ⥤ Type v := F.op ⋙ yoneda.obj y

/-- **The fibre of `F` over `y`**: the site of elements of `x ↦ Hom_D(F x, y)`, whose objects are
the pairs `(x, φ)` with `φ : F x ⟶ y`. -/
abbrev fibre : Type (max u₁ v) := CostructuredArrow (yoneda (C := C)) (fibrePresheaf F y)

/-- The projection `pr` of the fibre to `C`, `(x, φ) ↦ x`. -/
abbrev fibreProjection : fibre F y ⥤ C := CostructuredArrow.proj yoneda (fibrePresheaf F y)

/-- The topology of the fibre: by Stacks 0791 a sieve covers exactly when its image under the
projection covers. -/
abbrev fibreTopology : GrothendieckTopology (fibre F y) :=
  (fibreProjection F y).restrictedTopology J

/-- Restriction `pr⁻¹` of abelian sheaves to the fibre site: the inverse image of the
localization morphism of topoi. -/
abbrev fibreRestriction :
    Sheaf J AddCommGrpCat.{max u₁ u₂ v a} ⥤
      Sheaf (fibreTopology J F y) AddCommGrpCat.{max u₁ u₂ v a} :=
  (fibreProjection F y).sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v a}
    (fibreTopology J F y) J

/-! ### The fibre and the comma category of the right Kan extension -/

/-- The opposite of the fibre is the comma category `StructuredArrow (op y) F.op` over which the
right Kan extension along `F.op` is computed at `y`: a pair `(x, φ)` goes to `φ.op`. -/
def fibreOpToStructuredArrow : (fibre F y)ᵒᵖ ⥤ StructuredArrow (op y) F.op where
  obj X := StructuredArrow.mk (Y := op X.unop.left) (yonedaEquiv X.unop.hom).op
  map {X Y} g := StructuredArrow.homMk g.unop.left.op (by
    apply Quiver.Hom.unop_inj
    change F.map g.unop.left ≫ yonedaEquiv X.unop.hom = yonedaEquiv Y.unop.hom
    rw [← CostructuredArrow.w g.unop, ← yonedaEquiv_naturality]
    rfl)

/-- The functor from the opposite of the fibre to the comma category is faithful. -/
instance : (fibreOpToStructuredArrow F y).Faithful where
  map_injective {_ _} _ _ h :=
    Quiver.Hom.unop_inj <| CostructuredArrow.hom_ext _ _ <|
      Quiver.Hom.op_inj (congrArg CommaMorphism.right h)

/-- The functor from the opposite of the fibre to the comma category is full. -/
instance : (fibreOpToStructuredArrow F y).Full where
  map_surjective {X Y} φ := by
    have hw : F.map φ.right.unop ≫ yonedaEquiv X.unop.hom = yonedaEquiv Y.unop.hom :=
      congrArg Quiver.Hom.unop (StructuredArrow.w φ)
    refine ⟨(CostructuredArrow.homMk (φ.right.unop : Y.unop.left ⟶ X.unop.left) ?_).op, ?_⟩
    · exact yonedaEquiv.injective <| (yonedaEquiv_naturality (F := fibrePresheaf F y) X.unop.hom
        (φ.right.unop : Y.unop.left ⟶ X.unop.left)).symm.trans hw
    · ext
      rfl

/-- The functor from the opposite of the fibre to the comma category is essentially
surjective. -/
instance : (fibreOpToStructuredArrow F y).EssSurj where
  mem_essImage Z :=
    ⟨op (CostructuredArrow.mk (yonedaEquiv.symm Z.hom.unop :
        yoneda.obj Z.right.unop ⟶ fibrePresheaf F y)),
      ⟨StructuredArrow.isoMk (Iso.refl _) (by
        apply Quiver.Hom.unop_inj
        change F.map (𝟙 Z.right.unop) ≫ yonedaEquiv (yonedaEquiv.symm Z.hom.unop :
          yoneda.obj Z.right.unop ⟶ fibrePresheaf F y) = Z.hom.unop
        rw [F.map_id, Category.id_comp, Equiv.apply_symm_apply])⟩⟩

/-- The opposite of the fibre is equivalent to the comma category `StructuredArrow (op y) F.op`. -/
instance : (fibreOpToStructuredArrow F y).IsEquivalence where

/-- The comma category functor composed with the projection is the projection of the fibre. -/
theorem fibreOpToStructuredArrow_comp_proj :
    fibreOpToStructuredArrow F y ⋙ StructuredArrow.proj (op y) F.op = (fibreProjection F y).op :=
  rfl

/-! ### Degree zero -/

variable (A : Type*) [Category* A] [HasLimitsOfShape (StructuredArrow (op y) F.op) A]
  [HasLimitsOfShape (fibre F y)ᵒᵖ A] [∀ X : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension X]

/-- The value at `y` of the right Kan extension along `F.op` is the limit over the comma
category `StructuredArrow (op y) F.op`, naturally in the presheaf. -/
def ranEvaluationIsoLimStructuredArrow :
    F.op.ran ⋙ (evaluation Dᵒᵖ A).obj (op y) ≅
      (Functor.whiskeringLeft _ _ A).obj (StructuredArrow.proj (op y) F.op) ⋙ lim :=
  NatIso.ofComponents (fun X => F.op.ranObjObjIsoLimit X (op y)) (fun {X X'} η => by
    apply limit.hom_ext
    intro f
    simp only [Functor.comp_obj, evaluation_obj_obj, Functor.comp_map, evaluation_obj_map,
      whiskeringLeft_obj_obj, lim_obj, whiskeringLeft_obj_map, lim_map, assoc,
      ranObjObjIsoLimit_hom_π, ranObjObjIsoLimit_hom_π_assoc, limMap_π, Functor.whiskerLeft_app]
    rw [← NatTrans.naturality_assoc]
    congr 1
    simpa using congr_app (F.op.ranCounit.naturality η) f.right)

/-- **The presheaf direct image at `y` is the limit over the fibre**, naturally in the presheaf:
`(Ran_{F.op} X)(y) ≅ lim_{(x, φ) ∈ fibre} X(x)`. -/
def ranEvaluationIso :
    F.op.ran ⋙ (evaluation Dᵒᵖ A).obj (op y) ≅
      (Functor.whiskeringLeft _ _ A).obj (fibreProjection F y).op ⋙ lim :=
  ranEvaluationIsoLimStructuredArrow F y A ≪≫
    Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (StructuredArrow.proj (op y) F.op))
      (Functor.Initial.limIso (fibreOpToStructuredArrow F y)).symm

/-! ### The fibre site

The fibre site has objects in `Type (max u₁ v)` and morphisms in `Type v`. At the coefficient
universe `max u₁ u₂ v a` it admits sheafification and enough injective abelian sheaves and has
`Ext`-groups, by `site_hasSheafify_addCommGrp`, `site_enoughInjectives_addCommGrp` and
`site_hasExt_addCommGrp`. These are written out as `letI` rather than recorded as instances: the
universe `a` occurs only inside a `max`, so an instance stated at that universe could not be
found by unification. -/

section Derived

open Stacks.Cohomology.SiteModules

variable [HasSheafify J AddCommGrpCat.{max u₁ u₂ v a}]

/-- **The presheaf direct image at `y` is the module of global sections over the fibre**,
naturally in the abelian sheaf: `(F_*^{PSh} ℋ)(y) ≅ Γ(fibre of F over y, pr⁻¹ ℋ)`. This is the
degree-zero case of `derivedPresheafDirectImageEvaluationIso`, and the formula (07AU) in the
proof of Stacks 07AT. -/
def presheafDirectImageEvaluationIso :
    letI := site_hasSheafify_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
    (sheafToPresheaf J AddCommGrpCat.{max u₁ u₂ v a} ⋙ F.op.ran) ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{max u₁ u₂ v a}).obj (op y) ≅
      fibreRestriction.{u₁, u₂, v, a} J F y ⋙
        Sheaf.Γ (fibreTopology J F y) AddCommGrpCat.{max u₁ u₂ v a} :=
  letI := site_hasSheafify_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u₁ u₂ v a})
      (ranEvaluationIso F y AddCommGrpCat.{max u₁ u₂ v a}) ≪≫
    (Functor.isoWhiskerLeft (fibreRestriction.{u₁, u₂, v, a} J F y)
      (Sheaf.ΓNatIsoLim (fibreTopology J F y) AddCommGrpCat.{max u₁ u₂ v a})).symm

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max u₁ u₂ v a})]

/-- **The derived presheaf direct image at `y` is the cohomology of the fibre site**, naturally
in the abelian sheaf `ℋ`:

`(Rᵖ(F_*^{PSh}) ℋ)(y) ≅ Hᵖ(fibre of F over y, pr⁻¹ ℋ)`,

where `Rᵖ(F_*^{PSh})` is `CategoryTheory.Functor.derivedPresheafDirectImage`, the fibre is the
site of pairs `(x, φ : F x ⟶ y)` with the topology of Stacks 0791, `pr` is its projection to `C`
and `Hᵖ` is sheaf cohomology. This is the identification in the proof of Stacks 0GR2. -/
@[sga "4 V 2.4.2" "more general", sga "7 VI 3.1(c)" "more general"]
def derivedPresheafDirectImageEvaluationIso (p : ℕ) :
    letI := site_hasSheafify_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
    letI := site_hasExt_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
    derivedPresheafDirectImage.{u₁, u₂, v, v, a} J F p ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{max u₁ u₂ v a}).obj (op y) ≅
      fibreRestriction.{u₁, u₂, v, a} J F y ⋙
        Sheaf.functorH.{max u₁ u₂ v a, max u₁ u₂ v a, v, max u₁ v} (fibreTopology J F y) p :=
  letI := site_hasSheafify_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
  letI := site_hasExt_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
  letI := site_enoughInjectives_addCommGrp.{max u₁ v, v, max u₁ u₂ v a} (J := fibreTopology J F y)
  haveI := (sheafificationAdjunction J AddCommGrpCat.{max u₁ u₂ v a}).right_adjoint_additive
  haveI := (F.op.ranAdjunction AddCommGrpCat.{max u₁ u₂ v a}).right_adjoint_additive
  haveI : PreservesFiniteLimits (fibreRestriction.{u₁, u₂, v, a} J F y) :=
    (Functor.sheafAdjunctionContinuous (fibreProjection F y) AddCommGrpCat.{max u₁ u₂ v a}
      (fibreTopology J F y) J).rightAdjoint_preservesLimits.{0, 0}.preservesFiniteLimits
  haveI : PreservesFiniteColimits (fibreRestriction.{u₁, u₂, v, a} J F y) :=
    haveI : PreservesColimitsOfSize.{0, 0} (fibreRestriction.{u₁, u₂, v, a} J F y) :=
      (Functor.sheafAdjunctionCocontinuous (fibreProjection F y) AddCommGrpCat.{max u₁ u₂ v a}
        (fibreTopology J F y) J).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : (fibreRestriction.{u₁, u₂, v, a} J F y).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (fibreRestriction.{u₁, u₂, v, a} J F y).PreservesInjectiveObjects :=
    open Stacks.Sites.LocalizationShriek.LargeCoefficients in
    preservesInjectiveObjects_sheafPushforwardContinuous.{max u₁ u₂ a} (fibrePresheaf F y) J
  haveI := Stacks.Cohomology.GlobalSections.additive_Γ.{max u₁ u₂ v a, v, max u₁ v}
    (fibreTopology J F y)
  (Functor.rightDerivedCompIso (sheafToPresheaf J AddCommGrpCat.{max u₁ u₂ v a} ⋙ F.op.ran)
      ((evaluation Dᵒᵖ AddCommGrpCat.{max u₁ u₂ v a}).obj (op y)) p).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (presheafDirectImageEvaluationIso.{u₁, u₂, v, a} J F y) p ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (fibreRestriction.{u₁, u₂, v, a} J F y)
      (Sheaf.Γ (fibreTopology J F y) AddCommGrpCat.{max u₁ u₂ v a}) p ≪≫
    Functor.isoWhiskerLeft (fibreRestriction.{u₁, u₂, v, a} J F y)
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{max u₁ u₂ v a, v, max u₁ v}
        (fibreTopology J F y) p)

end Derived

end CategoryTheory.Functor.DirectImageFibre

end
