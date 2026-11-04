module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.UniquenessSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniquenessRepresentable
public import StacksFrontier.CategoryTheory.Comma.SliceRebase
public import StacksFrontier.CategoryTheory.DottedArrows.Connecting
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SectionDiagonal

/-!
# Valuative uniqueness is tested on the algebraic-space base changes (Stacks 0CLJ)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site which
is representable by algebraic spaces (Stacks 02ZW). Then `f` satisfies the uniqueness part of the
valuative criterion (Stacks 0CLG) exactly when every one of its base changes to an algebraic
space does, in the sense of Stacks 03IX: for every object `U` of the site, every scheme-valued
point `y` of `𝒴` over `U` and every algebraic space `F` over `U` representing the first
projection of the 2-fibre product `U ×_𝒴 𝒳`, the structure morphism of `F` satisfies the
uniqueness criterion for presheaves.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_baseChange`: **Stacks 0CLJ**.
* `AlgebraicGeometry.Stack.subsingleton_lift_baseChange_point`: the substantive half of the
  forward direction, with a predicate on the valuation ring threaded through both sides, so that
  a criterion tested only on a restricted class of valuation rings transfers to the base changes.

## Implementation notes

By `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_forall_nonempty_iso` the criterion
for a representable `f` says exactly that any two dotted arrows of any valuative diagram are
isomorphic, so both directions are statements about dotted arrows, and the base change is
present only through the representing presheaf.

The dictionary between the two sides is a pair of mutually inverse translations, each
of which is the content of a generic file imported here.

*From a dotted arrow to a section.* A dotted arrow `a` for a valuative diagram `D` gives a
section of the first projection of the 2-fibre product over the site of `D.whole`: its first
component is the identity and its second is the diagonal of `a`, the comparison 2-cell being
`a.β`. This is `CategoryTheory.TwoFibreProductOver.lift`, and
`AlgebraicGeometry.Stack.dottedArrowSection` below. Carried through the representability
equivalence it names a family of elements of the representing presheaf, and two dotted arrows
naming the same family are isomorphic, by
`CategoryTheory.PresheafOfCategories.exists_vertical_iso_of_sections_eq`.

*From a section to a dotted arrow.* Conversely a section of the first projection over a point of
the site gives a diagonal together with a 2-cell filling the square, which is
`StacksFrontier/CategoryTheory/TwoFibreProduct/SectionDiagonal.lean`; a lift in a valuative square
for the representing presheaf is such a section, over the slice of the site at the spectrum of
the valuation ring, and the two lifts of one square therefore give two dotted arrows of one
valuative diagram.

Two inputs make the generic point work. The slice of the site of `S` at the relocalization of an
object `A` is the slice of the site of `U` at `A` (`CategoryTheory.Over.sliceRebase`), which is
what identifies the base of the valuative diagram with a site object; and two dotted arrows are
always connected over an object isomorphic to one in the image of the left edge
(`CategoryTheory.DottedArrow.exists_hom_beta_app_of_iso_image`), which is what makes the two
sections agree at the generic point.

## References

* [Stacks Project, Tag 0CLJ](https://stacks.math.columbia.edu/tag/0CLJ)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory
  CategoryTheory.PresheafOfCategories Opposite

namespace AlgebraicGeometry.Stack

universe u w

/-- **The point of `𝒴` carried by the special point of a valuative diagram, read over the site of
its whole spectrum.** The left edge of a valuative diagram is a 1-morphism of categories fibred
in groupoids over the site of `S`; composing the iterated-slice comparison with the special point
makes it a scheme-valued point of `𝒴` over `D.whole` in the sense of Stacks 02ZW. -/
private def valuativeDiagramTargetPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (D : ValuativeDiagram B S hS 𝒳 𝒴 f) :
    BigFppfOver B D.whole.left.1 D.whole.left.2 ⥤ 𝒴.val.val.obj :=
  Over.iteratedSliceBackward D.whole ⋙ D.y.hom.toFunctor

/-- `AlgebraicGeometry.Stack.valuativeDiagramTargetPoint` is a scheme-valued point over
`D.whole`: it is a 1-morphism over the site of `S`, from the slice at `D.whole`. -/
private theorem valuativeDiagramTargetPoint_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (D : ValuativeDiagram B S hS 𝒳 𝒴 f) :
    valuativeDiagramTargetPoint B S hS D ⋙ 𝒴.val.val.p = Over.map D.whole.hom :=
  (congrArg (fun k => Over.iteratedSliceBackward D.whole ⋙ k) D.y.hom.w).trans
    (Over.iteratedSliceBackward_forget D.whole)

/-- **The section of the base-changed 2-fibre product attached to a dotted arrow.** For a dotted
arrow `a` of a valuative diagram `D`, the functor sending an object `V` of the site of `D.whole`
to the quadruple `(V, V, a V, a.β V)`: it is a section of the first projection of the 2-fibre
product `D.whole ×_𝒴 𝒳` along the identity. -/
private noncomputable def dottedArrowSection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    BigFppfOver B D.whole.left.1 D.whole.left.2 ⥤
      TwoFibreProductOver (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor :=
  TwoFibreProductOver.lift (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
    (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor (Over.map D.whole.hom)
    (𝟭 _) (Over.iteratedSliceBackward D.whole ⋙ a.a.hom.toFunctor) (Functor.id_comp _)
    ((congrArg (fun H => Over.iteratedSliceBackward D.whole ⋙ H) a.a.hom.w).trans
      (Over.iteratedSliceBackward_forget D.whole))
    (Functor.isoWhiskerLeft (Over.iteratedSliceBackward D.whole)
      (@asIso _ _ _ _ a.β.hom.toNatTrans (CatFiberedInGroupoids.isIso_toNatTrans a.β)))
    (fun V => a.β.hom.isHomLift' ((Over.iteratedSliceBackward D.whole).obj V))

/-- `AlgebraicGeometry.Stack.dottedArrowSection` is a section of the first projection along the
identity. -/
private theorem dottedArrowSection_comp_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    dottedArrowSection B S hS D a ⋙
      TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor = 𝟭 _ := rfl

/-- A morphism conjugated by two `eqToHom`s is the identity as soon as the conjugate is the
composite of those two `eqToHom`s. Stated rather than cancelled in place: cancelling the
monomorphism would make instance search look for `Mono (eqToHom ...)` in a category whose objects
are slices of the big fppf site, which is expensive, while substituting the two equalities is
immediate. -/
private theorem eq_id_of_conj_eqToHom {𝒜 : Type*} [Category 𝒜] {X Y Z : 𝒜}
    (p : X = Y) (q : Y = Z) (g : Y ⟶ Y)
    (h : eqToHom p ≫ eqToHom q = eqToHom p ≫ g ≫ eqToHom q) : g = 𝟙 Y := by
  subst p
  subst q
  simpa using h.symm

/-- **Two dotted arrows whose sections are isomorphic over the identity are isomorphic.** The
component of the isomorphism at `V` has first component the identity, so its second component is
a connecting morphism between the two dotted arrows over the object of the site of `S`
corresponding to `V`. Every object of the base of the valuative square is isomorphic to such a
one — that is the unit of the iterated-slice equivalence — and a connecting morphism transports
along an isomorphism of the base. -/
private theorem nonempty_iso_of_dottedArrowSection_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} [f.hom.hom.toFunctor.Faithful]
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)
    (η : dottedArrowSection B S hS D a ≅ dottedArrowSection B S hS D b)
    (hη : ∀ V, (TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
      (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor).IsHomLift (𝟙 V)
        (η.hom.app V)) : Nonempty (a ≅ b) := by
  refine CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom a b fun t => ?_
  refine CategoryTheory.DottedArrow.exists_hom_beta_app_of_iso a b
    ((Over.iteratedSliceEquiv D.whole).unitIso.app t) ?_
  set V := (Over.iteratedSliceForward D.whole).obj t
  refine ⟨(η.hom.app V).b, ?_⟩
  have hlift := hη V
  have ha : (η.hom.app V).a = 𝟙 V := by
    refine Eq.trans (IsHomLift.fac'
      (TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor)
      (𝟙 V) (η.hom.app V)) ?_
    show 𝟙 _ ≫ 𝟙 V ≫ 𝟙 _ = 𝟙 V
    simp
  have hw : (valuativeDiagramTargetPoint B S hS D).map (η.hom.app V).a ≫
      b.β.hom.toNatTrans.app ((Over.iteratedSliceBackward D.whole).obj V) =
      a.β.hom.toNatTrans.app ((Over.iteratedSliceBackward D.whole).obj V) ≫
        f.hom.hom.toFunctor.map (η.hom.app V).b := (η.hom.app V).w
  refine Eq.trans ?_ hw
  refine Eq.trans (Category.id_comp _).symm ?_
  exact congrArg
    (fun t => t ≫ b.β.hom.toNatTrans.app ((Over.iteratedSliceBackward D.whole).obj V))
    (((valuativeDiagramTargetPoint B S hS D).map_id V).symm.trans
      (congrArg (valuativeDiagramTargetPoint B S hS D).map ha.symm))

/-- **Two dotted arrows whose sections name the same family of elements of the representing
presheaf are isomorphic.** The two sections are 1-morphisms over the site of `D.whole` into a
category equivalent to the category of elements of the representing presheaf, so naming the same
family makes them isomorphic by a vertical isomorphism. -/
private theorem nonempty_iso_of_sections_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} [f.hom.hom.toFunctor.Faithful]
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)
    {F : (BigFppfOver B D.whole.left.1 D.whole.left.2)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (h : ∀ V, sectionOfBasedFunctor (dottedArrowSection B S hS D a ⋙ e.hom.functor)
        (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D a)) V =
      sectionOfBasedFunctor (dottedArrowSection B S hS D b ⋙ e.hom.functor)
        (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D b)) V) :
    Nonempty (a ≅ b) := by
  obtain ⟨η, hη⟩ := exists_vertical_iso_of_sections_eq e
    (dottedArrowSection B S hS D a) (dottedArrowSection B S hS D b)
    (dottedArrowSection_comp_fst B S hS D a) (dottedArrowSection_comp_fst B S hS D b) h
  exact nonempty_iso_of_dottedArrowSection_iso B S hS D a b η hη

/-- **The two sections of two dotted arrows name the same element over the generic point.** The
generic point of the valuative diagram is an object of the site of `D.whole` whose image under
the iterated-slice comparison is isomorphic to an object in the image of the left edge of the
diagram, so the two dotted arrows are connected there; the connecting morphism is a vertical
morphism of the 2-fibre product between the two sections at that object, and a morphism of a
category of elements over an identity does not change the element named. -/
private theorem sectionOfBasedFunctor_dottedArrowSection_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)
    {F : (BigFppfOver B D.whole.left.1 D.whole.left.2)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    sectionOfBasedFunctor (dottedArrowSection B S hS D a ⋙ e.hom.functor)
        (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D a))
        (Over.mk D.inclusion.left) =
      sectionOfBasedFunctor (dottedArrowSection B S hS D b ⋙ e.hom.functor)
        (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D b))
        (Over.mk D.inclusion.left) := by
  let V : BigFppfOver B D.whole.left.1 D.whole.left.2 := Over.mk D.inclusion.left
  let z := Over.mk (𝟙 D.generic)
  let I := Over.iteratedSliceBackward D.whole
  have hz : D.j.hom.toFunctor.obj z = (Over.map D.inclusion).obj z :=
    Functor.congr_obj D.j_canonical z
  let ζ : I.obj V ≅ D.j.hom.toFunctor.obj z :=
    (show I.obj V ≅ (Over.map D.inclusion).obj z from
      Over.isoMk (Over.isoMk (Iso.refl _) (by
        show 𝟙 _ ≫ D.generic.hom = D.inclusion.left ≫ D.whole.hom
        simpa only [Category.id_comp] using (Over.w D.inclusion).symm))
        (by ext; simp [V, I, z, Over.iteratedSliceBackward])) ≪≫ (eqToIso hz).symm
  obtain ⟨θ, hθ⟩ := CategoryTheory.DottedArrow.exists_hom_beta_app_of_iso_image a b z ζ
  have hθlift : 𝒳.val.val.p.IsHomLift (𝟙 ((Over.map D.whole.hom).obj V)) θ :=
    CategoryTheory.DottedArrow.isHomLift_of_beta_app_eq a b (I.obj V) hθ
  let φ : (dottedArrowSection B S hS D a).obj V ⟶ (dottedArrowSection B S hS D b).obj V :=
    { hbase := 𝟙 _
      a := 𝟙 V
      b := θ
      ha := IsHomLift.id rfl
      hb := hθlift
      w := by
        have hid := (valuativeDiagramTargetPoint B S hS D).map_id V
        refine Eq.trans (congrArg
          (fun t => t ≫ b.β.hom.toNatTrans.app (I.obj V)) hid) ?_
        exact (Category.id_comp _).trans hθ }
  have hvert : (discreteProjection F).IsHomLift (𝟙 V) (e.hom.functor.map φ) :=
    IsHomLift.of_fac' (discreteProjection F) (𝟙 V) (e.hom.functor.map φ)
      (Functor.congr_obj e.hom.w _) (Functor.congr_obj e.hom.w _)
      (Functor.congr_hom e.hom.w φ)
  exact (elementOf_eq_map
    (Functor.congr_obj e.hom.w ((dottedArrowSection B S hS D a).obj V))
    (Functor.congr_obj e.hom.w ((dottedArrowSection B S hS D b).obj V))
    (𝟙 V) (e.hom.functor.map φ) hvert).trans (Functor.map_id_apply F _ _)

/-- **Stacks 0CLJ, the backward direction.** If the structure morphism of an algebraic space
representing the base change of `f` along the special point of a valuative diagram satisfies the
uniqueness part of the valuative criterion for presheaves, then any two dotted arrows of that
diagram are isomorphic.

The two dotted arrows name two families of elements of the representing presheaf; they agree at
the generic point, hence everywhere by
`AlgebraicGeometry.Space.sectionOfBasedFunctor_eq_of_uniqueness`, and two dotted arrows naming
the same family are isomorphic. -/
private theorem nonempty_iso_of_baseChange_uniqueness
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} [f.hom.hom.toFunctor.Faithful]
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)
    {F : (BigFppfOver B D.whole.left.1 D.whole.left.2)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map D.whole.hom) 𝒳.val.val.p 𝒴.val.val.p
        (valuativeDiagramTargetPoint B S hS D) f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj D.whole.left.2))))
    (hu : Space.ValuativeCriterion.Uniqueness p) : Nonempty (a ≅ b) := by
  let _ := D.ring
  let _ := D.domain
  let _ := D.valuation
  have hC : ∀ {X Y : Scheme.{u}}, (X ≅ Y) → B.Contains Y → B.Contains X := fun i h =>
    lt_of_eq_of_lt (Scheme.size_congr i) h
  have hR : B.Contains (Spec (.of D.R)) := hC D.whole_iso.symm D.whole.left.2
  have hL : B.Contains (Spec (.of (FractionRing D.R))) := hC D.generic_iso.symm D.generic.left.2
  refine nonempty_iso_of_sections_eq B S hS D a b e ?_
  refine Space.sectionOfBasedFunctor_eq_of_uniqueness B D.whole.left.1 D.whole.left.2 p hu
    (dottedArrowSection B S hS D a ⋙ e.hom.functor)
    (dottedArrowSection B S hS D b ⋙ e.hom.functor)
    (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D a))
    (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D b))
    D.R (FractionRing D.R) hR hL D.whole_iso.symm ?_
  let i : siteObject B D.whole.left.1 D.whole.left.2 hL
      (Spec.map (CommRingCat.ofHom (algebraMap D.R (FractionRing D.R))) ≫
        D.whole_iso.inv) ⟶ Over.mk D.inclusion.left :=
    Over.homMk (ObjectProperty.homMk D.generic_iso.inv) (by
      apply ObjectProperty.hom_ext
      show D.generic_iso.inv ≫ D.inclusion.left.hom = _
      have hd := D.inclusion_spec
      change D.inclusion.left.hom = D.generic_iso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.R (FractionRing D.R))) ≫
          D.whole_iso.inv at hd
      rw [hd]
      simp)
  exact ((sectionOfBasedFunctor_map (dottedArrowSection B S hS D a ⋙ e.hom.functor)
      (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D a)) i).symm.trans
    (congrArg (F.map i.op)
      (sectionOfBasedFunctor_dottedArrowSection_eq B S hS D a b e))).trans
    (sectionOfBasedFunctor_map (dottedArrowSection B S hS D b ⋙ e.hom.functor)
      (e.comp_hom_functor_comp_eq (dottedArrowSection_comp_fst B S hS D b)) i)

/-- Two morphisms of presheaves out of a representable presheaf agree as soon as their sections
over the slice are connected, over the identity, at an object of the slice with invertible
structure morphism. -/
theorem eq_of_hom_sliceSectionOfHom {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type _} {A : C}
    (n₁ n₂ : yoneda.obj A ⟶ F) (X : Over A) [IsIso X.hom]
    (ψ : (sliceSectionOfHom n₁).obj X ⟶ (sliceSectionOfHom n₂).obj X)
    (hψ : ψ.base = 𝟙 X.left) : n₁ = n₂ := by
  have hv := elementOf_eq_map (P := F)
    (rfl : ((sliceSectionOfHom n₁).obj X).base = X.left)
    (rfl : ((sliceSectionOfHom n₂).obj X).base = X.left) (𝟙 X.left) ψ
    (IsHomLift.of_fac' (discreteProjection F) (𝟙 X.left) ψ rfl rfl (by
      show ψ.base = 𝟙 _ ≫ 𝟙 X.left ≫ 𝟙 _
      simpa using hψ))
  have hval : n₁.app (op X.left) (𝟙 _ ≫ X.hom) = n₂.app (op X.left) (𝟙 _ ≫ X.hom) := by
    rw [Category.id_comp]
    exact hv.trans (Functor.map_id_apply F _ _)
  exact (cancel_epi (yoneda.map X.hom)).mp (yonedaEquiv.injective hval)

/-- **Stacks 0CLJ, the forward direction, restricted along a predicate on the valuation ring.**
Let `Pred` be a property of valuation rings, allowed to depend on the ring structure as
`IsDiscreteValuationRing` does. If any two dotted arrows of any valuative diagram for `f` whose
valuation ring satisfies `Pred` are isomorphic, then, for the structure morphism of any algebraic
space representing a base change of `f` along a scheme-valued point, a valuative square whose
valuation ring satisfies `Pred` has at most one lift.

A valuative square for the representing presheaf and a lift of it give, through the
representability equivalence, a section of the first projection of the 2-fibre product over the
slice of the site of `S` at the spectrum of the valuation ring; the diagonal and filler read off
that section are a dotted arrow of a valuative diagram for `f`, the same diagram for both lifts.
An isomorphism of the two dotted arrows is then a vertical morphism between the two sections, and
evaluating it at the tautological object identifies the two lifts.

The valuation ring of the constructed diagram *is* the valuation ring of the square, with the same
ring structure, so the restriction passes through unchanged; with `Pred` the trivially true
predicate this is the forward direction of
`AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_baseChange`, and the predicate form is
what transfers a criterion tested on a restricted class of valuation rings.

The ring, domain and valuation-ring structures of the valuation ring of a
`AlgebraicGeometry.Stack.ValuativeDiagram` are fields of the structure which are not registered as
instances, so they are passed to `Pred` explicitly; those of a
`AlgebraicGeometry.Space.ValuativeSquare` are instances, so `Pred q.R` needs no annotation. -/
theorem subsingleton_lift_baseChange_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (Pred : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop)
    (h : ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f, @Pred D.R D.ring D.domain D.valuation →
      ∀ a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ, Nonempty (a ≅ b))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
    (q : Space.ValuativeSquare p) (hq : Pred q.R) : Subsingleton q.Lift := by
  classical
  refine ⟨fun l m => ?_⟩
  let A := siteObject B U.left.1 U.left.2 q.ring_mem q.base
  let G := siteObject B U.left.1 U.left.2 q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let i : G ⟶ A := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))))
  let r := Over.map U.hom
  let T := schemeFibredCategory B S hS (r.obj A)
  let T' := schemeFibredCategory B S hS (r.obj G)
  let J := Over.sliceRebase U A
  let s := J ⋙ Over.forget A
  have hs : s ⋙ r = T.val.p := Over.sliceRebase_comp_forget_map U A
  let H := J ⋙ sliceSectionOfHom l.map ⋙ e.inv.functor
  let K := J ⋙ sliceSectionOfHom m.map ⋙ e.inv.functor
  have hsec : ∀ n : yoneda.obj A ⟶ F, (J ⋙ sliceSectionOfHom n ⋙ e.inv.functor) ⋙
      TwoFibreProductOver.fst r 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor = s := fun n => by
    rw [Functor.assoc, Functor.assoc, e.inv.w, sliceSectionOfHom_comp_eq]
  have hH : H ⋙ TwoFibreProductOver.fst r 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor = s :=
    hsec l.map
  have hK : K ⋙ TwoFibreProductOver.fst r 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor = s :=
    hsec m.map
  let j : T' ⟶ T := InducedBicategory.mkHom ⟨Over.map (r.map i), rfl⟩
  let a := CatFiberedInGroupoids.diagonalOfSection (T := T) r y f.hom s hs H hH
  let b := CatFiberedInGroupoids.diagonalOfSection (T := T) r y f.hom s hs K hK
  let yT : T ⟶ 𝒴.1 := CatFiberedInGroupoids.targetOfSection (T := T) r y hy s hs
  let βa : yT ⟶ a ≫ f.hom :=
    CatFiberedInGroupoids.betaOfSection (T := T) r y hy f.hom s hs H hH
  let βb : yT ⟶ b ≫ f.hom :=
    CatFiberedInGroupoids.betaOfSection (T := T) r y hy f.hom s hs K hK
  have hgen : j.hom.toFunctor ⋙ H = j.hom.toFunctor ⋙ K := by
    have hn : ∀ n : yoneda.obj A ⟶ F,
        Over.map (r.map i) ⋙ Over.sliceRebase U A ⋙ sliceSectionOfHom n =
          Over.sliceRebase U G ⋙ sliceSectionOfHom (yoneda.map i ≫ n) := fun n =>
      (congrArg (fun k => k ⋙ sliceSectionOfHom n) (Over.sliceRebase_map U i)).trans
        (congrArg (fun k => Over.sliceRebase U G ⋙ k) (sliceSectionOfHom_map i n))
    exact congrArg (fun k => k ⋙ e.inv.functor)
      ((hn l.map).trans
        ((congrArg (fun n => Over.sliceRebase U G ⋙ sliceSectionOfHom n)
          (l.generic_comm.trans m.generic_comm.symm)).trans
          (hn m.map).symm))
  have hsj : (j.hom.toFunctor ⋙ s) ⋙ r = T'.val.p :=
    (congrArg (fun k => j.hom.toFunctor ⋙ k) hs).trans j.hom.w
  have hjH := congrArg (fun k => j.hom.toFunctor ⋙ k) hH
  have hjK := congrArg (fun k => j.hom.toFunctor ⋙ k) hK
  have hab : j ≫ a = j ≫ b :=
    CatFiberedInGroupoids.diagonalOfSection_congr (T := T') r y f.hom
      (j.hom.toFunctor ⋙ s) hsj _ _ hjH hjK hgen
  have hβgen := CatFiberedInGroupoids.betaOfSection_congr (T := T') r y hy f.hom
    (j.hom.toFunctor ⋙ s) hsj _ _ hjH hjK hgen
  let eL := FractionRing.algEquiv q.R q.K
  let eC : CommRingCat.of (FractionRing q.R) ≅ CommRingCat.of q.K :=
    eL.toRingEquiv.toCommRingCatIso
  let γ : j ≫ yT ⟶ (j ≫ a) ≫ f.hom := (j ◁ βa) ≫ (α_ j a f.hom).inv
  let D : ValuativeDiagram B S hS 𝒳 𝒴 f :=
    { R := q.R
      generic := r.obj G
      whole := r.obj A
      generic_iso := Scheme.Spec.mapIso eC.op
      whole_iso := Iso.refl _
      inclusion := r.map i
      inclusion_spec := by
        show Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
          Spec.map eC.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap q.R (FractionRing q.R))) ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1
        ext x
        exact (eL.commutes x).symm
      j := j
      j_canonical := rfl
      x := j ≫ a
      y := yT
      γ := γ }
  let da : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ :=
    { a := a
      α := 𝟙 _
      β := βa
      compat := by simp only [D, γ, id_whiskerRight, Category.comp_id] }
  let db : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ :=
    { a := b
      α := eqToHom hab.symm
      β := βb
      compat := by
        refine InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
        funext z
        show βa.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ 𝟙 _ =
          βb.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ 𝟙 _ ≫
            f.hom.hom.toFunctor.map ((eqToHom hab.symm).hom.toNatTrans.app z)
        refine Eq.trans (Category.comp_id _) ?_
        refine Eq.trans (CatFiberedInGroupoids.betaOfSection_app (T := T) r y hy f.hom s hs
          H hH (j.hom.toFunctor.obj z)) ?_
        refine Eq.trans ?_ (congrArg
          (fun t => βb.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
          (Category.id_comp _)).symm
        refine Eq.trans ?_ (congrArg (fun t => t ≫ f.hom.hom.toFunctor.map
          ((eqToHom hab.symm).hom.toNatTrans.app z))
          (CatFiberedInGroupoids.betaOfSection_app (T := T) r y hy f.hom s hs
            K hK (j.hom.toFunctor.obj z)).symm)
        refine Eq.trans (CatFiberedInGroupoids.betaOfSection_app (T := T') r y hy f.hom
          (j.hom.toFunctor ⋙ s) hsj (j.hom.toFunctor ⋙ H) hjH z).symm ?_
        refine Eq.trans (congrArg (fun t => t.hom.toNatTrans.app z) hβgen) ?_
        exact congrArg (fun t => t ≫ f.hom.hom.toFunctor.map
          ((eqToHom hab.symm).hom.toNatTrans.app z))
          (CatFiberedInGroupoids.betaOfSection_app (T := T') r y hy f.hom
            (j.hom.toFunctor ⋙ s) hsj (j.hom.toFunctor ⋙ K) hjK z) }
  obtain ⟨η⟩ := h D hq da db
  let z : T.val.obj := Over.mk (𝟙 (r.obj A))
  let φ := CatFiberedInGroupoids.sectionHomApp (T := T) r y hy f.hom s hs H K hH hK
    η.hom.θ η.hom.cond_β z
  have he : e.inv.functor.IsEquivalence := e.toEquivalence.isEquivalence_inverse
  let ψ := e.inv.functor.preimage φ
  have hψ : ψ.base = 𝟙 (s.obj z) := by
    have hh : (TwoFibreProductOver.fst r 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor).map φ =
        eqToHom (Functor.congr_obj e.inv.w _) ≫ ψ.base ≫
          eqToHom (Functor.congr_obj e.inv.w _).symm :=
      (congrArg (TwoFibreProductOver.fst r 𝒳.val.val.p 𝒴.val.val.p y
        f.hom.hom.toFunctor).map (e.inv.functor.map_preimage φ).symm).trans
        (Functor.congr_hom e.inv.w ψ)
    have hh2 : eqToHom (Functor.congr_obj hH z) ≫ eqToHom (Functor.congr_obj hK z).symm =
        eqToHom (Functor.congr_obj e.inv.w _) ≫ ψ.base ≫
          eqToHom (Functor.congr_obj e.inv.w _).symm :=
      (CatFiberedInGroupoids.sectionHomApp_a (T := T) r y hy f.hom s hs H K hH hK
        η.hom.θ η.hom.cond_β z).symm.trans hh
    exact eq_id_of_conj_eqToHom (Functor.congr_obj hH z)
      (Functor.congr_obj hK z).symm ψ.base hh2
  have hi : IsIso (J.obj z).hom := by
    show IsIso (Over.homMk (𝟙 A.left) : Over.mk (𝟙 A.left ≫ A.hom) ⟶ A)
    exact (Over.isoMk (Iso.refl _) (by simp) : Over.mk (𝟙 A.left ≫ A.hom) ≅ A).isIso_hom
  have hlm : l.map = m.map := eq_of_hom_sliceSectionOfHom l.map m.map (J.obj z) ψ hψ
  cases l
  cases m
  cases hlm
  rfl

/-- **Stacks 0CLJ.** For a 1-morphism of algebraic stacks representable by algebraic spaces, the
uniqueness part of the valuative criterion holds exactly when it holds for every base change to
an algebraic space along a scheme-valued point of the target.

The base change is described exactly as in Stacks 02ZW: for an object `U` of the site and a
scheme-valued point `y` of `𝒴` over `U`, it is the first projection of the 2-fibre product
`U ×_𝒴 𝒳`, and the condition is imposed on the structure morphism of *any* algebraic space `F`
over `U` equivalent to it over the site of `U`. Quantifying over all such `F` rather than over a
chosen one spares a consumer the transport along a comparison equivalence. -/
@[stacks 0CLJ]
theorem valuativeCriterionUniqueness_iff_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ValuativeCriterion.Uniqueness B S hS f ↔
      ∀ U : BigFppfOver B S hS,
        let 𝒰 := BigFppfOver B U.left.1 U.left.2
        let p𝒰 : 𝒰 ⥤ BigFppfOver B S hS := Over.map U.hom
        ∀ (y : 𝒰 ⥤ 𝒴.val.val.obj) (_hy : y ⋙ 𝒴.val.val.p = p𝒰) (F : 𝒰ᵒᵖ ⥤ Type u)
          (_hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
          (_e : StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst p𝒰 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor)
            (presheafOfCategories (F ⋙ typeToCat)).p)
          (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))),
          Space.ValuativeCriterion.Uniqueness p := by
  have hfaith : f.hom.hom.toFunctor.Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f.hom hf
  rw [valuativeCriterionUniqueness_iff_forall_nonempty_iso B S hS f hf]
  constructor
  · intro hiso U
    dsimp only
    intro y hy F _hF e p q
    exact subsingleton_lift_baseChange_point B S hS f (fun _ => True)
      (fun D _ => hiso D) U y hy F e p q trivial
  · intro hbase D a b
    obtain ⟨F, hF, ⟨e⟩⟩ := hf D.whole (valuativeDiagramTargetPoint B S hS D)
      (valuativeDiagramTargetPoint_comp B S hS D)
    let p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj D.whole.left.2))) :=
      { app := fun V => ↾fun _ => Over.mkIdTerminal.from V.unop
        naturality := by
          intros
          ext
          apply Over.mkIdTerminal.hom_ext }
    exact nonempty_iso_of_baseChange_uniqueness B S hS D a b e p
      (hbase D.whole _ (valuativeDiagramTargetPoint_comp B S hS D) F hF e p)

end AlgebraicGeometry.Stack

end
