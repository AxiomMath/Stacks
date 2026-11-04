module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Coherence of the dual, and the reflexive-hull adjunction from one local presentation

Let `X` be a scheme.  The reflexive-hull adjunction of
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) was reduced in
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/DualStalk.lean` to the single assumption that the
dual `F^∨ = SheafHom(F, 𝒪_X)` of a coherent module is coherent, which is the internal-Hom clause
of [Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2) at `𝒢 = 𝒪_X`.  This file reduces
that assumption further, to the *first* assertion of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) alone: that for a module of finite
presentation the dual is, around every point, the kernel of a morphism between two finite direct
sums of copies of the structure sheaf.

What makes the reduction possible is that the two other ingredients of Tag 01CQ's second
assertion are both in the library.  The passage "locally such a kernel, with coherent target,
hence coherent" is `Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean`, whose own module docstring
says it was written for exactly this specialization; and the coherence of `𝒪_X` on a locally
Noetherian scheme, which that lemma needs of its target, is
`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`, the structure-sheaf clause
of [Stacks, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ).

## Main definitions

* `HasLocalKernelPresentationDual X`: the first assertion of Tag 01CQ at `𝒢 = 𝒪_X`, as a
  predicate on `X`.  This is the one hypothesis every 0EBH-shaped statement below carries, so
  that all of them follow at once from Tag 01CQ.  That assertion is proved:
  `Stacks.AlgebraicGeometry.ReflexiveModules.hasLocalKernelPresentationDual` proves it
  unconditionally for every scheme, so every statement below is unconditional for a consumer
  that supplies it.  That theorem is not applied here: it carries its own copy of
  `HasLocalKernelPresentationDual`, and until the two copies are unified the module proving it
  cannot be imported into this one.

## Main results

* `isCoherent_dualSheaf_of_hasLocalKernelPresentation`: the internal-Hom clause of Tag 01Y2 at
  `𝒢 = 𝒪_X` from `HasLocalKernelPresentationDual`, on a locally Noetherian scheme.
* `isFinitePresentation_dualSheaf_of_hasLocalKernelPresentation`: the same input gives finite
  presentation of the dual, which is the form the stalk comparison of Tag 01CP consumes.
* `reflexiveHullAdjunctionOfLocalKernelPresentation`: **Tag 0EBH's adjunction from
  `HasLocalKernelPresentationDual` alone**, on an integral locally Noetherian scheme.
* `isCoherent_dualSheaf_of_isFinitePresentation_dual` and
  `reflexiveHullAdjunctionOfFinitePresentationDual`: the same two conclusions from the
  alternative input that the dual of a module of finite presentation is again of finite
  presentation.  On a locally Noetherian scheme that is equivalent to coherence of the dual by
  Tag 01XZ, and it is the shape an affine-local computation of the dual would produce.

## Implementation notes

The tag of Tag 0EBH is withheld on both adjunction statements, for the reason recorded in
`Adjunction.lean`: the conclusion asserts that the left adjoint lands in coherent reflexive
modules at the object `F^∨∨`, so it *implies* the coherence of the hull, which is
`isCoherent_and_isReflexive_dualSheaf_dualSheaf_of_adjunction`.  A statement carrying any of
these hypotheses is therefore strictly weaker than the tag.

Two coherence predicates realize Tag 01BV, with identical fields and no definitional conversion:
the root `SheafOfModules.IsCoherent` of Stacks Tag 01BW, which is what
`add_to_stacks 01BV` points at and what the dot-notation spelling `F.IsCoherent` resolves to for
`F : X.Modules`, and `Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, which carries `@[stacks 01BV]` and
over which the coherence-closure theory and the reflexive-hull adjunction are stated.  The
statements below are phrased over the second, matching `Adjunction.lean` and `DualStalk.lean`,
and cross to the first with `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent`
and `Stacks.SheafOfModules.IsCoherent.sheafOfModules`.  No third predicate is introduced.

`HasLocalKernelPresentationDual` is stated with the finite direct sums indexed by `Fin m` and
`Fin n` and the target spelled `SheafOfModules.unit X.ringCatSheaf`, because that is the shape
`isCoherent_of_locallyKernelFiniteCoproduct` consumes and the shape Tag 01CQ states; restating it
with an arbitrary finite index type would need a reindexing at every use.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open _root_.Stacks.AlgebraicGeometry.CoherenceCriteria
  (isCoherent'_of_isCoherent isCoherent_of_isFinitePresentation structureSheaf_isCoherent)

/-! ### The local kernel presentation of a dual -/

/-- **The first assertion of Stacks, Tag 01CQ, at `𝒢 = 𝒪_X`.**  For every `𝒪_X`-module `F` of
finite presentation and every point of `X` there is an open neighbourhood on which the dual
`F^∨ = SheafHom(F, 𝒪_X)` is the kernel of a morphism between two finite direct sums of copies of
the structure sheaf.

In the Stacks Project this is read off a finite presentation
`𝒪_U^{⊕ m} ⟶ 𝒪_U^{⊕ n} ⟶ F|_U ⟶ 0` by applying `SheafHom(-, 𝒪_U)`, which is left exact in its
first variable. -/
public def HasLocalKernelPresentationDual (X : Scheme.{u}) : Prop :=
  ∀ F : X.Modules, F.IsFinitePresentation → ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ m n : ℕ,
    ∃ f : (∐ fun _ : Fin m => (SheafOfModules.unit X.ringCatSheaf).over U) ⟶
          (∐ fun _ : Fin n => (SheafOfModules.unit X.ringCatSheaf).over U),
      Nonempty ((dualSheaf F).over U ≅ kernel f)

/-! ### Coherence of the dual -/

/-- A module that is coherent in the sense of `Stacks.SheafOfModules.IsCoherent` is of finite
presentation, by Tag 01BW (1). -/
private theorem isFinitePresentation_of_stacks_isCoherent {X : Scheme.{u}} (F : X.Modules)
    (hF : _root_.Stacks.SheafOfModules.IsCoherent F) : F.IsFinitePresentation :=
  have : _root_.SheafOfModules.IsCoherent F :=
    _root_.Stacks.SheafOfModules.IsCoherent.sheafOfModules F hF
  _root_.isFinitePresentation_of_isCoherent F

/-- **The internal-Hom clause of Stacks, Tag 01Y2, at `𝒢 = 𝒪_X`**, on a locally Noetherian
scheme, from the local kernel presentation of Tag 01CQ.

A coherent module is of finite presentation by Tag 01BW (1), so the hypothesis applies to it; the
structure sheaf is coherent by Tag 01XZ; and a sheaf of modules that is locally the kernel of a
morphism between finite direct sums of copies of a coherent sheaf is coherent. -/
public theorem isCoherent_dualSheaf_of_hasLocalKernelPresentation (X : Scheme.{u})
    [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X)
    (F : X.Modules) (hF : _root_.Stacks.SheafOfModules.IsCoherent F) :
    _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf F) := by
  have hunit : _root_.Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    isCoherent'_of_isCoherent (structureSheaf_isCoherent X)
  exact _root_.Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct
    (hLK F (isFinitePresentation_of_stacks_isCoherent F hF))

/-- **The dual of a coherent module is of finite presentation**, on a locally Noetherian scheme,
from the local kernel presentation of Tag 01CQ.  This is the form in which the stalk comparison of
Tag 01CP, and hence `isReflexive_dualSheaf_of_isFinitePresentation`, consumes the input. -/
public theorem isFinitePresentation_dualSheaf_of_hasLocalKernelPresentation (X : Scheme.{u})
    [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X)
    (F : X.Modules) (hF : _root_.Stacks.SheafOfModules.IsCoherent F) :
    (dualSheaf F).IsFinitePresentation :=
  isFinitePresentation_of_stacks_isCoherent _
    (isCoherent_dualSheaf_of_hasLocalKernelPresentation X hLK F hF)

/-- **The internal-Hom clause of Stacks, Tag 01Y2, at `𝒢 = 𝒪_X`** from the alternative input that
the dual of a module of finite presentation is again of finite presentation.

On a locally Noetherian scheme finite presentation and coherence agree, which is Tag 01XZ; the
two directions used here are Tag 01BW (1) on the source and Tag 01XZ (3) ⇒ (1) on the dual. -/
public theorem isCoherent_dualSheaf_of_isFinitePresentation_dual (X : Scheme.{u})
    [IsLocallyNoetherian X]
    (hFP : ∀ F : X.Modules, F.IsFinitePresentation → (dualSheaf F).IsFinitePresentation)
    (F : X.Modules) (hF : _root_.Stacks.SheafOfModules.IsCoherent F) :
    _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf F) :=
  isCoherent'_of_isCoherent
    (isCoherent_of_isFinitePresentation _ (hFP F (isFinitePresentation_of_stacks_isCoherent F hF)))

/-! ### The reflexive-hull adjunction -/

/-- **Stacks, Tag 0EBH, the adjunction**, on an integral locally Noetherian scheme, from the
first assertion of Tag 01CQ at `𝒢 = 𝒪_X` as its *only* input: taking reflexive hulls is left
adjoint to the inclusion of coherent reflexive modules into coherent modules, and the unit of the
adjunction is the canonical map to the double dual.

`reflexiveHullAdjunctionOfCoherentDual` of `DualStalk.lean` needs the coherence of the dual of a
coherent module; here that is supplied by `isCoherent_dualSheaf_of_hasLocalKernelPresentation`,
using Tag 01XZ for the coherence of `𝒪_X`.  The tag is withheld: the conclusion implies the
hypothesis of `reflexiveHullAdjunctionOfHull`, so the statement is weaker than Tag 0EBH. -/
public noncomputable def reflexiveHullAdjunctionOfLocalKernelPresentation (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X) :
    { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } :=
  reflexiveHullAdjunctionOfCoherentDual X
    (isCoherent_dualSheaf_of_hasLocalKernelPresentation X hLK)

/-- **Stacks, Tag 0EBH, the adjunction** from the alternative input that the dual of a module of
finite presentation is again of finite presentation.  The tag is withheld for the same reason. -/
public noncomputable def reflexiveHullAdjunctionOfFinitePresentationDual (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X]
    (hFP : ∀ F : X.Modules, F.IsFinitePresentation → (dualSheaf F).IsFinitePresentation) :
    { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } :=
  reflexiveHullAdjunctionOfCoherentDual X
    (isCoherent_dualSheaf_of_isFinitePresentation_dual X hFP)

/-! ### The adjunction at the category Tag 0EBH states it over -/

/-- **The reflexive-hull adjunction over an arbitrary property of modules.**  This is
`reflexiveHullAdjunctionOfHull` with the coherence predicate generalized to an arbitrary
`P : ObjectProperty X.Modules` closed under taking reflexive hulls.  Nothing in the construction
uses coherence: the hom bijection is `reflexiveHullHomEquiv` and the rest is
`CategoryTheory.Adjunction.leftAdjointOfEquiv`.

Generalizing is what lets the *same* theorem serve the two predicates that realize Tag 01BV —
the root `SheafOfModules.IsCoherent`, over which Tag 0EBH states the adjunction, and
`Stacks.SheafOfModules.IsCoherent`, over which the library's coherence-closure theory is stated —
without a second category, a second construction or a transport between them. -/
public noncomputable def reflexiveHullAdjunctionOfProperty (X : Scheme.{u})
    (P : ObjectProperty X.Modules)
    (hCoh : ∀ F : X.Modules, P F → P (dualSheaf (dualSheaf F)))
    (hRefl : ∀ F : X.Modules, P F → IsReflexive (dualSheaf (dualSheaf F))) :
    { p : (Σ L : P.FullSubcategory ⥤
        ObjectProperty.FullSubcategory (C := P.FullSubcategory) (fun F => IsReflexive F.obj),
        L ⊣ ObjectProperty.ι (fun F : P.FullSubcategory => IsReflexive F.obj)) //
      ∀ F : P.FullSubcategory,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } := by
  let obj : P.FullSubcategory →
      ObjectProperty.FullSubcategory (C := P.FullSubcategory) (fun F => IsReflexive F.obj) :=
    fun F => ⟨⟨dualSheaf (dualSheaf F.obj), hCoh F.obj F.property⟩, hRefl F.obj F.property⟩
  let e : ∀ F G, (obj F ⟶ G) ≃
      (F ⟶ (ObjectProperty.ι (fun F : P.FullSubcategory => IsReflexive F.obj)).obj G) :=
    fun F G => by
    letI : IsIso (toDoubleDual (dualSheaf (dualSheaf F.obj))) := hRefl F.obj F.property
    letI : IsIso (toDoubleDual G.obj.obj) := G.property
    exact
      { toFun := fun g => ⟨reflexiveHullHomEquiv F.obj G.obj.obj g.hom.hom⟩
        invFun := fun f => ⟨⟨(reflexiveHullHomEquiv F.obj G.obj.obj).symm f.hom⟩⟩
        left_inv := fun g => ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
          (reflexiveHullHomEquiv F.obj G.obj.obj).symm_apply_apply g.hom.hom
        right_inv := fun f => ObjectProperty.hom_ext _ <|
          (reflexiveHullHomEquiv F.obj G.obj.obj).apply_symm_apply f.hom }
  have he : ∀ F G G' (g : G ⟶ G') (h : obj F ⟶ G),
      e F G' (h ≫ g) = e F G h ≫
        (ObjectProperty.ι (fun F : P.FullSubcategory => IsReflexive F.obj)).map g :=
    fun F _ _ g h => ObjectProperty.hom_ext _
      (Category.assoc (toDoubleDual F.obj) h.hom.hom g.hom.hom).symm
  exact ⟨⟨Adjunction.leftAdjointOfEquiv e he, Adjunction.adjunctionOfEquivLeft e he⟩,
    fun F => ⟨rfl, (Category.comp_id _).trans (Category.comp_id (toDoubleDual F.obj))⟩⟩

/-- **The dual of a coherent module is coherent**, in the root `SheafOfModules.IsCoherent`
spelling that Tag 0EBH's category is cut out by, from the local kernel presentation of Tag
01CQ. -/
public theorem isCoherent_dualSheaf_of_hasLocalKernelPresentation'
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X)
    (F : X.Modules) (hF : F.IsCoherent) : (dualSheaf F).IsCoherent :=
  _root_.Stacks.SheafOfModules.IsCoherent.sheafOfModules _
    (isCoherent_dualSheaf_of_hasLocalKernelPresentation X hLK F
      (_root_.Stacks.SheafOfModules.isCoherent_of_sheafOfModules F hF))

/-- **The reflexive hull of a coherent module is reflexive**, on an integral locally Noetherian
scheme, from the local kernel presentation of Tag 01CQ.  This is the reflexivity half of Tag
0EBH's hull; the coherence half is
`isCoherent_dualSheaf_of_hasLocalKernelPresentation'` applied twice. -/
public theorem isReflexive_dualSheaf_dualSheaf_of_hasLocalKernelPresentation (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X)
    (F : X.Modules) (hF : F.IsCoherent) : IsReflexive (dualSheaf (dualSheaf F)) :=
  isReflexive_dualSheaf_of_isCoherent X
    (isCoherent_dualSheaf_of_hasLocalKernelPresentation X hLK) (dualSheaf F)
    (isCoherent_dualSheaf_of_hasLocalKernelPresentation X hLK F
      (_root_.Stacks.SheafOfModules.isCoherent_of_sheafOfModules F hF))

/-- **Stacks, Tag 0EBH, the adjunction, at the category the tag states it over**: on an integral
locally Noetherian scheme, taking reflexive hulls is left adjoint to the inclusion of coherent
reflexive modules into coherent modules, and the unit is the canonical map to the double dual.

The ambient category is `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`, the
full subcategory cut out by the root `SheafOfModules.IsCoherent` — the predicate that
`add_to_stacks 01BV` points at and the one Tag 0EBH's own statement uses — so this is the tag's
statement with no change of coherence class and no equivalence of categories interposed.

The tag is nevertheless withheld, because of the remaining hypothesis:
`HasLocalKernelPresentationDual X` is the first assertion of Tag 01CQ at `𝒢 = 𝒪_X`, and Tag 0EBH
does not assume it.  By
`isCoherent_and_isReflexive_dualSheaf_dualSheaf_of_adjunction` the conclusion implies the
coherence of the hull, so any statement carrying a hypothesis of this strength is weaker than the
tag. -/
public noncomputable def reflexiveHullAdjunction (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (hLK : HasLocalKernelPresentationDual X) :
    { p : (Σ L : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        ObjectProperty.FullSubcategory
          (C := _root_.AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
          (fun F => IsReflexive F.obj),
        L ⊣ ObjectProperty.ι
          (fun F : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf =>
            IsReflexive F.obj)) //
      ∀ F : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } :=
  reflexiveHullAdjunctionOfProperty X (fun M => M.IsCoherent)
    (fun F hF => isCoherent_dualSheaf_of_hasLocalKernelPresentation' X hLK _
      (isCoherent_dualSheaf_of_hasLocalKernelPresentation' X hLK F hF))
    (isReflexive_dualSheaf_dualSheaf_of_hasLocalKernelPresentation X hLK)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
