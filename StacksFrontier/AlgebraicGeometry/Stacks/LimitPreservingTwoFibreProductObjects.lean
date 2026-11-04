module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability

/-!
# The structure morphism of a 2-fibre product is limit preserving on objects

Let `𝒳 ⟶ 𝒴` and `𝒵 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the big fppf site
of a scheme `S`. Stacks 07XM asserts two things about the 2-fibre product `𝒳 ×_𝒴 𝒵`: part (1),
that its structure morphism to `(Sch/S)_{fppf}` is limit preserving on objects in the sense of
Stacks 06CU as soon as those of `𝒳` and of `𝒵` are and `𝒴` is limit preserving in the sense of
Stacks 07XL; and part (2), that `𝒳 ×_𝒴 𝒵` is itself limit preserving when `𝒳`, `𝒴` and `𝒵` are.
This file proves part (1), and the cancellation for Stacks 06CU that the same two hypotheses give.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct`:
  **Stacks 07XM, part (1)**.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`: the *cancellation* for
  Stacks 06CU — a 1-morphism `f : 𝒳 ⟶ 𝒴` is limit preserving on objects as soon as the structure
  morphism of `𝒳` is and `𝒴` is limit preserving. It is not one of the three stability properties
  of Stacks 06CU (base change, composition, reindexing) and does not follow from them; the source
  of Stacks 07XX uses it without stating it.

## Implementation notes

*What is and is not proved.* Only part (1) is proved here, and the tag carries that restriction.
Part (2), that the colimit comparison of Stacks 07XL is an equivalence for the 2-fibre product, is
`AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProduct` in
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProduct`. The source itself proves
only the essential surjectivity of part (1) and says the arguments for part (2) are omitted.

*The proof.* It is the source's. An object of `𝒳 ×_𝒴 𝒵` over an affine inverse limit `T = lim Tᵢ`
is a triple `(x, z, φ)` with `φ : f(x) ≅ g(z)` vertical over `T`. Limit preservation on objects for
`𝒳` and for `𝒵`, read against the identity comparison in the base, says exactly that `x` and `z`
are cartesian pullbacks of objects at finite stages up to vertical isomorphism; a single stage for
both is reached by pulling the first back along the transition morphism, which is where
cartesianness is used rather than a choice of pullbacks. The comparison `φ` then becomes a vertical
morphism between pullbacks of two objects of `𝒴` at that stage, and fullness of the colimit
comparison of Stacks 07XL — all that is taken from the hypothesis on `𝒴` — descends it to a
vertical morphism `φᵢ` at a later stage. Being vertical in a category fibred in groupoids, `φᵢ` is
an isomorphism, so the triple it assembles is an object of `𝒳 ×_𝒴 𝒵` over that stage, and the pair
of cartesian comparisons is a morphism of the 2-fibre product by
`CategoryTheory.TwoFibreProductOver.isStronglyCartesian_of_components`.

*Descending a morphism from the colimit.* `CategoryTheory.Cat.exists_stage_map_of_colimit` produces
the two endpoints of the descended morphism at a common stage but along two possibly different
transition morphisms, which no triple `(x, z, φ)` can be built from. A private lemma here
equalises them: the index category being cofiltered, its opposite is filtered, and
`CategoryTheory.IsFiltered.coeq` coequalises the two transitions at a further stage.

`Deformation.Artin.descentHom_of_full` in
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent` is the public statement of the
same descent, in a shape whose two factorisation equations are the ones a consumer wants; the
cancellation below uses it rather than the private lemma. The private lemma is retained because
the proof of part (1) is written against its comparison-by-comparison shape.

*The cancellation.* It needs both halves separately and nothing else: the hypothesis on `𝒳`
descends the object, and *fullness only* of the comparison for `𝒴` descends the leftover vertical
morphism. Pulling the prescribed target object back along the transition morphism is what turns
the given cartesian comparison into a vertical one, and that is the only step not already present
in the proof of part (1).

*The target.* `(Sch/S)_{fppf}` is `AlgebraicGeometry.Stack.terminalCFG`, the site with the identity
as structure functor, and the structure morphism is `AlgebraicGeometry.Stack.toTerminalCFG`. Its
structure functor being an identity, the comparison in the target that Stacks 06CU asks for is
determined by the morphism of the base it lies over, and the commuting square of Stacks 06CU holds
automatically; that bookkeeping is isolated in the private lemmas of the `Terminal` section.

## References

* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 07XX](https://stacks.math.columbia.edu/tag/07XX)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe uu u v w uC vC uX vX

section Bridge

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Functor.chosenPullbacks AsSmall.up AsSmall.down

/-- **Morphisms of a filtered colimit in `Cat` between images of objects of one stage come from a
single later stage.** This is `CategoryTheory.Cat.exists_stage_map_of_colimit` with the two
stages equalised, which filteredness allows. -/
private lemma exists_stage_map_of_colimit_of_eq
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{max uu v w, max uu v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max uu v w, max uu v w})]
    (j : I) (a b : F.obj j)
    (f : (colimit.ι F j).toFunctor.obj a ⟶ (colimit.ι F j).toFunctor.obj b) :
    ∃ (k : I) (r : j ⟶ k) (g : (F.map r).toFunctor.obj a ⟶ (F.map r).toFunctor.obj b),
      HEq ((colimit.ι F k).toFunctor.map g) f := by
  obtain ⟨l, s, t, g, hg⟩ := Cat.exists_stage_map_of_colimit.{uu, v, w} F j j a b f
  have hst : s ≫ IsFiltered.coeqHom s t = t ≫ IsFiltered.coeqHom s t :=
    IsFiltered.coeq_condition s t
  have hcs := congrArg Cat.Hom.toFunctor (F.map_comp s (IsFiltered.coeqHom s t))
  have hct := congrArg Cat.Hom.toFunctor (F.map_comp t (IsFiltered.coeqHom s t))
  have e₁ : (F.map (s ≫ IsFiltered.coeqHom s t)).toFunctor.obj a =
      (F.map (IsFiltered.coeqHom s t)).toFunctor.obj ((F.map s).toFunctor.obj a) :=
    Functor.congr_obj hcs a
  have e₂ : (F.map (IsFiltered.coeqHom s t)).toFunctor.obj ((F.map t).toFunctor.obj b) =
      (F.map (s ≫ IsFiltered.coeqHom s t)).toFunctor.obj b := by
    rw [hst]
    exact (Functor.congr_obj hct b).symm
  refine ⟨IsFiltered.coeq s t, s ≫ IsFiltered.coeqHom s t,
    eqToHom e₁ ≫ (F.map (IsFiltered.coeqHom s t)).toFunctor.map g ≫ eqToHom e₂, ?_⟩
  simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact (Functor.hcongr_hom
    (congrArg Cat.Hom.toFunctor (colimit.w F (IsFiltered.coeqHom s t))) g).trans hg

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {X : Type uX} [Category.{vX} X]

/-- **A vertical morphism over a cofiltered limit between pullbacks of objects of a stage comes
from a stage.** If the colimit comparison of the fibre categories at the cone is full, then a
vertical morphism `χ` between objects over the cone point which are cartesian pullbacks of objects
`a`, `b` at a stage `m` is, at some later stage `n`, the restriction of a vertical morphism `φ`
between cartesian pullbacks of `a` and `b` to that stage. -/
private theorem exists_stage_vertical_map_of_full (p : X ⥤ 𝒞) [p.IsFibered]
    {I : Type v} [Category.{w} I] [IsCofiltered I] (E : I ⥤ 𝒞) (d : Cone E)
    (hfull : (Deformation.Artin.colimitComparison p E d).Full)
    (m : I) (a b : p.Fiber (E.obj m)) {A Bo : X} (α : A ⟶ a.1) (β : Bo ⟶ b.1)
    (hα : p.IsStronglyCartesian (d.π.app m) α) (hβ : p.IsStronglyCartesian (d.π.app m) β)
    (χ : A ⟶ Bo) (hχ : p.IsHomLift (𝟙 d.pt) χ) :
    ∃ (n : I) (r : n ⟶ m) (an bn : p.Fiber (E.obj n))
      (αn : an.1 ⟶ a.1) (βn : bn.1 ⟶ b.1) (φ : an.1 ⟶ bn.1)
      (A' : A ⟶ an.1) (B' : Bo ⟶ bn.1),
      p.IsStronglyCartesian (E.map r) αn ∧ p.IsStronglyCartesian (E.map r) βn ∧
        p.IsHomLift (𝟙 (E.obj n)) φ ∧ p.IsHomLift (d.π.app n) A' ∧
        p.IsHomLift (d.π.app n) B' ∧ A' ≫ αn = α ∧ B' ≫ βn = β ∧ A' ≫ φ = χ ≫ B' := by
  have hA : p.obj A = d.pt := IsHomLift.domain_eq p (d.π.app m) α
  have hB : p.obj Bo = d.pt := IsHomLift.domain_eq p (d.π.app m) β
  let Af : p.Fiber d.pt := ⟨A, hA⟩
  let Bf : p.Fiber d.pt := ⟨Bo, hB⟩
  let FY := Deformation.Artin.fiberDiagram p E
  let K := Deformation.Artin.colimitComparison p E d
  let oa : p.SplitFiber (E.obj m) := ⟨E.obj m, a, 𝟙 (E.obj m)⟩
  let ob : p.SplitFiber (E.obj m) := ⟨E.obj m, b, 𝟙 (E.obj m)⟩
  let aSmall : (FY.obj (op m) : Type _) := AsSmall.up.{vX, max uC uX vC, max v w}.obj oa
  let bSmall : (FY.obj (op m) : Type _) := AsSmall.up.{vX, max uC uX vC, max v w}.obj ob
  have eqa : K.obj ((colimit.ι FY (op m)).toFunctor.obj aSmall) =
      Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m)) :=
    Functor.congr_obj (Deformation.Artin.colimitComparison_ι p E d m) aSmall
  have eqb : K.obj ((colimit.ι FY (op m)).toFunctor.obj bSmall) =
      Functor.pullbackFiber p b (d.π.app m ≫ 𝟙 (E.obj m)) :=
    Functor.congr_obj (Deformation.Artin.colimitComparison_ι p E d m) bSmall
  have hαc : p.IsStronglyCartesian (d.π.app m ≫ 𝟙 (E.obj m)) α := by
    simpa using hα
  have hβc : p.IsStronglyCartesian (d.π.app m ≫ 𝟙 (E.obj m)) β := by
    simpa using hβ
  let eA : Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m)) ≅ Af :=
    Functor.fiberIsoOfCartesian (d.π.app m ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap a.2 (d.π.app m ≫ 𝟙 (E.obj m))) α
      inferInstance inferInstance
  let eB : Functor.pullbackFiber p b (d.π.app m ≫ 𝟙 (E.obj m)) ≅ Bf :=
    Functor.fiberIsoOfCartesian (d.π.app m ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (d.π.app m ≫ 𝟙 (E.obj m))) β
      inferInstance inferInstance
  have hAinv : Functor.Fiber.fiberInclusion.map eA.inv ≫
      Functor.IsPreFibered.pullbackMap a.2 (d.π.app m ≫ 𝟙 (E.obj m)) = α :=
    Functor.fiberIsoOfCartesian_inv_fac (p := p) (d.π.app m ≫ 𝟙 (E.obj m))
      (z := Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m))) (z' := Af)
      (Functor.IsPreFibered.pullbackMap a.2 (d.π.app m ≫ 𝟙 (E.obj m))) α
      inferInstance inferInstance
  have hBinv : Functor.Fiber.fiberInclusion.map eB.inv ≫
      Functor.IsPreFibered.pullbackMap b.2 (d.π.app m ≫ 𝟙 (E.obj m)) = β :=
    Functor.fiberIsoOfCartesian_inv_fac (p := p) (d.π.app m ≫ 𝟙 (E.obj m))
      (z := Functor.pullbackFiber p b (d.π.app m ≫ 𝟙 (E.obj m))) (z' := Bf)
      (Functor.IsPreFibered.pullbackMap b.2 (d.π.app m ≫ 𝟙 (E.obj m))) β
      inferInstance inferInstance
  let χf : Af ⟶ Bf := ⟨χ, hχ⟩
  let ψ : K.obj ((colimit.ι FY (op m)).toFunctor.obj aSmall) ⟶
      K.obj ((colimit.ι FY (op m)).toFunctor.obj bSmall) :=
    eqToHom eqa ≫ eA.hom ≫ χf ≫ eB.inv ≫ eqToHom eqb.symm
  obtain ⟨Φ, hΦ⟩ := hfull.map_surjective ψ
  obtain ⟨kop, rop, g', hg'⟩ :=
    exists_stage_map_of_colimit_of_eq.{max vX uC uX vC, v, w} FY (op m) aSmall bSmall Φ
  obtain ⟨n⟩ := kop
  -- the two objects of the split fibre at the later stage `n`, and the morphism between them
  let α₀ : (⟨E.obj m, a, E.map rop.unop ≫ 𝟙 (E.obj m)⟩ : p.SplitFiber (E.obj n)) ⟶
      (⟨E.obj m, b, E.map rop.unop ≫ 𝟙 (E.obj m)⟩ : p.SplitFiber (E.obj n)) :=
    AsSmall.down.{vX, max uC uX vC, max v w}.map g'
  have hbase : d.π.app m ≫ 𝟙 (E.obj m) =
      d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m) := by
    rw [← Category.assoc, d.w rop.unop]
  have ef : Functor.pullbackFiber p a (d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m)) =
      Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m)) :=
    congrArg (fun g => Functor.pullbackFiber p a g) hbase.symm
  have efb : Functor.pullbackFiber p b (d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m)) =
      Functor.pullbackFiber p b (d.π.app m ≫ 𝟙 (E.obj m)) :=
    congrArg (fun g => Functor.pullbackFiber p b g) hbase.symm
  have e1 : (Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m))).1 =
      (Functor.pullbackFiber p a (d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m))).1 :=
    congrArg (fun z : p.Fiber d.pt => z.1) ef.symm
  have e1b : (Functor.pullbackFiber p b (d.π.app m ≫ 𝟙 (E.obj m))).1 =
      (Functor.pullbackFiber p b (d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m))).1 :=
    congrArg (fun z : p.Fiber d.pt => z.1) efb.symm
  -- the comparison morphisms asked for
  let A' : A ⟶ (Functor.pullbackFiber p a (E.map rop.unop ≫ 𝟙 (E.obj m))).1 :=
    Functor.Fiber.fiberInclusion.map eA.inv ≫ eqToHom e1 ≫
      Functor.pullbackFiberProj a (E.map rop.unop ≫ 𝟙 (E.obj m)) (d.π.app n)
  have hβn : p.IsStronglyCartesian (E.map rop.unop ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) := inferInstance
  have hβ₀ : p.IsHomLift (d.π.app m ≫ 𝟙 (E.obj m)) β := hβc.toIsHomLift
  let B' : Bo ⟶ (Functor.pullbackFiber p b (E.map rop.unop ≫ 𝟙 (E.obj m))).1 :=
    Functor.IsStronglyCartesian.map p (E.map rop.unop ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) hbase β
  have hB'fac : B' ≫ Functor.IsPreFibered.pullbackMap b.2
      (E.map rop.unop ≫ 𝟙 (E.obj m)) = β :=
    Functor.IsStronglyCartesian.fac p (E.map rop.unop ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) hbase β
  have hB'lift : p.IsHomLift (d.π.app n) B' :=
    Functor.IsStronglyCartesian.map_isHomLift p (E.map rop.unop ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) hbase β
  have hφlift : p.IsHomLift (𝟙 (E.obj n))
      (Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom α₀)) :=
    (Functor.SplitFiber.toFiberHom α₀).2
  have heqlift : p.IsHomLift (𝟙 d.pt) (eqToHom e1) :=
    IsHomLift.eqToHom_domain_lift_id e1
      (Functor.pullbackFiber p a (d.π.app m ≫ 𝟙 (E.obj m))).2
  have hA'lift : p.IsHomLift (d.π.app n) A' := by
    have h₁ : p.IsHomLift (𝟙 d.pt) (Functor.Fiber.fiberInclusion.map eA.inv) := eA.inv.2
    have h₃ : p.IsHomLift (d.π.app n)
        (Functor.pullbackFiberProj a (E.map rop.unop ≫ 𝟙 (E.obj m)) (d.π.app n)) :=
      inferInstance
    have h : p.IsHomLift (𝟙 d.pt ≫ 𝟙 d.pt ≫ d.π.app n)
        (Functor.Fiber.fiberInclusion.map eA.inv ≫ eqToHom e1 ≫
          Functor.pullbackFiberProj a (E.map rop.unop ≫ 𝟙 (E.obj m)) (d.π.app n)) :=
      inferInstance
    simpa using h
  -- `α₀` restricts to `χ`: the fullness datum, transported into the fibre over the cone point
  have hwa : (colimit.ι FY (op n)).toFunctor.obj ((FY.map rop).toFunctor.obj aSmall) =
      (colimit.ι FY (op m)).toFunctor.obj aSmall :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w FY rop)) aSmall
  have hwb : (colimit.ι FY (op n)).toFunctor.obj ((FY.map rop).toFunctor.obj bSmall) =
      (colimit.ι FY (op m)).toFunctor.obj bSmall :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w FY rop)) bSmall
  have h2 : HEq (K.map ((colimit.ι FY (op n)).toFunctor.map g')) (K.map Φ) :=
    Cat.map_heq_of_eq K hwa hwb hg'
  have h3 : HEq (K.map ((colimit.ι FY (op n)).toFunctor.map g'))
      (Functor.SplitFiber.restrictHom (d.π.app n) (Functor.SplitFiber.toFiberHom α₀)) :=
    Functor.hcongr_hom (Deformation.Artin.colimitComparison_ι p E d n) g'
  have hheq : HEq (Functor.SplitFiber.restrictHom (d.π.app n)
      (Functor.SplitFiber.toFiberHom α₀)) ψ :=
    h3.symm.trans (h2.trans (heq_of_eq hΦ))
  have hE1 := Cat.transport_hom_of_heq (ef.trans eqa.symm) (efb.trans eqb.symm) hheq
  have hE1' : Functor.SplitFiber.restrictHom (d.π.app n) (Functor.SplitFiber.toFiberHom α₀) =
      eqToHom ef ≫ eA.hom ≫ χf ≫ eB.inv ≫ eqToHom efb.symm := by
    rw [(comp_eqToHom_iff _ _ _).mp hE1]
    dsimp only [ψ]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  have hfac : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.restrictHom (d.π.app n) (Functor.SplitFiber.toFiberHom α₀)) ≫
      Functor.IsPreFibered.pullbackMap b.2 (d.π.app n ≫ E.map rop.unop ≫ 𝟙 (E.obj m)) =
      Functor.pullbackFiberProj a (E.map rop.unop ≫ 𝟙 (E.obj m)) (d.π.app n) ≫
        Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom α₀) ≫
        Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m)) :=
    Functor.SplitFiber.restrictHom_fac (d.π.app n) (Functor.SplitFiber.toFiberHom α₀)
  have hmain : Functor.pullbackFiberProj a (E.map rop.unop ≫ 𝟙 (E.obj m)) (d.π.app n) ≫
      Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom α₀) ≫
      Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m)) =
      eqToHom e1.symm ≫ Functor.Fiber.fiberInclusion.map eA.hom ≫ χ ≫ β := by
    rw [← hfac, hE1']
    simp only [Functor.map_comp, eqToHom_map, Category.assoc]
    rw [Functor.eqToHom_comp_pullbackMap b hbase e1b, hBinv]
    rfl
  have hA'fac : A' ≫ Functor.IsPreFibered.pullbackMap a.2
      (E.map rop.unop ≫ 𝟙 (E.obj m)) = α := by
    dsimp only [A']
    simp only [Category.assoc]
    rw [Functor.pullbackFiberProj_fac, Functor.eqToHom_comp_pullbackMap a hbase e1, hAinv]
  have hsquare : A' ≫ Functor.Fiber.fiberInclusion.map
      (Functor.SplitFiber.toFiberHom α₀) = χ ≫ B' := by
    have h₁ : p.IsHomLift (d.π.app n) (A' ≫ Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom α₀)) := by
      simpa using (inferInstance : p.IsHomLift (d.π.app n ≫ 𝟙 (E.obj n))
        (A' ≫ Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom α₀)))
    have h₂ : p.IsHomLift (d.π.app n) (χ ≫ B') := by
      simpa using (inferInstance : p.IsHomLift (𝟙 d.pt ≫ d.π.app n) (χ ≫ B'))
    refine Functor.IsStronglyCartesian.ext p (E.map rop.unop ≫ 𝟙 (E.obj m))
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) (d.π.app n) ?_
    simp only [Category.assoc, hB'fac]
    dsimp only [A']
    simp only [Category.assoc]
    rw [hmain]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hαnc : p.IsStronglyCartesian (E.map rop.unop)
      (Functor.IsPreFibered.pullbackMap a.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) := by
    have h : p.IsStronglyCartesian (E.map rop.unop ≫ 𝟙 (E.obj m))
        (Functor.IsPreFibered.pullbackMap a.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) := inferInstance
    simpa using h
  have hβnc : p.IsStronglyCartesian (E.map rop.unop)
      (Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m))) := by
    simpa using hβn
  exact ⟨n, rop.unop, Functor.pullbackFiber p a (E.map rop.unop ≫ 𝟙 (E.obj m)),
    Functor.pullbackFiber p b (E.map rop.unop ≫ 𝟙 (E.obj m)),
    Functor.IsPreFibered.pullbackMap a.2 (E.map rop.unop ≫ 𝟙 (E.obj m)),
    Functor.IsPreFibered.pullbackMap b.2 (E.map rop.unop ≫ 𝟙 (E.obj m)),
    Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom α₀), A', B',
    hαnc, hβnc, hφlift, hA'lift, hB'lift, hA'fac, hB'fac, hsquare⟩

end Bridge

section Terminal

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {X : Type uX} [Category.{vX} X]

/-- **The descent datum of Stacks 06CU for a structure morphism, from the bare descent of the
object.** The target being the base itself, the comparison in the target asked for by Stacks 06CU
is forced by the morphism of the base it lies over, and the commuting square is automatic. -/
private theorem exists_descent_datum_of_descent (p : X ⥤ 𝒞) [p.IsFibered]
    {I : Type v} [Category.{w} I] (E : I ⥤ 𝒞) (d : Cone E)
    (i : I) (y : (𝟭 𝒞).Fiber (E.obj i)) (x : p.Fiber d.pt) (γ : p.obj x.1 ⟶ y.1)
    (hγ : (𝟭 𝒞).IsStronglyCartesian (d.π.app i) γ)
    (i' : I) (j : i' ⟶ i) (x' : p.Fiber (E.obj i')) (xU : p.Fiber d.pt)
    (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1)
    (hδ : p.IsStronglyCartesian (d.π.app i') δ) (hβ : p.IsHomLift (𝟙 d.pt) β)
    (hβi : IsIso β) :
    ∃ (i' : I) (j : i' ⟶ i) (x' : p.Fiber (E.obj i')) (xU : p.Fiber d.pt)
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1) (γ' : p.obj x'.1 ⟶ y.1),
      p.IsStronglyCartesian (d.π.app i') δ ∧ p.IsHomLift (𝟙 d.pt) β ∧ IsIso β ∧
        (𝟭 𝒞).IsStronglyCartesian (E.map j) γ' ∧ p.map δ ≫ γ' = p.map β ≫ γ := by
  have hγ' : (𝟭 𝒞).IsHomLift (E.map j) (eqToHom x'.2 ≫ E.map j ≫ eqToHom y.2.symm) :=
    IsHomLift.of_fac' (𝟭 𝒞) (E.map j) _ x'.2 y.2 rfl
  refine ⟨i', j, x', xU, δ, β, eqToHom x'.2 ≫ E.map j ≫ eqToHom y.2.symm,
    hδ, hβ, hβi, ?_, ?_⟩
  · exact Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  · refine eq_of_isHomLift_id (d.π.app i) _ _ ?_ ?_
    · have h₁ : (𝟭 𝒞).IsHomLift (d.π.app i') (p.map δ) :=
        have := hδ.toIsHomLift
        IsHomLift.of_fac' (𝟭 𝒞) (d.π.app i') _ xU.2 x'.2
          (IsHomLift.fac' p (d.π.app i') δ)
      have hcomp : (𝟭 𝒞).IsHomLift (d.π.app i' ≫ E.map j)
          (p.map δ ≫ eqToHom x'.2 ≫ E.map j ≫ eqToHom y.2.symm) := inferInstance
      rwa [d.w j] at hcomp
    · have h₃ : (𝟭 𝒞).IsHomLift (𝟙 d.pt) (p.map β) :=
        have := hβ
        IsHomLift.of_fac' (𝟭 𝒞) (𝟙 d.pt) _ xU.2 x.2 (IsHomLift.fac' p (𝟙 d.pt) β)
      have h₄ : (𝟭 𝒞).IsHomLift (d.π.app i) γ := hγ.toIsHomLift
      exact IsHomLift.comp_lift_id_left' (𝟭 𝒞) d.pt _ _ _

/-- **The bare descent of an object, from the descent datum of Stacks 06CU for the structure
morphism.** Testing Stacks 06CU against the identity comparison in the base leaves exactly the
statement that the object is a cartesian pullback of an object at a stage dominating the
prescribed index, up to a vertical isomorphism. -/
private theorem exists_descent_of_descent_datum (p : X ⥤ 𝒞) [p.IsFibered]
    {I : Type v} [Category.{w} I] (E : I ⥤ 𝒞) (d : Cone E)
    (h : ∀ (i : I) (y : (𝟭 𝒞).Fiber (E.obj i)) (x : p.Fiber d.pt) (γ : p.obj x.1 ⟶ y.1),
      (𝟭 𝒞).IsStronglyCartesian (d.π.app i) γ →
      ∃ (i' : I) (j : i' ⟶ i) (x' : p.Fiber (E.obj i')) (xU : p.Fiber d.pt)
        (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1) (γ' : p.obj x'.1 ⟶ y.1),
        p.IsStronglyCartesian (d.π.app i') δ ∧ p.IsHomLift (𝟙 d.pt) β ∧ IsIso β ∧
          (𝟭 𝒞).IsStronglyCartesian (E.map j) γ' ∧ p.map δ ≫ γ' = p.map β ≫ γ)
    (i : I) (x : p.Fiber d.pt) :
    ∃ (i' : I) (_ : i' ⟶ i) (x' : p.Fiber (E.obj i')) (xU : p.Fiber d.pt)
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1),
      p.IsStronglyCartesian (d.π.app i') δ ∧ p.IsHomLift (𝟙 d.pt) β ∧ IsIso β := by
  have hlift : (𝟭 𝒞).IsHomLift (d.π.app i) (eqToHom x.2 ≫ d.π.app i) :=
    IsHomLift.of_fac' (𝟭 𝒞) (d.π.app i) (eqToHom x.2 ≫ d.π.app i) x.2 rfl (by simp)
  have := hlift
  have hSC : (𝟭 𝒞).IsStronglyCartesian (d.π.app i) (eqToHom x.2 ≫ d.π.app i) :=
    Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  obtain ⟨i', j, x', xU, δ, β, _, hδ, hβ, hβi, _, _⟩ :=
    h i ⟨E.obj i, rfl⟩ x (eqToHom x.2 ≫ d.π.app i) hSC
  exact ⟨i', j, x', xU, δ, β, hδ, hβ, hβi⟩

/-- A strongly cartesian morphism over a composite `π ≫ g` factors through the pullback along `g`
by a strongly cartesian morphism over `π`. -/
private theorem exists_stronglyCartesian_factor_pullback (p : X ⥤ 𝒞) [p.IsFibered]
    {a b c : 𝒞} (g : b ⟶ c) (π : a ⟶ b) (π' : a ⟶ c) (hfac : π' = π ≫ g)
    (x : p.Fiber c) {U : X} (δ : U ⟶ x.1) (hδ : p.IsStronglyCartesian π' δ) :
    ∃ δ' : U ⟶ (Functor.pullbackFiber p x g).1,
      δ' ≫ Functor.IsPreFibered.pullbackMap x.2 g = δ ∧ p.IsHomLift π δ' ∧
        p.IsStronglyCartesian π δ' := by
  have := hδ.toIsHomLift
  refine ⟨Functor.IsStronglyCartesian.map p g (Functor.IsPreFibered.pullbackMap x.2 g) hfac δ,
    Functor.IsStronglyCartesian.fac p g (Functor.IsPreFibered.pullbackMap x.2 g) hfac δ,
    Functor.IsStronglyCartesian.map_isHomLift p g (Functor.IsPreFibered.pullbackMap x.2 g) hfac δ,
    ?_⟩
  have hlift := Functor.IsStronglyCartesian.map_isHomLift p g
    (Functor.IsPreFibered.pullbackMap x.2 g) hfac δ
  have hcs : p.IsStronglyCartesian (π ≫ g)
      (Functor.IsStronglyCartesian.map p g (Functor.IsPreFibered.pullbackMap x.2 g) hfac δ ≫
        Functor.IsPreFibered.pullbackMap x.2 g) := by
    rw [Functor.IsStronglyCartesian.fac, ← hfac]; exact hδ
  exact Functor.IsStronglyCartesian.of_comp p (f := π) (g := g) (φ := _)
    (ψ := Functor.IsPreFibered.pullbackMap x.2 g)

/-- The image under a functor compatible with the projections of an object over `c` lies over
`c`. -/
private theorem obj_eq_of_comp_eq {Y : Type*} [Category Y] {F : X ⥤ Y} {q : Y ⥤ 𝒞} {p : X ⥤ 𝒞}
    (hF : F ⋙ q = p) {c : 𝒞} {x : X} (hx : p.obj x = c) : q.obj (F.obj x) = c :=
  (congrArg (fun G => G.obj x) hF).trans hx

end Terminal



section Main

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Bicategory.InducedBicategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (pf : 𝒳 ⟶ 𝒴) (qf : 𝒵 ⟶ 𝒴)

/-- **Stacks 07XM, part (1).** If the structure morphisms of `𝒳` and of `𝒵` to `(Sch/S)_{fppf}`
are limit preserving on objects and `𝒴` is limit preserving, then the structure morphism of the
2-fibre product `𝒳 ×_𝒴 𝒵` to `(Sch/S)_{fppf}` is limit preserving on objects.

Part (2) of Stacks 07XM, that `𝒳 ×_𝒴 𝒵` is limit preserving when `𝒳`, `𝒴` and `𝒵` are, is
`AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProduct`. -/
@[stacks 07XM "part (1)"]
theorem isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct
    (h𝒳 : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (h𝒵 : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒵
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒵)))
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒴) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf) (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS
        (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf))) := by
  intro I _ _ D c hc i y W γ hγ
  have hfibX : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hfibZ : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  have hfibY : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let inc := BigAffineFppf.inclusion B S hS
  let E := D ⋙ inc
  let d := inc.mapCone c
  let Fp := CatFiberedInGroupoids.homFunctor pf
  let Gq := CatFiberedInGroupoids.homFunctor qf
  let T := (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf).val.p
  have hFcomp : Fp ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p pf
  have hGcomp : Gq ⋙ 𝒴.val.p = 𝒵.val.p := CatFiberedInGroupoids.homFunctor_comp_p qf
  have hfibT : T.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf).isFiberedInGroupoids.isFibered
  -- the two hypotheses, in the shape of a descent of objects
  have hdX : ∀ (i₀ : I) (x : 𝒳.val.p.Fiber d.pt),
      ∃ (i' : I) (_ : i' ⟶ i₀) (x' : 𝒳.val.p.Fiber (E.obj i'))
        (xU : 𝒳.val.p.Fiber d.pt) (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1),
        𝒳.val.p.IsStronglyCartesian (d.π.app i') δ ∧
          𝒳.val.p.IsHomLift (𝟙 d.pt) β ∧ IsIso β :=
    fun i₀ x => exists_descent_of_descent_datum 𝒳.val.p E d (h𝒳 I D c hc) i₀ x
  have hdZ : ∀ (i₀ : I) (z : 𝒵.val.p.Fiber d.pt),
      ∃ (i' : I) (_ : i' ⟶ i₀) (z' : 𝒵.val.p.Fiber (E.obj i'))
        (zU : 𝒵.val.p.Fiber d.pt) (δ : zU.1 ⟶ z'.1) (β : zU.1 ⟶ z.1),
        𝒵.val.p.IsStronglyCartesian (d.π.app i') δ ∧
          𝒵.val.p.IsHomLift (𝟙 d.pt) β ∧ IsIso β :=
    fun i₀ z => exists_descent_of_descent_datum 𝒵.val.p E d (h𝒵 I D c hc) i₀ z
  have hfull : (Deformation.Artin.colimitComparison 𝒴.val.p E d).Full := (h𝒴 I D c hc).full
  -- the components of the given object of the 2-fibre product over the limit
  have hW : W.1.base = d.pt := W.2
  let x0 : 𝒳.val.p.Fiber d.pt := ⟨W.1.x, W.1.hx.trans hW⟩
  let z0 : 𝒵.val.p.Fiber d.pt := ⟨W.1.y, W.1.hy.trans hW⟩
  obtain ⟨i₁, j₁, x₁, xU, δx, βx, hδx, hβx, hβxi⟩ := hdX i x0
  obtain ⟨i₂, j₂, z₂, zU, δz, βz, hδz, hβz, hβzi⟩ := hdZ i₁ z0
  -- bring the first component to the same stage as the second
  have hfac1 : d.π.app i₁ = d.π.app i₂ ≫ E.map j₂ := (d.w j₂).symm
  let x₂ : 𝒳.val.p.Fiber (E.obj i₂) := Functor.pullbackFiber 𝒳.val.p x₁ (E.map j₂)
  obtain ⟨δx₂, -, -, hδx₂⟩ := exists_stronglyCartesian_factor_pullback 𝒳.val.p (E.map j₂)
    (d.π.app i₂) _ hfac1 x₁ δx hδx
  -- the two objects of `𝒴` at that stage, and the vertical comparison over the limit
  let aF : 𝒴.val.p.Fiber (E.obj i₂) := ⟨Fp.obj x₂.1, obj_eq_of_comp_eq hFcomp x₂.2⟩
  let bG : 𝒴.val.p.Fiber (E.obj i₂) := ⟨Gq.obj z₂.1, obj_eq_of_comp_eq hGcomp z₂.2⟩
  have hWiso : 𝒴.val.p.IsHomLift (𝟙 d.pt) W.1.iso.hom := by
    rw [← hW]; exact W.1.vertical
  let χIso : Fp.obj xU.1 ≅ Gq.obj zU.1 :=
    Fp.mapIso (asIso βx) ≪≫ W.1.iso ≪≫ (Gq.mapIso (asIso βz)).symm
  have hFβx : 𝒴.val.p.IsStronglyCartesian (𝟙 d.pt) (Fp.map βx) :=
    CatFiberedInGroupoids.isStronglyCartesian_map pf (𝟙 d.pt) βx
  have hGβz : 𝒴.val.p.IsStronglyCartesian (𝟙 d.pt) (Gq.map (inv βz)) := by
    have : 𝒵.val.p.IsHomLift (𝟙 d.pt) (inv βz) := IsHomLift.lift_id_inv_isIso 𝒵.val.p d.pt βz
    exact CatFiberedInGroupoids.isStronglyCartesian_map qf (𝟙 d.pt) (inv βz)
  have hχ : 𝒴.val.p.IsHomLift (𝟙 d.pt) χIso.hom := by
    have h1 : 𝒴.val.p.IsHomLift (𝟙 d.pt) (Fp.map βx) := hFβx.toIsHomLift
    have h3 : 𝒴.val.p.IsHomLift (𝟙 d.pt) (Gq.map (inv βz)) := hGβz.toIsHomLift
    have h : 𝒴.val.p.IsHomLift (𝟙 d.pt ≫ 𝟙 d.pt ≫ 𝟙 d.pt)
        (Fp.map βx ≫ W.1.iso.hom ≫ Gq.map (inv βz)) := inferInstance
    rwa [Category.id_comp, Category.id_comp] at h
  have hα : 𝒴.val.p.IsStronglyCartesian (d.π.app i₂) (Fp.map δx₂) := by
    have := hδx₂.toIsHomLift
    exact CatFiberedInGroupoids.isStronglyCartesian_map pf (d.π.app i₂) δx₂
  have hβ : 𝒴.val.p.IsStronglyCartesian (d.π.app i₂) (Gq.map δz) := by
    have := hδz.toIsHomLift
    exact CatFiberedInGroupoids.isStronglyCartesian_map qf (d.π.app i₂) δz
  -- fullness of the comparison for `𝒴` descends the vertical comparison to a stage
  obtain ⟨n, rr, an, bn, αn, βn, φ, A', B', hαn, hβn, hφ, hA'lift, hB'lift, hA'fac, hB'fac,
      hsq⟩ := exists_stage_vertical_map_of_full 𝒴.val.p E d hfull i₂ aF bG
    (Fp.map δx₂) (Gq.map δz) hα hβ χIso.hom hχ
  -- the two components at the final stage
  have hfac2 : d.π.app i₂ = d.π.app n ≫ E.map rr := (d.w rr).symm
  let xn : 𝒳.val.p.Fiber (E.obj n) := Functor.pullbackFiber 𝒳.val.p x₂ (E.map rr)
  let ζx' : xn.1 ⟶ x₂.1 := Functor.IsPreFibered.pullbackMap x₂.2 (E.map rr)
  let zn : 𝒵.val.p.Fiber (E.obj n) := Functor.pullbackFiber 𝒵.val.p z₂ (E.map rr)
  let ζz' : zn.1 ⟶ z₂.1 := Functor.IsPreFibered.pullbackMap z₂.2 (E.map rr)
  obtain ⟨δxn, hδxnfac, hδxnlift, hδxnSC⟩ := exists_stronglyCartesian_factor_pullback
    𝒳.val.p (E.map rr) (d.π.app n) _ hfac2 x₂ δx₂ hδx₂
  obtain ⟨δzn, hδznfac, hδznlift, hδznSC⟩ := exists_stronglyCartesian_factor_pullback
    𝒵.val.p (E.map rr) (d.π.app n) _ hfac2 z₂ δz hδz
  -- comparing the descended objects with the ones the fullness datum produced
  let xnF : 𝒴.val.p.Fiber (E.obj n) := ⟨Fp.obj xn.1, obj_eq_of_comp_eq hFcomp xn.2⟩
  let znG : 𝒴.val.p.Fiber (E.obj n) := ⟨Gq.obj zn.1, obj_eq_of_comp_eq hGcomp zn.2⟩
  have hFζx : 𝒴.val.p.IsStronglyCartesian (E.map rr) (Fp.map ζx') := by
    have : 𝒳.val.p.IsHomLift (E.map rr) ζx' :=
      (inferInstance : 𝒳.val.p.IsStronglyCartesian (E.map rr) ζx').toIsHomLift
    exact CatFiberedInGroupoids.isStronglyCartesian_map pf (E.map rr) ζx'
  have hGζz : 𝒴.val.p.IsStronglyCartesian (E.map rr) (Gq.map ζz') := by
    have : 𝒵.val.p.IsHomLift (E.map rr) ζz' :=
      (inferInstance : 𝒵.val.p.IsStronglyCartesian (E.map rr) ζz').toIsHomLift
    exact CatFiberedInGroupoids.isStronglyCartesian_map qf (E.map rr) ζz'
  let u : xnF ≅ an :=
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) (E.map rr) (z := xnF) (z' := an)
      (Fp.map ζx') αn inferInstance inferInstance
  let v : znG ≅ bn :=
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) (E.map rr) (z := znG) (z' := bn)
      (Gq.map ζz') βn inferInstance inferInstance
  have hufac : Functor.Fiber.fiberInclusion.map u.hom ≫ αn = Fp.map ζx' :=
    Functor.fiberIsoOfCartesian_hom_fac (p := 𝒴.val.p) (E.map rr) (z := xnF) (z' := an)
      (Fp.map ζx') αn inferInstance inferInstance
  have hvinv : Functor.Fiber.fiberInclusion.map v.inv ≫ Gq.map ζz' = βn :=
    Functor.fiberIsoOfCartesian_inv_fac (p := 𝒴.val.p) (E.map rr) (z := znG) (z' := bn)
      (Gq.map ζz') βn inferInstance inferInstance
  have hφiso : IsIso (⟨φ, hφ⟩ : an ⟶ bn) :=
    (𝒴.isFiberedInGroupoids.fiber_isGroupoid (E.obj n)).all_isIso _
  let Wiso : Fp.obj xn.1 ≅ Gq.obj zn.1 :=
    Functor.Fiber.fiberInclusion.mapIso
      (u ≪≫ asIso (⟨φ, hφ⟩ : an ⟶ bn) ≪≫ v.symm)
  -- the comparison between the two descended objects restricts to the given one
  have hu : Fp.map δxn ≫ Functor.Fiber.fiberInclusion.map u.hom = A' := by
    have h₁ : 𝒴.val.p.IsHomLift (d.π.app n)
        (Fp.map δxn ≫ Functor.Fiber.fiberInclusion.map u.hom) := by
      have hl : 𝒴.val.p.IsHomLift (d.π.app n) (Fp.map δxn) := by
        have := hδxnlift
        exact Functor.isHomLift_map_of_comp_eq hFcomp (d.π.app n) δxn
      have hr : 𝒴.val.p.IsHomLift (𝟙 (E.obj n))
          (Functor.Fiber.fiberInclusion.map u.hom) := u.hom.2
      have := hl
      have := hr
      have h : 𝒴.val.p.IsHomLift (d.π.app n ≫ 𝟙 (E.obj n))
          (Fp.map δxn ≫ Functor.Fiber.fiberInclusion.map u.hom) := inferInstance
      rwa [Category.comp_id] at h
    have h₂ := hA'lift
    refine Functor.IsStronglyCartesian.ext 𝒴.val.p (E.map rr) αn (d.π.app n) ?_
    rw [Category.assoc, hufac, ← Functor.map_comp, hδxnfac, hA'fac]
  have hsquareW : Fp.map δxn ≫ Wiso.hom = χIso.hom ≫ Gq.map δzn := by
    have := Functor.isHomLift_map_of_comp_eq hFcomp (d.π.app n) δxn
    have := Functor.isHomLift_map_of_comp_eq hGcomp (d.π.app n) δzn
    have : 𝒴.val.p.IsHomLift (𝟙 (E.obj n)) Wiso.hom :=
      (u ≪≫ asIso (⟨φ, hφ⟩ : an ⟶ bn) ≪≫ v.symm).hom.2
    have : 𝒴.val.p.IsHomLift (d.π.app n) (χIso.hom ≫ Gq.map δzn) := by
      simpa using (inferInstance :
        𝒴.val.p.IsHomLift (𝟙 d.pt ≫ d.π.app n) (χIso.hom ≫ Gq.map δzn))
    refine Functor.IsStronglyCartesian.ext 𝒴.val.p (E.map rr) (Gq.map ζz') (d.π.app n) ?_
    have hrhs : (χIso.hom ≫ Gq.map δzn) ≫ Gq.map ζz' = χIso.hom ≫ Gq.map δz := by
      rw [Category.assoc, ← Functor.map_comp, hδznfac]
    have hWisohom : Wiso.hom = Functor.Fiber.fiberInclusion.map u.hom ≫ φ ≫
        Functor.Fiber.fiberInclusion.map v.inv := by
      show Functor.Fiber.fiberInclusion.map
        (u.hom ≫ (⟨φ, hφ⟩ : an ⟶ bn) ≫ v.inv) = _
      rw [Functor.map_comp, Functor.map_comp]
      rfl
    rw [hrhs, hWisohom]
    simp only [Category.assoc]
    rw [hvinv, ← Category.assoc (Fp.map δxn), hu, ← Category.assoc A', hsq,
      Category.assoc, hB'fac]
  -- the two objects of the 2-fibre product and the two morphisms between them
  let WU : TwoFibreProductOver 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq :=
    { base := d.pt
      x := xU.1
      y := zU.1
      hx := xU.2
      hy := zU.2
      iso := χIso
      vertical := hχ }
  let W' : TwoFibreProductOver 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq :=
    { base := E.obj n
      x := xn.1
      y := zn.1
      hx := xn.2
      hy := zn.2
      iso := Wiso
      vertical := (u ≪≫ asIso (⟨φ, hφ⟩ : an ⟶ bn) ≪≫ v.symm).hom.2 }
  let Δ : WU ⟶ W' :=
    { hbase := d.π.app n
      a := δxn
      b := δzn
      ha := hδxnlift
      hb := hδznlift
      w := hsquareW }
  let Β : WU ⟶ W.1 :=
    { hbase := eqToHom hW.symm
      a := βx
      b := βz
      ha := by
        simpa using (inferInstance :
          𝒳.val.p.IsHomLift (𝟙 d.pt ≫ eqToHom hW.symm) βx)
      hb := by
        simpa using (inferInstance :
          𝒵.val.p.IsHomLift (𝟙 d.pt ≫ eqToHom hW.symm) βz)
      w := by
        show Fp.map βx ≫ W.1.iso.hom =
          (Fp.map βx ≫ W.1.iso.hom ≫ Gq.map (inv βz)) ≫ Gq.map βz
        rw [Category.assoc, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.comp_id] }
  have hΔlift : T.IsHomLift (d.π.app n) Δ := IsHomLift.map T Δ
  have hΔSC : T.IsStronglyCartesian (d.π.app n) Δ :=
    TwoFibreProductOver.isStronglyCartesian_of_components
      (𝒴.isFiberedInGroupoids.isFibredOneMorphism hFcomp)
      (𝒴.isFiberedInGroupoids.isFibredOneMorphism hGcomp)
      (d.π.app n) Δ hΔlift hδxnSC hδznSC
  have hΒlift : T.IsHomLift (𝟙 d.pt) Β := by
    apply IsHomLift.of_commsq T (𝟙 d.pt) Β rfl hW
    show eqToHom hW.symm ≫ eqToHom hW = eqToHom rfl ≫ 𝟙 d.pt
    simp
  have hΒiso : IsIso Β := TwoFibreProductOver.isIso_of_components Β
  exact exists_descent_datum_of_descent T E d i y W γ hγ n (rr ≫ j₂ ≫ j₁)
    ⟨W', rfl⟩ ⟨WU, rfl⟩ Δ Β hΔSC hΒlift hΒiso

end Main

section Cancellation

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Bicategory.InducedBicategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴)

/-- **The cancellation for Stacks 06CU.** If the structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is
limit preserving on objects and `𝒴` is limit preserving, then every 1-morphism `f : 𝒳 ⟶ 𝒴` is
limit preserving on objects.

This is the step the source of **Stacks 07XX** leaves implicit when it reads its condition (3) on
`𝒳 ⟶ (Sch/S)_{fppf}` and then applies Stacks 06CX to `f`. Given an object `x` of `𝒳` over an
affine inverse limit `T = lim Tᵢ` and a cartesian comparison `γ` of its image with an object `y`
of `𝒴` at a stage `i`, the hypothesis on `𝒳` descends `x` itself to a stage `i₁` dominating `i`,
up to a vertical isomorphism `βx`; pulling `y` back along the transition morphism factors `γ`
cartesianly over the cone leg at `i₁`. What is then left is a *vertical* comparison over `T`
between two objects of `𝒴` which are cartesian pullbacks of objects at the stage `i₁` — namely
the image of `βx` — and that is exactly what fullness of the colimit comparison for `𝒴`
descends, by `Deformation.Artin.descentHom_of_full`. Fullness is the half of limit preservation
that essential surjectivity does not give, and it is all that is taken from the hypothesis
on `𝒴`; this is the same use of it that the proof of Stacks 07XM part (1) above makes.

No stability property of Stacks 06CU is used: this is not a composition (Stacks 06CW), a base
change (Stacks 06CV) or a reindexing, and it does not follow from them. It carries no tag — the
tag 06CU is carried by the definition, and the source states no separate cancellation lemma. -/
theorem isLimitPreservingOnObjects_of_toTerminalCFG
    (h𝒳 : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒴) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳 𝒴 f := by
  intro I _ _ D c hc i y x γ hγ₀
  have hfibX : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hfibY : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let inc := BigAffineFppf.inclusion B S hS
  let E := D ⋙ inc
  let d := inc.mapCone c
  let Fp := CatFiberedInGroupoids.homFunctor f
  have hFcomp : Fp ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  have hγ : 𝒴.val.p.IsStronglyCartesian (d.π.app i) γ := hγ₀
  have hfull : (Deformation.Artin.colimitComparison 𝒴.val.p E d).Full := (h𝒴 I D c hc).full
  -- condition (3): the object `x` of `𝒳` descends to a stage dominating `i`
  obtain ⟨i₁, j₁, x₁, xU, δx, βx, hδx, hβx, hβxi⟩ :=
    exists_descent_of_descent_datum 𝒳.val.p E d (h𝒳 I D c hc) i x
  -- pull the target object `y` back to that stage, and factor `γ` through the pullback
  have hfac1 : d.π.app i = d.π.app i₁ ≫ E.map j₁ := (d.w j₁).symm
  let y₁ : 𝒴.val.p.Fiber (E.obj i₁) := Functor.pullbackFiber 𝒴.val.p y (E.map j₁)
  let ηy : y₁.1 ⟶ y.1 := Functor.IsPreFibered.pullbackMap y.2 (E.map j₁)
  have hηy : 𝒴.val.p.IsStronglyCartesian (E.map j₁) ηy := inferInstance
  have := hγ.toIsHomLift
  have := hηy
  let γ₁ : Fp.obj x.1 ⟶ y₁.1 :=
    Functor.IsStronglyCartesian.map 𝒴.val.p (E.map j₁) ηy hfac1 γ
  have hγ₁fac : γ₁ ≫ ηy = γ :=
    Functor.IsStronglyCartesian.fac 𝒴.val.p (E.map j₁) ηy hfac1 γ
  have hγ₁lift : 𝒴.val.p.IsHomLift (d.π.app i₁) γ₁ :=
    Functor.IsStronglyCartesian.map_isHomLift 𝒴.val.p (E.map j₁) ηy hfac1 γ
  -- the three objects of `𝒴` the descent of the comparison is read on
  let aF : 𝒴.val.p.Fiber (E.obj i₁) := ⟨Fp.obj x₁.1, obj_eq_of_comp_eq hFcomp x₁.2⟩
  let xUF : 𝒴.val.p.Fiber d.pt := ⟨Fp.obj xU.1, obj_eq_of_comp_eq hFcomp xU.2⟩
  let xF : 𝒴.val.p.Fiber d.pt := ⟨Fp.obj x.1, obj_eq_of_comp_eq hFcomp x.2⟩
  have hFδx : 𝒴.val.p.IsHomLift (d.π.app i₁) (Fp.map δx) := by
    have := hδx.toIsHomLift
    exact Functor.isHomLift_map_of_comp_eq hFcomp (d.π.app i₁) δx
  have hFβx : 𝒴.val.p.IsHomLift (𝟙 d.pt) (Fp.map βx) :=
    Functor.isHomLift_map_of_comp_eq hFcomp (𝟙 d.pt) βx
  -- condition (4), fullness only: the vertical comparison descends to a further stage
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, hdx, hdy, hδk, hψ, hdxfac, hsq⟩ :=
    Deformation.Artin.descentHom_of_full 𝒴.val.p 𝒴.isFiberedInGroupoids E d
      i₁ aF y₁ xUF xF (Fp.map δx) γ₁ hFδx hγ₁lift (Fp.map βx) hFβx
  have hdxSC : 𝒴.val.p.IsStronglyCartesian (E.map s) dx :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift (E.map s) dx
  -- the descended object of `𝒳` at that further stage
  have hfac2 : d.π.app i₁ = d.π.app k ≫ E.map s := (d.w s).symm
  let xk' : 𝒳.val.p.Fiber (E.obj k) := Functor.pullbackFiber 𝒳.val.p x₁ (E.map s)
  let ζx : xk'.1 ⟶ x₁.1 := Functor.IsPreFibered.pullbackMap x₁.2 (E.map s)
  have hζx : 𝒳.val.p.IsStronglyCartesian (E.map s) ζx := inferInstance
  have := hδx.toIsHomLift
  have := hζx
  obtain ⟨δxk, hδxkfac, hδxklift, hδxkSC⟩ := exists_stronglyCartesian_factor_pullback
    𝒳.val.p (E.map s) (d.π.app k) _ hfac2 x₁ δx hδx
  -- its image in `𝒴` is identified with the object the descent of the comparison produced
  let xkF : 𝒴.val.p.Fiber (E.obj k) := ⟨Fp.obj xk'.1, obj_eq_of_comp_eq hFcomp xk'.2⟩
  have hFζx : 𝒴.val.p.IsStronglyCartesian (E.map s) (Fp.map ζx) := by
    have := hζx.toIsHomLift
    exact CatFiberedInGroupoids.isStronglyCartesian_map f (E.map s) ζx
  let u : xkF ≅ xk :=
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) (E.map s) (z := xkF) (z' := xk)
      (Fp.map ζx) dx inferInstance inferInstance
  let uh : Fp.obj xk'.1 ⟶ xk.1 := Functor.Fiber.fiberInclusion.map u.hom
  have huhfac : uh ≫ dx = Fp.map ζx :=
    Functor.fiberIsoOfCartesian_hom_fac (p := 𝒴.val.p) (E.map s) (z := xkF) (z' := xk)
      (Fp.map ζx) dx inferInstance inferInstance
  have huhlift : 𝒴.val.p.IsHomLift (𝟙 (E.obj k)) uh := u.hom.2
  -- through that identification the two comparisons over the limit agree
  have hkey : Fp.map δxk ≫ uh = δk := by
    have h₁ : 𝒴.val.p.IsHomLift (d.π.app k) (Fp.map δxk ≫ uh) := by
      have hl : 𝒴.val.p.IsHomLift (d.π.app k) (Fp.map δxk) := by
        have := hδxklift
        exact Functor.isHomLift_map_of_comp_eq hFcomp (d.π.app k) δxk
      have := hl
      have := huhlift
      have h : 𝒴.val.p.IsHomLift (d.π.app k ≫ 𝟙 (E.obj k)) (Fp.map δxk ≫ uh) :=
        inferInstance
      rwa [Category.comp_id] at h
    have h₂ := hδk
    refine Functor.IsStronglyCartesian.ext 𝒴.val.p (E.map s) dx (d.π.app k) ?_
    rw [Category.assoc, huhfac, ← Functor.map_comp, hδxkfac, hdxfac]
  refine ⟨k, s ≫ j₁, xk', xU, δxk, βx, uh ≫ ψ ≫ dy ≫ ηy, hδxkSC, hβx, hβxi, ?_, ?_⟩
  · have := hηy.toIsHomLift
    have : 𝒴.val.p.IsHomLift (E.map (s ≫ j₁)) (uh ≫ ψ ≫ dy ≫ ηy) := by
      rw [E.map_comp]
      infer_instance
    exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift (E.map (s ≫ j₁)) _
  · calc Fp.map δxk ≫ uh ≫ ψ ≫ dy ≫ ηy
        = (Fp.map δxk ≫ uh) ≫ (ψ ≫ dy) ≫ ηy := by simp only [Category.assoc]
      _ = (δk ≫ ψ ≫ dy) ≫ ηy := by rw [hkey]; simp only [Category.assoc]
      _ = (Fp.map βx ≫ γ₁) ≫ ηy := by rw [hsq]
      _ = Fp.map βx ≫ γ := by rw [Category.assoc, hγ₁fac]

end Cancellation

end AlgebraicGeometry.Stack

end
