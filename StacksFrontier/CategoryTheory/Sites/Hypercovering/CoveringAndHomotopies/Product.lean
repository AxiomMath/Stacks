module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.FibreProduct

/-!
# Products of hypercoverings

Let `C` be a site given by a pretopology `J`, let `C` have fibre products and let `X : C`. The
product of two hypercoverings of `X`, taken in the category of simplicial semi-representable
objects over `X`, is again a hypercovering of `X`.

The proof is the one of the source: a product is the fibre product over the terminal object, the
morphism `L ⟶ *` is covering in degree zero because `L` is a hypercovering, and its relative
matching morphisms are covering because the matching objects of the terminal simplicial object
are terminal, so that the relative matching morphism is the matching morphism of `L` followed by
an isomorphism. Tag 01GH then applies.

## Main definitions

* `fibreProductIsoPullback`: the comparison isomorphism between the degreewise fibre product of
  two morphisms of simplicial objects and the fibre product taken in the functor category.

## Main results

* `isTerminal_truncation_obj`: the truncation of a terminal simplicial object is terminal.
* `isHypercovering_of_iso`: being a hypercovering transports along an isomorphism of simplicial
  semi-representable objects.
* `IsHypercovering.prod` is Tag 01GI.

## Implementation notes

The product is the categorical product in `SimplicialObject (SR(C, X))`, which exists because
`SR(C, X)` has finite limits (Tag 01G2, recorded as the instance
`hasFiniteLimits_formalCoproductOver`). Tag 01GH is stated for the degreewise fibre product
`SimplicialObject.fibreProduct`, so the product has to be compared with that construction; the
two differ by the isomorphism `fibreProductIsoPullback`, and `isHypercovering_of_iso` transports
the conclusion back.

## References

* [Stacks Project, Tag 01GI](https://stacks.math.columbia.edu/tag/01GI)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The truncation of a terminal simplicial object is terminal. -/
noncomputable def isTerminal_truncation_obj {D : Type u} [Category.{v} D] [HasTerminal D]
    (n : ℕ) {T : SimplicialObject D} (hT : IsTerminal T) :
    IsTerminal ((SimplicialObject.truncation n).obj T) := by
  have hTapp (i : (SimplexCategory.Truncated n)ᵒᵖ) :
      IsTerminal (T.obj ((SimplexCategory.Truncated.inclusion n).op.obj i)) :=
    IsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ D).obj
        ((SimplexCategory.Truncated.inclusion n).op.obj i)) T hT
  refine IsTerminal.ofUniqueHom (fun Y ↦ ?_) ?_
  · exact { app := fun i ↦ (hTapp i).from (Y.obj i)
            naturality := fun _ j _ ↦ (hTapp j).hom_ext _ _ }
  · intro Y f
    ext i
    exact (hTapp i).hom_ext _ _

/-- Being a hypercovering of `X` transports along an isomorphism of simplicial
semi-representable objects over `X`. -/
theorem isHypercovering_of_iso (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (e : K ≅ L)
    (hK : IsHypercovering J K) : IsHypercovering J L := by
  constructor
  · convert (IsCoveringOver.of_isIso J (e.inv.app (op ⦋0⦌))).comp J hK.1 using 1
    exact (terminal.hom_ext _ _).symm
  · intro n
    have he₁ : IsCoveringOver J (e.inv.app (op ⦋n + 1⦌)) := IsCoveringOver.of_isIso J _
    have he₂ : IsCoveringOver J
        (((SimplicialObject.cosk n).map e.hom).app (op ⦋n + 1⦌)) := by
      have : IsIso ((SimplicialObject.cosk n).map e.hom) := Functor.map_isIso _ _
      exact IsCoveringOver.of_isIso J _
    have hn : e.hom.app (op ⦋n + 1⦌) ≫
        ((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌) =
        ((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌) ≫
          ((SimplicialObject.cosk n).map e.hom).app (op ⦋n + 1⦌) :=
      NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality e.hom) (op ⦋n + 1⦌)
    have hmap : ((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌) =
        (e.inv.app (op ⦋n + 1⦌) ≫
          ((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)) ≫
          ((SimplicialObject.cosk n).map e.hom).app (op ⦋n + 1⦌) := by
      rw [← cancel_epi (e.hom.app (op ⦋n + 1⦌))]
      simpa only [← Category.assoc, e.hom_inv_id_app, Category.id_comp] using hn
    rw [hmap]
    exact (he₁.comp J (hK.2 n)).comp J he₂

/-- The degreewise fibre product of two morphisms of simplicial objects agrees with the fibre
product taken in the category of simplicial objects. -/
noncomputable def fibreProductIsoPullback {X : C}
    {K L T : SimplicialObject (FormalCoproduct.{w} (Over X))} (a : K ⟶ T) (b : L ⟶ T) :
    SimplicialObject.fibreProduct a b ≅ Limits.pullback a b :=
  (isPullback_pointwisePullback a b).isoIsPullback _ _ (IsPullback.of_hasPullback a b)

/-- A morphism from a hypercovering to a terminal simplicial object is covering in degree zero. -/
private theorem IsHypercovering.isCoveringOver_app_zero_of_isTerminal (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {L T : SimplicialObject (FormalCoproduct.{w} (Over X))} (hT : IsTerminal T)
    (hL : IsHypercovering J L) (b : L ⟶ T) : IsCoveringOver J (b.app (op ⦋0⦌)) := by
  have hT₀ : IsTerminal (T.obj (op ⦋0⦌)) :=
    IsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ (FormalCoproduct.{w} (Over X))).obj (op ⦋0⦌)) T hT
  let e := (terminalIsTerminal : IsTerminal (⊤_ FormalCoproduct.{w} (Over X))).uniqueUpToIso hT₀
  rw [← hT₀.hom_ext (terminal.from (L.obj (op ⦋0⦌)) ≫ e.hom) (b.app (op ⦋0⦌))]
  exact hL.1.comp J (IsCoveringOver.of_isIso J e.hom)

/-- The relative matching morphisms of a morphism from a hypercovering to a terminal simplicial
object are covering. -/
private theorem IsHypercovering.isCoveringOver_matching_of_isTerminal (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {L T : SimplicialObject (FormalCoproduct.{w} (Over X))} (hT : IsTerminal T)
    (hL : IsHypercovering J L) (b : L ⟶ T) (n : ℕ) : IsCoveringOver J
      (Limits.pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app T).app (op ⦋n + 1⦌)))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map b)).app (op ⦋n + 1⦌)))
        (b.app (op ⦋n + 1⦌))
        (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b)
          (op ⦋n + 1⦌))) := by
  let i := op (⦋n + 1⦌ : SimplexCategory)
  let f := ((SimplicialObject.coskAdj n).unit.app T).app i
  let g := ((SimplicialObject.Truncated.cosk n).map
    ((SimplicialObject.truncation n).map b)).app i
  have hf : IsIso f := by
    have hCosk : IsTerminal
        ((SimplicialObject.Truncated.cosk n).obj
          ((SimplicialObject.truncation n).obj T)) :=
      IsTerminal.isTerminalObj (G := SimplicialObject.Truncated.cosk n)
        (X := (SimplicialObject.truncation n).obj T) (isTerminal_truncation_obj n hT)
    have : IsIso ((SimplicialObject.coskAdj n).unit.app T) :=
      isIso_of_isTerminal hT hCosk _
    show IsIso (((SimplicialObject.coskAdj n).unit.app T).app i)
    infer_instance
  have hn : b.app i ≫ f = ((SimplicialObject.coskAdj n).unit.app L).app i ≫ g :=
    NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b) i
  have heq : Limits.pullback.lift (f := f) (g := g) (b.app i)
      (((SimplicialObject.coskAdj n).unit.app L).app i) hn =
      ((SimplicialObject.coskAdj n).unit.app L).app i ≫
        inv (Limits.pullback.snd f g) := by
    apply Limits.pullback.hom_ext
    · simp only [Limits.pullback.lift_fst, Category.assoc]
      rw [pullback_inv_snd_fst_of_left_isIso f g]
      rw [← cancel_mono f]
      simpa [Category.assoc] using hn
    · rw [Limits.pullback.lift_snd]
      simp
  rw [heq]
  exact (hL.2 n).comp J (IsCoveringOver.of_isIso J (inv (Limits.pullback.snd f g)))

/-- **Stacks Project, Tag 01GI.** The product of two hypercoverings of an object of a site with
fibre products is a hypercovering. -/
@[stacks 01GI]
theorem IsHypercovering.prod (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) :
    IsHypercovering J (K ⨯ L) := by
  let T : SimplicialObject (FormalCoproduct.{w} (Over X)) :=
    ⊤_ (SimplicialObject (FormalCoproduct.{w} (Over X)))
  have hT : IsTerminal T := terminalIsTerminal
  let a : K ⟶ T := terminal.from K
  let b : L ⟶ T := terminal.from L
  exact isHypercovering_of_iso J
    (prodIsoPullback K L ≪≫ (fibreProductIsoPullback a b).symm).symm
    (isHypercovering_fibreProduct J a b hK
      (IsHypercovering.isCoveringOver_app_zero_of_isTerminal J hT hL b)
      (IsHypercovering.isCoveringOver_matching_of_isTerminal J hT hL b))

end Stacks.CategoryTheory.Hypercovering

end
