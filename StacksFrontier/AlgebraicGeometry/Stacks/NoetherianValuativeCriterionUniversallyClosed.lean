module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageDiscreteValuationPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniversallyClosed
import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocalQuasiCompact
import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionClosedImmersion

/-!
# The Noetherian valuative criterion for universal closedness (Stacks 0H2C)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian and
`f` of finite type. Stacks 0H2C says that `f` is universally closed as soon as every valuative
square for `f` whose valuation ring is a *discrete* valuation ring acquires a dotted arrow after
an extension of the fraction field and passage to a dominating valuation ring.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistence`: the hypothesis of
  **Stacks 0H2C**, the existence part of the valuative criterion (**Stacks 0CLK**) restricted to
  discrete valuation rings.
* `AlgebraicGeometry.Stack.discreteExistence_baseChange`: that hypothesis is stable under base
  change, by **Stacks 0CLE**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_discreteExistence`: a finite-type
  1-morphism into a locally Noetherian algebraic stack satisfying it is closed on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence`: item (2) of
  **Stacks 0H2A** for such an `f`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistence`:
  **Stacks 0H2C**.

## Implementation notes

The hypothesis is phrased exactly as `AlgebraicGeometry.Stack.ValuativeCriterion.Existence` of
**Stacks 0CLK** is, through `AlgebraicGeometry.Stack.ValuativeSquare`, its
`DominatingExtension` — a field extension together with a valuation ring of it dominating the
given one — and the nonemptiness of `CategoryTheory.DottedArrow` at the pasted outer square; the
only change is the extra clause `IsDiscreteValuationRing q.R`. Nothing in the criterion asks the
dominating valuation ring to be discrete.

Base change of the hypothesis repeats the proof of **Stacks 0CLL** for
`AlgebraicGeometry.Stack.ValuativeCriterion.Existence`: the square for `f` obtained by pasting
with the base-change square has the *same* valuation ring, so the discreteness clause transports
for free, and the dotted arrow comes back along the equivalence of **Stacks 0CLE**. The two
auxiliary facts that proof needs — the normal form of the pasted 2-cell and the joint
detection of 2-isomorphisms by the projections of a 2-fibre product — are private there, so
they are re-proved here.

Closedness on points follows the proof of **Stacks 0CLW** for the full criterion. A closed
subset of `|𝒳|` is replaced by a closed substack supported on it, by the existence half of
**Stacks 0509**, `AlgebraicGeometry.Stack.exists_isClosedImmersion_range_pointsMap_eq`. The
hypothesis is not inherited by the substack directly: a valuative square for the composite
`i ≫ f` is read as one for `f` by `AlgebraicGeometry.Stack.ValuativeSquare.compRight`, the
hypothesis applied to it leaves behind the square for the closed immersion `i` of
`AlgebraicGeometry.Stack.ValuativeSquare.compUpper`, and the full criterion is available for `i`
by **Stacks 0CLP**. The point of `|𝒴|` prescribed in the closure of the image is reached by a
discrete valuative square by **Stacks 0H2B**.

Universal closedness follows from clause (2) of **Stacks 0H2A** by the implication from (2) to
(1), which holds because `f` is of finite type and hence quasi-compact:
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.universallyClosed_of_isQuasiCompactMorphism_of_isClosed_affine_lfp`.

## References

* [Stacks Project, Tag 0H2C](https://stacks.math.columbia.edu/tag/0H2C)
* [Stacks Project, Tag 0H2A](https://stacks.math.columbia.edu/tag/0H2A)
* [Stacks Project, Tag 0H2B](https://stacks.math.columbia.edu/tag/0H2B)
* [Stacks Project, Tag 0CLE](https://stacks.math.columbia.edu/tag/0CLE)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLL](https://stacks.math.columbia.edu/tag/0CLL)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

namespace ValuativeCriterion

/-- **The hypothesis of Stacks 0H2C.** A 1-morphism of algebraic stacks over `S` satisfies the
*discrete* existence part of the valuative criterion when every valuative square for it whose
valuation ring is a discrete valuation ring admits a dotted arrow after an extension of the
fraction field and passage to a dominating valuation ring.

This is `AlgebraicGeometry.Stack.ValuativeCriterion.Existence` of **Stacks 0CLK** with the extra
clause `IsDiscreteValuationRing q.R`; the dominating valuation ring is not asked to be
discrete. -/
@[stacks 0H2C "the hypothesis of the lemma: the existence part of the valuative criterion,
restricted to discrete valuation rings"]
abbrev DiscreteExistence (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : ValuativeSquare B S hS f, IsDiscreteValuationRing q.R →
    ∃ e : q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma)

end ValuativeCriterion

/-- **The hypothesis of Stacks 0H2C is stable under base change.** A base change of a
1-morphism of algebraic stacks satisfying the discrete existence part of the valuative criterion
satisfies it as well.

The valuative square for `f` obtained by pasting the given square with the base-change square
has the same valuation ring, so discreteness transports, and the dotted arrow comes back along
the equivalence of **Stacks 0CLE**. -/
@[stacks 0H2C "step 1 of the proof: the hypothesis is stable under base change, via Tag 0CLE"]
theorem discreteExistence_baseChange
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : ValuativeCriterion.DiscreteExistence B S hS f) :
    ValuativeCriterion.DiscreteExistence B S hS P.fst := by
  classical
  let φ := baseChangeFiller B S hS f g P
  obtain ⟨hcart⟩ := nonempty_isTwoCartesian_baseChange B S hS f g P hP
  intro q hqdvr
  obtain ⟨e, ⟨d⟩⟩ := hf
    { q with
      x := q.x ≫ P.snd.hom
      y := q.y ≫ g.hom
      γ := (α_ q.j q.y g.hom).inv ≫ (q.γ ▷ g.hom) ≫
        (α_ q.x P.fst.hom g.hom).hom ≫ (q.x ◁ φ.hom) ≫
        (α_ q.x P.snd.hom f.hom).inv } hqdvr
  let E : q.DominatingExtension :=
    { R' := e.R', commRing := e.commRing, domain := e.domain,
      valuationRing := e.valuationRing, K' := e.K', field := e.field, algebra := e.algebra,
      isFractionRing := e.isFractionRing, ringMap := e.ringMap, fieldMap := e.fieldMap,
      isLocalHom := e.isLocalHom, fraction_comm := e.fraction_comm,
      ring_mem := e.ring_mem, field_mem := e.field_mem,
      specialOver := e.specialOver, specialOver_left := e.specialOver_left,
      genericOver := e.genericOver, genericOver_left := e.genericOver_left,
      genericMap := e.genericMap, genericMap_left := e.genericMap_left,
      j := e.j, j_canonical := e.j_canonical, a := e.a, a_canonical := e.a_canonical,
      k := e.k, k_canonical := e.k_canonical, commute := e.commute }
  have hγ : IsIso E.inducedGamma :=
    (CatFiberedInGroupoids.homGroupoid _ _).all_isIso E.inducedGamma
  obtain ⟨E'⟩ := CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence
    E.j (E.k ≫ q.x) P.snd.hom P.fst.hom f.hom (E.a ≫ q.y) g.hom φ
    (asIso E.inducedGamma) hcart
  have hγeq : ((α_ E.j (E.a ≫ q.y) g.hom).symm ≪≫
      Bicategory.whiskerRightIso (asIso E.inducedGamma) g.hom ≪≫
      (α_ (E.k ≫ q.x) P.fst.hom g.hom) ≪≫
      Bicategory.whiskerLeftIso (E.k ≫ q.x) φ ≪≫
      (α_ (E.k ≫ q.x) P.snd.hom f.hom).symm).hom = e.inducedGamma := by
    dsimp only [ValuativeSquare.DominatingExtension.inducedGamma]
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerRightIso_hom,
      Bicategory.whiskerLeftIso_hom]
    exact CatFiberedInGroupoids.pastedGamma e.j e.a e.k q.j q.y q.x P.fst.hom P.snd.hom
      g.hom f.hom e.commute q.γ φ.hom
  exact ⟨E, ⟨E'.inverse.obj
    { a := d.a, α := d.α, β := d.β, compat := hγeq.trans d.compat }⟩⟩

namespace AlgebraicStacks

/-- **Closedness on points from the hypothesis of Stacks 0H2C.** Let `f : 𝒳 ⟶ 𝒴` be a
finite-type 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian which satisfies
the discrete existence part of the valuative criterion. Then `f` is closed on points.

A closed subset of `|𝒳|` is the set of points of a closed substack `i : 𝒵 ⟶ 𝒳` by the existence
half of **Stacks 0509**, so its image is
the image of `|𝒵| → |𝒴|`. A point in the closure of that image is reached by a discrete
valuative square for `i ≫ f` (**Stacks 0H2B**); read as a square for `f` it yields a lift to `𝒳`
over a dominating valuation ring, and the full existence criterion, available for the closed
immersion `i` by **Stacks 0CLP**, lifts that further to `𝒵`. -/
@[stacks 0H2C "steps 3 and 4 of the proof: closedness on points"]
theorem isClosed_of_discreteExistence (f : 𝒳 ⟶ 𝒴)
    (hf : IsFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hlift : ValuativeCriterion.DiscreteExistence B S hS f) :
    IsClosed B S hS f := by
  classical
  intro T hT
  let _ : TopologicalSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) :=
    Stack.pointTopology B S hS 𝒳.val
  let _ : TopologicalSpace (Stack.points B S hS 𝒴.val.val 𝒴.val.property) :=
    Stack.pointTopology B S hS 𝒴.val
  obtain ⟨𝒵, i, hi, hrange⟩ := Stack.exists_isClosedImmersion_range_pointsMap_eq 𝒳 T hT
  have hcomp : IsFiniteType B S hS (i ≫ f) :=
    isFiniteType_comp B S hS i f (isProper_of_isClosedImmersion B S hS i hi).2.1 hf
  have hcomp_pts : ∀ z, Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom
      (Stack.pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z) =
      Stack.pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒴.val.property (i ≫ f).hom.hom z :=
    fun z => Stack.pointsMap_comp B S hS _ 𝒵.val.property 𝒳.val.property 𝒴.val.property
      i.hom.hom f.hom.hom z
  have himg : Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom '' T =
      Set.range (Stack.pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒴.val.property
        (i ≫ f).hom.hom) := by
    rw [← hrange, ← Set.range_comp]
    exact congrArg Set.range (funext hcomp_pts)
  have hclosed : @_root_.IsClosed _ (Stack.pointTopology B S hS 𝒴.val)
      (Set.range (Stack.pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒴.val.property
        (i ≫ f).hom.hom)) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨q, hqdvr, hz, hqy⟩ :=
      Stack.exists_discreteValuationRing_of_mem_closure_range_pointsMap B S hS (i ≫ f)
        hcomp h𝒴 y hy
    obtain ⟨e, ⟨d⟩⟩ := hlift (Stack.ValuativeSquare.compRight B S hS q) hqdvr
    obtain ⟨pR, z, hpR, hiz, -⟩ := Stack.exists_point_of_valuativeSquare B S hS i
      (Stack.valuativeCriterionExistence_of_isClosedImmersion B S hS i hi)
      (Stack.ValuativeSquare.compUpper B S hS q e d)
    have hloc := e.isLocalHom
    have hpReq : Stack.pointsMap B S hS _ _ (Stack.schemeFibredCategory B S hS
          (Stack.ValuativeSquare.specialObject B S hS q)).property e.a.hom pR =
        Stack.pointClass B S hS _ _ (Stack.closedPointFieldValuedPoint B S hS
          (Stack.ValuativeSquare.specialObject B S hS q) (IsLocalRing.closedPoint q.R) hz) := by
      apply Stack.schemePoint_injective B S hS (Stack.ValuativeSquare.specialObject B S hS q)
      rw [Stack.schemePoint_naturality]
      erw [hpR]
      rw [Stack.schemeMapOfFunctor_eq_of_toFunctor_eq B S hS e.a.hom e.specialOver e.a_canonical]
      change (B.inclusion).map e.specialOver.left _ = _
      rw [e.specialOver_left]
      exact AlgebraicGeometry.Spec_closedPoint.trans
        (Stack.schemePoint_closedPointFieldValuedPoint B S hS
          (Stack.ValuativeSquare.specialObject B S hS q)
          (IsLocalRing.closedPoint q.R) hz).symm
    refine ⟨z, (hcomp_pts z).symm.trans ?_⟩
    refine Eq.trans (congrArg (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property
      𝒴.val.property f.hom.hom) hiz) ?_
    refine Eq.trans (Stack.pointsMap_comp B S hS _ _ 𝒳.val.property 𝒴.val.property
      (Stack.ValuativeSquare.compUpper B S hS q e d).y.hom f.hom.hom pR) ?_
    refine Eq.trans (congrFun (Stack.pointsMap_eq_of_basedNatTrans B S hS _ _
      𝒴.val.property d.β.hom).symm pR) ?_
    refine Eq.trans (Stack.pointsMap_comp B S hS _ _
      (Stack.schemeFibredCategory B S hS
        (Stack.ValuativeSquare.specialObject B S hS q)).property
      𝒴.val.property e.a.hom q.y.hom pR).symm ?_
    exact Eq.trans (congrArg (Stack.pointsMap B S hS _ _ 𝒴.val.property q.y.hom) hpReq) hqy
  rw [himg]
  exact hclosed

/-- **Stacks 0H2A, item (2), from the hypothesis of Stacks 0H2C.** Let `f : 𝒳 ⟶ 𝒴` be a
finite-type 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian which satisfies
the discrete existence part of the valuative criterion. Then for every object `Z` of the site
whose scheme is affine and every 1-morphism `Stack.schemeStack Z ⟶ 𝒴` locally of finite
presentation, the map `|𝒳 ×_𝒴 Z| → |Z|` is closed.

The base change is again of finite type (**Stacks 06Q7**), its target is again locally
Noetherian (**Stacks 06R6**), and it again satisfies the hypothesis by
`AlgebraicGeometry.Stack.discreteExistence_baseChange`. Affineness of `Z` is not used. -/
@[stacks 0H2C "clause (2) of Tag 0H2A for `f`"]
theorem isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence
    (f : 𝒳 ⟶ 𝒴) (hf : IsFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hlift : ValuativeCriterion.DiscreteExistence B S hS f) :
    ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴),
        IsLocallyOfFinitePresentation B S hS g →
          IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst := by
  intro Z _ g hg
  refine isClosed_of_discreteExistence B S hS _
    (isFiniteType_baseChange B S hS f g _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hf)
    (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS g
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hg) h𝒴)
    (Stack.discreteExistence_baseChange B S hS f g _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hlift)

/-- **Stacks 0H2C.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴`
locally Noetherian and `f` of finite type. If every valuative square for `f` whose valuation ring
is a discrete valuation ring admits a dotted arrow after an extension of the fraction field and
passage to a dominating valuation ring, then `f` is universally closed.

Clause (2) of **Stacks 0H2A** holds for `f` by
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence`, and `f` is of
finite type, hence quasi-compact, so (2) implies (1) of **Stacks 0H2A**. -/
@[stacks 0H2C "the lemma"]
theorem universallyClosed_of_discreteExistence
    (f : 𝒳 ⟶ 𝒴) (hf : IsFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hlift : ValuativeCriterion.DiscreteExistence B S hS f) :
    UniversallyClosed B S hS f :=
  universallyClosed_of_isQuasiCompactMorphism_of_isClosed_affine_lfp B S hS f hf.2
    (isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_discreteExistence
      B S hS f hf h𝒴 hlift)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
