module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily

/-!
# The intertwining identity as the `ψ`-equivariance of one comparison

Property (1) of [Stacks, Tag 01O7] on a chart is reduced, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily`, to the predicate
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.Intertwines`, one identity
per bidegree. That predicate is stated in the vocabulary the reduction produced it in: both of its
sides are untwistings, the left one of the degreewise family `degreewise` and the right one of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.rightLaw` applied to the
contraction `contractHom`, so the tensor powers `L^{⊗ (-n)}`, the contraction `powContract` and
the inverse law `laurentInvLaw` all occur in it, in both of its sides, and the isomorphism `α` and
the twisting `ψ` occur inside those composites rather than as factors of them.

This file rewrites that identity as what it mathematically is. Let

`G_n = comparison : f^*ℳ_{nd} ⟶ h^*ℳ̃ ⊗ L^{⊗ n}`

be the degree-`n` comparison — the arrow of [Stacks, Tag 01O6]'s summand followed by
`pullbackShiftedIso`, and the untwisting of the degree-`n` member of the family, by
`untwist_degreewise`. Then `Intertwines` in bidegree `(n, i)` is

`act ≫ G_{n+i} = (G_n ▷ f^*𝒜_{id}) ≫ ((h^*ℳ̃ ⊗ L^{⊗ n}) ◁ ψ.app i) ≫ laurentShiftAct`,

which is `intertwines_iff_compatible`: **the family `G` carries the action of `𝒜_{id}` on
`ℳ_{nd}` to multiplication by `ψ(𝒜_{id})` in the Laurent algebra.** In this form

* `α` occurs only inside `G`, and `G` is the composite the construction names;
* `ψ` occurs exactly once, as the single factor `ψ.app i`, and in no other place;
* everything else — `laurentShiftAct` — mentions neither `α`, nor `ψ`, nor `𝒜`, nor `ℳ`, and it is
  *computed*: by `laurentShiftAct_eq` it is the associator followed by the multiplication
  `L^{⊗ n} ⊗ L^{⊗ i} ⟶ L^{⊗ (n+i)}` of the Laurent algebra whiskered into `h^*ℳ̃`. No untwisting,
  no tensor power of `L^{⊗ (-•)}` and no contraction survive in the compatibility.

That is the shape in which the identity is a **compatibility of `α` with `ψ`** rather than a
property of either, which is what the module docstring of `ChartDegreewiseFamily` records and what
makes the unconditional form `∀ α ψ p, Intertwines …` not a theorem.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.comparison`: **the
  degree-`n` comparison `f^*ℳ_{nd} ⟶ h^*ℳ̃ ⊗ L^{⊗ n}`**, the shifted arrow followed by
  `shiftHom`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.laurentContract`: the
  `ψ`-free tail `L^{⊗ i} ⊗ L^{⊗ (-(n+i))} ⟶ L^{⊗ (-n)}` of
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.twistLaw`, which is all that is
  left of a balancing relation once `ψ.app i` is taken off it.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.laurentShiftAct`: **the
  multiplication `(h^*ℳ̃ ⊗ L^{⊗ n}) ⊗ L^{⊗ i} ⟶ h^*ℳ̃ ⊗ L^{⊗ (n+i)}`** of the Laurent algebra on
  the twists of `h^*ℳ̃`, as the untwisting of the contraction `powContract` against the
  degree-`(-(n+i))` piece. It involves no data of the chart beyond `L`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.Compatible`: **the
  compatibility of `α` with `ψ` in one bidegree**, the `ψ`-equivariance of `comparison` displayed
  above.

## Main results

* `Stacks.Monoidal.untwist_whiskerLeft_middle`: untwisting pulls a morphism of the middle factor
  out of a middle-whiskered composite, so the only occurrence of `ψ` in a balancing relation
  becomes a factor of the untwisted identity.
* `Stacks.Monoidal.contract_mul_assoc`: a contraction of a triple product against a pairing into
  the unit does not depend on the bracketing of the triple, in an arbitrary monoidal category.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.laurentContract_isoLeft`:
  **the associativity of the Laurent algebra on a triple of total degree zero**, read into the
  monoidal unit through the inverse laws of its two outer pairings.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.laurentShiftAct_eq`:
  **`laurentShiftAct` is the associator followed by the Laurent multiplication**, whiskered into
  `h^*ℳ̃` — the closed form, with the untwisting discharged.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.degreewise_eq_comparison`:
  the degreewise family is `comparison` whiskered by `L^{⊗ (-n)}` and contracted — so `comparison`
  carries the whole family.
* `ChartDegreewiseFamily.intertwines_iff_compatible`:
  **the intertwining identity is exactly the compatibility.**
* `ChartDegreewiseFamily.existsUnique_hom_of_compatible`:
  **the comparison `ℳ̃_T ⟶ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] exists and is unique on a
  chart for a compatible pair `(α, ψ)`.**

## Implementation notes

The monoidal bookkeeping is done twice over, once abstractly and once concretely, and the split is
forced. Inside an arbitrary monoidal category — `untwist_whiskerLeft_middle` and
`contract_mul_assoc` — `rw` works on the pentagon and on the naturality of the associator. At the
spelling the summands of [Stacks, Tag 01O6] carry it does **not**: a goal naming both
`Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.toRingedSpace.presheaf _` — the two
spellings of the structure sheaf of rings, equal by `rfl` — is not type-correct at the `implicit`
transparency level, so `rw` refuses to build a motive over it, and
`MonoidalCategory.whiskerLeft_comp` is reported as not matching a goal that visibly contains its
pattern. Every concrete step below is therefore `Eq.trans`/`congrArg` on explicit morphisms, where
the comparison happens at default transparency; `powContract_eq`, which crosses the two spellings
three times, is the clearest case.

## What is NOT here

No tag is carried.

This file belongs to the route to property (1) of [Stacks, Tag 01O7] through the
isomorphism `α : h^*𝒪(d) ≅ L`, and the remarks in this section concern that route only.
The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this file:
on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

`Compatible` is an equivalent
restatement of `Intertwines`, not a discharge of it: the equivalence below is an `Iff`, and nothing
here exhibits a pair for which either side holds. What the restatement buys is that the remaining
obligation is one equivariance between two named morphisms, with `ψ` appearing as a single factor
and no monoidal bookkeeping left in it; the account of why no unconditional form exists, and of
which pair a proof must be taken at, is in `ChartDegreewiseFamily`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow (baseHom)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections (laurentInvLaw rightLaw)
open Stacks.Monoidal (untwist)
open Stacks.RingedSpace (structureRingSheaf pullbackFunctor)

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Untwisting pulls a morphism of the middle factor out of a middle-whiskered composite.** If
the morphism `Y ⊗ K ⟶ W` that a composite out of `(X ⊗ Y) ⊗ K` acts by is itself a morphism
`f : Y ⟶ Y'` whiskered by `K`, followed by `τ : Y' ⊗ K ⟶ W`, then the untwisting of the composite
is `X ◁ f` followed by the untwisting of the composite built from `τ` alone.

This is the step that turns the `ψ`-side of a balancing relation of [Stacks, Tag 01O6] into an
identity in which `ψ` occurs as a single factor: `ψ` enters a relation only through
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.twistLaw`, which is exactly of
the shape `f ▷ K ≫ τ` with `f = ψ.app i`. -/
theorem untwist_whiskerLeft_middle {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y Y' W N : C} (f : Y ⟶ Y')
    (τ : Y' ⊗ K ⟶ W) (c : X ⊗ W ⟶ N) :
    untwist e (((α_ X Y K).hom ≫ X ◁ (f ▷ K ≫ τ)) ≫ c) =
      X ◁ f ≫ untwist e (((α_ X Y' K).hom ≫ X ◁ τ) ≫ c) := by
  have h : ((α_ X Y K).hom ≫ X ◁ (f ▷ K ≫ τ)) ≫ c =
      (X ◁ f) ▷ K ≫ (((α_ X Y' K).hom ≫ X ◁ τ) ≫ c) := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← Category.assoc ((α_ X Y K).hom), ← MonoidalCategory.associator_naturality_middle]
    simp only [Category.assoc]
  rw [h, untwist_whiskerRight_comp]

/-- `untwist_whiskerLeft_middle` with its three composites supplied as free morphisms and their
shapes as hypotheses, which is how it is applied: at the point of use each hypothesis is `rfl`,
while the statement names only one spelling of each object. This is the same packaging
`untwist_eq_of_whiskerLeft` uses, and for the same reason. -/
theorem untwist_eq_of_whiskerLeft_middle {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y Y' W N : C}
    (f : Y ⟶ Y') (τ : Y' ⊗ K ⟶ W) (c : X ⊗ W ⟶ N) {ν : Y ⊗ K ⟶ W}
    {w : (X ⊗ Y) ⊗ K ⟶ N} {g : (X ⊗ Y') ⊗ K ⟶ N} (hν : ν = f ▷ K ≫ τ)
    (hw : w = ((α_ X Y K).hom ≫ X ◁ ν) ≫ c)
    (hg : g = ((α_ X Y' K).hom ≫ X ◁ τ) ≫ c) :
    untwist e w = X ◁ f ≫ untwist e g := by
  subst hν hw hg
  exact untwist_whiskerLeft_middle e f τ c

/-- **A contraction of a triple product against a pairing into the unit does not depend on how the
triple is bracketed**, once the bracketing identity holds on the triple itself. Given
`lc : B ⊗ K ⟶ D`, `mA : A ⊗ D ⟶ 𝟙`, `mAB : A ⊗ B ⟶ E` and `mE : E ⊗ K ⟶ 𝟙` with

`(α_ A B K).hom ≫ A ◁ lc ≫ mA = mAB ▷ K ≫ mE`,

the same identity holds with an extra factor `N` carried along on the left and the pairing read
through the contraction `(α_ N _ _).hom ≫ N ◁ _ ≫ (ρ_ N).hom` of
`Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso`'s shape.

Everything here is formal: the pentagon moves the outer `K` across the associator and the
naturality of the associator in its middle and right variables carries `lc`, `mA`, `mAB` and `mE`
past it. This is the step that turns the associativity of the Laurent algebra into the closed form
of `laurentShiftAct`, exactly as `contract_whiskerRight` turns the snake identity into
`untwist_powContractIso`. -/
theorem contract_mul_assoc {A B K D E : C} (lc : B ⊗ K ⟶ D) (mA : A ⊗ D ⟶ 𝟙_ C)
    (mAB : A ⊗ B ⟶ E) (mE : E ⊗ K ⟶ 𝟙_ C)
    (hstar : (α_ A B K).hom ≫ A ◁ lc ≫ mA = mAB ▷ K ≫ mE) (N : C) :
    ((α_ (N ⊗ A) B K).hom ≫ (N ⊗ A) ◁ lc) ≫
        ((α_ N A D).hom ≫ N ◁ mA ≫ (ρ_ N).hom) =
      (((α_ N A B).hom ≫ N ◁ mAB) ▷ K) ≫
        ((α_ N E K).hom ≫ N ◁ mE ≫ (ρ_ N).hom) := by
  have h1 : ((α_ (N ⊗ A) B K).hom ≫ (N ⊗ A) ◁ lc) ≫
        ((α_ N A D).hom ≫ N ◁ mA ≫ (ρ_ N).hom) =
      ((α_ N A B).hom ▷ K) ≫ (α_ N (A ⊗ B) K).hom ≫
        N ◁ ((α_ A B K).hom ≫ A ◁ lc ≫ mA) ≫ (ρ_ N).hom := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [MonoidalCategory.associator_naturality_right_assoc,
      ← MonoidalCategory.pentagon_assoc]
  have h2 : ((α_ N A B).hom ▷ K) ≫ (α_ N (A ⊗ B) K).hom ≫
        N ◁ (mAB ▷ K ≫ mE) ≫ (ρ_ N).hom =
      (((α_ N A B).hom ≫ N ◁ mAB) ▷ K) ≫
        ((α_ N E K).hom ≫ N ◁ mE ≫ (ρ_ N).hom) := by
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    rw [← MonoidalCategory.associator_naturality_middle_assoc]
  rw [h1, hstar, h2]

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] SheafGradedModule.sectionModuleDecomposition

/-! ### The Laurent tail of a balancing relation -/

section Laurent

variable {Y : Scheme.{u}} (L : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]

/-- **The `ψ`-free tail of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.twistLaw`**, the multiplication
`L^{⊗ i} ⊗ L^{⊗ (-(n+i))} ⟶ L^{⊗ (-n)}` of the Laurent algebra followed by the reindexing of the
degree. The whole dependence of a balancing relation on `ψ` is the morphism `ψ.app i` that
`twistLaw` precomposes this with. -/
def laurentContract (p : ℤ × ℤ) :
    (laurent L).piece p.2 ⊗ (laurent L).piece (-(p.1 + p.2)) ⟶ (laurent L).piece (-p.1) :=
  (laurent L).mulSheaf p.2 (-(p.1 + p.2)) ≫
    eqToHom (congrArg (laurent L).piece (by ring : p.2 + -(p.1 + p.2) = -p.1))

/-! ### The associativity of the Laurent algebra in total degree zero -/

private theorem reindex_hom_eqToHom {n m : ℤ} (h : n = m) :
    (LaurentPullback.reindexIso L h).hom = eqToHom (congrArg (laurent L).piece h) := by
  cases h; rfl

private theorem whiskerLeft_eqToHom_mulSheaf (a : ℤ) {x y z : ℤ} (h : x = y) (h2 : a + y = z) :
    MonoidalCategoryStruct.whiskerLeft ((laurent L).piece a)
          (eqToHom (congrArg (laurent L).piece h)) ≫
        ((laurent L).mulSheaf a y ≫ eqToHom (congrArg (laurent L).piece h2)) =
      (laurent L).mulSheaf a x ≫
        eqToHom (congrArg (laurent L).piece (by rw [h]; exact h2 : a + x = z)) := by
  cases h
  simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id]
  exact Category.id_comp _

/-- **The two bracketings of the triple product `L^{⊗ n} ⊗ L^{⊗ i} ⊗ L^{⊗ (-(n+i))}` agree**, as
morphisms into the degree-`(n+i) + (-(n+i))` piece: multiplying the last two factors first, by
`laurentContract`, and then into the first, is multiplying the first two first and then into the
last. This is the associativity law of [Stacks, Tag 01CU] with the reindexings of the degree
composed, `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.mulIso_assoc` being that
law at the spelling in force. -/
private theorem laurentContract_mul_assoc (p : ℤ × ℤ) :
    (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
          ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1) (laurentContract L p) ≫
          (laurent L).mulSheaf p.1 (-p.1) ≫
            eqToHom (congrArg (laurent L).piece
              (by ring : p.1 + -p.1 = p.1 + p.2 + -(p.1 + p.2))) =
      MonoidalCategoryStruct.whiskerRight
          (C := SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
          ((laurent L).mulSheaf p.1 p.2) ((laurent L).piece (-(p.1 + p.2))) ≫
        (laurent L).mulSheaf (p.1 + p.2) (-(p.1 + p.2)) := by
  have hassoc := LaurentPullback.mulIso_assoc L p.1 p.2 (-(p.1 + p.2))
  simp only [← LaurentPullback.mulSheaf_laurent, reindex_hom_eqToHom] at hassoc
  refine Eq.trans ?_ hassoc.symm
  refine congrArg (fun z => (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
    ((laurent L).piece (-(p.1 + p.2)))).hom ≫ z) ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((laurent L).mulSheaf p.1 (-p.1) ≫
      eqToHom (congrArg (laurent L).piece
        (show p.1 + -p.1 = p.1 + p.2 + -(p.1 + p.2) by ring))))
    (MonoidalCategory.whiskerLeft_comp ((laurent L).piece p.1)
      ((laurent L).mulSheaf p.2 (-(p.1 + p.2)))
      (eqToHom (congrArg (laurent L).piece
        (show p.2 + -(p.1 + p.2) = -p.1 by ring))))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun z => MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1)
      ((laurent L).mulSheaf p.2 (-(p.1 + p.2))) ≫ z)
    (whiskerLeft_eqToHom_mulSheaf L p.1 (show p.2 + -(p.1 + p.2) = -p.1 by ring)
      (show p.1 + -p.1 = p.1 + p.2 + -(p.1 + p.2) by ring))

/-- `laurentContract_mul_assoc` with both sides carried on to the degree-zero piece, which is the
monoidal unit — the degree the two inverse laws of the Laurent algebra land in. -/
private theorem laurentContract_mul_assoc_zero (p : ℤ × ℤ) :
    (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
          ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1) (laurentContract L p) ≫
          ((laurent L).mulSheaf p.1 (-p.1) ≫
            eqToHom (congrArg (laurent L).piece (add_neg_cancel p.1))) =
      MonoidalCategoryStruct.whiskerRight
          (C := SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
          ((laurent L).mulSheaf p.1 p.2) ((laurent L).piece (-(p.1 + p.2))) ≫
        ((laurent L).mulSheaf (p.1 + p.2) (-(p.1 + p.2)) ≫
          eqToHom (congrArg (laurent L).piece (add_neg_cancel (p.1 + p.2)))) := by
  have h := congrArg (fun z => z ≫ eqToHom (congrArg (laurent L).piece
      (add_neg_cancel (p.1 + p.2)))) (laurentContract_mul_assoc L p)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ h
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun z => (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
    ((laurent L).piece (-(p.1 + p.2)))).hom ≫ z) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun z => MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1)
    (laurentContract L p) ≫ z) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun z => (laurent L).mulSheaf p.1 (-p.1) ≫ z) (eqToHom_trans _ _).symm

/-- **The inverse law `L^{⊗ n} ⊗ L^{⊗ (-n)} ≅ 𝒪_Y` of the Laurent algebra is its
multiplication**, followed by the reindexing of the degree to zero. -/
private theorem isoLeft_hom (n : ℤ) :
    (RelationSections.laurentHasInverse L n).isoLeft.hom =
      (laurent L).mulSheaf n (-n) ≫
        eqToHom (congrArg (laurent L).piece (add_neg_cancel n)) :=
  (congrArg (fun z => z ≫ (LaurentPullback.reindexIso L (add_neg_cancel n)).hom)
      (LaurentPullback.mulSheaf_laurent L n (-n)).symm).trans
    (congrArg (fun z => (laurent L).mulSheaf n (-n) ≫ z)
      (reindex_hom_eqToHom L (add_neg_cancel n)))

/-- **`laurentContract` paired against `L^{⊗ n}` is the multiplication into `L^{⊗ (n+i)}` paired
against `L^{⊗ (-(n+i))}`**: the associativity of the Laurent algebra, with both sides read into
the monoidal unit through the inverse laws. This is the hypothesis
`Stacks.Monoidal.contract_mul_assoc` consumes. -/
theorem laurentContract_isoLeft (p : ℤ × ℤ) :
    (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
          ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1) (laurentContract L p) ≫
          (RelationSections.laurentHasInverse L p.1).isoLeft.hom =
      MonoidalCategoryStruct.whiskerRight
          (C := SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
          ((laurent L).mulSheaf p.1 p.2) ((laurent L).piece (-(p.1 + p.2))) ≫
        (RelationSections.laurentHasInverse L (p.1 + p.2)).isoLeft.hom :=
  (congrArg (fun z => (α_ ((laurent L).piece p.1) ((laurent L).piece p.2)
          ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        MonoidalCategoryStruct.whiskerLeft ((laurent L).piece p.1) (laurentContract L p) ≫ z)
      (isoLeft_hom L p.1)).trans
    ((laurentContract_mul_assoc_zero L p).trans
      (congrArg (fun z => MonoidalCategoryStruct.whiskerRight
            (C := SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
            ((laurent L).mulSheaf p.1 p.2) ((laurent L).piece (-(p.1 + p.2))) ≫ z)
        (isoLeft_hom L (p.1 + p.2)).symm))

end Laurent

variable {S : Scheme.{u}} [IsAffine S] {A : SheafGradedAlgebra S} (𝔐 : SheafGradedModule A)
  (d : ℕ) {Y : Scheme.{u}}
  (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme)
  {L : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)}
  [Stacks.Ample.IsInvertibleModule Y L]
  [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]

/-- **The multiplication `(h^*ℳ̃ ⊗ L^{⊗ n}) ⊗ L^{⊗ i} ⟶ h^*ℳ̃ ⊗ L^{⊗ (n+i)}`** of the Laurent
algebra of `L` on the twists of `h^*ℳ̃`: the degree-`i` factor multiplied into the degree-`n` one,
written as the untwisting along `laurentInvLaw` of the contraction `powContract` preceded by the
Laurent multiplication `laurentContract`.

It is the whole of the `ψ`-side of a balancing relation of [Stacks, Tag 01O6] once the module
factor and `ψ.app i` have been split off, by `untwist_rightLaw_contractHom`, and it mentions
neither the isomorphism `α`, nor `ψ`, nor `𝒜`, nor any homogeneous piece of `ℳ`. Its closed form
is not computed; see the module docstring. -/
def laurentShiftAct (p : ℤ × ℤ) :
    (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) ⊗ (laurent L).piece p.2 ⟶
      pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece (p.1 + p.2) :=
  untwist (laurentInvLaw L (p.1 + p.2))
    (((α_ (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) ((laurent L).piece p.2)
            ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) (laurentContract L p)) ≫
      powContract 𝔐 d φ p.1)

omit [IsAffine S] in
/-- **The contraction `powContract` written out**: the associator, the inverse law of the Laurent
algebra whiskered into `h^*ℳ̃`, and the right unitor. This is
`Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso` at the strict monoidal structure of
[Stacks, Tag 01CA], where its three factors are the associator, the tensor product of an
isomorphism with the identity and the right unitor on the nose. -/
theorem powContract_eq (n : ℤ) :
    powContract 𝔐 d φ n =
      (α_ (pullbackAssociated 𝔐 d φ) ((laurent L).piece n) ((laurent L).piece (-n))).hom ≫
        MonoidalCategoryStruct.whiskerLeft (pullbackAssociated 𝔐 d φ)
            ((RelationSections.laurentHasInverse L n).isoLeft.hom) ≫
          (ρ_ (pullbackAssociated 𝔐 d φ)).hom := by
  have h0 : powContract 𝔐 d φ n =
      (Stacks.SheafOfModules.tensorSheafAssociator Y.toRingedSpace.presheaf (isSheafStruct Y)
            (pullbackAssociated 𝔐 d φ) ((laurent L).piece n) ((laurent L).piece (-n))).hom ≫
          (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso Y.toRingedSpace.presheaf
              (isSheafStruct Y) (Iso.refl (pullbackAssociated 𝔐 d φ))
              (RelationSections.laurentHasInverse L n).isoLeft).hom ≫
            (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso Y.toRingedSpace.presheaf
              (isSheafStruct Y) (pullbackAssociated 𝔐 d φ)).hom :=
    rfl
  have h1 : (Stacks.SheafOfModules.tensorSheafAssociator Y.toRingedSpace.presheaf
        (isSheafStruct Y) (pullbackAssociated 𝔐 d φ) ((laurent L).piece n)
        ((laurent L).piece (-n))).hom =
      (α_ (pullbackAssociated 𝔐 d φ) ((laurent L).piece n) ((laurent L).piece (-n))).hom :=
    congrArg Iso.hom (Stacks.SheafOfModules.associator_eq_tensorSheafAssociator
      Y.toRingedSpace.presheaf (isSheafStruct Y) (pullbackAssociated 𝔐 d φ)
      ((laurent L).piece n) ((laurent L).piece (-n))).symm
  have h2 : (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso Y.toRingedSpace.presheaf
        (isSheafStruct Y) (Iso.refl (pullbackAssociated 𝔐 d φ))
        (RelationSections.laurentHasInverse L n).isoLeft).hom =
      MonoidalCategoryStruct.whiskerLeft (pullbackAssociated 𝔐 d φ)
        ((RelationSections.laurentHasInverse L n).isoLeft.hom) :=
    (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq Y.toRingedSpace.presheaf (isSheafStruct Y)
        (Iso.refl (pullbackAssociated 𝔐 d φ))
        (RelationSections.laurentHasInverse L n).isoLeft).trans
      (MonoidalCategory.id_tensorHom (pullbackAssociated 𝔐 d φ)
        (RelationSections.laurentHasInverse L n).isoLeft.hom)
  have h3 : (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso Y.toRingedSpace.presheaf
        (isSheafStruct Y) (pullbackAssociated 𝔐 d φ)).hom =
      (ρ_ (pullbackAssociated 𝔐 d φ)).hom :=
    congrArg Iso.hom (Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor
      Y.toRingedSpace.presheaf (isSheafStruct Y) (pullbackAssociated 𝔐 d φ)).symm
  exact h0.trans (congrArg₂ (· ≫ ·) h1 (congrArg₂ (· ≫ ·) h2 h3))

omit [IsAffine S] in
/-- **The Laurent multiplication in closed form**: `laurentShiftAct` is the associator followed by
the multiplication `L^{⊗ n} ⊗ L^{⊗ i} ⟶ L^{⊗ (n+i)}` of the Laurent algebra whiskered into
`h^*ℳ̃`. So the compatibility `Compatible` below says exactly that the degreewise comparison
carries the action of `𝒜_{id}` to multiplication by `ψ(𝒜_{id})`, with no untwisting left in it.

The untwisting along `laurentInvLaw` cancels the contraction `powContract` — that is
`untwist_powContract` — so the identity reduces to the associativity of the Laurent algebra on the
triple `L^{⊗ n} ⊗ L^{⊗ i} ⊗ L^{⊗ (-(n+i))}` of total degree zero, carried from `L^{⊗ n}` to
`h^*ℳ̃ ⊗ L^{⊗ n}` by `Stacks.Monoidal.contract_mul_assoc`. -/
theorem laurentShiftAct_eq (p : ℤ × ℤ) :
    laurentShiftAct 𝔐 d φ p =
      (α_ (pullbackAssociated 𝔐 d φ) ((laurent L).piece p.1) ((laurent L).piece p.2)).hom ≫
        MonoidalCategoryStruct.whiskerLeft (pullbackAssociated 𝔐 d φ)
          ((laurent L).mulSheaf p.1 p.2) :=
  Stacks.Monoidal.untwist_eq_of_whiskerRight (laurentInvLaw L (p.1 + p.2))
    (untwist_powContract 𝔐 d φ (p.1 + p.2))
    ((congrArg (fun z =>
            ((α_ (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) ((laurent L).piece p.2)
                  ((laurent L).piece (-(p.1 + p.2)))).hom ≫
                MonoidalCategoryStruct.whiskerLeft
                  (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) (laurentContract L p)) ≫ z)
          (powContract_eq 𝔐 d φ p.1)).trans
      ((Stacks.Monoidal.contract_mul_assoc (laurentContract L p)
            (RelationSections.laurentHasInverse L p.1).isoLeft.hom
            ((laurent L).mulSheaf p.1 p.2)
            (RelationSections.laurentHasInverse L (p.1 + p.2)).isoLeft.hom
            (laurentContract_isoLeft L p) (pullbackAssociated 𝔐 d φ)).trans
        (congrArg (fun z =>
            MonoidalCategoryStruct.whiskerRight
                ((α_ (pullbackAssociated 𝔐 d φ) ((laurent L).piece p.1)
                      ((laurent L).piece p.2)).hom ≫
                  MonoidalCategoryStruct.whiskerLeft (pullbackAssociated 𝔐 d φ)
                    ((laurent L).mulSheaf p.1 p.2))
                ((laurent L).piece (-(p.1 + p.2))) ≫ z)
          (powContract_eq 𝔐 d φ (p.1 + p.2)).symm)))

/-! ### The degreewise comparison -/

/-- **The degree-`n` comparison `f^*ℳ_{nd} ⟶ h^*ℳ̃ ⊗ L^{⊗ n}`** of property (1) of [Stacks, Tag
01O7] on a chart: the shifted arrow `f^*ℳ_{nd} ⟶ h^*(ℳ(dn)~)` followed by
`shiftHom`, the comparison `h^*(ℳ(dn)~) ≅ h^*ℳ̃ ⊗ L^{⊗ n}`.

It carries the whole degreewise family — `degreewise_eq_comparison` — and it is the untwisting of
the family's degree-`n` member, which is `untwist_degreewise`. Every tensor power of `L` that the
summands of [Stacks, Tag 01O6] carry has disappeared from its source. -/
def comparison (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    (pullbackFunctor (baseHom A (chartHom d φ)).toLRSHom.toShHom).obj
        ((situationModule 𝔐).piece (n * (d : ℤ))) ⟶
      pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece n :=
  shiftedArrow 𝔐 d φ n ≫ shiftHom 𝔐 d φ α n

/-- **The untwisting of the degreewise family is `comparison`.** This is `untwist_degreewise`
read through the definition of `comparison`. -/
theorem untwist_degreewise_eq_comparison
    (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L) (n : ℤ) :
    untwist (laurentInvLaw L n) (degreewise 𝔐 d φ α n) = comparison 𝔐 d φ α n :=
  untwist_degreewise 𝔐 d φ α n

/-- **The degreewise family is `comparison` whiskered by `L^{⊗ (-n)}` and contracted.** So the
family of property (1) of [Stacks, Tag 01O7] on a chart is determined by the single family of
comparisons `comparison`, with no tensor power of `L` in its source. -/
theorem degreewise_eq_comparison (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (n : ℤ) :
    degreewise 𝔐 d φ α n =
      MonoidalCategoryStruct.whiskerRight (comparison 𝔐 d φ α n) ((laurent L).piece (-n)) ≫
        powContract 𝔐 d φ n :=
  (Category.assoc
        (MonoidalCategoryStruct.whiskerRight (shiftedArrow 𝔐 d φ n) ((laurent L).piece (-n)))
        (MonoidalCategoryStruct.whiskerRight (shiftHom 𝔐 d φ α n) ((laurent L).piece (-n)))
        (powContract 𝔐 d φ n)).symm.trans
    (congrArg (· ≫ powContract 𝔐 d φ n)
      (MonoidalCategory.comp_whiskerRight (shiftedArrow 𝔐 d φ n) (shiftHom 𝔐 d φ α n)
        ((laurent L).piece (-n))).symm)

/-! ### The `ψ`-side, with `ψ` as a factor -/

/-- **The `ψ`-side of a balancing relation of [Stacks, Tag 01O6], untwisted, is `shiftHom`
whiskered by `f^*𝒜_{id}`, then `ψ.app i`, then the Laurent multiplication.** Both splittings are
formal: the module factor comes off by `untwist_eq_of_whiskerLeft`, which is how
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.untwist_relRightComp` is proved,
and `ψ.app i` comes off by `untwist_eq_of_whiskerLeft_middle`, `ψ` entering `twistLaw` precisely
as a morphism of the middle factor. -/
theorem untwist_rightLaw_contractHom
    (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ) :
    untwist (laurentInvLaw L (p.1 + p.2))
        (rightLaw L (baseHom A (chartHom d φ)) (d : ℤ) ψ p (contractHom 𝔐 d φ α p.1)) =
      MonoidalCategoryStruct.whiskerRight (shiftHom 𝔐 d φ α p.1)
          (AffineTensorGeneral.pullbackSheafMod (baseHom A (chartHom d φ))
            (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2)) ≫
        MonoidalCategoryStruct.whiskerLeft
            (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) (ψ.app p.2) ≫
          laurentShiftAct 𝔐 d φ p :=
  (Stacks.Monoidal.untwist_eq_of_whiskerLeft (laurentInvLaw L (p.1 + p.2))
      (RelationSections.twistLaw L (baseHom A (chartHom d φ)) (d : ℤ) ψ p)
      (shiftHom 𝔐 d φ α p.1) (powContract 𝔐 d φ p.1) rfl rfl rfl).trans
    (congrArg (MonoidalCategoryStruct.whiskerRight (shiftHom 𝔐 d φ α p.1) _ ≫ ·)
      (Stacks.Monoidal.untwist_eq_of_whiskerLeft_middle (laurentInvLaw L (p.1 + p.2))
        (ψ.app p.2) (laurentContract L p) (powContract 𝔐 d φ p.1) rfl rfl rfl))

/-! ### The compatibility -/

/-- **The compatibility of `α` with `ψ` in bidegree `(n, i)`**: the degreewise comparison
`comparison` carries the pulled-back action of `𝒜_{id}` on `ℳ_{nd}` to multiplication by
`ψ(𝒜_{id})` in the Laurent algebra of `L`.

This is the intertwining identity of property (1) of [Stacks, Tag 01O7] — `Intertwines` — with the
untwisting carried out on both sides: see `intertwines_iff_compatible`. In this form `α` occurs
only inside `comparison`, `ψ` occurs exactly once as the factor `ψ.app i`, and the remaining
factor `laurentShiftAct` depends on neither.

**It is a compatibility of the two data and not a property of either**, so there is no
unconditional form; the account is in the module docstring of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily`. -/
def Compatible (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ) :
    Prop :=
  act (baseHom A (chartHom d φ)) (situationModule 𝔐) (d : ℤ) p.1 p.2 ≫
      comparison 𝔐 d φ α (p.1 + p.2) =
    MonoidalCategoryStruct.whiskerRight (comparison 𝔐 d φ α p.1)
        (AffineTensorGeneral.pullbackSheafMod (baseHom A (chartHom d φ))
          (RelationSections.algebraPiece (situationAlgebra A) (d : ℤ) p.2)) ≫
      MonoidalCategoryStruct.whiskerLeft
          (pullbackAssociated 𝔐 d φ ⊗ (laurent L).piece p.1) (ψ.app p.2) ≫
        laurentShiftAct 𝔐 d φ p

/-- **The intertwining identity is exactly the compatibility of `α` with `ψ`.** The left-hand
sides agree by `untwist_degreewise`, the right-hand sides by `untwist_rightLaw_contractHom`
together with the splitting of `comparison`'s own whiskering. -/
theorem intertwines_iff_compatible
    (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L) (p : ℤ × ℤ) :
    Intertwines 𝔐 d φ α ψ p ↔ Compatible 𝔐 d φ α ψ p := by
  dsimp only [Intertwines, Compatible, comparison]
  rw [untwist_degreewise, untwist_rightLaw_contractHom, MonoidalCategory.comp_whiskerRight,
    Category.assoc]

/-- **The comparison `ℳ̃_T ⟶ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] exists and is unique on
a chart for a compatible pair `(α, ψ)`.** It is `existsUnique_hom_of_intertwines` with its
hypothesis supplied in the compatibility form.

This is **not** property (1): the compatibility is a hypothesis, and that the resulting morphism is
an **isomorphism** — which is local on the cover of `Y` by the nonvanishing opens of `ψ` — is not
asserted. -/
theorem existsUnique_hom_of_compatible
    (α : pullbackTwist (A.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ L)
    (ψ : Twisting (baseHom A (chartHom d φ)) (situationAlgebra A) (d : ℤ) L)
    (hc : ∀ p : ℤ × ℤ, Compatible 𝔐 d φ α ψ p) :
    ∃! g : Twisting.associatedSheaf (situationModule 𝔐) ψ ⟶ pullbackAssociated 𝔐 d φ,
      ∀ n : ℤ, Twisting.pureTensor (situationModule 𝔐) ψ n ≫ g = degreewise 𝔐 d φ α n :=
  existsUnique_hom_of_intertwines 𝔐 d φ α ψ fun p =>
    (intertwines_iff_compatible 𝔐 d φ α ψ p).2 (hc p)


end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily

end
