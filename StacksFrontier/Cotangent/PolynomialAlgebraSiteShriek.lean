module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAnEvaluation
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek on the site of a polynomial algebra

Let `A → B` be a ring map and let `C_{B/A}` be the site of polynomial `A`-algebras augmented to
`B`, with its projection `π` to the ringed point, as in
`StacksFrontier/Cotangent/PolynomialAlgebraSite.lean`. If `B` is *itself* a polynomial algebra over
`A`, then the identity map `B → B` is an object of `C_{B/A}`, and it is terminal there: any
augmentation `α : P → B` admits exactly one map to it, namely `α` itself. So the index category
`(C_{B/A})ᵒᵖ` of a presheaf has a terminal object, and the lower shriek of Stacks 08PF, which is
the colimit over that index category, is evaluation at `B → B`. Being an evaluation it is exact,
and this is Stacks 08QG.

## Main definitions

* `CommAlgCat.polynomialIdentityAugmentation`: the identity augmentation `B → B`.
* `CommAlgCat.polynomialIdentityObj`: the same, as an object of `(C_{B/A})ᵒᵖ`.

## Main results

* `CommAlgCat.polynomialIdentityAugmentation_isTerminal`: the identity augmentation is terminal.
* `CommAlgCat.polynomialProjection_toToposHom_inverseImage`: the functor whose left adjoint is
  taken below really is the inverse image of the `π` of Stacks 08PR.
* `CommAlgCat.polynomialAbelianLowerShriekEvaluationIso`: **Stacks 08QG**, `π_!` is evaluation at
  `B → B`.
* `CommAlgCat.polynomialAbelianLowerShriek_pointSectionsIso`: **Stacks 08QG**, the formula
  `π_!ℱ = ℱ(B → B)`, naturally in `ℱ`.
* `CommAlgCat.polynomialAbelianLowerShriek_preservesFiniteLimits` and
  `CommAlgCat.polynomialAbelianLowerShriek_preservesColimitsOfShape`: **Stacks 08QG**, `π_!` is
  exact.

## Implementation notes

The coefficient universe of the abelian sheaves is `max (u + 1) m` for a free `m`, the smallest
universe in which the site `C_{B/A}` — whose objects live in `Type (u + 1)` — has colimits of
abelian groups. That is what makes restriction along the point functor a right adjoint
unconditionally, so that `π_!` can be named before anything is known about `B`; the hypothesis
that `B` is a polynomial algebra enters only in the three statements of Stacks 08QG, exactly as
in the source.

The content is the terminal object: everything else is the general statement
`Stacks.ChaoticSite.lowerShriek_pointSections_evaluationIso` for a chaotic site whose index
category has a terminal object, specialized here. In particular exactness is not proved again —
`π_!` preserves finite limits because it is an evaluation, and all colimits because it is a left
adjoint.

The topology is the one `C_{B/A}` inherits from the ringed point, `CommAlgCat.polynomialTopology`,
and not `GrothendieckTopology.trivial`; the two are equal (`CommAlgCat.polynomialTopology_eq_bot`)
but not syntactically, and it is the inherited spelling that the morphism of ringed topoi `π` of
Stacks 08PR is formed over. The general statements are parametrized by the topology for this
reason.

## References

* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CommAlgCat

universe m u

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The identity augmentation -/

/-- The identity augmentation `B → B`, an object of the site `C_{B/A}` when `B` is itself a
polynomial algebra over `A`. -/
def polynomialIdentityAugmentation (hB : IsPolynomialAlgebra A B) :
    PolynomialAugmentation A B :=
  ⟨Over.mk (𝟙 B), hB⟩

/-- The identity augmentation is terminal among polynomial `A`-algebras augmented to `B`: an
augmentation `α : P → B` has exactly one map to it over `B`, namely `α`. -/
def polynomialIdentityAugmentation_isTerminal (hB : IsPolynomialAlgebra A B) :
    IsTerminal (polynomialIdentityAugmentation A B hB) :=
  IsTerminal.ofUniqueHom
    (fun X => ObjectProperty.homMk (Over.mkIdTerminal.from X.obj))
    (fun _ f => ObjectProperty.hom_ext _ (Over.mkIdTerminal.hom_ext f.hom _))

/-- The identity augmentation, read as an object of `(C_{B/A})ᵒᵖ`, the index category of a
presheaf on the site `C_{B/A}`. -/
abbrev polynomialIdentityObj (hB : IsPolynomialAlgebra A B) : (polynomialSite A B)ᵒᵖ :=
  op (op (polynomialIdentityAugmentation A B hB))

/-- The identity augmentation is a terminal object of the index category of presheaves on
`C_{B/A}`: the site is the opposite of the category of augmentations, and presheaves on it are
indexed by the opposite of that again. -/
def polynomialIdentityObj_isTerminal (hB : IsPolynomialAlgebra A B) :
    IsTerminal (polynomialIdentityObj A B hB) :=
  (polynomialIdentityAugmentation_isTerminal A B hB).op.op

/-! ### Lower shriek -/

/-- `π^{-1}` on abelian sheaves: restriction along the unique functor `C_{B/A} ⥤ *`. -/
abbrev polynomialAbelianInverseImage :
    Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{max (u + 1) m} ⥤
      Sheaf (polynomialTopology A B) AddCommGrpCat.{max (u + 1) m} :=
  (Functor.star (polynomialSite A B)).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) m} (polynomialTopology A B)
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))

/-- The geometric inverse image of the morphism of ringed topoi `π` of Stacks 08PR is
restriction along the point functor of `C_{B/A}`. So `CommAlgCat.polynomialAbelianInverseImage`
is that inverse image read on abelian sheaves, and the lower shriek below is the `π_!` of the
source rather than of some other morphism. -/
theorem polynomialProjection_toToposHom_inverseImage :
    (polynomialProjection A B).toToposHom.inverseImage =
      (Functor.star (polynomialSite A B)).sheafPushforwardContinuous (Type (u + 1))
        (polynomialTopology A B) (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) :=
  (polynomialRingedPoint A B).fibredSituation.inducedProjection.inverseImage_eq

/-- `π_!` on abelian sheaves, the left adjoint of `π^{-1}`. It exists for any ring map `A → B`,
the site `C_{B/A}` being small enough for abelian groups in `Type (max (u + 1) m)` to have the
colimits that build it. -/
abbrev polynomialAbelianLowerShriek :
    Sheaf (polynomialTopology A B) AddCommGrpCat.{max (u + 1) m} ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{max (u + 1) m} :=
  (Functor.star (polynomialSite A B)).sheafPullback AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B) (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))

/-- **Stacks 08QG.** For `B` a polynomial algebra over `A`, evaluation at the identity
augmentation `B → B` is left adjoint to `π^{-1}`: it *is* a lower shriek. -/
@[stacks 08QG "evaluation at B → B is a lower shriek"]
def polynomialEvaluationLowerShriekAdjunction (hB : IsPolynomialAlgebra A B) :
    Stacks.ChaoticSite.evaluationLowerShriek AddCommGrpCat.{max (u + 1) m}
        (polynomialIdentityObj A B hB) (polynomialTopology A B) ⊣
      polynomialAbelianInverseImage.{m} A B :=
  Stacks.ChaoticSite.evaluationLowerShriekAdjunction AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B) (polynomialIdentityObj_isTerminal A B hB)

/-- **Stacks 08QG.** For `B` a polynomial algebra over `A`, the lower shriek `π_!` of Stacks 08PR
is canonically evaluation at the identity augmentation `B → B`. -/
@[stacks 08QG "π_! is evaluation at B → B"]
def polynomialAbelianLowerShriekEvaluationIso (hB : IsPolynomialAlgebra A B) :
    polynomialAbelianLowerShriek.{m} A B ≅
      Stacks.ChaoticSite.evaluationLowerShriek AddCommGrpCat.{max (u + 1) m}
        (polynomialIdentityObj A B hB) (polynomialTopology A B) :=
  Stacks.ChaoticSite.lowerShriekEvaluationIso AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B) (polynomialIdentityObj_isTerminal A B hB)

/-- **Stacks 08QG.** `π_!ℱ = ℱ(B → B)`: the sections of `π_!ℱ` at the point are the sections of
`ℱ` over the identity augmentation, naturally in `ℱ`. -/
@[stacks 08QG "π_!F = F(B → B)"]
def polynomialAbelianLowerShriek_pointSectionsIso (hB : IsPolynomialAlgebra A B) :
    polynomialAbelianLowerShriek.{m} A B ⋙
        Stacks.ChaoticSite.pointSections AddCommGrpCat.{max (u + 1) m} ≅
      sheafToPresheaf (polynomialTopology A B) AddCommGrpCat.{max (u + 1) m} ⋙
        (evaluation (polynomialSite A B)ᵒᵖ AddCommGrpCat.{max (u + 1) m}).obj
          (polynomialIdentityObj A B hB) :=
  Stacks.ChaoticSite.lowerShriek_pointSections_evaluationIso AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B) (polynomialIdentityObj_isTerminal A B hB)

/-- **Stacks 08QG.** For `B` a polynomial algebra over `A`, `π_!` preserves finite limits. With
`CommAlgCat.polynomialAbelianLowerShriek_preservesColimitsOfShape` this is the exactness of `π_!`
asserted by the source. -/
@[stacks 08QG "π_! is exact: finite limits"]
theorem polynomialAbelianLowerShriek_preservesFiniteLimits (hB : IsPolynomialAlgebra A B) :
    PreservesFiniteLimits (polynomialAbelianLowerShriek.{m} A B) :=
  Stacks.ChaoticSite.lowerShriek_preservesFiniteLimits AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B) (polynomialIdentityObj_isTerminal A B hB)

/-- **Stacks 08QG.** `π_!` preserves all colimits, being a left adjoint; no hypothesis on `B` is
needed for this half of exactness. -/
@[stacks 08QG "π_! is exact: colimits"]
instance polynomialAbelianLowerShriek_preservesColimitsOfShape {K : Type*} [Category* K] :
    PreservesColimitsOfShape K (polynomialAbelianLowerShriek.{m} A B) :=
  Stacks.ChaoticSite.lowerShriek_preservesColimitsOfShape AddCommGrpCat.{max (u + 1) m}
    (polynomialTopology A B)

end CommAlgCat

end
