module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.BigFppfAbelianSheaves
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.BasePullbackEquivalence
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.ClassifyingStack
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.PartA
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Torsion

/-!
# Stacks 0AFB and 0AFC: the Hom-stack `Mor_S(X, [S/A])` is not algebraic

In the situation of Section 0AF8 (`Stacks.Examples.NonAlgebraicHomStack.Situation`), let
`𝒳 = Mor_S(X, [S/A])` be the Hom-stack from the total space `X` of the family `f : X ⟶ S` over
`S = Spec k⟦t⟧` to the classifying stack `[S/A]` of the constant abelian scheme `A = A₀ ×_k S`.
This file assembles the source's proof:

* `H¹(X, A)` is torsion (`Stacks.Examples.NonAlgebraicHomStack.isAddTorsion_H1_totalObj`, from
  Stacks 0AF9 and 0AFA), `X` being a regular integral Noetherian surface;
* the restrictions `H¹(X_{n+1}, A) ⟶ H¹(Xₙ, A)` are surjective, part (b)
  (`Stacks.Examples.NonAlgebraicHomStack.surjective_restrictSucc_pointsSheaf`), the special fibre
  being a curve;
* `H¹(X₀, A)` is not torsion, part (a)
  (`Stacks.Examples.NonAlgebraicHomStack.not_isAddTorsion_H1_specialFibre`);

so that `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective; by the computation of the fibre categories
of `𝒳` as groupoids of `A`-torsors
(`Stacks.Examples.NonAlgebraicHomStack.exists_not_restriction_homStack`, through the classifying
invariant of `[S/A]` with values in `H¹(-, A)`), the functor
`𝒳(S) ⟶ lim 𝒳(Sₙ)` is not essentially surjective (Stacks 0AFB), and by Stacks 07X8 `𝒳` is not
an algebraic stack (Stacks 0AFC).

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.Situation.not_surjective_toCompatibleSystems`:
  `H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.exists_not_restriction_homStackClassifyingStack`:
  **Stacks 0AFB**.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`:
  **Stacks 0AFC**.

## Implementation notes

The Hom-stack is `AlgebraicGeometry.Stack.homStack`, the pullback of the target along the base
change functor `T ↦ X ×_S T` of the big fppf site of `S`; its fibre over `T` is the fibre of the
target over `X ×_S T`, which by 2-Yoneda is the source's `Mor_T(X ×_S T, [S/A] ×_S T)`. The target
`[S/A]` is `AlgebraicGeometry.Stack.classifyingStackOfGroupScheme`, the quotient stack of the
trivial action of `A` on `S`. The proofs go through its small model
`Stacks.Examples.NonAlgebraicHomStack.Situation.classifyingStackModel`, which has the universes
of the 2-category of algebraic stacks, where Stacks 07X8 is proved: the class in `H¹` of the torsor
attached to an object is a classifying invariant of the small model, transported to `[S/A]` along
the equivalence over the site, and the Hom-stacks into `[S/A]` and into its small model are
equivalent over the site (`CategoryTheory.BasedCategory.basePullbackEquivalenceOver`), so that
non-algebraicity transports by Stacks 03YQ. The versions for the small model,
`Stacks.Examples.NonAlgebraicHomStack.Situation.exists_not_restriction_homStack` and
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStack`, are stated too.

The cohomology groups are computed with the abelian sheaves on the big fppf site of `S`, which
admit sheafification and have `Ext`-groups in the universe of the schemes
(`AlgebraicGeometry.BigFppfOver.hasSheafify_abelian`,
`AlgebraicGeometry.BigFppfOver.hasExt_abelian`); none of this appears in the statements of
Stacks 0AFB and 0AFC.

The thickenings are indexed as in `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack`: level `n`
lies over `Spec (k⟦t⟧/(tⁿ⁺¹))`, one off the source's `Sₙ = Spec (k[t]/(tⁿ))`; the limit is the
same.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0AFC](https://stacks.math.columbia.edu/tag/0AFC)
* [Stacks Project, Section 0AF8](https://stacks.math.columbia.edu/tag/0AF8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Deformation.Artin AlgebraicGeometry.Stack

universe w u

namespace Stacks.Examples.NonAlgebraicHomStack.Situation

variable {k : Type u} [Field k] (sit : Situation k)

/-- The thickening `Spec (k⟦t⟧ / (t)) ⟶ Spec k⟦t⟧` maps every point to the closed point. -/
theorem adicThickeningι_zero_apply (y : adicThickening (PowerSeries k) (uniformizer k) 0) :
    adicThickeningι (PowerSeries k) (uniformizer k) 0 y = closedPoint (PowerSeries k) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk (uniformizer k ^ (0 + 1))) y.asIdeal =
    maximalIdeal (PowerSeries k)
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := PowerSeries k ⧸ uniformizer k ^ (0 + 1)) y
  have : (Ideal.comap (Ideal.Quotient.mk (uniformizer k ^ (0 + 1))) y.asIdeal).IsPrime :=
    Ideal.comap_isPrime _ _
  refine le_antisymm (le_maximalIdeal this.ne_top) ?_
  rw [PowerSeries.maximalIdeal_eq_span_X]
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha)]
  exact y.asIdeal.zero_mem

/-- **The special fibre `X₀` is a curve**: it has dimension at most one, being homeomorphic to a
subspace of the fibre of `f` over the closed point of `S`, which has dimension one. -/
theorem topologicalKrullDim_specialFibre_le_one :
    topologicalKrullDim (thickening sit.f 0) ≤ 1 := by
  have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) 0) := by
    unfold adicThickeningι
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let s : base k := closedPoint (PowerSeries k)
  have hmem : ∀ x : thickening sit.f 0, thickeningToTotal sit.f 0 x ∈ sit.f ⁻¹' {s} := by
    intro x
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply, adicThickeningι_zero_apply]
  calc topologicalKrullDim (thickening sit.f 0)
      ≤ topologicalKrullDim (sit.f ⁻¹' {s}) :=
        ((thickeningToTotal sit.f 0).isClosedEmbedding.isInducing.codRestrict
          hmem).topologicalKrullDim_le
    _ = topologicalKrullDim (sit.f.fiber s) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (sit.f.fiberHomeo s).isHomeomorph).symm
    _ = 1 := sit.dim_fiber s

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k))

/-- **`H¹(X, A) ⟶ lim H¹(Xₙ, A)` is not surjective**, in the situation of Section 0AF8: the source's
reduction of Stacks 0AFB, with its three inputs `H¹(X, A)` torsion (Stacks 0AF9 and 0AFA),
`H¹(X_{n+1}, A) ⟶ H¹(Xₙ, A)` surjective (part (b)) and `H¹(X₀, A)` not torsion (part (a)) all
proved. -/
theorem not_surjective_toCompatibleSystems
    [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})] :
    ¬ Function.Surjective (toCompatibleSystems B hS sit.f (sit.contains_X hS)
      (sit.contains_thickening hS) (sit.pointsSheafA B hS (sit.contains_abelianScheme hS))) := by
  have := sit.isIntegral
  have := sit.isNoetherian
  have := sit.smooth_abelianScheme
  exact NonAlgebraicHomStack.not_surjective_toCompatibleSystems B hS sit.f (sit.contains_X hS)
    (sit.contains_thickening hS) _
    (isAddTorsion_H1_totalObj B hS sit.f (sit.contains_X hS) sit.isRegular
      sit.topologicalKrullDim_eq_two sit.abelianScheme (sit.contains_abelianScheme hS))
    (surjective_restrictSucc_pointsSheaf B hS sit.f (sit.contains_thickening hS) sit.abelianScheme
      (sit.contains_abelianScheme hS) sit.topologicalKrullDim_specialFibre_le_one)
    (not_isAddTorsion_H1_specialFibre sit B hS)

/-- The Hom-stack `Mor_S(X, 𝒵)` into the small model `𝒵` of `[S/A]`
(`Stacks.Examples.NonAlgebraicHomStack.Situation.classifyingStackModel`), which is equivalent over
the site to `Mor_S(X, [S/A])`. -/
abbrev homStackModel : BasedCategory.{u, u + 1} (BigFppfOver B (base k) hS) :=
  homStack (totalObj B hS sit.f (sit.contains_X hS))
    (sit.classifyingStackModel B hS (sit.contains_abelianScheme hS))

/-- **Stacks 0AFB for the small model of `[S/A]`.** In the situation of Section 0AF8, let
`𝒳 = Mor_S(X, 𝒵)` for the small model `𝒵` of `[S/A]`. The functor
`𝒳(S) ⟶ lim 𝒳(Sₙ)` is not essentially surjective: there is a formal object `ξ` of `𝒳` over the
complete local ring `k⟦t⟧`, with `ξₙ` lying over `Sₙ = Spec (k⟦t⟧/(tⁿ⁺¹))`, such that no object
`x` of `𝒳` admits morphisms `ξₙ ⟶ x` lying over the closed immersions `Sₙ ⟶ S`; in a category
fibred in groupoids such morphisms are exactly the identifications of `ξₙ` with the restrictions
`x|_{Sₙ}`, so `ξ` is not isomorphic to the image of an object of `𝒳(S)`. -/
theorem exists_not_restriction_homStack :
    ∃ ξ : FormalObject B (base k) hS (sit.homStackModel B hS).p,
      ξ.base = powerSeriesFormalBase k ∧
      (∀ n, (sit.homStackModel B hS).p.obj (ξ.level n) = truncationObj B hS n) ∧
      ∀ (x : (sit.homStackModel B hS).obj) (r : ∀ n, ξ.level n ⟶ x),
        ¬ ∀ n, (sit.homStackModel B hS).p.IsHomLift
          (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
            (powerSeriesFormalBase_contains B hS) n) (r n) := by
  let _hsh := BigFppfOver.hasSheafify_abelian B (base k) hS
  let _hext := BigFppfOver.hasExt_abelian B (base k) hS
  exact NonAlgebraicHomStack.exists_not_restriction_homStack B hS sit.f (sit.contains_X hS)
    (sit.contains_thickening hS) _ _
    (sit.isFiberedInGroupoids_classifyingStackModel B hS (sit.contains_abelianScheme hS))
    (sit.isClassifyingInvariant_classifyingStackModelClass B hS (sit.contains_abelianScheme hS))
    (sit.not_surjective_toCompatibleSystems B hS)

/-- **Stacks 0AFC for the small model of `[S/A]`.** In the situation of Section 0AF8, the Hom-stack
`Mor_S(X, 𝒵)` into the small model `𝒵` of `[S/A]` is not an algebraic stack: it has a formal
object which is not effective (the proof of Stacks 0AFB),
while every formal object of an algebraic stack is effective (Stacks 07X8). -/
theorem not_isAlgebraicStack_homStack :
    ¬ Stack.IsAlgebraicStack.{u, w} B (base k) hS (sit.homStackModel B hS) := by
  let _hsh := BigFppfOver.hasSheafify_abelian B (base k) hS
  let _hext := BigFppfOver.hasExt_abelian B (base k) hS
  exact NonAlgebraicHomStack.not_isAlgebraicStack_homStack B hS sit.f (sit.contains_X hS)
    (sit.contains_thickening hS) _ _
    (sit.isFiberedInGroupoids_classifyingStackModel B hS (sit.contains_abelianScheme hS))
    (sit.isClassifyingInvariant_classifyingStackModelClass B hS (sit.contains_abelianScheme hS))
    (sit.not_surjective_toCompatibleSystems B hS)

/-! ### The Hom-stack into the quotient stack `[S/A]` itself -/

/-- The Hom-stack `𝒳 = Mor_S(X, [S/A])` of Section 0AF8, with `[S/A]` the quotient stack
`AlgebraicGeometry.Stack.classifyingStackOfGroupScheme` of the trivial action of `A` on `S`. -/
abbrev homStackClassifyingStack : BasedCategory (BigFppfOver B (base k) hS) :=
  homStack (totalObj B hS sit.f (sit.contains_X hS))
    (Stack.classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme
      (sit.contains_abelianScheme hS))

/-- The quotient stack `[S/A]` is fibred in groupoids. -/
theorem isFiberedInGroupoids_classifyingStack :
    (Stack.classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme
      (sit.contains_abelianScheme hS)).p.IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (sit.classifyingStackModelEquivalenceOver B hS (sit.contains_abelianScheme hS)).symm
    (sit.isFiberedInGroupoids_classifyingStackModel B hS (sit.contains_abelianScheme hS))

/-- **Stacks 0AFB.** In the situation of Section 0AF8, let `𝒳 = Mor_S(X, [S/A])`, with `[S/A]` the
quotient stack of the trivial action of `A` on `S`. The functor `𝒳(S) ⟶ lim 𝒳(Sₙ)` is not
essentially surjective: there is a formal object `ξ` of `𝒳` over the complete local ring `k⟦t⟧`,
with `ξₙ` lying over `Sₙ = Spec (k⟦t⟧/(tⁿ⁺¹))`, such that no object `x` of `𝒳` admits morphisms
`ξₙ ⟶ x` lying over the closed immersions `Sₙ ⟶ S`; in a category fibred in groupoids such
morphisms are exactly the identifications of `ξₙ` with the restrictions `x|_{Sₙ}`.

The fibre categories of `𝒳` are classified by `H¹(X ×_S -, A)`: the class in `H¹` of the torsor
attached to an object of `[S/A]` (Stacks 04WM, 03AJ) is transported from the small model of
`[S/A]` along its equivalence over the site with `[S/A]`. -/
@[stacks 0AFB "for the Hom-stack Mor_S(X, [S/A]) of the situation of Section 0AF8: k \
  algebraically closed and not the algebraic closure of a finite field, S = Spec k⟦t⟧, X ⟶ S \
  projective and flat with geometrically connected curves as fibres, X regular, the special \
  fibre a nodal curve with smooth components whose dual graph has a loop of rational curves, \
  A = A₀ ×_k S for a non-zero abelian variety A₀, and [S/A] the quotient stack of the trivial \
  action of A on S. The torsion of H¹(X, A), part (a) and part (b) are proved from these data. \
  Not essentially surjective is stated as: some formal object over k⟦t⟧ admits no morphisms, \
  over the closed immersions Sₙ ⟶ S, to an object over S. The index of the thickenings is \
  shifted by one against the source: level n lies over Spec k⟦t⟧/(t^(n+1))"]
theorem exists_not_restriction_homStackClassifyingStack :
    ∃ ξ : FormalObject B (base k) hS (sit.homStackClassifyingStack B hS).p,
      ξ.base = powerSeriesFormalBase k ∧
      (∀ n, (sit.homStackClassifyingStack B hS).p.obj (ξ.level n) = truncationObj B hS n) ∧
      ∀ (x : (sit.homStackClassifyingStack B hS).obj) (r : ∀ n, ξ.level n ⟶ x),
        ¬ ∀ n, (sit.homStackClassifyingStack B hS).p.IsHomLift
          (restrictionToBase B (base k) hS (powerSeriesFormalBase k) hS
            (powerSeriesFormalBase_contains B hS) n) (r n) := by
  let _hsh := BigFppfOver.hasSheafify_abelian B (base k) hS
  let _hext := BigFppfOver.hasExt_abelian B (base k) hS
  let hA := sit.contains_abelianScheme hS
  let e := sit.classifyingStackModelEquivalenceOver B hS hA
  have := e.isEquivalence_inv_functor
  have hcl := (sit.isClassifyingInvariant_classifyingStackModelClass B hS hA).comp
    e.inv.functor e.inv.w
  obtain ⟨c, hc⟩ := exists_forall_toCompatibleSystems_ne B hS sit.f (sit.contains_X hS)
    (sit.contains_thickening hS) _ (sit.not_surjective_toCompatibleSystems B hS)
  exact exists_not_restriction_of_compatible
    (isFiberedInGroupoids_homStack _ _ (sit.isFiberedInGroupoids_classifyingStack B hS))
    (isClassifyingInvariant_homStackClass (sit.isFiberedInGroupoids_classifyingStack B hS) hcl)
    (powerSeriesFormalBase k) hS (powerSeriesFormalBase_contains B hS)
    (prodTruncationSystem B hS sit.f (sit.contains_X hS) (sit.contains_thickening hS) _ c)
    (prodTruncationSystem_succ B hS sit.f (sit.contains_X hS) (sit.contains_thickening hS) _ c)
    (exists_ne_prodTruncationSystem B hS sit.f (sit.contains_X hS) (sit.contains_thickening hS)
      _ c hc)

/-- **Stacks 0AFC.** In the situation of Section 0AF8, the Hom-stack `𝒳 = Mor_S(X, [S/A])`, with
`[S/A]` the quotient stack of the trivial action of `A` on `S`, is not an algebraic stack. It is
equivalent over the site to the Hom-stack into the small model of `[S/A]`
(`CategoryTheory.BasedCategory.basePullbackEquivalenceOver`), which is not algebraic by
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStack`, and algebraicity
is invariant under equivalence over the site (Stacks 03YQ). -/
@[stacks 0AFC "for the Hom-stack Mor_S(X, [S/A]) of the situation of Section 0AF8: k \
  algebraically closed and not the algebraic closure of a finite field, S = Spec k⟦t⟧, X ⟶ S \
  projective and flat with geometrically connected curves as fibres, X regular, the special \
  fibre a nodal curve with smooth components whose dual graph has a loop of rational curves, \
  A = A₀ ×_k S for a non-zero abelian variety A₀, and [S/A] the quotient stack of the trivial \
  action of A on S. Derived from the proof of 0AFB and from Stacks 07X8 as proved in this \
  library (Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks)"]
theorem not_isAlgebraicStack_homStackClassifyingStack :
    ¬ Stack.IsAlgebraicStack.{u, w} B (base k) hS (sit.homStackClassifyingStack B hS) :=
  fun h => sit.not_isAlgebraicStack_homStack B hS
    (Stack.isAlgebraicStack_of_equivalenceOver B (base k) hS
      (BasedCategory.basePullbackEquivalenceOver _
        (sit.classifyingStackModelEquivalenceOver B hS (sit.contains_abelianScheme hS)).symm) h)

end Stacks.Examples.NonAlgebraicHomStack.Situation

end
