module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageGradedPiece

/-!
# One step of the adic tower as a square-zero extension with its kernel named

`Stacks.Thickenings.firstOrderThickening_squareZeroExtension_kernel` turns a first-order
thickening `i : X ⟶ Y` over a base into a square-zero extension of `𝒪_X` realized by `Y`, and
names its kernel only up to the identification `i_* E.I ≅ ker(𝒪_Y ⟶ i_*𝒪_X)`.  For the step
`Uₙ ⊆ Uₙ₊₁` of the adic tower of a family `p : U ⟶ Spec A` that is not yet usable: the
hypotheses the step of [Stacks, Tag 05YV] has to be fed —
`Stacks.Thickenings.SquareZeroExtension.exists_realization_pushforward_of_isZero_rightDerived`
asks for the vanishing of `R¹` on `E.I` and the quasi-coherence of its direct image — are
statements about `E.I`, while everything the filtration argument knows is a statement about the
**graded piece** `Iⁿ⁺¹(𝒪_U/Iⁿ⁺²𝒪_U)`, which lives on `U`.

This file closes that last gap.  It applies
`Stacks.BaseAdicFiltration.pushforwardKernelImmersionStructureMapIsoGradedPiece` to the kernel
the previous step leaves anonymous, and so produces the extension of the stage with its kernel
identified **on `U`**, as the graded piece:

```
(ιₙ)_* E.I  ≅  Iⁿ⁺¹(𝒪_U/Iⁿ⁺²𝒪_U).
```

Here `ιₙ : Uₙ ⟶ U` is the immersion of the stage, so the identification is of sheaves on `U`,
where the graded pieces are named and where their direct sum decomposition
(`Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece_unit`) and the vanishing of `R¹` on
them (`Stacks.BaseAdicFiltration.isZero_rightDerived_one_gradedPiece_unit`) are available.

## Main results

* `Stacks.Thickenings.firstOrderThickening_squareZeroExtension_kernel_of_eq` —
  `Stacks.Thickenings.firstOrderThickening_squareZeroExtension_kernel` with the structure
  morphism of the thickened subscheme presented by a factorization rather than as a composite.
* `Stacks.BaseAdicFiltration.adicStageSucc_comp_adicStageToBase` — the step of the tower lies
  over the base.
* `Stacks.BaseAdicFiltration.exists_squareZeroExtension_adicStage_gradedPiece` — **the step of
  the adic tower as a square-zero extension of the structure sheaf of the stage over `Spec A`,
  realized by the next stage, with its kernel identified on `U` as the graded piece.**

## Implementation notes

The factorized form of [Stacks, Tag 05YV] is needed because
`Stacks.Thickenings.SquareZeroExtension` is indexed by the structure morphism of the subscheme,
and the structure morphism of the adic stage,
`Stacks.BaseAdicFiltration.adicStageToBase`, is *equal* to the composite
`Uₙ ⟶ Uₙ₊₁ ⟶ Spec A` but not syntactically that composite — the equality is
`Stacks.BaseAdicFiltration.adicStageSucc_comp_adicStageι` with `p` appended, which is a theorem
about ideal sheaves and not a reduction.  Substituting the factorization in the statement, where
the third morphism is still a variable, discharges the transport once and for all, and in
particular avoids an `eqToHom` on the extension itself, whose `I` field a later consumer would
have to push the transport through.

The identification of the direct images is `SheafOfModules.pushforwardComp`, whose components
are identities on sections, composed with an `eqToIso` on the object for the factorization;
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` would also do, but it inserts a restriction
map along an `eqToHom` of opens where the `eqToIso` inserts nothing.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- **Every first-order thickening over a base, with the base morphism given by a
factorization.** This is
`Stacks.Thickenings.firstOrderThickening_squareZeroExtension_kernel` for a structure morphism
`k : X ⟶ S` presented together with a factorization `i ≫ g = k` rather than as the composite
itself; the extension is indexed by `k`, so a consumer whose `k` is only *equal* to the
composite needs this form. -/
public theorem firstOrderThickening_squareZeroExtension_kernel_of_eq {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (g : Y ⟶ S) {k : X ⟶ S} (hk : i ≫ g = k)
    (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    ∃ E : SquareZeroExtension k,
      Nonempty ((Scheme.Modules.pushforward i).obj E.I ≅
        kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ∧
      ∃ r : Realization E, r.ambient = Y ∧ HEq r.immersion i ∧ HEq r.toBase g := by
  subst hk
  exact firstOrderThickening_squareZeroExtension_kernel i g hi

end Stacks.Thickenings

namespace Stacks.BaseAdicFiltration

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ)

/-- **The step of the adic tower lies over the base**: the inclusion of the stage `n` into the
stage `n + 1`, followed by the structure morphism of the stage `n + 1`, is the structure
morphism of the stage `n`. -/
theorem adicStageSucc_comp_adicStageToBase :
    adicStageSucc p I n ≫ adicStageToBase p I (n + 1) = adicStageToBase p I n := by
  rw [adicStageToBase, adicStageToBase, ← Category.assoc, adicStageSucc_comp_adicStageι]

/-- The direct image to `U` of a module on the stage `n`, computed through the stage `n + 1`:
pushing forward along the step and then along the immersion of the stage `n + 1` is pushing
forward along the immersion of the stage `n`. -/
def pushforwardAdicStageSuccIso (M : (adicStage p I n).Modules) :
    (Scheme.Modules.pushforward (adicStageι p I (n + 1))).obj
        ((Scheme.Modules.pushforward (adicStageSucc p I n)).obj M) ≅
      (Scheme.Modules.pushforward (adicStageι p I n)).obj M :=
  (Scheme.Modules.pushforwardComp (adicStageSucc p I n) (adicStageι p I (n + 1))).app M ≪≫
    eqToIso (congrArg (fun φ : adicStage p I n ⟶ U =>
      (Scheme.Modules.pushforward φ).obj M) (adicStageSucc_comp_adicStageι p I n))

/-- **One step of the adic tower as a square-zero extension with its kernel named as the graded
piece.** For a family `p : U ⟶ Spec A` and an ideal `I` of `A`, the stage `n` of the `I`-adic
tower of closed subschemes of `U` carries a square-zero extension of its structure sheaf over
`Spec A`, realized by the stage `n + 1`, whose kernel pushed forward to `U` along the immersion
of the stage is the graded piece `Iⁿ⁺¹(𝒪_U/Iⁿ⁺²𝒪_U)`.

The two hypotheses that
`Stacks.Thickenings.SquareZeroExtension.exists_realization_pushforward_of_isZero_rightDerived`
asks about the kernel of the extension are, through this identification, hypotheses about the
graded piece — which is where the filtration argument of [Stacks, Tag 0E3X] has them. -/
theorem exists_squareZeroExtension_adicStage_gradedPiece :
    ∃ E : Stacks.Thickenings.SquareZeroExtension (adicStageToBase p I n),
      Nonempty ((Scheme.Modules.pushforward (adicStageι p I n)).obj E.I ≅
        (gradedPiece p I (n + 1) (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules) ∧
      ∃ r : Stacks.Thickenings.Realization E,
        r.ambient = adicStage p I (n + 1) ∧
          HEq r.immersion (adicStageSucc p I n) ∧
            HEq r.toBase (adicStageToBase p I (n + 1)) := by
  obtain ⟨E, ⟨e⟩, r, hamb, him, htb⟩ :=
    Stacks.Thickenings.firstOrderThickening_squareZeroExtension_kernel_of_eq
      (adicStageSucc p I n) (adicStageToBase p I (n + 1))
      (adicStageSucc_comp_adicStageToBase p I n)
      (adicStageSucc_isFirstOrderThickening p I n)
  refine ⟨E, ⟨?_⟩, r, hamb, him, htb⟩
  exact (pushforwardAdicStageSuccIso p I n E.I).symm ≪≫
    (Scheme.Modules.pushforward (adicStageι p I (n + 1))).mapIso e ≪≫
      pushforwardKernelImmersionStructureMapIsoGradedPiece p I n

end Stacks.BaseAdicFiltration

end
