module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSupplementaryBound

/-!
# Stacks 0EIF from Stacks 0BLX, under either form of condition (3)

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, `U = Spec(A) ∖ V(𝔞)` and `F` a coherent module
on `U`. `StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneRealization` and
`StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneClosure` carry out the source's
proof of Stacks 0EIF when condition (3) holds in the form (3)(a). This file runs the same proof
under the bundled conditions `Stacks.Algebraization.FormalSectionsHypotheses`, whose third clause
is the disjunction (3)(a) or (3)(b) of the source.

## Main results

* `exists_ideal_isIso_homology_zero_completionUnit_of_formalSectionsHypotheses`
  — the first half of the source's proof: under conditions (1), (2) and (3), for a proper `𝔞`,
  there is an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` making
  `Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)` an isomorphism.
* `isIso_comparisonMap_of_formalSectionsHypotheses_of_completedComplement`
  — the assembly: the comparison map is an isomorphism, granting
  `Stacks.Algebraization.CompletedComplementIsFormalSections` (Stacks 0BLX, 0A0K and 0D60 in the
  affine shape the source's last step consumes). That input is proved, and this declaration
  consumed, in `StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAlgebraizationTheorem`.

## Implementation notes

Stacks 0BK0 gives a finite module `M` and an isomorphism `F ≅ M̃|_U`, and the source then argues
about `M`. Condition (3)(a) is not transported across that isomorphism: the first half of the
proof takes an arbitrary coherent `F` together with an isomorphism `F ≅ M̃|_U` and consumes the
conditions on `F` itself. Only the conclusions cross the isomorphism: the associated-point
identification by `Stacks.Divisors.associatedPoints_congr`, and the comparison map by
`Stacks.Algebraization.isIso_comparisonMap_of_iso`. The degenerate case `𝔞 = A`, where the
library's Stacks 0EFL has no instances, is
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_eq_top`.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The first half of the source's proof, at the hypotheses of Stacks 0EIF -/

/-- **The first half of the source's proof of Stacks 0EIF, with every input discharged from its
hypotheses.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` with `𝔞` proper, and let `M` be a
finite `A`-module whose sheaf `M̃|_U` on `U = Spec(A) ∖ V(𝔞)` is isomorphic to a coherent `F`
satisfying conditions (1), (2) and (3) of Stacks 0EIF. Then there is an ideal `J₀ ⊆ 𝔞` with
`V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` for which the unit of derived `I`-adic completion is invertible on
`H⁰` of the derived sections of `M̃` on `V = Spec(A) ∖ V(J₀)`:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism, for every localization triangle datum of `J₀`.

This is `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf`
with its ring-theoretic inputs supplied from the sheaf-level hypotheses. Under condition (3)(a)
the dimension function and its extreme values come from condition (1) through
`Stacks.Algebraization.exists_isGreatest_isLeast_dualizingDimension`, and condition (3)(a) in its
ring-theoretic form comes from `supportDim_le_zero_of_isSerreOneOffVanishing`. Under condition
(3)(b) the dimension function is the one of the hypothesis, and its extreme values on
`V(𝔞) ∩ V(I)` exist and differ by at most `2` by
`Stacks.Algebraization.exists_isGreatest_isLeast_of_le_add_two`.

The properness of `𝔞` is where the library's Stacks 0EFL stops applying: `V(𝔞) ∩ V(I)` is empty
for `𝔞 = A`. That case is
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_eq_top`. -/
public theorem exists_ideal_isIso_homology_zero_completionUnit_of_formalSectionsHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hle : I ≤ a)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {F : (complementZeroLocus A a : Scheme).Modules} (hFc : F.IsCoherent)
    (e : F ≅ (complementTilde A a (ModuleCat.of A M) :
      (complementZeroLocus A a : Scheme).Modules))
    (hFSH : FormalSectionsHypotheses A I a F)
    (hane : a ≠ ⊤) :
    ∃ J₀ : Ideal A, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
        ∀ D : LocalizationTriangleData.{u, u} A J₀ J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj (ModuleCat.of A M)))) := by
  obtain ⟨K, hK⟩ := hFSH.dualizing
  have hne := nonempty_zeroLocus_inter_of_ne_top I a hle hane
  have hdim : AssociatedPointsClosureDimensionBound A I a
      (complementTilde A a (ModuleCat.of A M) : (complementZeroLocus A a : Scheme).Modules) :=
    fun x hx => hFSH.associatedPointsDimension x
      ((Stacks.Divisors.associatedPoints_congr e).symm.subset hx)
  rcases hFSH.serreOneOrSmallDimension with hS | ⟨δ, hδ2⟩
  · obtain ⟨δ, δmax, δmin, hδ, hmax, hmin⟩ :=
      exists_isGreatest_isLeast_dualizingDimension I a hFSH.dualizing hne
    exact exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf I a K δ δmax δmin
      hFSH.adicComplete hK hδ hmax hmin hdim
      (Or.inl fun p hp hpI =>
        supportDim_le_zero_of_isSerreOneOffVanishing I a hle hFc e hS p hp hpI)
  · obtain ⟨δmax, δmin, hmax, hmin, h2⟩ :=
      exists_isGreatest_isLeast_of_le_add_two I a δ.toFun hδ2 hne
    exact exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf I a K δ.toFun
      δmax δmin hFSH.adicComplete hK (isDimensionFunctionProp_toFun δ) hmax hmin hdim
      (Or.inr h2)

/-- **The comparison map of Stacks 0EIF is an isomorphism, granting Stacks 0BLX in the shape
`Stacks.Algebraization.CompletedComplementIsFormalSections`.**

The source's proof, assembled: Stacks 0BK0 writes the coherent module as `M̃|_U` for a finite
`M` (`Stacks.LocalCohomology.coherent_complement_affine`); conditions (1), (2) and (3) feed
Stacks 0EFL and produce an ideal `J₀ ⊆ 𝔞` making `Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)` an isomorphism
(`exists_ideal_isIso_homology_zero_completionUnit_of_formalSectionsHypotheses`, and
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_eq_top` in the
degenerate case `𝔞 = A` where Stacks 0EFL does not apply); the Milnor sequence of the derived
limit then surjects that group onto `lim Γ(U, M̃/Iⁿ M̃)`, which is surjectivity of the comparison
map (`Stacks.Algebraization.surjective_comparisonAt_of_completedComplementIsFormalSections`);
injectivity is unconditional. Finally Stacks 0BK0's isomorphism is transported back by
`Stacks.Algebraization.isIso_comparisonMap_of_iso`. -/
public theorem isIso_comparisonMap_of_formalSectionsHypotheses_of_completedComplement
    (h0BLX : CompletedComplementIsFormalSections.{u})
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I a : Ideal B) (hle : I ≤ a)
    (G : (complementZeroLocus B a : Scheme).Modules) [hG : G.IsCoherent]
    (hFSH : FormalSectionsHypotheses B I a G) :
    IsIso (comparisonMap B I a G) := by
  obtain ⟨⟨N, hN, ⟨e⟩⟩, -⟩ :=
    Stacks.LocalCohomology.coherent_complement_affine B a a.fg_of_isNoetherianRing G
  have := hN
  have hex : ∃ J₀ : Ideal B, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set B) ∩ PrimeSpectrum.zeroLocus (I : Set B) =
        PrimeSpectrum.zeroLocus (a : Set B) ∩ PrimeSpectrum.zeroLocus (I : Set B),
        ∀ D : LocalizationTriangleData.{u, u} B J₀ J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
            ((adicCompletionUnit B I I.fg_of_isNoetherianRing).app
              (D.complement.obj N))) := by
    by_cases hane : a = ⊤
    · exact exists_ideal_isIso_homology_zero_completionUnit_of_eq_top I a N
        hFSH.adicComplete hane
    · exact exists_ideal_isIso_homology_zero_completionUnit_of_formalSectionsHypotheses I a hle
        hG e hFSH hane
  obtain ⟨J₀, hJ₀, hV, hunit⟩ := hex
  obtain ⟨D⟩ := Stacks.LocalCohomology.nonempty_localizationTriangleData.{u, u} B J₀
    J₀.fg_of_isNoetherianRing
  exact isIso_comparisonMap_of_iso B I a e.symm
    (isIso_comparisonMap_complementTilde_of_completedComplementIsFormalSections hle N hJ₀ D
      hV h0BLX (hunit D))

end Stacks.Algebraization

end
