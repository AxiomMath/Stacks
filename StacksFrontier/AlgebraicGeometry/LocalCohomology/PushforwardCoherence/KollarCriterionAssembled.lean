module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CoherenceEquivalence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumCoherentPushforward

/-!
# Kollár's criterion

Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes and `F` a coherent
`𝒪_U`-module. [Stacks, Tag 0BK3] (Kollár's criterion) says that `j_*F` is coherent if and only
if for every associated point `x` of `F`, every point `w` of the reduced closure of `{j x}` in
`X` lying outside the image of `j`, and every associated prime `𝔭` of the completed local ring
`𝒪^∧_{Z_x, w}`, one has `2 ≤ dim(𝒪^∧_{Z_x, w} ⧸ 𝔭)`.

The criterion is deduced from [Stacks, Tag 0BJZ] and [Stacks, Tag 0BK1]: `j_*F` is coherent if
and only if, for every associated point `x` of `F`, the direct image of the structure sheaf of the
reduced closure `W_x` of `{x}` along `W_x ⟶ U ⟶ X` is coherent; and the latter holds when the
dimension condition on the completed local rings holds.

## Main results

* `Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_isCoherent_pushforward_pointClosure`:
  `j_*F` is coherent if and only if `(i_{W_x} ≫ j)_* 𝒪_{W_x}` is coherent for every associated
  point `x` of `F`.
* `Stacks.LocalCohomology.two_le_ringKrullDim_quotient_adicCompletion_of_isCoherent_pushforward`:
  the forward implication of Kollár's criterion.
* `Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`:
  Kollár's criterion.

## Implementation notes

The two shapes of the iterated direct image — `j_* i_{W,*} 𝒪_W` and `(i_W ≫ j)_* 𝒪_W` — are
interchanged by `AlgebraicGeometry.Scheme.Modules.pushforwardComp`; [Stacks, Tag 0BJZ] is proved
in the first and the criterion consumes it in the second.

Local Noetherianness of `U` is not assumed: it follows from that of `X` along the open immersion.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)

universe u

namespace Stacks.LocalCohomology

open Stacks.AlgebraicGeometry.CoherenceFromPointClosures in
/-- **[Stacks, Tag 0BJZ], along the composite.** Let `X` be a locally Noetherian scheme,
`j : U ⟶ X` the inclusion of an open subscheme and `F` a coherent `𝒪_U`-module. Then `j_*F` is
coherent if and only if `(i_{W_x} ≫ j)_* 𝒪_{W_x}` is coherent for every associated point `x` of
`F`, where `W_x` is the reduced closure of `{x}` in `U`. -/
theorem isCoherent_pushforward_iff_forall_isCoherent_pushforward_pointClosure {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent ↔
      ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
        ((Scheme.Modules.pushforward ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subschemeι ≫ j)).obj
          (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent := by
  refine Iff.trans (isCoherent_pushforward_iff_forall_isAssociatedPoint j F).symm ⟨?_, ?_⟩
  · intro h x hx
    have : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι ⋙ Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent := h x hx
    exact isCoherent_of_iso ((Scheme.Modules.pushforwardComp
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))).subschemeι
      j).app _).symm
  · intro h x hx
    have := h x hx
    exact isCoherent_of_iso ((Scheme.Modules.pushforwardComp
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))).subschemeι
      j).app _)

/-- **[Stacks, Tag 0BK3], the implication (1) ⇒ (2).** Let `j : U ⟶ X` be an open immersion
with `X` locally Noetherian and let `F` be a coherent `𝒪_U`-module whose direct image `j_*F` is
coherent. Then for every associated point `x` of `F`, every point `w` of the reduced closure of
`{j x}` in `X` whose image lies outside the image of `j`, and every associated prime `𝔭` of the
completed local ring of that closure at `w`, one has `2 ≤ dim` of the corresponding quotient. -/
theorem two_le_ringKrullDim_quotient_adicCompletion_of_isCoherent_pushforward {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
      ∀ w : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme,
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subschemeι.base w ∉ Set.range j.base →
        ∀ p : Ideal (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
          ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)),
          IsAssociatedPrimeStacks
            (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
            (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)) p →
          (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
            (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
            ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w) ⧸ p) :=
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  fun x hx _ hw _ hp =>
    two_le_ringKrullDim_quotient_adicCompletion_stalk_pointClosure j x
      ((isCoherent_pushforward_iff_forall_isCoherent_pushforward_pointClosure j F).mp hF x hx)
      hw hp

/-- **Kollár's criterion.** Let `j : U ⟶ X` be an open immersion with `X`
locally Noetherian and let `F` be a coherent `𝒪_U`-module. Then `j_*F` is coherent if and only
if for every associated point `x` of `F`, every point `w` of the reduced closure of `{j x}` in
`X` whose image lies outside the image of `j`, and every associated prime `𝔭` of the completed
local ring of that closure at `w`, one has `2 ≤ dim` of the corresponding quotient. -/
@[stacks 0BK3]
theorem isCoherent_pushforward_iff_forall_two_le_ringKrullDim
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (F : U.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent ↔
      ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
        ∀ w : (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subschemeι.base w ∉ Set.range j.base →
          ∀ p : Ideal (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
            ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)),
            IsAssociatedPrimeStacks
              (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
                ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
                ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)) p →
            (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
              (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w) ⧸ p) :=
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure j F
    (isCoherent_pushforward_iff_forall_isCoherent_pushforward_pointClosure j F)
    fun _ _ j' hj' hint hln hne hdim =>
      have := hj'
      have := hint
      have := hln
      have := hne
      isCoherent_pushforward_structureSheaf_of_completion_associatedPrime_dim j' hdim

end Stacks.LocalCohomology

end
