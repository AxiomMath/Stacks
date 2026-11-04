module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzFiniteLocallyFreeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleNeighbourhoodExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeColimitFullyFaithful

/-!
# Fundamental group Lefschetz: `colim_𝒱 FÉt_V ≃ FÉt_Y` for the zero scheme of an ample section

Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible `𝒪_X`-module,
`s ∈ Γ(X, L)`, `Y = Z(s)` its zero scheme and `𝒱` the set of open subschemes of `X` containing
`Y`, ordered by reverse inclusion. [Stacks, Tag 0ELD] says that if

`depth(𝒪_{X, x}) + dim({x}‾) > 2`

for every `x ∈ X ∖ Y`, then the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence.

## How the equivalence is written

An object of `colim_𝒱 FÉt_V` is a finite étale cover of some `V ∈ 𝒱`, and a morphism between two
such covers is a morphism of their restrictions to some smaller member of `𝒱`, two of them being
identified when they agree on a still smaller member. The restriction functor to `FÉt_Y` is then
an equivalence exactly when

1. it is fully faithful, which is `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful X Y`:
   every morphism of the restrictions to `Y` of two covers of `V ∈ 𝒱` is the restriction of a
   morphism over some smaller `V' ∈ 𝒱`, and two morphisms over `V` with the same restriction to
   `Y` agree over some smaller `V' ∈ 𝒱`;
2. it is essentially surjective: every finite étale cover of `Y` is isomorphic to the restriction
   to `Y` of a finite étale cover of some `V ∈ 𝒱`.

## Proof

The source's proof: Tag 0ELD is a formal consequence of [Stacks, Tag 0EK1] and
[Stacks, Tag 0EL7].

* Full faithfulness is
  `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_zeroScheme_of_depth`.
* For essential surjectivity, [Stacks, Tag 0EL7]
  (`Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`)
  says that completion `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully faithful on finite locally free
  objects and that every finite locally free object of `Coh(X, I)` is the completion of a finite
  locally free module on some `V ∈ 𝒱`. These are the two inputs of the construction in the proof
  of [Stacks, Tag 0EK1]
  (`Stacks.FundamentalGroup.exists_finiteEtale_neighbourhood_extension_of_completion`), which
  extends every finite étale cover of `Y` to a neighbourhood.

The depth hypothesis is written as `Stacks.FundamentalGroup.DepthAddDimGtTwoOutsideSupport`, in
the extended integers; `two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport` reads it
in `WithBot ℕ∞`, the spelling Tag 0EL7 uses.

## Main results

* `Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_zeroScheme_of_depth` —
  [Stacks, Tag 0ELD].

## References

* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization

/-- The hypothesis of [Stacks, Tag 0ELD], `depth(𝒪_{X, x}) + dim({x}‾) > 2` off `Y`, read in
`WithBot ℕ∞` through `Stacks.Algebraization.localDepthAddDimClosure`, as
[Stacks, Tag 0EL7] states it. -/
public theorem two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport
    {X : Scheme.{u}} {Y : X.IdealSheafData} (h : DepthAddDimGtTwoOutsideSupport X Y) (x : X)
    (hx : x ∉ (Y.support : Set X)) :
    ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x := by
  by_contra hle
  have hm := krullDimToEInt_mono (not_lt.mp hle)
  rw [localDepthAddDimClosure, krullDimToEInt_add, krullDimToEInt_coe,
    krullDimToEInt_natCast] at hm
  exact absurd (h x hx) (not_lt.mpr hm)

/-- **Stacks Project, Tag 0ELD.** Let `k` be a field, `X` a proper scheme over `k`, `L` an ample
invertible `𝒪_X`-module, `s ∈ Γ(X, L)`, `Y = Z(s)` the zero scheme of `s`, and `𝒱` the open
subschemes of `X` containing `Y`, ordered by reverse inclusion. If
`depth(𝒪_{X, x}) + dim({x}‾) > 2` for every `x ∈ X ∖ Y`, then the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence.

The equivalence `colim_𝒱 FÉt_V ≃ FÉt_Y` is stated as its two halves: the restriction functor is
fully faithful (`FiniteEtaleColimitFullyFaithful X Y`: morphisms of restrictions to `Y` come from
morphisms over a smaller neighbourhood, and morphisms with equal restrictions to `Y` agree over a
smaller neighbourhood), and essentially surjective (every finite étale cover of `Y` is the
restriction of a finite étale cover of some open neighbourhood of `Y`). -/
@[stacks 0ELD "the restriction functor colim_V FÉt_V → FÉt_Y is an equivalence, stated as its \
fully faithful half and its essentially surjective half, at exactly the source's hypotheses"]
public theorem finiteEtaleColimitEquivalence_zeroScheme_of_depth
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s)) :
    FiniteEtaleColimitFullyFaithful X (zeroScheme X L s) ∧
      ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
        ∃ (W : Neighborhood X (zeroScheme X L s))
          (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
          Nonempty ((finiteEtaleBaseChange
            (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A) := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  obtain ⟨-, hff, hess⟩ :=
    completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure k X g L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hL) s
      (two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport hdepth)
  refine ⟨finiteEtaleColimitFullyFaithful_zeroScheme_of_depth k g L hL s hdepth, fun A =>
    exists_finiteEtale_neighbourhood_extension_of_completion _ hff (fun F hF => ?_) A⟩
  obtain ⟨V, hV, G, hG, -, e⟩ := hess F hF
  exact ⟨V, hV, restrictCoherentModules V.ι G, hG, e⟩

end Stacks.FundamentalGroup

end
