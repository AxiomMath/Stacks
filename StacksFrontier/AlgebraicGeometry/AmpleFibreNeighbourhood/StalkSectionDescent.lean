module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk

/-!
# A section over the spectrum of a local ring of the base comes from a neighbourhood

Let `𝒢` be a quasi-coherent `𝒪_S`-module and `y` a point of `S`.  The canonical morphism
`Spec 𝒪_{S, y} ⟶ S` lies over every open neighbourhood of `y`
(`AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem`), so a section of `𝒢` over an open `U ∋ y`
pulls back to a global section of `(S.fromSpecStalk y)^* 𝒢`.  This file proves that **every**
global section of `(S.fromSpecStalk y)^* 𝒢` arises this way, from an affine open neighbourhood
of `y`:

  `Γ(𝒢, U) ⟶ Γ(Spec 𝒪_{S, y}, (S.fromSpecStalk y)^* 𝒢)` is jointly surjective over `U ∋ y`.

This is the descent step a limit argument needs: a statement about one section of a pullback to
`Spec 𝒪_{S, y}` is spread out to a statement about a section over a genuine open of `S`, which is
how the replacement of `S` by `Spec 𝒪_{S, y}` in the proof of [Stacks, Tag 0D2N] is undone.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_eq`: **the theorem.** For every
  `n : Γ((S.fromSpecStalk y)^* 𝒢, ⊤)` there are an affine open `U ∋ y` and an `a : Γ(𝒢, U)` whose
  pullback, `AlgebraicGeometry.Scheme.Modules.pullbackSection`, is `n`.

## The route

The whole content is already in
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_pullbackSectionₗ` of
`StacksFrontier/AlgebraicGeometry/PullbackSections/Stalk.lean`: for an affine open `U₀ ∋ y`, pulling
sections back exhibits `Γ((S.fromSpecStalk y)^* 𝒢, ⊤)` as the localisation of `Γ(𝒢, U₀)` at the
prime complement of the prime of `Γ(S, U₀)` corresponding to `y` — the hypothesis it needs, that
`Γ(Spec 𝒪_{S, y}, ⊤)` is the corresponding localisation of `Γ(S, U₀)`, is
`AlgebraicGeometry.isLocalization_sections_fromSpecStalk`.  The instantiation here is exactly the
one made inside `AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv`.

Given that, `IsLocalizedModule.surj` writes `n` as a fraction: there are `a : Γ(𝒢, U₀)` and `r`
outside the prime of `y` with `r • n` the pullback of `a`.  The affine open the section descends
to is the basic open `S.basicOpen r ⊆ U₀`, which

* contains `y`, because the germ of `r` at `y` is the image of `r` under the localisation map
  `Γ(S, U₀) ⟶ 𝒪_{S, y}` and is therefore a unit (`IsLocalization.map_units`), which is what
  `AlgebraicGeometry.Scheme.mem_basicOpen` asks for;
* is affine, by `AlgebraicGeometry.IsAffineOpen.basicOpen`;
* carries a unit restriction of `r`, by
  `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`.

Scaling the restriction of `a` to `S.basicOpen r` by the inverse of that unit gives the section:
pulling back is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`
(`AlgebraicGeometry.pullbackSectionHom_smul`) and commutes with shrinking the open downstairs
(`AlgebraicGeometry.pullbackSectionHom_map`), and the two scalars that appear multiply to `1`
because `AlgebraicGeometry.Scheme.Hom.map_appLE` identifies the image of `r` read on `U₀` with the
image of its restriction read on `S.basicOpen r`.

No appeal to the stalk `𝒢_y` itself is needed, and no unit has to be cancelled inside
`Γ(Spec 𝒪_{S, y}, ⊤)`: the inverse is taken in `Γ(S, S.basicOpen r)`, where `r` is a unit by
construction, and pushed forward.

## Implementation notes

The statement is phrased with `AlgebraicGeometry.Scheme.Modules.pullbackSection`, the bare
function, rather than with its linear upgrade `pullbackSectionₗ`: the type of the latter carries
the module structure of `AlgebraicGeometry.Scheme.Modules.pullbackSectionsModule` as a `let`, so a
statement about it has to open with a `letI` — compare
`AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv` — and here nothing is gained by
it, because the conclusion is an equality of elements and not a linearity assertion.

The proof is carried out at `AlgebraicGeometry.pullbackSectionHom`, which lands in the type
spelled `Γ((S.fromSpecStalk y)^* 𝒢, ⊤)`, rather than at `pullbackSection`, which lands in the
definitionally equal but differently spelled `((pullback _).obj 𝒢).val.obj (op ⊤)`: instance
search finds the module structure on the sections only at the first spelling, so the scalar
multiplications of the computation do not elaborate at the second.  The two are the same function
by `AlgebraicGeometry.pullbackSectionHom_apply`, which is `rfl`, so the final `exact` crosses the
boundary for free.

## No attribute

No `@[stacks]` attribute is attached: this is the surjectivity half of the localisation
description of `Γ((S.fromSpecStalk y)^* 𝒢, ⊤)`, extracted in the form a descent argument consumes,
and not itself a numbered result of the Stacks project.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01HX](https://stacks.math.columbia.edu/tag/01HX)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- **Every section of the pullback of a quasi-coherent module to the spectrum of a local ring of
the base comes from a section over an open neighbourhood of the point.**

For a quasi-coherent `𝒪_S`-module `𝒢`, a point `y` of `S` and a global section `n` of
`(S.fromSpecStalk y)^* 𝒢`, there are an *affine* open `U ∋ y` and a section `a : Γ(𝒢, U)` whose
pullback along `Spec 𝒪_{S, y} ⟶ S` — legitimate over the whole of `Spec 𝒪_{S, y}`, which lies
over `U` by `AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem` — is `n`.

The affineness of `U` is free: `U` is produced as a basic open of an affine neighbourhood of `y`,
so `AlgebraicGeometry.IsAffineOpen.basicOpen` applies, and it is worth recording because the
consumers of this statement go on to use the affine description of the sections over `U`.

Both the existence and the shape of `U` are read off the localisation description of the sections
of the pullback, `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_pullbackSectionₗ`: `n` is a
fraction `a / r` over an affine open `U₀ ∋ y`, and `U` is the locus `S.basicOpen r` where the
denominator is invertible. -/
theorem exists_mem_pullbackSection_eq {S : Scheme.{u}} (𝒢 : S.Modules) [𝒢.IsQuasicoherent]
    (y : S) (n : Γ((Scheme.Modules.pullback (S.fromSpecStalk y)).obj 𝒢, ⊤)) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (a : Γ(𝒢, U)),
      Scheme.Modules.pullbackSection (S.fromSpecStalk y) 𝒢 U ⊤
        (le_preimage_fromSpecStalk_of_mem y U hy) a = n := by
  obtain ⟨U₀, hU₀, hy₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : S.Opens) from trivial)
  have h₀ : (⊤ : (Spec (S.presheaf.stalk y)).Opens) ≤ S.fromSpecStalk y ⁻¹ᵁ U₀ :=
    le_preimage_fromSpecStalk_of_mem y U₀ hy₀
  let := Scheme.Modules.pullbackSectionsModule (S.fromSpecStalk y) 𝒢 U₀ ⊤ h₀
  let : Algebra Γ(S, U₀) (S.presheaf.stalk y) := (S.presheaf.germ U₀ y hy₀).hom.toAlgebra
  let : IsLocalization.AtPrime (S.presheaf.stalk y) (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal :=
    hU₀.isLocalization_stalk ⟨y, hy₀⟩
  have := Scheme.Modules.isLocalizedModule_pullbackSectionₗ (S.fromSpecStalk y) 𝒢 hU₀
    (isAffineOpen_top (Spec (S.presheaf.stalk y))) h₀
    (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
    (isLocalization_sections_fromSpecStalk y hU₀ hy₀)
  -- Write `n` as a fraction `a / r` of sections over the affine open `U₀`.
  obtain ⟨⟨a, r⟩, hra⟩ := IsLocalizedModule.surj
    (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
    (Scheme.Modules.pullbackSectionₗ (S.fromSpecStalk y) 𝒢 U₀ ⊤ h₀) n
  -- The denominator is invertible in `𝒪_{S, y}`, so `y` lies in its basic open.
  have hunit : IsUnit ((S.presheaf.germ U₀ y hy₀).hom (r : Γ(S, U₀))) :=
    IsLocalization.map_units (S.presheaf.stalk y) r
  have hyU : y ∈ S.basicOpen (r : Γ(S, U₀)) :=
    (S.mem_basicOpen (r : Γ(S, U₀)) y hy₀).mpr hunit
  have hUU₀ : S.basicOpen (r : Γ(S, U₀)) ≤ U₀ := S.basicOpen_le _
  have h : (⊤ : (Spec (S.presheaf.stalk y)).Opens) ≤
      S.fromSpecStalk y ⁻¹ᵁ S.basicOpen (r : Γ(S, U₀)) :=
    le_preimage_fromSpecStalk_of_mem y _ hyU
  -- There the denominator itself becomes invertible, with inverse `u`.
  have hru : IsUnit (S.presheaf.map (homOfLE hUU₀).op (r : Γ(S, U₀))) :=
    S.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨u, hu⟩ := hru.exists_right_inv
  have hres : pullbackSectionHom (S.fromSpecStalk y) 𝒢 (S.basicOpen (r : Γ(S, U₀))) ⊤ h
        (𝒢.presheaf.map (homOfLE hUU₀).op a) =
      pullbackSectionHom (S.fromSpecStalk y) 𝒢 U₀ ⊤ h₀ a :=
    pullbackSectionHom_map (S.fromSpecStalk y) 𝒢 U₀ _ hUU₀ ⊤ h h₀ a
  have hra' : ((S.fromSpecStalk y).appLE U₀ ⊤ h₀).hom (r : Γ(S, U₀)) • n =
      pullbackSectionHom (S.fromSpecStalk y) 𝒢 U₀ ⊤ h₀ a := hra
  have happ : ((S.fromSpecStalk y).appLE (S.basicOpen (r : Γ(S, U₀))) ⊤ h).hom
        (S.presheaf.map (homOfLE hUU₀).op (r : Γ(S, U₀))) =
      ((S.fromSpecStalk y).appLE U₀ ⊤ h₀).hom (r : Γ(S, U₀)) :=
    (CommRingCat.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom
        (Scheme.Hom.map_appLE (S.fromSpecStalk y) h (homOfLE hUU₀).op) _)
  have key : pullbackSectionHom (S.fromSpecStalk y) 𝒢 (S.basicOpen (r : Γ(S, U₀))) ⊤ h
      (u • 𝒢.presheaf.map (homOfLE hUU₀).op a) = n :=
    calc pullbackSectionHom (S.fromSpecStalk y) 𝒢 (S.basicOpen (r : Γ(S, U₀))) ⊤ h
            (u • 𝒢.presheaf.map (homOfLE hUU₀).op a)
        = ((S.fromSpecStalk y).appLE (S.basicOpen (r : Γ(S, U₀))) ⊤ h).hom u •
            pullbackSectionHom (S.fromSpecStalk y) 𝒢 (S.basicOpen (r : Γ(S, U₀))) ⊤ h
              (𝒢.presheaf.map (homOfLE hUU₀).op a) :=
          pullbackSectionHom_smul (S.fromSpecStalk y) 𝒢 _ ⊤ h _ _
      _ = ((S.fromSpecStalk y).appLE (S.basicOpen (r : Γ(S, U₀))) ⊤ h).hom u •
            (((S.fromSpecStalk y).appLE U₀ ⊤ h₀).hom (r : Γ(S, U₀)) • n) := by
          rw [hres, hra']
      _ = n := by
          rw [smul_smul, ← happ, ← map_mul, mul_comm u _, hu, map_one, one_smul]
  exact ⟨S.basicOpen (r : Γ(S, U₀)), hU₀.basicOpen _, hyU,
    u • 𝒢.presheaf.map (homOfLE hUU₀).op a, key⟩

end Stacks.AmpleFibreNeighbourhood

end
