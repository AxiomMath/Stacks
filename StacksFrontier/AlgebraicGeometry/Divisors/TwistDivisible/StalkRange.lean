module

public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafSum
public import StacksFrontier.AlgebraicGeometry.Divisors.MinimalTwistSection
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistDivisible.RankOne
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistDivisible.StalkBasis
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf

/-!
# The image of `𝒪_X ⟶ 𝒪_X(D)` on a stalk

Let `D ⊆ X` be an effective Cartier divisor, `𝒪_X(D)` its invertible sheaf ([Stacks, Tag 01WX])
and `1_D ⟶` the inclusion `𝒪_X ⟶ 𝒪_X(D)`, multiplication by the canonical section. This file
computes the image of that inclusion on the stalk at an arbitrary point `x`:

`image of (𝒪_X ⟶ 𝒪_X(D))_x = ℐ_{D,x} · 𝒪_X(D)_x`,

where `ℐ_{D,x}` is the stalk at `x` of the ideal sheaf of `D`
(`AlgebraicGeometry.IdealSheafData.stalk`). Both sides are submodules of the stalk of `𝒪_X(D)`,
and the identity holds at every point with no local hypothesis whatever: off the support of `D`
it reads "the inclusion is surjective on the stalk", and on the support it is the statement that
the canonical section vanishes to exactly the order the divisor prescribes.

The proof is one local computation. On an affine open `V ∋ x` carrying a rank-one dual basis `b`
of the ideal sheaf — which exists by the converse half of [Stacks, Tag 0B8M] — the dual
coordinate `λ` of `b` trivializes `𝒪_X(D)` over every open inside `V`, so its germ is a basis of
the stalk (`Stacks.Divisors.TwistDivisible.bijective_smul_germAt`), and the canonical section is
`a · λ` with `a` the image in `𝒪_X` of the basis section of `b`
(`Stacks.Divisors.canonicalSection_eq_smul_dualBasisOne_lam`). The stalk of the structure sheaf
as a module over itself is free on the germ of the unit section, so the image of the inclusion
is the span of the germ of `a · λ`, which is `(germ a) · 𝒪_X(D)_x`. Finally `a` generates the
ideal of `D` over `V` — this is the local equation of the zero scheme of the canonical section,
`Stacks.Divisors.zeroScheme_ideal_eq_span_idealSheafSection` read through
`Stacks.Divisors.zeroScheme_canonicalSection` — and the stalk of an ideal sheaf is the image of
its ideal on an affine open.

## Main results

* `Stacks.Divisors.TwistDivisible.range_stalkHom_unitToInvertibleSheaf`: **the image of
  `𝒪_X ⟶ 𝒪_X(D)` on the stalk at `x` is `ℐ_{D,x} · 𝒪_X(D)_x`.**
* `Stacks.Divisors.TwistDivisible.exists_bijective_smul_modStalk`: the stalk of `𝒪_X(D)` at any
  point is free of rank one over the local ring, with an explicit germ as generator.
* `Stacks.Divisors.TwistDivisible.span_oneGerm_eq_top`: the stalk of the structure sheaf as a
  module over itself is spanned by the germ of the unit section.

## Implementation notes

**`idealStalk` exists to fix one spelling.** `AlgebraicGeometry.IdealSheafData.stalk D x` is an
ideal of `X.presheaf.stalk x`, while the submodules here live over
`Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x`. The two rings are equal by `rfl`, but
instance search is syntactic and the scalar action of one on a module over the other fails to
synthesize; `idealStalk` is the same ideal with its type declared at the second spelling.

**The unit section is read through `unitHomEquiv`, not through its inverse.** The inclusion
`𝒪_X ⟶ 𝒪_X(D)` is `unitHomEquiv.symm` of the canonical section, and unfolding that inverse goes
through `LinearMap.ringLmapEquivSelf` and exhausts the kernel's heartbeats. Going forwards
instead — `unitHomEquiv` of the inclusion is the canonical section, which is
`Stacks.Divisors.unitHomEquiv_unitToInvertibleSheaf` — makes the value of the inclusion on the
unit section a structure projection, and that is a cheap `rfl`.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.ReflexiveModules (ringGermAt oneGerm oneSection germAt_oneSection
  unitStalkEquiv stalkHom stalkHom_germAt unitModule)

universe u

namespace Stacks.Divisors.TwistDivisible

variable {X : Scheme.{u}}

/-- **The stalk of the structure sheaf as a module over itself is spanned by the germ of the
unit section.** -/
theorem span_oneGerm_eq_top (x : X) :
    Submodule.span (ringStalk X.sheaf x) {oneGerm X x} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun m => ?_
  obtain ⟨r, hr⟩ := (unitStalkEquiv X x).surjective m
  rw [← hr]
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)

/-- The canonical section of `𝒪_X(D)`, read at the two spellings the library uses for it, is the
same section. -/
theorem canonicalSections_eq_canonicalSection' (D : X.IdealSheafData) :
    Stacks.Divisors.canonicalSections D = Stacks.Divisors.canonicalSection' D :=
  rfl

/-- The stalk of an ideal sheaf at a point, with its type declared at the `ringStalk` spelling
of the local ring, which is the one the stalk of a module is a module over. -/
noncomputable abbrev idealStalk (D : X.IdealSheafData) (x : X) : Ideal (ringStalk X.sheaf x) :=
  AlgebraicGeometry.IdealSheafData.stalk D x

/-- **The stalk of `𝒪_X(D)` is free of rank one.** The generator produced is the germ of the
dual coordinate of a rank-one dual basis of the ideal sheaf on an affine neighbourhood, which
trivializes `𝒪_X(D)` over every open inside that neighbourhood. -/
theorem exists_bijective_smul_modStalk (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (x : X) :
    ∃ g : modStalk (Stacks.Divisors.divisorSheaf D) x,
      Function.Bijective (fun r : ringStalk X.sheaf x => r • g) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property (Stacks.Divisors.negativeTwist' D) :=
    ‹Stacks.Divisors.IsEffectiveCartierDivisor D›
  obtain ⟨V, hxV, -, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
    (Stacks.Divisors.negativeTwist' D) x (Opens.mem_top x)
  refine ⟨germAt (Stacks.Divisors.divisorSheaf D) (V : X.Opens) x hxV
    (Stacks.Divisors.dualBasisOneLam D b), bijective_smul_germAt hxV _ ?_⟩
  intro W hW
  have hb := Stacks.Divisors.bijective_smulSectionMap_dualBasisOne_lam D
    (b.restrict (homOfLE hW))
  have hfun : (fun c : Γ(X, W) =>
      c • res (Stacks.Divisors.divisorSheaf D) hW (Stacks.Divisors.dualBasisOneLam D b))
      = fun c => Stacks.SheafOfModules.smulSectionMap (b.restrict (homOfLE hW)).lam c := by
    funext c
    exact (Stacks.SheafOfModules.smulSectionMap_apply _ c).symm
  rw [hfun]
  exact hb

/-- **The image of `𝒪_X ⟶ 𝒪_X(D)` on the stalk at `x` is `ℐ_{D,x} · 𝒪_X(D)_x`.** For an
effective Cartier divisor `D` this holds at every point, with no local hypothesis: the canonical
section is the local equation of `D` times a basis of the stalk, and the local equation generates
the ideal of `D`. -/
theorem range_stalkHom_unitToInvertibleSheaf (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (x : X) :
    LinearMap.range (stalkHom (Stacks.Divisors.unitToInvertibleSheaf D) x)
      = idealStalk D x •
        (⊤ : Submodule (ringStalk X.sheaf x)
          (modStalk (Stacks.Divisors.divisorSheaf D) x)) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property (Stacks.Divisors.negativeTwist' D) :=
    ‹Stacks.Divisors.IsEffectiveCartierDivisor D›
  obtain ⟨V, hxV, -, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
    (Stacks.Divisors.negativeTwist' D) x (Opens.mem_top x)
  have hgen : ∀ (W : X.Opens) (hW : W ≤ (V : X.Opens)),
      Function.Bijective (fun c : Γ(X, W) =>
        c • res (Stacks.Divisors.divisorSheaf D) hW (Stacks.Divisors.dualBasisOneLam D b)) := by
    intro W hW
    have hb := Stacks.Divisors.bijective_smulSectionMap_dualBasisOne_lam D
      (b.restrict (homOfLE hW))
    have hfun : (fun c : Γ(X, W) =>
        c • res (Stacks.Divisors.divisorSheaf D) hW (Stacks.Divisors.dualBasisOneLam D b))
        = fun c => Stacks.SheafOfModules.smulSectionMap (b.restrict (homOfLE hW)).lam c := by
      funext c
      exact (Stacks.SheafOfModules.smulSectionMap_apply _ c).symm
    rw [hfun]
    exact hb
  have hbasis := bijective_smul_germAt hxV (Stacks.Divisors.dualBasisOneLam D b) hgen
  have hspan : Submodule.span (ringStalk X.sheaf x)
      {germAt (Stacks.Divisors.divisorSheaf D) (V : X.Opens) x hxV
        (Stacks.Divisors.dualBasisOneLam D b)} = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun m => ?_
    obtain ⟨r, hr⟩ := hbasis.2 m
    rw [← hr]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  have hcan : (Stacks.Divisors.canonicalSections D).eval (op (V : X.Opens))
      = Stacks.Divisors.idealSheafSection D b.e • Stacks.Divisors.dualBasisOneLam D b := by
    rw [canonicalSections_eq_canonicalSection' D]
    exact Stacks.Divisors.canonicalSection_eq_smul_dualBasisOne_lam D b
  have hgerm : stalkHom (Stacks.Divisors.unitToInvertibleSheaf D) x (oneGerm X x)
      = ringGermAt X (V : X.Opens) x hxV (Stacks.Divisors.idealSheafSection D b.e) •
        germAt (Stacks.Divisors.divisorSheaf D) (V : X.Opens) x hxV
          (Stacks.Divisors.dualBasisOneLam D b) := by
    rw [← germAt_oneSection X x (V : X.Opens) hxV]
    refine (stalkHom_germAt (Stacks.Divisors.unitToInvertibleSheaf D) x
      (V : X.Opens) hxV (oneSection X (V : X.Opens))).trans ?_
    have h0 : ((Stacks.Divisors.invertibleSheaf D).unitHomEquiv
        (Stacks.Divisors.unitToInvertibleSheaf D)).eval (op (V : X.Opens))
        = Scheme.Modules.Hom.app (Stacks.Divisors.unitToInvertibleSheaf D) (V : X.Opens)
          (oneSection X (V : X.Opens)) := rfl
    have hq4 : Scheme.Modules.Hom.app (Stacks.Divisors.unitToInvertibleSheaf D) (V : X.Opens)
        (oneSection X (V : X.Opens))
        = (Stacks.Divisors.canonicalSections D).eval (op (V : X.Opens)) :=
      h0.symm.trans (congrArg
        (fun s : _root_.SheafOfModules.sections (Stacks.Divisors.invertibleSheaf D) =>
          s.eval (op (V : X.Opens)))
        (Stacks.Divisors.unitHomEquiv_unitToInvertibleSheaf D))
    refine Eq.trans (congrArg
      (fun z : Γ(Stacks.Divisors.divisorSheaf D, (V : X.Opens)) =>
        germAt (Stacks.Divisors.divisorSheaf D) (V : X.Opens) x hxV z) (hq4.trans hcan)) ?_
    exact germAt_smul' (Stacks.Divisors.divisorSheaf D) hxV _ _
  have hrange := range_eq_span_singleton
    (stalkHom (Stacks.Divisors.unitToInvertibleSheaf D) x) (oneGerm X x) (span_oneGerm_eq_top x)
  rw [hrange, hgerm]
  refine (span_singleton_smul_eq _ _ hspan).trans ?_
  congr 1
  have hid : D.ideal V = Ideal.span {Stacks.Divisors.idealSheafSection D b.e} :=
    (congrArg (fun J : X.IdealSheafData => J.ideal V)
        (Stacks.Divisors.zeroScheme_canonicalSection D)).symm.trans
      (Stacks.Divisors.zeroScheme_ideal_eq_span_idealSheafSection D V b _ rfl)
  show Ideal.span {ringGermAt X (V : X.Opens) x hxV (Stacks.Divisors.idealSheafSection D b.e)}
      = AlgebraicGeometry.IdealSheafData.stalk D x
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ D x V hxV, hid, Ideal.map_span,
    Set.image_singleton]
  rfl

end Stacks.Divisors.TwistDivisible

end
