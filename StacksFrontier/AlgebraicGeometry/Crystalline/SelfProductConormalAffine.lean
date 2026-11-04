module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Affineness of the opens of a self-product lying over an affine open

Fix a global crystalline situation `(p, (S, I, γ), X)` and a product `(U(1), T(1), δ(1))` of an
object `(U, T, δ)` of the small crystalline site `Cris(X/S)` with itself, presented as in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean` by a limit binary fan with
projections `pr₀, pr₁`.  Write `p₀, p₁ : T(1) ⟶ T` for the ambient components of the two
projections, `Δ : T ⟶ T(1)` for the ambient component of the diagonal, and
`p₀⁻¹V ⊓ p₁⁻¹V` — `Crystalline.GlobalCrystallineSituation.smallSelfProductOpen` — for the open
of `T(1)` lying over an open `V` of `T`.

The affine opens of `T` are what the comparison of [Stacks, Tag 07J1] is read on, and the source's
reduction to the affine case needs the opens of `T(1)` lying over them to be affine too.  They are:
`Δ` is a closed immersion, hence finite, and a homeomorphism on spaces, hence surjective, and it
pulls `p₀⁻¹V ⊓ p₁⁻¹V` back to `V`; so restricting `Δ` over that open gives a finite surjective
morphism with affine source, and [Stacks, Tag 01ZT] — `Stacks.Thickenings.isAffine_of_isThickening`
and the underlying `Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective` — says its
target is affine.

Because `Δ` is a homeomorphism on spaces, `W ↦ Δ⁻¹W` is injective on opens of `T(1)`, and that
identifies `p₀⁻¹V ⊓ p₁⁻¹V` with `p₀⁻¹V` itself: the second coprojection's preimage already
contains the first's.  On basic opens this reads as a basic open of `T(1)`, cut out by the first
coprojection of the defining section.

## Main results

* `Crystalline.GlobalCrystallineSituation.isAffineOpen_smallSelfProductOpen` — the open
  `p₀⁻¹V ⊓ p₁⁻¹V` of `T(1)` lying over an affine open `V` of `T` is affine.
* `Crystalline.GlobalCrystallineSituation.preimage_smallSelfProductAmbientDiagonal_injective` —
  an open of `T(1)` is determined by its preimage under the ambient diagonal.
* `Crystalline.GlobalCrystallineSituation.firstCoprojection_preimage_eq` — the open lying over
  `V` is the preimage of `V` under the first coprojection alone.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductOpen_basicOpen` — the open lying over
  the basic open of a section `f` is the basic open of `p₀^♯ f`.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}

/-- **The open of `T(1)` lying over an affine open of `T` is affine.**  The ambient diagonal
`Δ : T ⟶ T(1)` is a closed immersion, hence finite, and a homeomorphism on spaces, hence
surjective; it pulls `p₀⁻¹V ⊓ p₁⁻¹V` back to `V`, so its restriction over that open is a finite
surjective morphism with affine source, and [Stacks, Tag 01ZT] applies. -/
@[stacks 07J1 "the open of T(1) corresponding to an affine open of T is affine, by Limits, \
Lemma 01ZT applied to the restriction of the diagonal"]
theorem isAffineOpen_smallSelfProductOpen (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V : B.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (smallSelfProductOpen pr₀ pr₁ V) := by
  have : IsClosedImmersion (smallSelfProductAmbientDiagonal h).hom :=
    isClosedImmersion_smallSelfProductAmbientDiagonal h
  have : Surjective (smallSelfProductAmbientDiagonal h).hom :=
    ⟨(isHomeomorph_smallSelfProductAmbientDiagonal h).surjective⟩
  have hpre : IsAffineOpen
      ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V) := by
    rwa [diagonal_preimage_smallSelfProductOpen]
  let : IsAffine
      ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ
        smallSelfProductOpen pr₀ pr₁ V).toScheme := hpre
  let : Surjective
      ((smallSelfProductAmbientDiagonal h).hom ∣_ smallSelfProductOpen pr₀ pr₁ V) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance _
  exact Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective
    ((smallSelfProductAmbientDiagonal h).hom ∣_ smallSelfProductOpen pr₀ pr₁ V)

/-- **An open of `T(1)` is determined by its preimage under the ambient diagonal.**  The diagonal
is a homeomorphism on spaces, in particular surjective, so two opens with the same preimage have
the same points. -/
theorem preimage_smallSelfProductAmbientDiagonal_injective (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    Function.Injective
      fun W : D.obj.thickening.target.scheme.Opens ↦
        (smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ W := by
  intro W Z hWZ
  refine SetLike.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (isHomeomorph_smallSelfProductAmbientDiagonal h).surjective x
  exact SetLike.ext_iff.mp hWZ y

/-- **The open lying over `V` is the preimage of `V` under the first coprojection alone.**  Both
opens have the same preimage under the diagonal, namely `V`, because the diagonal is a section of
the first coprojection. -/
theorem firstCoprojection_preimage_eq (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    pr₀.hom.targetHom.hom ⁻¹ᵁ V = smallSelfProductOpen pr₀ pr₁ V := by
  refine preimage_smallSelfProductAmbientDiagonal_injective h ?_
  dsimp only
  rw [diagonal_preimage_smallSelfProductOpen h V]
  show ((smallSelfProductAmbientDiagonal h).hom ≫ pr₀.hom.targetHom.hom) ⁻¹ᵁ V = V
  rw [ambientDiagonal_comp_fst h]
  rfl

/-- **The open lying over a basic open is a basic open.**  It is cut out by the first coprojection
of the defining section, the open lying over `V` being the preimage of `V` under that
coprojection. -/
theorem smallSelfProductOpen_basicOpen (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductOpen pr₀ pr₁ (B.obj.thickening.target.scheme.basicOpen f) =
      D.obj.thickening.target.scheme.basicOpen (firstCoprojectionSection pr₀ pr₁ V f) := by
  rw [firstCoprojectionSection, Scheme.basicOpen_appLE, firstCoprojection_preimage_eq h]
  exact (inf_eq_right.mpr (smallSelfProductOpen_mono pr₀ pr₁
    (B.obj.thickening.target.scheme.basicOpen_le f))).symm

end Crystalline.GlobalCrystallineSituation

end
