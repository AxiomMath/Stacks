module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.SmallCover
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineEtaleCover

/-!
# The Keel–Mori theorem (Stacks 0DUT)

Let `𝒳` be an algebraic stack whose inertia `I_𝒳 ⟶ 𝒳` is finite. Then there is a uniform
categorical moduli space `f : 𝒳 ⟶ M`, and `f` is separated, quasi-compact and a universal
homeomorphism.

The proof follows the source. Stacks 0DUE supplies a family of separated étale stabilizer
preserving 1-morphisms `gᵢ : 𝒳ᵢ ⟶ 𝒳` from well-nigh affine stacks covering `𝒳`
(`AlgebraicGeometry.Stack.exists_isWellNighAffine_etale_cover`). After re-indexing it by the
points of one smooth chart of `𝒳`, so that the disjoint union of the moduli spaces is an object
of the site (the source's footnote, `AlgebraicGeometry.Stack.exists_keelMoriCover_isSmall`), the
moduli spaces `Mᵢ` of the `𝒳ᵢ` (Stacks 0DUP) and those `Mᵢⱼ` of the `𝒳ᵢ ×_𝒳 𝒳ⱼ` (Stacks 0DUS)
form an étale equivalence relation (Stacks 0DT7), whose quotient `M = U/R` (Stacks 02WW) receives
the glued moduli map `f`. The squares `𝒳ᵢ = Mᵢ ×_M 𝒳` are 2-cartesian (Stacks 0DUD), so that
separatedness, quasi-compactness and being a universal homeomorphism descend from the `fᵢ`
(Stacks 06TZ, 0DTL, 0DTQ), and the uniformity of `f` is glued from that of the `fᵢ`
(`AlgebraicGeometry.Stack.KeelMoriCover.exists_keelMoriModuliSpace_of_isSmall`).

## Main results

* `AlgebraicGeometry.Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia`:
  **Stacks 0DUT**.
* `AlgebraicGeometry.Stack.exists_keelMoriModuliSpace_hasWellNighAffineModuliPieces`: the same
  together with the well-nigh affine pieces the moduli space is built from (the input of
  Stacks 0DUV).

## References

* [Stacks Project, Tag 0DUT](https://stacks.math.columbia.edu/tag/0DUT)
-/

@[expose] public section

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Keel–Mori theorem, with the pieces of the moduli space** (Stacks 0DUT, and the
construction in its proof): for an algebraic stack with finite inertia there is a uniform
categorical moduli space `f : 𝒳 ⟶ M` which is separated, quasi-compact and a universal
homeomorphism, and `M` is covered by étale morphisms `Mⱼ ⟶ M` over which `f` is the uniform
categorical moduli space of a well-nigh affine stack `𝒳ⱼ = Mⱼ ×_M 𝒳`. -/
theorem exists_keelMoriModuliSpace_hasWellNighAffineModuliPieces
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
      IsUniformCategoricalModuliSpace B S hS M f.hom ∧ AlgebraicStacks.IsSeparated B S hS f ∧
        IsQuasiCompactMorphism.{u, w} B S hS f ∧ UniversalHomeomorphism B S hS f ∧
          HasWellNighAffineModuliPieces B S hS f := by
  obtain ⟨ι, 𝒳ᵢ, g, hcov, hwna, hstab, hrep⟩ := exists_isWellNighAffine_etale_cover B S hS 𝒳 hI
  exact exists_keelMoriModuliSpace_of_cover B S hS 𝒳 𝒳ᵢ g hcov hwna (fun i => (hstab i).1)
    (fun i => (hrep i).1) (fun i => (hrep i).2.1) (fun i => (hrep i).2.2)

/-- **Stacks 0DUT (Keel–Mori).** Let `𝒳` be an algebraic stack whose inertia `I_𝒳 ⟶ 𝒳` is
finite. Then there exists a uniform categorical moduli space `f : 𝒳 ⟶ M`, and `f` is separated,
quasi-compact, and a universal homeomorphism. -/
@[stacks 0DUT]
theorem exists_isUniformCategoricalModuliSpace_of_isFinite_inertia
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
      IsUniformCategoricalModuliSpace B S hS M f.hom ∧ AlgebraicStacks.IsSeparated B S hS f ∧
        IsQuasiCompactMorphism.{u, w} B S hS f ∧ UniversalHomeomorphism B S hS f := by
  obtain ⟨M, f, h₁, h₂, h₃, h₄, -⟩ :=
    exists_keelMoriModuliSpace_hasWellNighAffineModuliPieces B S hS 𝒳 hI
  exact ⟨M, f, h₁, h₂, h₃, h₄⟩

end AlgebraicGeometry.Stack

end
