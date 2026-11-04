module

public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Sets.CompactOpenCovered
public import StacksFrontier.AlgebraicGeometry.Size.Basic
import StacksFrontier.AlgebraicGeometry.Size.FiniteType
import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import all StacksFrontier.AlgebraicGeometry.Size.Coverings

/-!
# Additions to `Coverings`

Supplementary declarations for the module above, kept in their own module.
-/

@[expose] public section

open CategoryTheory Cardinal TopologicalSpace

namespace Cardinal

end Cardinal

namespace AlgebraicGeometry

end AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

universe w v u

namespace FppfCovering

variable {T : Scheme.{u}} (𝒞 : FppfCovering.{v} T)

end FppfCovering

/-- Every fppf covering `𝒞` of a scheme `X` is refined by an fppf covering `𝒲` of `X` by
*affine* schemes whose index type lies in the universe of `X`, has at most `Scheme.size X`
members, and all of whose members have size at most `Scheme.size X`.

The refinement is assembled from the finite families of affine opens of members of `𝒞`
covering the affine opens of `X` supplied by
`FppfCovering.exists_finite_affineOpens_cover`, so its index type is
`Σ U : X.affineOpens, Fin (n U)` and its members are affine. Each member is an affine open
`V` of some `𝒞.X i`, and the composite `V ⟶ 𝒞.X i ⟶ X` is locally of finite type with `V`
quasi-compact, so `Scheme.size V ≤ Scheme.size X` by Stacks 04T7. -/
lemma exists_small_affine_refinement (X : Scheme.{u}) (𝒞 : FppfCovering.{v} X) :
    ∃ 𝒲 : FppfCovering.{u} X,
      𝒲.IsRefinement 𝒞 ∧
      Cardinal.mk 𝒲.ι ≤ Scheme.size X ∧
      (∀ j, IsAffine (𝒲.X j)) ∧
      ∀ j, Scheme.size (𝒲.X j) ≤ Scheme.size X := by
  choose n a V hVaff hVcov using 𝒞.exists_finite_affineOpens_cover
  refine ⟨{ ι := Σ U : X.affineOpens, Fin (n U)
            X := fun ⟨U, k⟩ => (V U k).toScheme
            f := fun ⟨U, k⟩ => (V U k).ι ≫ 𝒞.f (a U k)
            flat := fun ⟨U, k⟩ => by have := 𝒞.flat (a U k); infer_instance
            lfp := fun ⟨U, k⟩ => by have := 𝒞.lfp (a U k); infer_instance
            jointly_surjective := ?_ }, fun ⟨U, k⟩ => ⟨a U k, (V U k).ι, rfl⟩, ?_,
    fun ⟨U, k⟩ => hVaff U k, ?_⟩
  · intro t
    obtain ⟨W, hW, htW, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top t)
    have htU : t ∈ ⋃ k, (𝒞.f (a ⟨W, hW⟩ k)) '' (V ⟨W, hW⟩ k : Set (𝒞.X (a ⟨W, hW⟩ k))) := by
      rw [hVcov ⟨W, hW⟩]; exact htW
    obtain ⟨k, x, hxV, hxt⟩ := Set.mem_iUnion.mp htU
    exact ⟨⟨⟨W, hW⟩, k⟩, ⟨x, hxV⟩, hxt⟩
  · exact Cardinal.mk_sigma_fin_le n X.aleph0_le_size X.mk_affineOpens_le_size
  · rintro ⟨U, k⟩
    have := 𝒞.flat (a U k)
    have := 𝒞.lfp (a U k)
    have : IsAffine (V U k).toScheme := hVaff U k
    exact Scheme.size_le_of_locallyOfFiniteType ((V U k).ι ≫ 𝒞.f (a U k))

