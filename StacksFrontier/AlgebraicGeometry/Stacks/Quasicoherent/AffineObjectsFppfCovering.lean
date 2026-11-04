module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# The objects lying over affine schemes cover a fibred fppf site and are quasi-compact

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids with its associated fppf topology.
This file records two facts about the objects of `𝒳` lying over affine schemes, in the shapes in
which a direct image computed on such objects consumes them:

* every sieve containing all the arrows out of objects lying over affine schemes is a covering
  sieve (`AlgebraicGeometry.FibredSite.mem_of_forall_isAffine`), since every object carries a
  covering family by such objects;
* an object lying over an affine scheme is a quasi-compact object of the site in the sense of
  Stacks 090H (`AlgebraicGeometry.FibredSite.isQuasiCompactObject_of_isAffine`), by the finite
  subcovering property of
  `AlgebraicGeometry.BigFppfOver.hasFiniteSubcovering_associatedTopology`.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

include hp in
/-- **Every sieve containing all the arrows out of objects lying over affine schemes is a
covering sieve** of the associated fppf site. -/
theorem mem_of_forall_isAffine (U : 𝒳) (T : Sieve U)
    (hT : ∀ ⦃V : 𝒳⦄ (f : V ⟶ U), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj V)) →
      T f) :
    T ∈ BigFppfOver.associatedTopology B S hS p .fppf U := by
  obtain ⟨I, y, φ, haff, hcov, -⟩ := exists_affine_fppf_ofArrows B S hS p hp U
  refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_ hcov
  rintro W g ⟨Y, a, b, ⟨j⟩, rfl⟩
  exact T.downward_closed (hT (φ j) (haff j)) a

include hp in
/-- **An object lying over an affine scheme is a quasi-compact object** of the associated fppf
site (Stacks 090H): every covering family is refined by a covering family with finitely many
members. -/
theorem isQuasiCompactObject_of_isAffine (x : 𝒳)
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    (BigFppfOver.associatedTopology B S hS p .fppf).IsQuasiCompactObject x := by
  intro 𝒰 h𝒰
  obtain ⟨n, W, g, hg, hcov⟩ :=
    BigFppfOver.hasFiniteSubcovering_associatedTopology B S hS p hp x hx _ h𝒰
  choose k a ha using fun i => (Sieve.mem_ofArrows_iff _ _ _).1 (hg i)
  let 𝒱 : PreZeroHypercover.{max v w} x := ⟨ULift (Fin n), fun i => W i.down, fun i => g i.down⟩
  have hsieve : 𝒱.sieve₀ = Sieve.ofArrows W g := by
    apply le_antisymm
    · rintro Z h ⟨Y', c, d, ⟨i⟩, rfl⟩
      exact ⟨_, c, g i.down, ⟨i.down⟩, rfl⟩
    · rintro Z h ⟨Y', c, d, ⟨i⟩, rfl⟩
      exact ⟨_, c, 𝒱.f ⟨i⟩, Presieve.ofArrows.mk (ι := 𝒱.I₀) ⟨i⟩, rfl⟩
  exact ⟨𝒱, ⟨fun i => k i.down, fun i => a i.down, fun i => (ha i.down).symm⟩, hsieve ▸ hcov,
    Set.finite_range _⟩

end AlgebraicGeometry.FibredSite
