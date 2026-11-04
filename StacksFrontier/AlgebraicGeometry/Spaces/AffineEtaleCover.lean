module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Affine coverings of an object of the big fppf site

Every object `T` of the big fppf category over a scheme `S` is covered, in the topology of that
site, by a family of objects whose underlying schemes are affine: take the affine open cover of
the underlying scheme of `T`, which is a family of open immersions, and regard each member as an
object over `S` through its composite with the structure morphism of `T`.

An open immersion is étale, so the same family is an affine *étale* covering, which is the form
in which a descent argument along affine charts uses it.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affine_open_cover_of_openCover`: an open cover of the
  underlying scheme of `T` by affine schemes, read as a covering family inside the site.
* `AlgebraicGeometry.BigFppfOver.exists_affine_open_cover`: a covering family of `T` by affine
  objects along open immersions.
* `AlgebraicGeometry.BigFppfOver.exists_finite_affine_open_cover`: the same for a quasi-compact
  `T`, with a finite index.
* `AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`: the same family, with étaleness of
  each member recorded as `AlgebraicGeometry.Space.IsEtale` of its image under Yoneda.

## Implementation notes

The index type is the one of the open cover of the underlying scheme that is read into the site,
and it lies in the working universe, which is what the sheaf conditions on the site consume: for
`AlgebraicGeometry.BigFppfOver.exists_affine_open_cover` it is the set of points of the
underlying scheme of `T`, the index type of `AlgebraicGeometry.Scheme.affineCover`, and for
`AlgebraicGeometry.BigFppfOver.exists_finite_affine_open_cover` a finite subset of it.

That the members of the affine cover are again objects of the size-bounded category underlying
the site is **Stacks 000R (3)**, `AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open cover of the underlying scheme of an object of the big fppf category over `S` by
affine schemes is a covering family inside the site.** Each member of the cover is regarded as an
object over `S` by composing with the structure morphism of `T`, and is again an object of the
size-bounded category underlying the site by **Stacks 000R (3)**. The index type of the cover is
the index type of the resulting family, so a cover with a finite index yields a finite covering
family. Joint surjectivity is recorded both on points of the underlying scheme and as a
covering sieve of the site. -/
theorem exists_affine_open_cover_of_openCover (T : BigFppfOver B S hS)
    (c : Scheme.OpenCover.{u} ((toScheme B S hS).obj T)) (hc : ∀ i, IsAffine (c.X i)) :
    ∃ (V : c.I₀ → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (V i))) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS T ∧
      ∀ x : (toScheme B S hS).obj T, ∃ i y, (toScheme B S hS).map (π i) y = x := by
  have hsize (i : c.I₀) : B.Contains (c.X i) :=
    Scheme.size_lt_of_isOpenImmersion (c.f i) T.left.property
  let V (i : c.I₀) : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (c.f i ≫ B.inclusion.map T.hom) : B.obj (hsize i) ⟶ B.obj hS)
  let π (i : c.I₀) : V i ⟶ T := Over.homMk (ObjectProperty.homMk (c.f i)) rfl
  refine ⟨V, π, fun i => hc i, fun i => inferInstanceAs (IsOpenImmersion (c.f i)), ?_,
    fun x => c.exists_eq x⟩
  exact sieve_generate_ofArrows_mem_topology V π
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ c.mem₀)

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An object of the big fppf category over `S` is covered by affine objects along open
immersions.** The family is the affine open cover of the underlying scheme, each member regarded
as an object over `S` by composing with the structure morphism. -/
theorem exists_affine_open_cover (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (V i))) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS T := by
  obtain ⟨V, π, hV, hπ, hc, -⟩ := exists_affine_open_cover_of_openCover B S hS T
    ((toScheme B S hS).obj T).affineCover fun i => inferInstance
  exact ⟨_, V, π, hV, hπ, hc⟩

end

/-- **An object of the big fppf category over `S` is covered by affine objects along open
immersions.** The family is the affine open cover of the underlying scheme, each member regarded
as an object over `S` by composing with the structure morphism. Joint surjectivity is recorded
both on points of the underlying scheme and as a covering sieve of the site. -/
theorem exists_affine_open_cover' (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (V i))) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS T ∧
      ∀ x : (toScheme B S hS).obj T, ∃ i y, (toScheme B S hS).map (π i) y = x := by
  obtain ⟨V, π, h⟩ := exists_affine_open_cover_of_openCover B S hS T
    ((toScheme B S hS).obj T).affineCover fun i => inferInstance
  exact ⟨_, V, π, h⟩

/-- **An object of the big fppf category over `S` whose underlying scheme is quasi-compact is
covered by *finitely many* affine objects along open immersions.** The family is a finite
subcover of the affine open cover of the underlying scheme, which exists because that scheme is
quasi-compact (`AlgebraicGeometry.Scheme.OpenCover.finiteSubcover`); its members are members of
the affine open cover itself, so they are affine and the maps are open immersions.

This is the form of `AlgebraicGeometry.BigFppfOver.exists_affine_open_cover` that an argument
reducing a quasi-compact test object of the site to affine ones needs: a finiteness condition
read off a covering is only available for a covering with finitely many members. -/
theorem exists_finite_affine_open_cover (T : BigFppfOver B S hS)
    [CompactSpace ((toScheme B S hS).obj T)] :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      Finite I ∧
      (∀ i, IsAffine ((toScheme B S hS).obj (V i))) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS T := by
  obtain ⟨V, π, haff, hopen, hcov, -⟩ := exists_affine_open_cover_of_openCover B S hS T
    ((toScheme B S hS).obj T).affineCover.finiteSubcover fun i => inferInstance
  exact ⟨_, V, π, inferInstance, haff, hopen, hcov⟩

/-- **An object of the big fppf category over `S` is covered by affine objects along étale
morphisms.** This is `AlgebraicGeometry.BigFppfOver.exists_affine_open_cover` together with the
fact that an open immersion of schemes is étale; étaleness is recorded for the image under Yoneda
of each member, which is the shape **Stacks 03FR** gives it. -/
theorem exists_affine_etale_cover (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (V i))) ∧
      (∀ i, Space.IsEtale B S hS (yoneda.map (π i))) ∧
      Sieve.generate (Presieve.ofArrows V π) ∈ topology B S hS T := by
  obtain ⟨I, V, π, hV, hπ, hc, -⟩ := exists_affine_open_cover' B S hS T
  refine ⟨I, V, π, hV, fun i => ?_, hc⟩
  have := hπ i
  exact (Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (π i))).2
    ((Space.presheaf_yoneda_map_etale_iff B S hS (π i)).2 inferInstance)

end AlgebraicGeometry.BigFppfOver

end
