module

public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus

/-!
# Lifting germs to sections on an affine neighbourhood inside the flat locus

A finite family of elements of the local ring `𝒪_{X, x}` is a family of germs of sections on
some neighbourhood of `x`, and an affine neighbourhood can be chosen inside any prescribed open
set.  Taking the prescribed open set to be the flat locus of a morphism locally of finite
presentation gives an affine neighbourhood which is flat over the base and on which the family
is represented by global sections.

## Main results

* `Stacks.AlgebraicGeometry.germ_stalkMap_topIso_hom`: the stalk map of an open immersion sends
  the germ of a section of `X` on `U` to the germ of the corresponding global section of `U`.
* `Stacks.AlgebraicGeometry.exists_affineOpen_lifts_of_stalk`: a finite family in a local ring
  is the family of germs of global sections of an affine open inside a prescribed open set.
* `Stacks.AlgebraicGeometry.flat_of_le_flatLocus`: an open subscheme contained in the flat locus
  is flat over the base.
* `Stacks.AlgebraicGeometry.exists_affineOpen_lifts_of_isFlatAt`: the two combined, which is the
  first step of Stacks tag 06LI.

## Implementation notes

The germ condition is stated without transporting along `U.ι ⟨x, hx⟩ = x`:  that equality holds
by `rfl`, so `X.presheaf.stalk (U.ι ⟨x, hx⟩)` and `X.presheaf.stalk x` are the same type up to
unfolding and `exact` accepts an element of either where the other is expected.

Sections of `U.toScheme` over `⊤` are sections of `X` over `U.ι ''ᵁ ⊤`, which is `U` only
propositionally;  `Scheme.Opens.topIso` is that comparison, and `germ_stalkMap_topIso_hom` is
the only place the two spellings have to be reconciled.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- **The germ of a global section of an open subscheme.**  For `U` an open of `X` and
`a : Γ(U, ⊤)`, the stalk map of `U.ι` carries the germ at `x` of the section of `X` on `U`
corresponding to `a` to the germ of `a` at the corresponding point of `U`. -/
theorem germ_stalkMap_topIso_hom (U : X.Opens) (y : U.toScheme) (a : Γ(U.toScheme, ⊤)) :
    (U.ι.stalkMap y).hom (X.presheaf.germ U y.1 y.2 (U.topIso.hom a)) =
      U.toScheme.presheaf.germ ⊤ y trivial a := by
  have h1 : X.presheaf.germ U y.1 y.2 (U.topIso.hom a) =
      X.presheaf.germ (U.ι ''ᵁ ⊤) y.1 ⟨y, trivial, rfl⟩ a := by
    rw [Scheme.Opens.topIso_hom]
    exact X.presheaf.germ_res_apply (i := eqToHom U.ι_image_top.symm) y.1 y.2 a
  have hiso : U.ι.stalkMap y = (U.stalkIso y).inv := (Scheme.Opens.stalkIso_inv U y).symm
  rw [h1, hiso]
  exact congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ U.toScheme.presheaf.stalk y => k.hom a)
    (Scheme.Opens.germ_stalkIso_inv U ⊤ y trivial)

/-- **A finite family in a local ring of a scheme is a family of germs of global sections of an
affine neighbourhood.**  Given `h : Fin r → 𝒪_{X, x}` and an open set `O` containing `x`, there
is an affine open `U ≤ O` containing `x` and global sections `a` of `U` whose germs at `x` are
the `h i`. -/
theorem exists_affineOpen_lifts_of_stalk (x : X) {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (O : X.Opens) (hxO : x ∈ O) :
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Fin r → Γ(U.1.toScheme, ⊤)), U.1 ≤ O ∧
      ∀ i, (U.1.ι.stalkMap ⟨x, hx⟩).hom (h i) =
        U.1.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ trivial (a i) := by
  classical
  choose W hxW s hs using fun i : Fin r => X.presheaf.exists_germ_eq (h i)
  have hmem (z : X) : z ∈ (⨅ i, W i : X.Opens) ↔ ∀ i, z ∈ W i := by
    simp [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ O ⊓ ⨅ i, W i from ⟨hxO, (hmem x).2 hxW⟩) (O ⊓ ⨅ i, W i).isOpen
  have hUW (i : Fin r) : U ≤ W i := fun z hz => (hmem z).1 (hUV hz).2 i
  refine ⟨⟨U, hU⟩, hxU, fun i => (Scheme.Opens.topIso U).inv.hom
    (X.presheaf.map (homOfLE (hUW i)).op (s i)), fun z hz => (hUV hz).1, fun i => ?_⟩
  rw [← germ_stalkMap_topIso_hom U ⟨x, hxU⟩, Iso.inv_hom_id_apply, TopCat.Presheaf.germ_res_apply,
    hs i]

variable {S : Scheme.{u}}

/-- **An open subscheme inside the flat locus is flat over the base.**  If `f` is flat at every
point of an open set `U`, then the restriction of `f` to `U` is a flat morphism. -/
theorem flat_of_le_flatLocus (f : X ⟶ S) (U : X.Opens)
    (hU : ∀ x ∈ U, IsFlatAt f.toLRSHom.toShHom x) : Flat (U.ι ≫ f) := by
  refine Flat.of_stalkMap _ fun x => ?_
  rw [Scheme.Hom.stalkMap_comp U.ι f x]
  refine RingHom.Flat.comp ?_ ?_
  · exact hU (U.ι x) x.2
  · exact RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (C := CommRingCat) (U.ι.stalkMap x))

/-- **The first step of Stacks tag 06LI.**  Let `f : X ⟶ S` be locally of finite presentation
and flat at `x`.  Then a finite family of elements of `𝒪_{X, x}` is the family of germs at `x`
of global sections of an affine open `U` containing `x` which is itself flat over `S`. -/
theorem exists_affineOpen_lifts_of_isFlatAt (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x) (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Fin r → Γ(U.1.toScheme, ⊤)), Flat (U.1.ι ≫ f) ∧
      ∀ i, (U.1.ι.stalkMap ⟨x, hx⟩).hom (h i) =
        U.1.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ trivial (a i) := by
  obtain ⟨U, hxU, a, hUO, ha⟩ := exists_affineOpen_lifts_of_stalk x h
    ⟨{z : X | IsFlatAt f.toLRSHom.toShHom z}, isOpen_setOf_isFlatAt f⟩ hflat
  exact ⟨U, hxU, a, flat_of_le_flatLocus f U.1 fun z hz => hUO hz, ha⟩

end Stacks.AlgebraicGeometry

end
