module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Etale.AffineImageFlatSections

/-!
# Covering the small étale site by affine objects with affine image

An object of the small étale site of a scheme `S` is covered by those of its affine opens whose
image in `S` is an affine open: étale morphisms are open, and an affine open `V` of the object
can be cut down to `V ∩ f⁻¹U'` for an affine open `U' ⊆ f(V)`, which is affine with image
exactly `U'`. Over such an open the structure morphism is an étale morphism of affine schemes,
so the ring map `𝒪_S(U') ⟶ Γ(V ∩ f⁻¹U', 𝒪)` is flat.

## Main definitions

* `AlgebraicGeometry.SmallEtale.AffineImageIndex`: the pairs of an affine open of an object of
  the small étale site and an affine open of `S` which is its image.
* `AlgebraicGeometry.SmallEtale.affineImageCover`: the covering family of those affine opens.

## Main results

* `AlgebraicGeometry.SmallEtale.mem_topology_sieve₀_affineImageCover`: it is a covering family
  for the small étale topology.
* `AlgebraicGeometry.SmallEtale.flat_appLE_affineImageCover`: the sections of the structure sheaf
  over a member are flat over the sections of `𝒪_S` on its image.
* `AlgebraicGeometry.SmallEtale.faithfullyFlat_appLE_affineImageCover`: those sections are in
  fact faithfully flat, the image of a member being the whole of the affine open.
* `AlgebraicGeometry.SmallEtale.exists_cover_isAffineOpen_range_flat`: the two previous results
  packaged as one covering with objectwise flatness.

## References

* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An affine open of the underlying scheme of an object of the small étale site of `S`, together
with an affine open of `S` which is exactly its image under the structure morphism. -/
public def AffineImageIndex (T : SmallEtale B S hS) : Type (u + 1) :=
  ULift.{u + 1} (Σ V : T.obj.left.obj.Opens, {U : S.Opens //
    IsAffineOpen V ∧ IsAffineOpen U ∧
      T.obj.hom.hom.base '' (V : Set T.obj.left.obj) = (U : Set S)})

/-- **The covering of an object of the small étale site by its affine opens with affine image.**
Its index type is `AlgebraicGeometry.SmallEtale.AffineImageIndex` and its members are the open
immersions of those affine opens. -/
public noncomputable def affineImageCover (T : SmallEtale B S hS) :
    PreZeroHypercover.{u + 1} T where
  I₀ := AffineImageIndex B S hS T
  X i := openSubObj B S hS T i.down.1
  f i := openSubHom B S hS T i.down.1

/-- **The affine opens with affine image cover, for the small étale topology.** -/
public theorem mem_topology_sieve₀_affineImageCover (T : SmallEtale B S hS) :
    (affineImageCover B S hS T).sieve₀ ∈ topology B S hS T := by
  have : Etale T.obj.hom.hom := T.property
  refine Precoverage.generate_mem_toGrothendieck
    (presieve₀_mem_precoverage_of_isOpenImmersion B S hS _ (fun x => ?_)
      (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.ι))))
  obtain ⟨V, U, hxV, hV, hU, himage⟩ :=
    Etale.exists_isAffineOpen_image_isAffineOpen T.obj.hom.hom x
  exact ⟨⟨⟨V, U, hV, hU, himage⟩⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

/-- The underlying scheme of a member of
`AlgebraicGeometry.SmallEtale.affineImageCover` is affine. -/
public theorem isAffine_affineImageCover_X (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T) :
    _root_.AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)) :=
  i.down.2.2.1

/-- The image in `S` of a member of `AlgebraicGeometry.SmallEtale.affineImageCover` is the
affine open recorded by its index. -/
public theorem range_affineImageCover_X (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T) :
    Set.range ((affineImageCover B S hS T).X i).obj.hom.hom.base =
      ((i.down.2.1 : S.Opens) : Set S) := by
  refine .trans ?_ i.down.2.2.2.2
  change Set.range (i.down.1.ι ≫ T.obj.hom.hom).base = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]

/-- **Étale ring maps are flat, on a member of the affine-image covering.** The sections of the
structure sheaf of a member of `AlgebraicGeometry.SmallEtale.affineImageCover` are flat over the
sections of `𝒪_S` on the affine open which is its image. -/
public theorem flat_appLE_affineImageCover (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T)
    (e : (⊤ : ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)).Opens) ≤
      ((affineImageCover B S hS T).X i).obj.hom.hom ⁻¹ᵁ (i.down.2.1 : S.Opens)) :
    ((((affineImageCover B S hS T).X i).obj.hom.hom).appLE
      (i.down.2.1 : S.Opens) ⊤ e).hom.Flat := by
  have : Etale ((affineImageCover B S hS T).X i).obj.hom.hom :=
    ((affineImageCover B S hS T).X i).property
  have : _root_.AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)) :=
    isAffine_affineImageCover_X B S hS T i
  exact Etale.flat_appLE_top _ i.down.2.2.2.1 e

/-- **Étale ring maps are faithfully flat, on a member of the affine-image covering.** The
sections of the structure sheaf of a member of `AlgebraicGeometry.SmallEtale.affineImageCover`
are faithfully flat over the sections of `𝒪_S` on the affine open which is its image. -/
public theorem faithfullyFlat_appLE_affineImageCover (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T)
    (e : (⊤ : ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)).Opens) ≤
      ((affineImageCover B S hS T).X i).obj.hom.hom ⁻¹ᵁ (i.down.2.1 : S.Opens)) :
    ((((affineImageCover B S hS T).X i).obj.hom.hom).appLE
      (i.down.2.1 : S.Opens) ⊤ e).hom.FaithfullyFlat := by
  have : Etale ((affineImageCover B S hS T).X i).obj.hom.hom :=
    ((affineImageCover B S hS T).X i).property
  have : _root_.AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)) :=
    isAffine_affineImageCover_X B S hS T i
  exact Etale.faithfullyFlat_appLE_top _ i.down.2.2.2.1 e
    (range_affineImageCover_X B S hS T i).ge

/-- **Every object of the small étale site of `S` is covered by affine objects whose image in `S`
is an affine open and over which the structure sheaf is flat.** This is the hypothesis of
Stacks 0GN1 for the presheaf of rings `V ↦ 𝒪_S(f(V))` and the presheaf of modules
`V ↦ Γ(V, 𝒪_V)`. -/
public theorem exists_cover_isAffineOpen_range_flat (T : SmallEtale B S hS) :
    ∃ (I : Type (u + 1)) (X : I → SmallEtale B S hS) (g : ∀ i, X i ⟶ T) (U : I → S.Opens)
      (e : ∀ i, (⊤ : ((toScheme B S hS).obj (X i)).Opens) ≤ (X i).obj.hom.hom ⁻¹ᵁ U i),
      Sieve.ofArrows X g ∈ topology B S hS T ∧
        (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, Set.range (X i).obj.hom.hom.base = ((U i : S.Opens) : Set S)) ∧
        ∀ i, ((X i).obj.hom.hom.appLE (U i) ⊤ (e i)).hom.Flat := by
  exact ⟨AffineImageIndex B S hS T, (affineImageCover B S hS T).X,
    (affineImageCover B S hS T).f, fun i => i.down.2.1,
    fun i x _ => (range_affineImageCover_X B S hS T i).le ⟨x, rfl⟩,
    mem_topology_sieve₀_affineImageCover B S hS T, fun i => i.down.2.2.2.1,
    range_affineImageCover_X B S hS T, fun i => flat_appLE_affineImageCover B S hS T i _⟩

end AlgebraicGeometry.SmallEtale

end
