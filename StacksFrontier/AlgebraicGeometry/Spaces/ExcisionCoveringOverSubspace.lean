module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization

/-!
# The excision covering attached to an étale morphism which is an isomorphism over a subspace

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` and let `iY : Z ⟶ Y`
be a closed subspace whose inverse image `iX : W ⟶ X` is carried isomorphically onto it by
`k : W ⟶ Z`, as in [Stacks, Tag 0A4P]. Then two morphisms into `X` which agree after composition
with `f` and whose common composite factors through `Z` are equal, and `X` together with the open
complement of `Z` covers `Y` in the spaces-étale topology of [Stacks, Tag 03G0].

## Main definitions

* `AlgebraicGeometry.Space.complementSpace`, `AlgebraicGeometry.Space.complementHom` and
  `AlgebraicGeometry.Space.complementObj`: the open complement of a closed subspace, as an
  algebraic space, as an étale morphism to the ambient space, and as an object of the
  spaces-étale site.
* `AlgebraicGeometry.Space.excisionCover`: the two-element family `{X ⟶ Y, Y ∖ Z ⟶ Y}`.

## Main results

* `AlgebraicGeometry.Space.eq_of_comp_eq_of_factorsThrough_subspace`: two morphisms into `X`
  agreeing in `Y`, with common composite factoring through `Z`, are equal.
* `AlgebraicGeometry.Space.range_pointsMap_complementHom`: the point set of the open complement
  is the complement of the point set of `Z`.
* `AlgebraicGeometry.Space.subset_range_pointsMap_of_isPullback_of_isIso`: the point set of `Z`
  is contained in the image of `|f|`.
* `AlgebraicGeometry.Space.isCovering_excisionCover` and
  `AlgebraicGeometry.Space.generate_excisionCover_mem_topology`: the two-element family is a
  covering family, and the sieve it generates is a covering sieve.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Agreement

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- **A morphism which is an isomorphism over a subspace has one section through that
subspace.** Let `f : X ⟶ Y` be a morphism of algebraic spaces, let `iY : Z ⟶ Y` be a subspace
and let `iX : W ⟶ X` be its inverse image, presented by the cartesian square `hk` with
`k : W ⟶ Z` an isomorphism. Then two morphisms `a, b` into `X` whose composites with `f` agree
and factor through `iY` are equal. -/
theorem eq_of_comp_eq_of_factorsThrough_subspace {f : X ⟶ Y} {iY : Z ⟶ Y} {iX : W ⟶ X}
    {k : W ⟶ Z} [IsIso k] (hk : IsPullback k.hom iX.hom iY.hom f.hom)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : V ⟶ X.1) (z : V ⟶ Z.1)
    (ha : a ≫ f.hom = z ≫ iY.hom) (hb : b ≫ f.hom = z ≫ iY.hom) :
    a = b := by
  have hki : k.hom ≫ (inv k).hom = 𝟙 W.1 :=
    congrArg (fun m : W ⟶ W => m.hom) (IsIso.hom_inv_id k)
  have hmono : ∀ g h : V ⟶ W.1, g ≫ k.hom = h ≫ k.hom → g = h := by
    intro g h e
    rw [← Category.comp_id g, ← Category.comp_id h, ← hki, ← Category.assoc, ← Category.assoc, e]
  rw [← hk.lift_snd z a ha.symm, ← hk.lift_snd z b hb.symm,
    hmono (hk.lift z a ha.symm) (hk.lift z b hb.symm) (by rw [hk.lift_fst, hk.lift_fst])]

/-- **The point set of a subspace which `f` is an isomorphism over is contained in the image of
`|f|`.** Given the cartesian square `hk` with `k` invertible, every point of `Z` is the image
under `|f|` of a point of `X`. -/
theorem subset_range_pointsMap_of_isPullback_of_isIso {f : X ⟶ Y} {iY : Z ⟶ Y} {iX : W ⟶ X}
    {k : W ⟶ Z} [IsIso k] (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    Set.range (pointsMap B S hS Z.1 iY.hom) ⊆ Set.range (pointsMap B S hS X.1 f.hom) := by
  have hik : (inv k).hom ≫ k.hom = 𝟙 Z.1 :=
    congrArg (fun m : Z ⟶ Z => m.hom) (IsIso.inv_hom_id k)
  rintro x ⟨z, rfl⟩
  refine ⟨pointsMap B S hS W.1 iX.hom (pointsMap B S hS Z.1 (inv k).hom z), ?_⟩
  calc pointsMap B S hS X.1 f.hom
        (pointsMap B S hS W.1 iX.hom (pointsMap B S hS Z.1 (inv k).hom z))
      = pointsMap B S hS W.1 (iX.hom ≫ f.hom) (pointsMap B S hS Z.1 (inv k).hom z) :=
        (pointsMap_comp_apply B S hS _ _ _).symm
    _ = pointsMap B S hS W.1 (k.hom ≫ iY.hom) (pointsMap B S hS Z.1 (inv k).hom z) := by
        rw [hk.w]
    _ = pointsMap B S hS Z.1 iY.hom
          (pointsMap B S hS W.1 k.hom (pointsMap B S hS Z.1 (inv k).hom z)) :=
        pointsMap_comp_apply B S hS _ _ _
    _ = pointsMap B S hS Z.1 iY.hom
          (pointsMap B S hS Z.1 ((inv k).hom ≫ k.hom) z) := by
        rw [pointsMap_comp_apply]
    _ = pointsMap B S hS Z.1 iY.hom z := by rw [hik, pointsMap_id]; rfl

end Agreement

section Complement

attribute [local instance] pointTopology

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The open complement of the point set of a closed subspace, as an algebraic space: the open
subspace of Stacks 03BZ cut out by the complement of the point set. -/
def complementSpace (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom) :
    AlgebraicSpaces B S hS :=
  ⟨(openSubspaceOfPoints B S hS Y.1
      (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ).toFunctor,
    (isOpenSubspace_openSubspaceOfPoints B S hS Y.property _
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS Y.property iY.hom
        hiY).isOpen_compl).1⟩

/-- The inclusion of the open complement of a closed subspace into the ambient space. -/
def complementHom (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom) :
    complementSpace B S hS iY hiY ⟶ Y :=
  ObjectProperty.homMk
    (openSubspaceOfPoints B S hS Y.1 (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ).ι

/-- The inclusion of the open complement is étale, being an open immersion. -/
theorem isEtale_complementHom (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom) :
    IsEtale B S hS (complementHom B S hS iY hiY).hom :=
  isEtale_ι_of_isOpenSubspace (isOpenSubspace_openSubspaceOfPoints B S hS Y.property _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS Y.property iY.hom hiY).isOpen_compl)

/-- **The point set of the open complement is the complement of the point set**, Stacks 03BZ,
part (1). -/
theorem range_pointsMap_complementHom (iY : Z ⟶ Y)
    (hiY : IsClosedImmersion B S hS iY.hom) :
    Set.range (pointsMap B S hS (complementSpace B S hS iY hiY).1
        (complementHom B S hS iY hiY).hom) =
      (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The open complement of a closed subspace, as an object of the spaces-étale site of the
ambient space. -/
def complementObj (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom) :
    SpacesEtale B S hS Y :=
  ⟨Over.mk (complementHom B S hS iY hiY), isEtale_complementHom B S hS iY hiY⟩

/-- **The excision covering of Stacks 0A4P**: the two-element family consisting of `f : X ⟶ Y`
and of the inclusion of the open complement of `Z`, as a family over the terminal object of the
spaces-étale site of `Y`, indexed by `ULift.{u + 1} Bool`. -/
abbrev excisionCover (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y)
    (hiY : IsClosedImmersion B S hS iY.hom) :
    PreZeroHypercover.{u + 1} (SpacesEtale.idObj B S hS Y) where
  I₀ := ULift.{u + 1} Bool
  X i := Bool.rec (complementObj B S hS iY hiY) (etaleObject B S hS f hf) i.down
  f _ := (SpacesEtale.isTerminal_idObj B S hS Y).from _

/-- **The excision family is a covering family**, for `f` an isomorphism over `Z`; `f` itself
need not be surjective. -/
theorem isCovering_excisionCover {W : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom)
    {iX : W ⟶ X} {k : W ⟶ Z} [IsIso k] (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    SpacesEtale.IsCovering B S hS Y
      ⟨SpacesEtale.idObj B S hS Y, excisionCover B S hS f hf iY hiY⟩ := by
  intro x
  by_cases hx : x ∈ Set.range (pointsMap B S hS Z.1 iY.hom)
  · obtain ⟨y, hy⟩ := subset_range_pointsMap_of_isPullback_of_isIso B S hS hk hx
    refine ⟨ULift.up true, y, ?_⟩
    rwa [SpacesEtale.toSpaces_map_from_idObj]
  · obtain ⟨y, hy⟩ : x ∈ Set.range (pointsMap B S hS (complementSpace B S hS iY hiY).1
        (complementHom B S hS iY hiY).hom) := by
      rwa [range_pointsMap_complementHom B S hS iY hiY]
    refine ⟨ULift.up false, y, ?_⟩
    rwa [SpacesEtale.toSpaces_map_from_idObj]

/-- The sieve generated by the excision family is a covering sieve of the spaces-étale
topology. -/
theorem generate_excisionCover_mem_topology {W : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom)
    {iX : W ⟶ X} {k : W ⟶ Z} [IsIso k] (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    Sieve.generate (excisionCover B S hS f hf iY hiY).presieve₀ ∈
      SpacesEtale.topology B S hS Y (SpacesEtale.idObj B S hS Y) :=
  Precoverage.generate_mem_toGrothendieck
    ⟨_, rfl, isCovering_excisionCover B S hS f hf iY hiY hk⟩

end Complement

end AlgebraicGeometry.Space

end
