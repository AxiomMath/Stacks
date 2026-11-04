module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct

/-!
# A clopen set of points decomposes an algebraic space into complementary clopen subspaces

Let `F` be an algebraic space over a scheme `S` and let `T` be a subset of its point space
`|F|` of Tag 03BU which is both open and closed. This file proves that the two open subspaces
of Tag 03BZ cut out by `T` and by its complement are *both* open and closed subspaces of `F`
in the sense of Stacks 02YU, that their join sheafifies to the whole of `F`, and that their
meet is the sheafification of the bottom subfunctor.

That package is exactly the shape in which Stacks 082H and Stacks 0ADU state the
decomposition `U ×_Y X = W ⨿ V`, and a clopen set of points is exactly the datum those proofs
produce: in Stacks 082H the piece `V` arises as the *image* of a scheme which is étale onto it
and finite over the base — open by Tag 03IR and closed by Tag 04NX — and the complementary
piece `W` is defined as the set-theoretic complement `X \ V`. Deducing the decomposition from
a clopen set of points therefore follows the source argument, whereas deducing it from a
coproduct presentation of `F` (as
`AlgebraicGeometry.Sheaf.exists_clopen_subspace_decomposition_of_isColimit_cofan` does)
assumes a differently shaped and strictly stronger datum which the source never constructs.

## Main definitions

No new definitions are introduced. The two subspaces are
`AlgebraicGeometry.Space.openSubspaceOfPoints` applied to `T` and to `Tᶜ`.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap`:
  a relative open immersion of presheaves whose image on points is closed is a relative closed
  immersion. This is the missing half of the Tag 03BZ correspondence: Tag 03BZ identifies open
  subspaces with open sets of points, and this says that such a subspace is in addition a
  closed subspace as soon as its set of points is closed.
* `AlgebraicGeometry.Space.isClosedSubspace_openSubspaceOfPoints`: the subspace cut out by a
  clopen set of points is a closed subspace.
* `AlgebraicGeometry.Space.sheafify_sup_openSubspaceOfPoints_eq_top` and
  `AlgebraicGeometry.Space.inf_openSubspaceOfPoints_eq_sheafify_bot`: the two lattice
  identities for the pieces cut out by a clopen set of points and its complement.
* `AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isClopen`: the whole
  package, with the point sets of the two pieces identified as `T` and `Tᶜ`.

## Implementation notes

The closed-immersion criterion is where the geometry sits. A represented base change of a
relative open immersion `f` along a section `q` of the target over an object `A` of the site is
an open immersion of schemes `b ⟶ A`, and its image in `A` is computed to be the image under
the Tag 03BX bijection `|h_A| ≃ A` of the preimage along `q` of the point set of `f`
(`AlgebraicGeometry.Space.range_snd_eq_image_preimage_range_pointsMap`). One inclusion is the
cartesian square read on points; the other is the surjectivity of the comparison map from the
points of a fibre product to the fibre product of the point sets
(`AlgebraicGeometry.Space.exists_points_of_isPullback`), which lifts a point of `A` whose image
lies in the point set of `f` to a point of `b`. Closedness of the point set then transfers to
closedness of that image through
`AlgebraicGeometry.Space.isClosed_pointTopology_yoneda_iff_isClosed_image`, and an open
immersion with closed image is a closed immersion
(`AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`).

Both lattice identities need their sheafification, for the two reasons recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenSubfunctorDecomposition.lean`. For the join, a
section over a test object `A` which meets both `T` and `Tᶜ` lies in neither piece before
refinement; the refinement used is the two-member Zariski cover of `A` by the open subschemes
cutting out the preimages of `T` and of `Tᶜ`, which cover because the two sets do and which is
an fppf covering sieve by
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`. For the meet, a
section lying in both pieces has all of its points in `T ∩ Tᶜ = ∅`, so the test object has no
points, and an object of the site with no points is covered by the empty sieve
(`AlgebraicGeometry.BigFppfOver.bot_mem_topology`); conversely a covering by the empty sieve
forces the test object to have no points, since every covering sieve is jointly surjective on
points, and then every section lies in every piece.

Nothing here carries a Stacks tag. Stacks 082H, 0ADU and 02WO assert the *existence* of such a
decomposition; this file supplies the step from a clopen set of points to the properties their
conclusions are phrased with, not the construction of that set.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An open immersion with closed point set is a closed immersion -/

section ClosedImmersion

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of a represented base change of a relative open immersion, read on points.**
For a relative open immersion `f` of presheaves on the big fppf site of `S` and a section `q`
of its target over an object `A` of the site, the image in `A` of the chosen represented base
change is the image under the Tag 03BX bijection of the preimage along `q` of the point set of
`f`.

The inclusion of the image is the cartesian square read on points. The reverse inclusion is the
surjectivity of the comparison map of
`AlgebraicGeometry.Space.exists_points_of_isPullback`: a point of `A` whose image lies in the
point set of `f` is the projection of a point of the base change. -/
theorem range_snd_eq_image_preimage_range_pointsMap (f : F ⟶ G)
    (hopen : IsOpenImmersion B S hS f) {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ G) :
    Set.range ((BigFppfOver.toScheme B S hS).map (hopen.rep.snd q)) =
      pointsToScheme B S hS A ''
        (pointsMap B S hS (yoneda.obj A) q ⁻¹' Set.range (pointsMap B S hS F f)) := by
  have sq := hopen.rep.isPullback q
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨z, rfl⟩
    set w := (pointsEquivScheme B S hS (hopen.rep.pullback q)).symm z with hw
    have hwz : pointsToScheme B S hS (hopen.rep.pullback q) w = z :=
      (pointsEquivScheme B S hS (hopen.rep.pullback q)).apply_symm_apply z
    refine ⟨pointsMap B S hS (yoneda.obj (hopen.rep.pullback q))
      (yoneda.map (hopen.rep.snd q)) w, ?_, ?_⟩
    · show pointsMap B S hS (yoneda.obj A) q _ ∈ Set.range (pointsMap B S hS F f)
      rw [← pointsMap_comp_apply, ← sq.w, pointsMap_comp_apply]
      exact ⟨_, rfl⟩
    · rw [pointsToScheme_pointsMap_yoneda, hwz]
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := hw
    obtain ⟨r, -, hr2⟩ := exists_points_of_isPullback B S hS sq v w hv
    exact ⟨pointsToScheme B S hS (hopen.rep.pullback q) r, by
      rw [← pointsToScheme_pointsMap_yoneda, hr2]⟩

/-- **A relative open immersion with closed point set is a relative closed immersion.** If `f`
is an open immersion of presheaves on the big fppf site of `S` in the sense of Stacks 02YU and
the image of its point set is closed in the point space of its target, then `f` is a closed
immersion.

Each represented base change of `f` is an open immersion of schemes whose image is, by
`AlgebraicGeometry.Space.range_snd_eq_image_preimage_range_pointsMap`, the transport of a
preimage of the point set of `f`; that preimage is closed because the induced map on points is
continuous, and an open immersion of schemes with closed image is a closed immersion. -/
theorem isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap (f : F ⟶ G)
    (hopen : IsOpenImmersion B S hS f)
    (hclosed : IsClosed (Set.range (pointsMap B S hS F f))) :
    IsClosedImmersion B S hS f := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun {A} q => ?_
  refine ⟨hopen.rep.pullback q, hopen.rep.fst q, hopen.rep.snd q, hopen.rep.isPullback q, ?_⟩
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hopen.rep.snd q)) := hopen.property_snd q
  show _root_.AlgebraicGeometry.IsClosedImmersion _
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [range_snd_eq_image_preimage_range_pointsMap B S hS f hopen q]
  exact (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS A _).mp
    (hclosed.preimage (continuous_pointsMap B S hS q))

end ClosedImmersion

/-! ### The subspace cut out by a clopen set of points -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The subspace cut out by a clopen set of points is a closed subspace.** Combined with
`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints`, the subfunctor cut out by a
clopen set of points of an algebraic space over `S` is both an open and a closed subspace. -/
theorem isClosedSubspace_openSubspaceOfPoints (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) (hTo : IsOpen T) (hTc : IsClosed T) :
    IsClosedSubspace B S hS (openSubspaceOfPoints B S hS F T) :=
  ⟨(isOpenSubspace_openSubspaceOfPoints B S hS hF T hTo).1,
    isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap B S hS _
      (presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS T hTo)
      ((range_pointsMap_ι_openSubspaceOfPoints B S hS T).symm ▸ hTc)⟩

/-! ### The two lattice identities -/

/-- An open set of points cuts out, on a refinement of any test object, a piece containing the
restricted section, and that refinement is the open subscheme of points landing in the set. -/
private theorem exists_restrict_mem_openSubspaceOfPoints (T : Set (points B S hS F))
    (hT : IsOpen T) (A : BigFppfOver B S hS) (x : F.obj (op A)) :
    ∃ (b : BigFppfOver B S hS) (i : b ⟶ A),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      (∀ p : FieldValuedPoint B S hS (yoneda.obj A),
        pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm x) (p.class B S hS (yoneda.obj A)) ∈ T ↔
          schemePoint B S hS A p ∈ Set.range ((BigFppfOver.toScheme B S hS).map i)) ∧
      F.map i.op x ∈ (openSubspaceOfPoints B S hS F T).obj (op b) := by
  obtain ⟨V, hVopen, hmem⟩ := (isOpen_pointTopology_iff B S hS T).mp hT A (yonedaEquiv.symm x)
  obtain ⟨b, i, hoi, hr, -⟩ := exists_restrict_bigFppfOver A ⟨V, hVopen⟩
  have hr' : Set.range ((BigFppfOver.toScheme B S hS).map i) = V := hr
  simp only [Set.mem_preimage] at hmem
  rw [← hr'] at hmem
  refine ⟨b, i, hoi, hmem, ?_⟩
  have hkey : yonedaEquiv.symm (F.map i.op x) = yoneda.map i ≫ yonedaEquiv.symm x :=
    yonedaEquiv_symm_map i.op x
  rw [mem_openSubspaceOfPoints_iff]
  show Set.range (pointsMap B S hS (yoneda.obj b) (yonedaEquiv.symm (F.map i.op x))) ⊆ T
  rw [hkey]
  rintro y ⟨w, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  rw [pointsMap_comp_apply, pointsMap_class,
    hmem (FieldValuedPoint.map B S hS (yoneda.obj b) (yoneda.map i) p),
    schemePoint_map_yoneda]
  exact ⟨_, rfl⟩

/-- A section lies in the sheafification of the bottom subfunctor exactly when the empty sieve
covers the object it lives on. -/
private theorem mem_sheafify_bot_iff_bot_mem {A : BigFppfOver B S hS} (x : F.obj (op A)) :
    x ∈ ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).obj (op A) ↔
      (⊥ : Sieve A) ∈ BigFppfOver.topology B S hS A := by
  have hsieve : (⊥ : Subfunctor F).sieveOfSection x = ⊥ :=
    le_antisymm (fun _ _ h => h) bot_le
  have h : (⊥ : Subfunctor F).sieveOfSection x ∈ BigFppfOver.topology B S hS A ↔
      (⊥ : Sieve A) ∈ BigFppfOver.topology B S hS A := by rw [hsieve]
  exact h

/-- An object of the site carrying a section of the subfunctors cut out by a set of points and
by its complement has no points. -/
private theorem isEmpty_of_mem_inf {T : Set (points B S hS F)} {A : BigFppfOver B S hS}
    {x : F.obj (op A)}
    (hx : x ∈ (openSubspaceOfPoints B S hS F Tᶜ ⊓ openSubspaceOfPoints B S hS F T).obj (op A)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := by
  obtain ⟨hW, hV⟩ := hx
  refine ⟨fun y => ?_⟩
  obtain ⟨w, -⟩ := surjective_pointsToScheme B S hS A y
  exact hW ⟨w, rfl⟩ (hV ⟨w, rfl⟩)

/-- An object of the site with no points carries a section of the subfunctor cut out by any set
of points. -/
private theorem mem_openSubspaceOfPoints_of_isEmpty (T : Set (points B S hS F))
    {A : BigFppfOver B S hS} (hA : IsEmpty ((BigFppfOver.toScheme B S hS).obj A))
    (x : F.obj (op A)) : x ∈ (openSubspaceOfPoints B S hS F T).obj (op A) := by
  rintro y ⟨w, rfl⟩
  exact (hA.false (pointsToScheme B S hS A w)).elim

/-- **The pieces cut out by a clopen set of points and its complement locally cover.** Their
join sheafifies to the whole presheaf.

The sheafification is not removable: a section over a test object which the two sets split into
two nonempty halves lies in neither piece until it is restricted. The refinement is the
two-member Zariski cover of the test object by the open subschemes cutting out the preimages of
the two sets, which is an fppf covering sieve. -/
theorem sheafify_sup_openSubspaceOfPoints_eq_top (T : Set (points B S hS F))
    (hTo : IsOpen T) (hTc : IsClosed T) :
    (openSubspaceOfPoints B S hS F Tᶜ ⊔ openSubspaceOfPoints B S hS F T).sheafify
      (BigFppfOver.topology B S hS) = ⊤ := by
  refine le_antisymm le_top fun Aop x _ => ?_
  obtain ⟨A⟩ := Aop
  obtain ⟨bT, iT, hoiT, hT, hmemT⟩ := exists_restrict_mem_openSubspaceOfPoints B S hS T hTo A x
  obtain ⟨bC, iC, hoiC, hC, hmemC⟩ :=
    exists_restrict_mem_openSubspaceOfPoints B S hS Tᶜ hTc.isOpen_compl A x
  set Xc : Bool → BigFppfOver B S hS := fun i => Bool.rec bC bT i with hXc
  set fc : ∀ i, Xc i ⟶ A := fun i => Bool.rec (motive := fun j => Xc j ⟶ A) iC iT i with hfc
  have hsieve : Sieve.ofArrows Xc fc ∈ BigFppfOver.topology B S hS A := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS fc
      (fun i => by cases i <;> assumption) fun y => ?_
    obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A y
    by_cases hmem : pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm x)
        (p.class B S hS (yoneda.obj A)) ∈ T
    · exact ⟨true, hp ▸ (hT p).mp hmem⟩
    · exact ⟨false, hp ▸ (hC p).mp hmem⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hsieve
  rw [Sieve.generate_le_iff]
  rintro Z g ⟨i⟩
  cases i with
  | false => exact Or.inl hmemC
  | true => exact Or.inr hmemT

/-- **The pieces cut out by a set of points and its complement are locally disjoint.** Their
meet is the sheafification of the bottom subfunctor.

It is the sheafification of `⊥` and not `⊥` itself because an object of the site whose
underlying scheme has no points carries a section of every subfunctor cut out by a set of
points; the content of the statement is that those objects are the only ones carrying a section
of both pieces. -/
theorem inf_openSubspaceOfPoints_eq_sheafify_bot (T : Set (points B S hS F)) :
    openSubspaceOfPoints B S hS F Tᶜ ⊓ openSubspaceOfPoints B S hS F T
      = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS) := by
  refine le_antisymm ?_ ?_
  · rintro ⟨A⟩ x hx
    rw [mem_sheafify_bot_iff_bot_mem]
    exact BigFppfOver.bot_mem_topology A (isEmpty_of_mem_inf B S hS hx)
  · rintro ⟨A⟩ x hx
    rw [mem_sheafify_bot_iff_bot_mem] at hx
    have hA : IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := by
      refine ⟨fun y => ?_⟩
      obtain ⟨Y, f, hf, -⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hx y
      exact hf
    exact ⟨mem_openSubspaceOfPoints_of_isEmpty B S hS Tᶜ hA x,
      mem_openSubspaceOfPoints_of_isEmpty B S hS T hA x⟩

/-! ### The decomposition -/

/-- **A clopen set of points decomposes an algebraic space into complementary open-and-closed
subspaces.** For an algebraic space `F` over `S` and a subset `T` of its point space which is
both open and closed, there are two subfunctors of `F` which are open subspaces and closed
subspaces in the sense of Stacks 02YU, whose join sheafifies to the whole of `F`, whose meet is
the sheafification of the bottom subfunctor, and whose point sets are `T` and its complement.

This is the shape in which Stacks 082H and Stacks 0ADU state the decomposition
`U ×_Y X = W ⨿ V`, deduced from the datum those proofs actually construct: a set of points
which is open because it is the image of an étale morphism (Tag 03IR) and closed because the
source is universally closed over the base (Tag 04NX). -/
theorem exists_clopen_subspace_decomposition_of_isClopen (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) (hTo : IsOpen T) (hTc : IsClosed T) :
    ∃ W V : Subfunctor F,
      IsOpenSubspace B S hS W ∧ IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS V.toFunctor V.ι) = T ∧
      Set.range (pointsMap B S hS W.toFunctor W.ι) = Tᶜ :=
  ⟨openSubspaceOfPoints B S hS F Tᶜ, openSubspaceOfPoints B S hS F T,
    isOpenSubspace_openSubspaceOfPoints B S hS hF Tᶜ hTc.isOpen_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hF Tᶜ hTc.isOpen_compl hTo.isClosed_compl,
    isOpenSubspace_openSubspaceOfPoints B S hS hF T hTo,
    isClosedSubspace_openSubspaceOfPoints B S hS hF T hTo hTc,
    sheafify_sup_openSubspaceOfPoints_eq_top B S hS T hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS T,
    range_pointsMap_ι_openSubspaceOfPoints B S hS T,
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ⟩

end AlgebraicGeometry.Space

end
