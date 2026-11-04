module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Universally closed morphisms of algebraic spaces with a one-point base

Stacks 04XW asserts that a universally closed morphism of algebraic spaces is quasi-compact.
Its proof reduces to an affine base and then, fibre by fibre, to a base which is the spectrum
of a field. This file proves the field case: if `h : W ⟶ h_V` is universally closed and the
point space of the target is a single point, then the point space of `W` is quasi-compact.

The argument is the one Mathlib runs for schemes in
`AlgebraicGeometry.compactSpace_of_universallyClosed`, transcribed to the point topology of
Tag 03BX. A covering of `|W|` by quasi-compact open sets is chosen, indexed by a set `I`; the
base is enlarged to `T = Spec(k[a_i ; i ∈ I])`; a closed set `Z` of `|T ×_{h_V} W|` is cut out
as the complement of the union of the `|T_i| × |W_i|`; and universal closedness makes the
image of `|Z|` in `|T|` closed. A basic open neighbourhood `D(g)` of the point of `T` where
every `a_i = 1` then avoids that image, and the finitely many variables occurring in `g` index
a finite subfamily of the covering which must already cover `|W|`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.contains_Spec_mvPolynomial`: a polynomial algebra over a field of
  the site, on an index set small for the site's cutoff, has spectrum again in the site.
* `AlgebraicGeometry.Space.exists_isCompact_isOpen_cover_points`: the point space of an
  algebraic space over `S` is covered by quasi-compact open sets indexed by a set small for
  the site's cutoff.
* `AlgebraicGeometry.Space.compactSpace_points_of_universallyClosed_of_subsingleton_base`: a
  universally closed morphism of algebraic spaces whose target is representable with
  one-point point space has quasi-compact source.

## Implementation notes

No declaration here carries `@[stacks 04XW]`. The statement of that tag is unconditional and
is closed in `StacksFrontier/AlgebraicGeometry/Spaces/UniversallyClosedAffineBase.lean`; what is
proved here is one of the two steps of its proof.

Three ingredients of the source's proof are *not* needed in this formulation, because
`AlgebraicGeometry.Space.UniversallyClosed` of Tag 03HI is literally a condition on maps of
point *sets*:

* the closed set `Z` is a plain subset of the point space, so the reduced closed subspace
  structure of Tag 03IQ is not constructed; instantiating the universally closed hypothesis at
  `T` gives closedness of the image of `Z` directly;
* the open sets `|T_i| × |W_i|` are intersections of preimages of open point sets, so the
  product form of open immersions in Stacks 02YV and 02YW is not used;
* the finite subfamily produced at the end is handled by `Set.Finite.isCompact_biUnion`
  applied to open sets which are already known to be quasi-compact, so no separate
  finite-union rung is needed.

The index set of the covering is the set of affine opens of a chosen atlas of `W`, whose
cardinality is bounded by the atlas's `AlgebraicGeometry.Scheme.size` by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`; this is what keeps
`Spec(k[a_i ; i ∈ I])` inside the site, via `AlgebraicGeometry.Scheme.size_Spec` and
`MvPolynomial.cardinalMk_le_max`. Note that no closure property of the cutoff beyond
`ℵ₀ < B.cutoff` is involved: the size of a spectrum is the maximum of `ℵ₀` and the
cardinality of the ring, and a maximum of finitely many cardinals below the cutoff is below
the cutoff.

Where Mathlib's scheme proof uses `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`
to lift a pair of points to the fibre product, the space proof uses Tag 03H4,
`AlgebraicGeometry.Space.exists_points_of_isPullback`; the two points are comparable over the
base because the base has a one-point point space, which replaces Mathlib's
`Subsingleton.elim` on the points of a field spectrum.

`AlgebraicGeometry.Space.pointTopology` is installed as a local instance. Inside this
namespace `IsClosed` is `AlgebraicGeometry.Space.IsClosed`, closedness of a morphism of
algebraic spaces, so topological closedness of a set of points is written `_root_.IsClosed`;
likewise `_root_.PrimeSpectrum.basicOpen` is written out because `AlgebraicGeometry` has a
`PrimeSpectrum` namespace of its own.

## References

* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 04XU](https://stacks.math.columbia.edu/tag/04XU)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A polynomial algebra over a field of the site stays in the site -/

/-- **A polynomial algebra on a small index set stays in the site.** If the spectrum of `K`
lies in the big fppf site `B` and the index set `I` has cardinality below the site's cutoff,
then the spectrum of `K[a_i ; i ∈ I]` lies in `B`.

By Stacks 000P the size of a spectrum is the maximum of `ℵ₀` and the cardinality of the ring,
and `#K[a_i ; i ∈ I] ≤ max {#K, #I, ℵ₀}`, so the conclusion is a maximum of three cardinals
each below the cutoff. -/
theorem contains_Spec_mvPolynomial {I K : Type u} [CommRing K]
    (hK : B.Contains (Spec (CommRingCat.of K))) (hI : #I < B.cutoff) :
    B.Contains (Spec (CommRingCat.of (MvPolynomial I K))) := by
  have hK' : max ℵ₀ #K < B.cutoff := (Scheme.size_Spec (CommRingCat.of K)).symm.trans_lt hK
  exact (Scheme.size_Spec (CommRingCat.of (MvPolynomial I K))).trans_lt <|
    (max_le_max le_rfl MvPolynomial.cardinalMk_le_max).trans_lt <| max_lt B.aleph0_lt_cutoff
      (max_lt (max_lt ((le_max_right ℵ₀ _).trans_lt hK') hI) B.aleph0_lt_cutoff)

/-! ### A covering of the point space by quasi-compact open sets -/

/-- **The point space of an algebraic space is covered by quasi-compact open sets.** For an
algebraic space `F` over `S` there is an index set `I` of cardinality below the site's cutoff
and a family of subsets of `|F|`, each open and quasi-compact, covering `|F|`.

The family is the family of images in `|F|` of the affine opens of a chosen atlas `U ⟶ F`.
Each image is open because an atlas is open on points by clause (3) of Tag 03BX and
quasi-compact because an affine open of a scheme is quasi-compact; together they cover because
an atlas is surjective on points by Tag 03H5. The index set is the set of affine opens of the
atlas, whose cardinality is bounded by the atlas's size. -/
theorem exists_isCompact_isOpen_cover_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (O : I → Set (points B S hS F)), #I < B.cutoff ∧
      (∀ i, IsOpen (O i)) ∧ (∀ i, IsCompact (O i)) ∧ ⋃ i, O i = Set.univ := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  let X : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj U
  let e := schemePointsHomeomorph B S hS U
  refine ⟨X.affineOpens,
    fun i => pointsMap B S hS (yoneda.obj U) f '' (e ⁻¹' (i.1 : Set X)),
    (Scheme.mk_affineOpens_le_size X).trans_lt U.left.2,
    fun i => isOpenMap_pointsMap_of_presheafEtale B S hS f hetale _
      (i.1.2.preimage e.continuous),
    fun i => (e.isCompact_preimage.mpr i.2.isCompact).image (continuous_pointsMap B S hS f),
    Set.eq_univ_of_univ_subset fun y _ => ?_⟩
  obtain ⟨w, rfl⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U f).1 hsurj y
  refine Set.mem_iUnion.2 ⟨⟨(X.affineCover.f (X.affineCover.idx (e w))).opensRange,
    isAffineOpen_opensRange _⟩, ⟨w, ?_, rfl⟩⟩
  simpa using X.affineCover.covers (e w)

/-! ### The case of a one-point base -/

/-- Killing the variables outside `g.vars` moves a point of `D(g)` to a point of `D(g)` lying
outside `D(a_i)` for every variable `a_i` not occurring in `g`. -/
theorem exists_mem_basicOpen_forall_notMem_basicOpen_X {I K : Type*} [CommRing K]
    (t : PrimeSpectrum (MvPolynomial I K)) (g : MvPolynomial I K)
    (hg : t ∈ _root_.PrimeSpectrum.basicOpen g) :
    ∃ t' : PrimeSpectrum (MvPolynomial I K), t' ∈ _root_.PrimeSpectrum.basicOpen g ∧
      ∀ i ∉ g.vars, t' ∉ _root_.PrimeSpectrum.basicOpen (MvPolynomial.X i) := by
  classical
  let φ : MvPolynomial I K →+* MvPolynomial I K :=
    (MvPolynomial.aeval fun i : I => if i ∈ g.vars then MvPolynomial.X i else 0).toRingHom
  refine ⟨_root_.PrimeSpectrum.comap φ t, ?_, fun i hi => ?_⟩
  · rw [_root_.PrimeSpectrum.mem_basicOpen]
    show φ g ∉ t.asIdeal
    rwa [show φ g = g from MvPolynomial.aeval_ite_mem_eq_self g subset_rfl]
  · rw [_root_.PrimeSpectrum.mem_basicOpen, not_not]
    show φ (MvPolynomial.X i) ∈ t.asIdeal
    simp [φ, hi]

/-- **A universally closed morphism of algebraic spaces over a one-point base has
quasi-compact source.** Let `V` be an object of the big fppf site of `S` whose point space is
a single point, and suppose the spectrum of a field `K` of the site maps to the scheme
underlying `V`. If `h : W ⟶ h_V` is a universally closed morphism of algebraic spaces over
`S`, then `|W|` is quasi-compact.

This is the field case of the proof of Stacks 04XW, which is the argument Mathlib runs for
schemes in `AlgebraicGeometry.compactSpace_of_universallyClosed`. Choose a covering of `|W|`
by quasi-compact open sets `W_i`, `i ∈ I`, and enlarge the base to
`T = Spec(K[a_i ; i ∈ I])`, which is again an object of the site. The complement `Z` of
`⋃_i (|T_i| ∩ |W_i|)` inside `|T ×_{h_V} W|` is closed, so universal closedness makes its
image in `|T|` closed, and that image misses the point `t` where every `a_i = 1`: any point of
`Z` above `t` would lie over some `W_i` while `t ∈ T_i`. A basic open `D(g)` separates `t`
from the image. If the finitely many variables of `g` indexed a family that did not cover
`|W|`, a point `x` outside it together with the point `t'` obtained from `t` by setting the
remaining variables to zero would, by Tag 03H4, lift to a point of `Z` above `t'`,
contradicting `D(g)` missing the image. Hence finitely many `W_i` cover `|W|`. -/
theorem compactSpace_points_of_universallyClosed_of_subsingleton_base
    (V : BigFppfOver B S hS) (K : Type u) [Field K]
    (hK : B.Contains (Spec (CommRingCat.of K)))
    (c : Spec (CommRingCat.of K) ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hVsub : Subsingleton (points B S hS (yoneda.obj V)))
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (_hV : IsAlgebraicSpace B S hS (yoneda.obj V)) (h : W ⟶ yoneda.obj V)
    (hh : UniversallyClosed B S hS h) :
    CompactSpace (points B S hS W) := by
  classical
  obtain ⟨I, O, hIcard, hOopen, hOcompact, hOcover⟩ :=
    exists_isCompact_isOpen_cover_points B S hS hW
  let a : B.inclusion.obj (B.obj (contains_Spec_mvPolynomial B hK hIcard)) ⟶
      B.inclusion.obj V.left :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := K) (σ := I))) ≫ c
  let T : BigFppfOver B S hS := Over.mk ((B.inclusion.preimage a) ≫ V.hom)
  let q : T ⟶ V := Over.homMk (B.inclusion.preimage a)
  let e := schemePointsHomeomorph B S hS T
  let Ti : I → ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    fun i => _root_.PrimeSpectrum.basicOpen (MvPolynomial.X i)
  let P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := pullback (yoneda.map q) h
  let fT : P ⟶ yoneda.obj T := pullback.fst (yoneda.map q) h
  let pr : P ⟶ W := pullback.snd (yoneda.map q) h
  have hfT : IsClosedMap (pointsMap B S hS P fT) :=
    hh (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) (yoneda.map q)
  set Zs : Set (points B S hS P) :=
    (⋃ i, (pointsMap B S hS P fT ⁻¹' (e ⁻¹' (Ti i : Set _))) ∩
      (pointsMap B S hS P pr ⁻¹' O i))ᶜ with hZsdef
  have hZs : _root_.IsClosed Zs :=
    isClosed_compl_iff.2 <| isOpen_iUnion fun i =>
      (((Ti i).2.preimage e.continuous).preimage (continuous_pointsMap B S hS fT)).inter
        ((hOopen i).preimage (continuous_pointsMap B S hS pr))
  set Zimg : Set ((BigFppfOver.toScheme B S hS).obj T) := e '' (pointsMap B S hS P fT '' Zs)
  let Zc : ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    ⟨Zimgᶜ, (e.isClosedMap _ (hfT Zs hZs)).isOpen_compl⟩
  let ψ : MvPolynomial I K →ₐ[K] K := MvPolynomial.aeval (fun _ => 1)
  let t : (BigFppfOver.toScheme B S hS).obj T :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht : ∀ i, t ∈ Ti i := fun i => show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    rintro ⟨y, ⟨z, hzZs, rfl⟩, hzt⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.1 hOcover (pointsMap B S hS P pr z)
    exact hzZs (Set.mem_iUnion.2 ⟨i, show e _ ∈ Ti i from hzt ▸ ht i, hi⟩)
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp _root_.PrimeSpectrum.isBasis_basic_opens htZc
  obtain ⟨t', ht'g, ht'X⟩ : ∃ t' : (BigFppfOver.toScheme B S hS).obj T, _ :=
    exists_mem_basicOpen_forall_notMem_basicOpen_X t g htU'
  have hnot : t' ∉ Zimg := hU'le ht'g
  suffices hcovσ : ⋃ i ∈ g.vars, O i = Set.univ from
    ⟨hcovσ ▸ g.vars.isCompact_biUnion fun i _ => hOcompact i⟩
  refine Set.iUnion₂_eq_univ_iff.2 fun x => ?_
  by_contra! hx
  obtain ⟨z, hz₁, hz₂⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback (yoneda.map q) h) (e.symm t') x (Subsingleton.elim _ _)
  refine hnot ⟨pointsMap B S hS P fT z, ⟨z, ?_, rfl⟩, by rw [hz₁, e.apply_symm_apply]⟩
  rw [hZsdef, Set.mem_compl_iff, Set.mem_iUnion]
  rintro ⟨i, hi₁, hi₂⟩
  rw [Set.mem_preimage, hz₁, Set.mem_preimage, e.apply_symm_apply] at hi₁
  exact ht'X i (fun hiσ => hx i hiσ (hz₂ ▸ hi₂)) hi₁

end AlgebraicGeometry.Space

end
