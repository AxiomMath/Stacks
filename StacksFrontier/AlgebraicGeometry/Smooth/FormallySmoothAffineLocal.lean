module

public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Basic

/-!
# Affine-local criteria for formal smoothness

A morphism of schemes `f : X ⟶ S` is formally smooth when it has the infinitesimal lifting
property against first-order thickenings of affine schemes,
`Stacks.Smooth.FormallySmoothScheme`. [Stacks Project, Tag 0D0F] lists four criteria for this
and asserts them equivalent:

1. `f` is formally smooth;
2. every point of `X` has an open neighbourhood `U`, lying over an open `V` of `S`, such that
   `f.resLE V U` is formally smooth;
3. for every pair of affine opens `U ⊆ X`, `V ⊆ S` with `U ≤ f ⁻¹ᵁ V` the ring map
   `Γ(S, V) ⟶ Γ(X, U)` is formally smooth;
4. there is an affine open covering of `S` and, over each member, an affine open covering of its
   inverse image, on whose charts the ring map of (3) is formally smooth.

This file proves the implications `1 → 3`, `1 → 2`, `3 → 4` and `4 → 2`, and the local existence
step of the remaining implication. Tag 02H3, the restriction of formal smoothness to a
compatible pair of opens, is `AlgebraicGeometry.FormallySmooth.resLE`.

## Main results

* `Stacks.Smooth.formallySmooth_appLE_iff_resLE`: the chart dictionary. For affine opens `V ⊆ S`
  and `W ⊆ X` with `W ≤ f ⁻¹ᵁ V`, formal smoothness of the ring map `Γ(S, V) ⟶ Γ(X, W)` is
  formal smoothness of the restricted morphism `f.resLE V W`.
* `Stacks.Smooth.formallySmooth_appLE_of_formallySmoothScheme` is `1 → 3`.
* `Stacks.Smooth.exists_opens_formallySmoothScheme_resLE` is `1 → 2`.
* `Stacks.Smooth.exists_affineOpenCover_of_formallySmooth_appLE` is `3 → 4`.
* `Stacks.Smooth.exists_opens_formallySmoothScheme_resLE_of_affineOpenCover` is `4 → 2`.
* `Stacks.Smooth.exists_isAffineOpen_lift_of_formallySmooth_appLE` is step (I) of `4 → 1`: under
  criterion (3), a lifting problem along a first-order thickening is solvable over an affine open
  neighbourhood of every point of the thickening.

## Implementation notes

The chart dictionary is the one inlined in
`AlgebraicGeometry.exists_lift_of_range_subset_of_formallySmooth`; it is stated here as an `Iff`
because the forward direction, which is what `1 → 3` needs, is not available elsewhere.
`AlgebraicGeometry.arrowResLEAppIso` is proved in Mathlib under
`backward.isDefEq.respectTransparency false` and so is used only as an argument to
`RingHom.RespectsIso.arrow_mk_iso_iff`, never under `rw`.

The index types of criterion (4) are produced as subtypes of `Scheme.affineOpens`, which lie in
`Type u` because the underlying space of a `Scheme.{u}` does. The inner covering of `f ⁻¹ᵁ V j` is
the family of *all* affine opens of `X` contained in it, whose supremum is that open because the
affine opens are a basis; that is `Stacks.Smooth.iSup_affineOpens_le_eq`.

The chart-local solver of step (I) is
`AlgebraicGeometry.exists_lift_of_range_subset_of_formallySmooth`. It lives in
`StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme` although it is a statement about formal
smoothness and not about étaleness; it is imported rather than reproved.

What criterion (4) does **not** yet give is the implication `2 → 1`, the local-to-global step.
`Stacks.Smooth.exists_isAffineOpen_lift_of_formallySmooth_appLE` produces the local solutions and
`Stacks.Smooth.exists_lift_of_isOpenCover` glues solutions that agree pairwise, but under
criterion (3) alone the local solutions need not agree: their pairwise differences are a Čech
`1`-cocycle with values in `SheafHom (a^* Ω_{X/S}) 𝒞_{T/T'}`, and correcting them requires that
cocycle to be a coboundary. That is the vanishing of `H¹(T, SheafHom (a^* Ω) 𝒞)`, which is
[Stacks Project, Tag 0D0E] for the locally projective module `a^* Ω_{X/S}` of
[Stacks Project, Tag 06B5]; neither is in the library. The analogous step under the stronger
hypothesis that `f` is smooth, where `Ω_{X/S}` is finite locally free, is carried out in
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag`.

## References

* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Smooth

/-- The affine opens of a scheme contained in a given open have that open as their supremum,
because the affine opens form a basis of the underlying space. -/
theorem iSup_affineOpens_le_eq (X : Scheme.{u}) (W : X.Opens) :
    (⨆ U : {V : X.affineOpens // (V : X.Opens) ≤ W}, (U.1 : X.Opens)) = W := by
  refine le_antisymm (iSup_le fun U => U.2) fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩

/-- **The chart dictionary for formal smoothness.** For affine opens `V` of `S` and `W` of `X`
with `W ≤ f ⁻¹ᵁ V`, the ring map `Γ(S, V) ⟶ Γ(X, W)` is formally smooth exactly when the
restricted morphism `f.resLE V W` is. The two are the same arrow up to the isomorphism
`AlgebraicGeometry.arrowResLEAppIso`, and formal smoothness of ring maps respects isomorphisms of
arrows. -/
theorem formallySmooth_appLE_iff_resLE {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ V) :
    (f.appLE V W e).hom.FormallySmooth ↔ FormallySmooth (f.resLE V W e) := by
  have hVa : IsAffine (V : Scheme.{u}) := hV
  have hWa : IsAffine (W : Scheme.{u}) := hW
  rw [formallySmooth_iff_of_isAffine]
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V W e)).symm

/-- **Criterion (1) implies criterion (3) of [Stacks Project, Tag 0D0F].** A formally smooth
morphism induces a formally smooth ring map on every compatible pair of affine opens. -/
theorem formallySmooth_appLE_of_formallySmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmoothScheme f) (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) : (f.appLE V U hUV).hom.FormallySmooth :=
  (formallySmooth_appLE_iff_resLE f hV hU hUV).mpr
    ((formallySmooth_of_formallySmoothScheme hf).resLE hUV)

/-- **Criterion (1) implies criterion (2) of [Stacks Project, Tag 0D0F].** A formally smooth
morphism is formally smooth on a neighbourhood of every point of its source; one may take the
neighbourhoods to be everything. -/
theorem exists_opens_formallySmoothScheme_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmoothScheme f) (x : X) :
    ∃ (U : X.Opens) (V : S.Opens), x ∈ U ∧ f.base x ∈ V ∧
      ∃ hUV : U ≤ f ⁻¹ᵁ V, FormallySmoothScheme (f.resLE V U hUV) :=
  ⟨⊤, ⊤, trivial, trivial, le_of_eq f.preimage_top.symm,
    AlgebraicGeometry.FormallySmooth.resLE hf ⊤ ⊤ (le_of_eq f.preimage_top.symm)⟩

/-- **Criterion (3) implies criterion (4) of [Stacks Project, Tag 0D0F].** If every compatible
pair of affine opens carries a formally smooth ring map, then such coverings exist: take all
affine opens of `S`, and over each one all affine opens of `X` contained in its inverse image. -/
theorem exists_affineOpenCover_of_formallySmooth_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ U : X.Opens, IsAffineOpen U → ∀ V : S.Opens, IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth) :
    ∃ (J : Type u) (V : J → S.Opens), IsOpenCover V ∧ (∀ j, IsAffineOpen (V j)) ∧
      ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
        (∀ i, IsAffineOpen (U i)) ∧
          ∀ i, (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.FormallySmooth :=
  ⟨S.affineOpens, fun j => (j : S.Opens), iSup_affineOpens_eq_top S, fun j => j.2, fun j =>
    ⟨{V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ (j : S.Opens)}, fun i => (i.1 : X.Opens),
      iSup_affineOpens_le_eq X _, fun i => i.1.2, fun i => hf _ i.1.2 _ j.2 _⟩⟩

/-- **Criterion (4) implies criterion (2) of [Stacks Project, Tag 0D0F].** The charts of the
coverings are themselves neighbourhoods on which the restricted morphism is formally smooth, by
the chart dictionary `Stacks.Smooth.formallySmooth_appLE_iff_resLE` and the equivalence of the two
presentations of formal smoothness. -/
theorem exists_opens_formallySmoothScheme_resLE_of_affineOpenCover {X S : Scheme.{u}} (f : X ⟶ S)
    {J : Type u} {V : J → S.Opens} (hV : IsOpenCover V) (hVaff : ∀ j, IsAffineOpen (V j))
    (hf : ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
      (∀ i, IsAffineOpen (U i)) ∧
        ∀ i, (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.FormallySmooth) (x : X) :
    ∃ (U : X.Opens) (W : S.Opens), x ∈ U ∧ f.base x ∈ W ∧
      ∃ hUW : U ≤ f ⁻¹ᵁ W, FormallySmoothScheme (f.resLE W U hUW) := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hV.iSup_eq_top ▸ Opens.mem_top (f.base x))
  obtain ⟨I, U, hU, hUaff, hUfs⟩ := hf j
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ show x ∈ f ⁻¹ᵁ V j from hj)
  refine ⟨U i, V j, hi, hj, (le_iSup U i).trans hU.le, (formallySmoothScheme_iff _).mpr ?_⟩
  exact (formallySmooth_appLE_iff_resLE f (hVaff j) (hUaff i) _).mp (hUfs i)

/-- **Step (I) of the implication `4 → 1` of [Stacks Project, Tag 0D0F].** Let `f : X ⟶ S` satisfy
criterion (3), let `i : T ⟶ T'` be a first-order thickening and let `a : T ⟶ X`, `h : T' ⟶ S`
present a lifting problem for `f`. Then every point of `T'` has an affine open neighbourhood over
which the restricted lifting problem has a solution.

One chooses affine opens `V ⊆ S` and `W ⊆ X` around the images of the point with `W ≤ f ⁻¹ᵁ V`,
on which criterion (3) gives a formally smooth ring map, and shrinks the neighbourhood so that its
inverse image in `T` maps into `W`; the shrinking is possible because a thickening is a
homeomorphism on points and so carries opens of `T` to opens of `T'`. The solution over the
shrunken neighbourhood is then
`AlgebraicGeometry.exists_lift_of_range_subset_of_formallySmooth`. -/
theorem exists_isAffineOpen_lift_of_formallySmooth_appLE {X S T T' : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ U : X.Opens, IsAffineOpen U → ∀ V : S.Opens, IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth)
    {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) (a : T ⟶ X) (h : T' ⟶ S)
    (hcomm : a ≫ f = i ≫ h) (t : T') :
    ∃ V' : T'.Opens, IsAffineOpen V' ∧ t ∈ V' ∧ ∃ b : (V' : Scheme.{u}) ⟶ X,
      b ≫ f = V'.ι ≫ h ∧ (i ∣_ V') ≫ b = (i ⁻¹ᵁ V').ι ≫ a := by
  have hci : IsClosedImmersion i := hi.1
  obtain ⟨t₀, rfl⟩ := hi.isThickening.2 t
  obtain ⟨V, hV, hsV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (f.base (a.base t₀)))
  obtain ⟨W, hW, hxW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := a.base t₀) hsV
  have homeo : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, hi.isThickening.2⟩
  obtain ⟨V', hV', htV', hV'le⟩ : ∃ V' : T'.Opens, IsAffineOpen V' ∧ i.base t₀ ∈ V' ∧
      V' ≤ (⟨i.base '' (a ⁻¹ᵁ W : Set T), homeo.isOpenMap _ (a ⁻¹ᵁ W).isOpen⟩ : T'.Opens) :=
    exists_isAffineOpen_mem_and_subset (x := i.base t₀) ⟨t₀, hxW, rfl⟩
  have hpre : i ⁻¹ᵁ V' ≤ a ⁻¹ᵁ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hV'le hx
    exact homeo.injective hxy ▸ hy
  have hV'a : IsAffine (V' : Scheme.{u}) := hV'
  obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_range_subset_of_formallySmooth f
    (isFirstOrderThickening_morphismRestrict hi V') ((i ⁻¹ᵁ V').ι ≫ a) (V'.ι ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← morphismRestrict_ι, Category.assoc])
    hV hW hWV (hf W hW V hV hWV)
    (by rintro y ⟨x, rfl⟩; rw [Scheme.Hom.comp_apply]; exact hpre x.2)
  exact ⟨V', hV', htV', b, hb₁, hb₂⟩

end Stacks.Smooth

end
