module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedPointwise
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formally étale morphisms of schemes, and flat unramified morphisms

A morphism of schemes `f : X ⟶ S` is *formally étale* when every commutative square

```
T  --g--→ X
|         |
i         f
↓         ↓
T' --p--→ S
```

with `i : T ⟶ T'` a first-order thickening of affine schemes has exactly one diagonal filler.
This is the unique-lifting counterpart of the lifting property
`Stacks.Smooth.FormallySmoothScheme`, and it is [Stacks Project, Tag 02HG].

The result proved here is [Stacks Project, Tag 04FF]: an unramified flat morphism is formally
étale. Uniqueness of the filler is formal unramifiedness,
`AlgebraicGeometry.FormallyUnramified.hom_ext`; existence is local on `T'` and glues, with the
local solutions coming from the ring-theoretic core
`Stacks.FormallyEtale.formallyEtale_of_flat` — a flat, formally unramified algebra of essentially
finite type is formally étale — applied to the affine charts supplied by
`AlgebraicGeometry.exists_formallySmooth_appLE`.

## Main definitions

* `AlgebraicGeometry.FormallyEtale` is the unique infinitesimal lifting property against
  first-order thickenings of affine schemes.

## Main results

* `AlgebraicGeometry.exists_lift_of_range_subset_of_formallySmooth`: the lifting problem along a
  first-order thickening with affine ambient scheme has a solution as soon as the given morphism
  maps into one affine chart `W ⊆ X` lying over an affine open `V ⊆ S` on which
  `Γ(S, V) ⟶ Γ(X, W)` is formally smooth.
* `AlgebraicGeometry.exists_isAffineOpen_lift_of_unramified_flat`: for `f` unramified and flat,
  every point of `T'` has an affine open neighbourhood over which the lifting problem has a
  solution.
* `AlgebraicGeometry.formallyEtale_of_unramified_flat` is Tag 04FF: an unramified flat morphism of
  schemes is formally étale.

## Implementation notes

The Stacks proof of Tag 04FF goes through conormal sheaves: for `f` unramified the diagonal
`X ⟶ X ×_S X` is an open immersion, and flatness identifies the pullback of `𝒞_{X/S}` along one
projection with the conormal sheaf of the other, which vanishes on the image of the diagonal. The
route taken here is the ring-theoretic one instead, and it needs none of the conormal-sheaf
machinery: unramifiedness of `f` is by definition a condition on affine charts, flatness holds on
*every* pair of affine charts by `AlgebraicGeometry.Flat.flat_appLE`, and
`Stacks.FormallyEtale.formallyEtale_of_flat` turns a chart satisfying both into a formally étale —
hence formally smooth — ring map. So the lifting problem is solvable over any open of `T'` whose
closed subscheme maps into a single chart.

Three ingredients from the library do the rest, all for an arbitrary morphism and with no affineness
hypothesis on it.

* `Stacks.Smooth.isFirstOrderThickening_morphismRestrict` restricts the thickening to an open of
  `T'`, and `Stacks.Smooth.morphismRestrict_comp_homOfLE` compares two such restrictions.
* `Stacks.Smooth.exists_lift_of_isOpenCover` glues solutions over an open cover of `T'` that agree
  on pairwise intersections.
* `Stacks.Smooth.lift_unique`, that is `AlgebraicGeometry.FormallyUnramified.hom_ext`, makes any
  two solutions agree, which both supplies the compatibility the gluing step needs and gives the
  uniqueness half of formal étaleness. The morphism property `FormallyUnramified f` comes from
  pointwise unramifiedness by `AlgebraicGeometry.formallyUnramified_of_unramified`.

This is exactly the shape of `Stacks.Smooth.formallySmoothScheme_of_formallyUnramified`, which
proves formal smoothness of an étale morphism; what changes is only the source of the local
solutions, which there is smoothness of `f` and here is the chart computation above. Accordingly
`AlgebraicGeometry.exists_lift_of_range_subset_of_formallySmooth` is
`Stacks.Smooth.exists_lift_of_range_subset` with the hypothesis `AlgebraicGeometry.Smooth f`
replaced by formal smoothness of the one chart that is used; the passage from the chart map
`f.appLE V W hWV` to the restricted morphism `f.resLE V W hWV`, whose global sections it is, is
`AlgebraicGeometry.arrowResLEAppIso` together with
`RingHom.FormallySmooth.respectsIso`.

The first-order thickening predicate is `Stacks.Thickenings.IsFirstOrderThickening`, which is the
one the lemmas of `Stacks.Smooth` are stated with. The library carries a second abbreviation,
`Stacks.Thickenings.IsFirstOrderThickening`, for the very same conjunction
`IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`; it is not imported here, and either spelling unfolds to the
other.

## References

* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FF](https://stacks.math.columbia.edu/tag/04FF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ S` is **formally étale** when it has the unique infinitesimal
lifting property: for every first-order thickening `i : T ⟶ T'` of affine schemes, every
commutative square
```
T  --g--→ X
|         |
i         f
↓         ↓
T' --p--→ S
```
has exactly one diagonal filler `h : T' ⟶ X`, that is exactly one morphism with `i ≫ h = g` and
`h ≫ f = p`. -/
@[stacks 02HG, ega "IV 17.1.1", sga "3 XI 1.1"]
abbrev FormallyEtale {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ ⦃T T' : Scheme.{u}⦄ [IsAffine T] [IsAffine T'] (i : T ⟶ T')
    (_hi : Stacks.Thickenings.IsFirstOrderThickening i) (p : T' ⟶ S) (g : T ⟶ X),
      g ≫ f = i ≫ p → ∃! h : T' ⟶ X, i ≫ h = g ∧ h ≫ f = p

/-- **A lifting problem that fits in a single formally smooth chart has a solution.** Let
`f : X ⟶ S` be a morphism of schemes and let `i : T ⟶ T'` be a first-order thickening with `T'`
affine, presenting a lifting problem through `a : T ⟶ X` and `h : T' ⟶ S`. If `a` maps into an
affine open `W` of `X` which lies over an affine open `V` of `S`, and `Γ(S, V) ⟶ Γ(X, W)` is
formally smooth, then the problem has a solution.

This is `Stacks.Smooth.exists_lift_of_range_subset` with smoothness of `f` weakened to formal
smoothness of the single chart that the proof uses: the chart map `f.appLE V W hWV` is the map on
global sections of `f.resLE V W hWV` by `AlgebraicGeometry.arrowResLEAppIso`, so the affine case
`Stacks.Smooth.formallySmoothScheme_of_formallySmooth` applies to the restriction. That `h` maps
into `V` is automatic: a thickening is surjective on points, so `h` and `a ≫ f` have the same
image. -/
@[sga "3 IX 3.3" "special case"]
theorem exists_lift_of_range_subset_of_formallySmooth {X S T T' : Scheme.{u}} (f : X ⟶ S)
    {i : T ⟶ T'} (hi : Stacks.Thickenings.IsFirstOrderThickening i) [IsAffine T'] (a : T ⟶ X)
    (h : T' ⟶ S) (hcomm : a ≫ f = i ≫ h) {V : S.Opens} {W : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V)
    (hfs : (f.appLE V W hWV).hom.FormallySmooth) (hran : Set.range a.base ⊆ (W : Set X)) :
    ∃ b : T' ⟶ X, b ≫ f = h ∧ i ≫ b = a := by
  have hci : IsClosedImmersion i := hi.1
  have hVa : IsAffine (V : Scheme.{u}) := hV
  have hWa : IsAffine (W : Scheme.{u}) := hW
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hranW : Set.range a.base ⊆ Set.range W.ι.base := by
    rwa [Scheme.Opens.range_ι]
  have hranV : Set.range h.base ⊆ Set.range V.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨x₀, rfl⟩ := hi.isThickening.2 x
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    exact hWV (hran ⟨x₀, rfl⟩)
  have hfs' : Stacks.Smooth.FormallySmooth (f.resLE V W hWV) := by
    rw [Stacks.Smooth.formallySmooth_iff_of_isAffine]
    exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V W hWV)).mpr hfs
  obtain ⟨b₀, hb₁, hb₂⟩ :=
    Stacks.Smooth.formallySmoothScheme_of_formallySmooth hfs' (T := T) (T' := T')
      inferInstance inferInstance i hi (IsOpenImmersion.lift W.ι a hranW)
      (IsOpenImmersion.lift V.ι h hranV) (by
        rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
          IsOpenImmersion.lift_fac, ← Category.assoc, IsOpenImmersion.lift_fac, hcomm])
  refine ⟨b₀ ≫ W.ι, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hWV, ← Category.assoc, hb₁,
      IsOpenImmersion.lift_fac]
  · rw [← Category.assoc, hb₂, IsOpenImmersion.lift_fac]

/-- **A lifting problem for a flat unramified morphism is solvable locally on the thickening.**
Let `f : X ⟶ S` be unramified and flat, let `i : T ⟶ T'` be a first-order thickening and let
`a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem for `f`. Then every point of `T'` has an
affine open neighbourhood `V'` over which the restricted lifting problem has a solution.

The chart around the image of the point is the one supplied by
`AlgebraicGeometry.exists_formallySmooth_appLE`, and `V'` is shrunk so that `i ⁻¹ᵁ V'` maps into
it, which is possible because a thickening is a homeomorphism on points and so pushes an open of
`T` forward to an open of `T'`. -/
theorem exists_isAffineOpen_lift_of_unramified_flat {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [Unramified f] [Flat f] {i : T ⟶ T'} (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (a : T ⟶ X) (h : T' ⟶ S) (hcomm : a ≫ f = i ≫ h) (t : T') :
    ∃ V' : T'.Opens, IsAffineOpen V' ∧ t ∈ V' ∧ ∃ b : (V' : Scheme.{u}) ⟶ X,
      b ≫ f = V'.ι ≫ h ∧ (i ∣_ V') ≫ b = (i ⁻¹ᵁ V').ι ≫ a := by
  have hci : IsClosedImmersion i := hi.1
  obtain ⟨t₀, rfl⟩ := hi.isThickening.2 t
  obtain ⟨W, V, hW, hV, hWV, hxW, hfs⟩ := exists_formallySmooth_appLE f (a.base t₀)
  have homeo : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, hi.isThickening.2⟩
  set Ω : T'.Opens := ⟨i.base '' (a ⁻¹ᵁ W : Set T), homeo.isOpenMap _ (a ⁻¹ᵁ W).isOpen⟩
  obtain ⟨V', hV', htV', hV'le⟩ : ∃ V' : T'.Opens, IsAffineOpen V' ∧ i.base t₀ ∈ V' ∧ V' ≤ Ω := by
    obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'le⟩ :=
      T'.isBasis_affineOpens.exists_subset_of_mem_open (show i.base t₀ ∈ Ω from ⟨t₀, hxW, rfl⟩)
        Ω.isOpen
    exact ⟨V', hV', htV', hV'le⟩
  have hpre : i ⁻¹ᵁ V' ≤ a ⁻¹ᵁ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hV'le hx
    exact homeo.injective hxy ▸ hy
  have hV'a : IsAffine (V' : Scheme.{u}) := hV'
  obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_range_subset_of_formallySmooth f
    (Stacks.Smooth.isFirstOrderThickening_morphismRestrict hi V') ((i ⁻¹ᵁ V').ι ≫ a) (V'.ι ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← morphismRestrict_ι, Category.assoc])
    hV hW hWV hfs (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hpre x.2)
  exact ⟨V', hV', htV', b, hb₁, hb₂⟩

/-- **An unramified flat morphism of schemes is formally étale.** Existence of the filler is
local on the thickening by `AlgebraicGeometry.exists_isAffineOpen_lift_of_unramified_flat`; the
local fillers agree on overlaps by `Stacks.Smooth.lift_unique` applied to the restricted
thickening, so they glue by `Stacks.Smooth.exists_lift_of_isOpenCover`; and that same uniqueness
is the `∃!`. -/
@[stacks 04FF]
theorem formallyEtale_of_unramified_flat {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] [Flat f] :
    FormallyEtale f := by
  have hfu : FormallyUnramified f := formallyUnramified_of_unramified f
  intro T T' _ _ i hi p g hcomm
  have hci : IsClosedImmersion i := hi.1
  choose V' hV'affine htV' b hbf hba using
    exists_isAffineOpen_lift_of_unramified_flat f hi g p hcomm
  have hcover : TopologicalSpace.IsOpenCover V' :=
    top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, htV' x⟩
  have hbb : ∀ j k : T', T'.homOfLE (inf_le_left : V' j ⊓ V' k ≤ V' j) ≫ b j =
      T'.homOfLE (inf_le_right : V' j ⊓ V' k ≤ V' k) ≫ b k := by
    intro j k
    have hres : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
        (i ∣_ (V' j ⊓ V' k)) ≫ T'.homOfLE e ≫ b l = (i ⁻¹ᵁ (V' j ⊓ V' k)).ι ≫ g := by
      intro l e
      rw [← Category.assoc, Stacks.Smooth.morphismRestrict_comp_homOfLE, Category.assoc, hba l,
        ← Category.assoc, Scheme.homOfLE_ι]
    have hresf : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
        (T'.homOfLE e ≫ b l) ≫ f = (V' j ⊓ V' k).ι ≫ p := by
      intro l e
      rw [Category.assoc, hbf l, ← Category.assoc, Scheme.homOfLE_ι]
    have hthick := Stacks.Smooth.isFirstOrderThickening_morphismRestrict hi (V' j ⊓ V' k)
    have hci' : IsClosedImmersion (i ∣_ (V' j ⊓ V' k)) := hthick.1
    exact FormallyUnramified.hom_ext (i ∣_ (V' j ⊓ V' k)) ⟨2, hthick.2⟩ f
      (by rw [hres j inf_le_left, hres k inf_le_right])
      (by rw [hresf j inf_le_left, hresf k inf_le_right])
  obtain ⟨c, hc₁, hc₂⟩ :=
    Stacks.Smooth.exists_lift_of_isOpenCover f i g p V' hcover b hbf hba hbb
  exact ⟨c, ⟨hc₂, hc₁⟩, fun d hd => Stacks.Smooth.lift_unique f hi hd.2 hc₁ hd.1 hc₂⟩

end AlgebraicGeometry

end
