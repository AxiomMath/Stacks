module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.TwoOpens
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nagata compactification over a Noetherian base

Over a Noetherian base, a separated morphism of finite type is compactifiable. This is the
induction of the Stacks proof of Nagata's theorem: a Noetherian scheme has a finite affine open
cover all of whose members contain one fixed dense open
(`AlgebraicGeometry.exists_finite_dense_affine_open_cover`), each member is quasi-affine and hence
compactifiable, and two compactifiable opens with dense intersection whose union is everything
glue to a compactification of the union (`AlgebraicGeometry.hasCompactification_of_two_opens`,
[Stacks, Tag 0F40]).

## Main results

* `AlgebraicGeometry.hasCompactification_of_isNoetherian`: a separated morphism of finite type to
  a Noetherian scheme is compactifiable.

## Implementation notes

The induction runs over `Finset`s of opens of the source rather than over an iterated binary
union, so the cover of `AlgebraicGeometry.exists_finite_dense_affine_open_cover` is used exactly
as that statement produces it: a finite set `F` of affine opens covering the scheme and a dense
open `U` below every member of `F`. For a subset `G ⊆ F` with `V ∈ F` the two opens that
[Stacks, Tag 0F40] is applied to are the inverse images in `V ⊔ G.sup id` of `V` and of
`G.sup id`; the inverse image of `U` lies in both and is dense, because the inclusion of an open
subscheme is an open map.

Every morphism out of a Noetherian scheme is quasi-compact, so the quasi-compactness that
`AlgebraicGeometry.HasCompactification.of_isOpenImmersion` asks of the open immersions is
automatic here and is never an extra assumption.

The base case of the induction is the empty open, which is affine and hence quasi-affine, so it
and the affine members of the cover are both handled by
`AlgebraicGeometry.HasCompactification.of_isQuasiAffine`.

## References

* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F40](https://stacks.math.columbia.edu/tag/0F40)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Compactifiability passes from an open to a smaller open.** If `V ≤ W` are opens of `X` and
`V` is compactifiable over `S`, then the inverse image of `V` in `W` — which is `V` again — is
compactifiable over `S` as an open of `W`. -/
theorem hasCompactification_restrict_of_le {X S : Scheme.{u}} (f : X ⟶ S) {V W : X.Opens}
    (hVW : V ≤ W) [QuasiCompact (Scheme.Opens.isoOfLE hVW).hom]
    (h : HasCompactification (V.ι ≫ f)) :
    HasCompactification ((W.ι ⁻¹ᵁ V).ι ≫ (W.ι ≫ f)) := by
  have : IsOpenImmersion (Scheme.Opens.isoOfLE hVW).hom := IsOpenImmersion.of_isIso _
  refine HasCompactification.of_eq ?_
    (HasCompactification.of_isOpenImmersion (Scheme.Opens.isoOfLE hVW).hom h)
  rw [← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc]

/-- **Nagata compactification over a Noetherian base.** A separated morphism of finite type to a
Noetherian scheme is compactifiable.

Cover the — Noetherian — source by finitely many affine opens each containing one fixed dense
open. Each member is affine, hence quasi-affine, hence compactifiable; adding the members one at a
time, the union so far and the next member are two opens with dense intersection, so
[Stacks, Tag 0F40] compactifies their union. -/
@[sga "4 XVII 3.2.2" "(ii)", sga "4½ Arcata 4.5.1" "more general", sga "7 XIII 2.1.6"]
theorem hasCompactification_of_isNoetherian {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] : HasCompactification f := by
  classical
  have hX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨F, U, hFaffine, hFcover, hFle, hUdense⟩ :=
    exists_finite_dense_affine_open_cover (X := X)
  -- The empty open: empty, hence affine, hence quasi-affine.
  have hbot : HasCompactification ((⊥ : X.Opens).ι ≫ f) := by
    have : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun x => x.2⟩
    exact HasCompactification.of_isQuasiAffine _
  -- A member of the cover: affine, hence quasi-affine.
  have hmem : ∀ V ∈ F, HasCompactification (V.ι ≫ f) := by
    intro V hV
    have : IsAffine ((V : X.Opens) : Scheme.{u}) := hFaffine V hV
    exact HasCompactification.of_isQuasiAffine _
  -- Compactifiability of an open depends only on the open.
  have hcongr : ∀ {V W : X.Opens}, V = W → HasCompactification (V.ι ≫ f) →
      HasCompactification (W.ι ≫ f) := by
    intro V W h hV
    subst h
    exact hV
  -- The induction over subsets of the cover.
  have key : ∀ G : Finset X.Opens, G ⊆ F → HasCompactification ((G.sup id).ι ≫ f) := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
        intro _
        exact hcongr Finset.sup_empty.symm hbot
    | @insert V G hVG ih =>
        intro hsub
        have hVF : V ∈ F := hsub (Finset.mem_insert_self V G)
        have hGF : G ⊆ F := fun W hW => hsub (Finset.mem_insert_of_mem hW)
        have hsup : (insert V G).sup id = V ⊔ G.sup id := by simp
        refine hcongr hsup.symm ?_
        rcases Finset.eq_empty_or_nonempty G with rfl | hGne
        · exact hcongr (by simp) (hmem V hVF)
        · set W : X.Opens := V ⊔ G.sup id with hW
          have hVW : V ≤ W := le_sup_left
          have hGW : G.sup id ≤ W := le_sup_right
          -- the two opens of `W`
          have hcover : (W.ι ⁻¹ᵁ V) ⊔ (W.ι ⁻¹ᵁ G.sup id) = ⊤ := by
            ext x
            show (x.1 ∈ V ∨ x.1 ∈ G.sup id) ↔ True
            exact iff_true_intro x.2
          -- the inverse image of the dense open lies in both and is dense
          obtain ⟨V₀, hV₀⟩ := hGne
          have hUV : U ≤ V := hFle V hVF
          have hUG : U ≤ G.sup id := le_trans (hFle V₀ (hGF hV₀)) (Finset.le_sup (f := id) hV₀)
          have hdense : Dense (((W.ι ⁻¹ᵁ V) ⊓ (W.ι ⁻¹ᵁ G.sup id) : W.toScheme.Opens) :
              Set W.toScheme) := by
            refine (hUdense.preimage W.ι.isOpenEmbedding.isOpenMap).mono ?_
            intro x hx
            exact ⟨hUV hx, hUG hx⟩
          exact hasCompactification_of_two_opens (W.ι ≫ f)
            (W.ι ⁻¹ᵁ V) (W.ι ⁻¹ᵁ G.sup id) hcover hdense
            (hasCompactification_restrict_of_le f hVW (hmem V hVF))
            (hasCompactification_restrict_of_le f hGW (ih hGF))
  -- The cover is everything.
  have hFtop : F.sup id = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    obtain ⟨V, hVF, hxV⟩ := hFcover x
    exact Finset.le_sup (f := id) hVF hxV
  have htop : HasCompactification ((⊤ : X.Opens).ι ≫ f) :=
    hcongr hFtop (key F Finset.Subset.rfl)
  have : IsOpenImmersion X.topIso.inv := IsOpenImmersion.of_isIso _
  refine HasCompactification.of_eq ?_
    (HasCompactification.of_isOpenImmersion X.topIso.inv htop)
  rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

end AlgebraicGeometry
