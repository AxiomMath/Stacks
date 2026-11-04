module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Peeling
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.SquareGlueing

/-!
# Glueing near a closed point of an open subscheme, in terms of the ambient scheme

[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA) is a statement about a scheme and
a closed point of it.  The induction which proves
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) applies it to an *open subscheme*
`W` of a scheme `S`, at a closed point `t` of `S` lying in `W`.  The glueing data of Tag 0BPA
over `W` is then written in terms of `W`'s own opens, `W`'s own local ring at the point and
`W`'s own punctured local scheme, while the induction needs it written in terms of `S`: the
open `V = W ∖ {t}` of `S`, the local ring `𝒪_{S, t}` and the preimage of `V` in
`Spec 𝒪_{S, t}`.

This file reconciles the two.  The three comparison isomorphisms are an isomorphism of `V` with
the punctured open of `W` at `t`, the isomorphism of local schemes
`Spec 𝒪_{S, t} ≅ Spec 𝒪_{W, t}` induced by the open immersion, and the restriction of the latter
to the two descriptions of the overlap.
`AlgebraicGeometry.restrictionFunctorOfSquare_isEquivalence_of_iso` then carries Tag 0BPA across.

The resulting statement is about an arbitrary factorization `V ⟶ W` of the inclusion of `V` and
an arbitrary factorization `Spec 𝒪_{S, t} ⟶ W` of `Scheme.fromSpecStalk`, so that it applies
to whichever maps the ambient situation supplies rather than to one particular construction of
them; both are unique, because the inclusion of `W` is a monomorphism.

## Main definitions

* `AlgebraicGeometry.isoPreimageOfLE`: an open contained in another is isomorphic to its
  preimage in the larger one.
* `AlgebraicGeometry.specStalkIsoOfMem`: the local scheme of a scheme at a point of an open
  subscheme agrees with the local scheme of that open subscheme there.
* `AlgebraicGeometry.opensIsoOfPreimageEq`: an open of the source of an isomorphism of schemes
  is isomorphic to an open of the target of which it is the preimage.

## Main results

* `AlgebraicGeometry.restrictionFunctorAtPoint_eq_restrictionFunctorOfSquare`: the canonical
  restriction functor of Tag 0BPA is the canonical functor of the base-change square of the
  inclusion of the open and the map from the local scheme.
* `AlgebraicGeometry.restrictionFunctorOfSquare_isEquivalence_of_ambientOpen`: **Stacks
  Project, Lemma 32.14.1 (0BPA)** over an open subscheme `W` of `S`, written in terms of `S`:
  for a closed point `t` of `S` lying in `W` whose complement `V` in `W` has quasi-compact
  inclusion in `S`, the canonical functor from schemes of finite presentation over `W` to the
  glueing data of the square `V ⟵ Spec 𝒪_{S,t} ∩ V ⟶ Spec 𝒪_{S,t}` over `W` is an equivalence.

## Implementation notes

The point of `W` under the closed point `t` of `S` is obtained by destructing an existential,
rather than written as `⟨t, htW⟩`: the membership `t ∈ W` is phrased through the `SetLike`
instance of `TopologicalSpace.Opens` while the points of `W` as a scheme are the elements of the
underlying *set* of `W`, so the two spellings of the subtype are definitionally equal but not
syntactically equal, and the second one makes instance search and rewriting fail.

## References

* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- The canonical restriction functor of **Stacks Project, Tag 0BPA** is the canonical functor
attached to the base-change square of the inclusion of the open `U` and the map from the local
scheme at `s`. -/
theorem restrictionFunctorAtPoint_eq_restrictionFunctorOfSquare (S : Scheme.{u}) (U : S.Opens)
    (s : S) :
    GlueingNearPoint.restrictionFunctorAtPoint S U s =
      restrictionFunctorOfSquare U.ι (S.fromSpecStalk s)
        (morphismRestrict_ι (S.fromSpecStalk s) U) :=
  rfl

/-! ### Comparison isomorphisms for an open subscheme -/

/-- A point of an open subscheme lying over a closed point of the ambient scheme is closed: it is
cut out by that closed point along the inclusion of the open. -/
theorem isClosed_singleton_of_mem {S : Scheme.{u}} (W : S.Opens) {t : S}
    (ht : IsClosed ({t} : Set S)) (p : W.toScheme) (hp : W.ι p = t) :
    IsClosed ({p} : Set W.toScheme) := by
  have hpre : (W.ι ⁻¹' ({t} : Set S)) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨hp, fun _ hx ↦ W.ι.isOpenEmbedding.injective (hx.trans hp.symm)⟩
  rw [← hpre]
  exact ht.preimage W.ι.continuous

/-- The complement, in the ambient scheme, of a closed point inside an open subscheme pulls back
to the punctured open of that open subscheme at the point. -/
theorem preimage_ι_eq_puncturedOpen {S : Scheme.{u}} (W : S.Opens) {t : S} (V : S.Opens)
    (hV : (V : Set S) = (W : Set S) ∩ ({t}ᶜ : Set S)) (p : W.toScheme) (hp : W.ι p = t)
    (hcl : IsClosed ({p} : Set W.toScheme)) :
    W.ι ⁻¹ᵁ V = GlueingNearPoint.puncturedOpen hcl := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
  show W.ι x ∈ (V : Set S) ↔ x ∈ ({p} : Set W.toScheme)ᶜ
  rw [hV]
  refine ⟨fun hx hxe ↦ hx.2 ?_, fun hx ↦ ⟨x.2, fun hxe ↦ hx ?_⟩⟩
  · rw [Set.mem_singleton_iff] at hxe
    rw [hxe]
    exact hp
  · exact W.ι.isOpenEmbedding.injective (hxe.trans hp.symm)

/-- An open of the ambient scheme which is the intersection of `W` with the complement of a point
is contained in `W`. -/
theorem le_of_eq_inter_compl {S : Scheme.{u}} (W : S.Opens) {t : S} (V : S.Opens)
    (hV : (V : Set S) = (W : Set S) ∩ ({t}ᶜ : Set S)) : V ≤ W := by
  have hs : (V : Set S) ⊆ (W : Set S) := by
    rw [hV]
    exact Set.inter_subset_left
  exact hs

/-- The isomorphism between an open `V` of `S` contained in `W` and its preimage in `W`. -/
noncomputable def isoPreimageOfLE {S : Scheme.{u}} (W V : S.Opens) (hVW : V ≤ W) :
    V.toScheme ≅ (W.ι ⁻¹ᵁ V).toScheme :=
  (S.homOfLE hVW).isoOpensRange ≪≫ W.toScheme.isoOfEq (Scheme.opensRange_homOfLE hVW)

/-- The isomorphism `isoPreimageOfLE` followed by the inclusion of the preimage of `V` in `W` is
the inclusion `S.homOfLE hVW` of `V` into `W`. -/
@[reassoc (attr := simp)]
theorem isoPreimageOfLE_hom_ι {S : Scheme.{u}} (W V : S.Opens) (hVW : V ≤ W) :
    (isoPreimageOfLE W V hVW).hom ≫ (W.ι ⁻¹ᵁ V).ι = S.homOfLE hVW := by
  simp [isoPreimageOfLE]

/-- The isomorphism of local schemes induced by an open immersion: the local scheme of `S` at a
point of an open subscheme `W` agrees with the local scheme of `W` there. -/
noncomputable def specStalkIsoOfMem {S : Scheme.{u}} (W : S.Opens) (p : W.toScheme) :
    Spec (S.presheaf.stalk (W.ι p)) ≅ Spec (W.toScheme.presheaf.stalk p) :=
  (asIso (Spec.map (W.ι.stalkMap p))).symm

/-- The forward map of `specStalkIsoOfMem` is the inverse of `Spec` of the stalk map of `W.ι`. -/
theorem specStalkIsoOfMem_hom {S : Scheme.{u}} (W : S.Opens) (p : W.toScheme) :
    (specStalkIsoOfMem W p).hom = CategoryTheory.inv (Spec.map (W.ι.stalkMap p)) :=
  rfl

/-- The isomorphism of local schemes is compatible with any factorization through `W` of the map
from the local scheme of the ambient scheme. -/
theorem specStalkIsoOfMem_hom_fromSpecStalk {S : Scheme.{u}} (W : S.Opens) (p : W.toScheme)
    {d : Spec (S.presheaf.stalk (W.ι p)) ⟶ W.toScheme}
    (hd : d ≫ W.ι = S.fromSpecStalk (W.ι p)) :
    (specStalkIsoOfMem W p).hom ≫ W.toScheme.fromSpecStalk p = d := by
  rw [← cancel_mono W.ι, hd, specStalkIsoOfMem_hom, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk, IsIso.inv_hom_id_assoc]

/-- An open of the source of an isomorphism of schemes which is the preimage of an open of the
target is isomorphic to it. -/
noncomputable def opensIsoOfPreimageEq {X Y : Scheme.{u}} (e : X ≅ Y) {A : X.Opens} {B : Y.Opens}
    (hAB : A = e.hom ⁻¹ᵁ B) : A.toScheme ≅ B.toScheme :=
  X.isoOfEq hAB ≪≫ asIso (e.hom ∣_ B)

/-- The isomorphism `opensIsoOfPreimageEq` followed by the inclusion of `B` equals the inclusion
of `A` followed by `e.hom`. -/
@[reassoc]
theorem opensIsoOfPreimageEq_hom_ι {X Y : Scheme.{u}} (e : X ≅ Y) {A : X.Opens} {B : Y.Opens}
    (hAB : A = e.hom ⁻¹ᵁ B) :
    (opensIsoOfPreimageEq e hAB).hom ≫ B.ι = A.ι ≫ e.hom := by
  simp [opensIsoOfPreimageEq]

/-- The inclusion of `B` followed by `e.inv` equals the inverse of `opensIsoOfPreimageEq`
followed by the inclusion of `A`. -/
theorem ι_inv_eq_opensIsoOfPreimageEq_inv_ι {X Y : Scheme.{u}} (e : X ≅ Y) {A : X.Opens}
    {B : Y.Opens} (hAB : A = e.hom ⁻¹ᵁ B) :
    B.ι ≫ e.inv = (opensIsoOfPreimageEq e hAB).inv ≫ A.ι := by
  rw [Iso.eq_inv_comp, ← Category.assoc, opensIsoOfPreimageEq_hom_ι, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! ### Tag 0BPA over an open subscheme -/

/-- The punctured open of an open subscheme at a closed point of the ambient scheme has
quasi-compact inclusion as soon as the corresponding open of the ambient scheme has. -/
theorem quasiCompact_ι_puncturedOpen_of_mem {S : Scheme.{u}} (W : S.Opens) (V : S.Opens)
    (hqc : QuasiCompact V.ι) {p : W.toScheme} (hcl : IsClosed ({p} : Set W.toScheme))
    (hPV : W.ι ⁻¹ᵁ V = GlueingNearPoint.puncturedOpen hcl) :
    QuasiCompact (GlueingNearPoint.puncturedOpen hcl).ι := by
  have hretro : IsRetrocompact (V : Set S) :=
    GlueingNearPoint.isRetrocompact_of_quasiCompact_ι V hqc
  have h2 : IsRetrocompact (W.ι ⁻¹' (V : Set S)) :=
    IsRetrocompact.preimage_of_isOpenEmbedding W.ι.isOpenEmbedding hretro
  refine quasiCompact_ι_of_isRetrocompact _ ?_
  rw [← hPV]
  exact h2

/-- **Stacks Project, Lemma 32.14.1 (0BPA)** over an open subscheme `W` of a scheme `S`, written
in terms of `S`.

Let `t` be a closed point of `S` lying in `W` and let `V` be the open of `S` cutting out the
complement of `t` in `W`, assumed to have quasi-compact inclusion in `S`.  Then the canonical
functor from schemes of finite presentation over `W` to the glueing data of the commutative
square whose bottom row is a factorization `V ⟶ W` of the inclusion of `V` and whose right column
is a factorization `Spec 𝒪_{S, t} ⟶ W` of `AlgebraicGeometry.Scheme.fromSpecStalk` is an
equivalence. -/
theorem restrictionFunctorOfSquare_isEquivalence_of_ambientOpen {S : Scheme.{u}} (W : S.Opens)
    {t : S} (ht : IsClosed ({t} : Set S)) (htW : t ∈ W) (V : S.Opens)
    (hV : (V : Set S) = (W : Set S) ∩ ({t}ᶜ : Set S)) (hqc : QuasiCompact V.ι)
    {c : V.toScheme ⟶ W.toScheme} (hc : c ≫ W.ι = V.ι)
    {d : Spec (S.presheaf.stalk t) ⟶ W.toScheme} (hd : d ≫ W.ι = S.fromSpecStalk t)
    (h : (S.fromSpecStalk t ∣_ V) ≫ c = (S.fromSpecStalk t ⁻¹ᵁ V).ι ≫ d) :
    (restrictionFunctorOfSquare c d h).IsEquivalence := by
  obtain ⟨p, rfl⟩ : ∃ p : W.toScheme, W.ι p = t := ⟨⟨t, htW⟩, rfl⟩
  have hcl : IsClosed ({p} : Set W.toScheme) := isClosed_singleton_of_mem W ht p rfl
  have hPV : W.ι ⁻¹ᵁ V = GlueingNearPoint.puncturedOpen hcl :=
    preimage_ι_eq_puncturedOpen W V hV p rfl hcl
  have hVW : V ≤ W := le_of_eq_inter_compl W V hV
  have hqcP : QuasiCompact (GlueingNearPoint.puncturedOpen hcl).ι :=
    quasiCompact_ι_puncturedOpen_of_mem W V hqc hcl hPV
  -- the comparison isomorphism of the opens
  have hc0 : (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV).hom ≫
      (GlueingNearPoint.puncturedOpen hcl).ι = c := by
    rw [← cancel_mono W.ι, hc]
    simp
  have hc' : (GlueingNearPoint.puncturedOpen hcl).ι =
      (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV).inv ≫ c :=
    (Iso.eq_inv_comp _).2 hc0
  have hγι : (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV).inv ≫ V.ι =
      (GlueingNearPoint.puncturedOpen hcl).ι ≫ W.ι := by
    rw [hc', Category.assoc, hc]
  -- the comparison isomorphism of the local schemes
  have hd0 : (specStalkIsoOfMem W p).hom ≫ W.toScheme.fromSpecStalk p = d :=
    specStalkIsoOfMem_hom_fromSpecStalk W p hd
  have hd' : W.toScheme.fromSpecStalk p = (specStalkIsoOfMem W p).inv ≫ d :=
    (Iso.eq_inv_comp _).2 hd0
  have hδι : (specStalkIsoOfMem W p).inv ≫ S.fromSpecStalk (W.ι p) =
      W.toScheme.fromSpecStalk p ≫ W.ι := by
    rw [hd', Category.assoc, hd]
  -- the comparison isomorphism of the overlaps
  have hQ : S.fromSpecStalk (W.ι p) ⁻¹ᵁ V = (specStalkIsoOfMem W p).hom ⁻¹ᵁ
      (W.toScheme.fromSpecStalk p ⁻¹ᵁ GlueingNearPoint.puncturedOpen hcl) := by
    rw [← Scheme.Hom.comp_preimage, hd0, ← hPV, ← Scheme.Hom.comp_preimage, hd]
  have hb : (W.toScheme.fromSpecStalk p ⁻¹ᵁ GlueingNearPoint.puncturedOpen hcl).ι ≫
        (specStalkIsoOfMem W p).inv =
      (opensIsoOfPreimageEq (specStalkIsoOfMem W p) hQ).inv ≫
        (S.fromSpecStalk (W.ι p) ⁻¹ᵁ V).ι :=
    ι_inv_eq_opensIsoOfPreimageEq_inv_ι (specStalkIsoOfMem W p) hQ
  have ha : (W.toScheme.fromSpecStalk p ∣_ GlueingNearPoint.puncturedOpen hcl) ≫
        (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV).inv =
      (opensIsoOfPreimageEq (specStalkIsoOfMem W p) hQ).inv ≫
        (S.fromSpecStalk (W.ι p) ∣_ V) := by
    have h1 : ((W.toScheme.fromSpecStalk p ∣_ GlueingNearPoint.puncturedOpen hcl) ≫
          (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV).inv) ≫ V.ι =
        (W.toScheme.fromSpecStalk p ⁻¹ᵁ GlueingNearPoint.puncturedOpen hcl).ι ≫
          (specStalkIsoOfMem W p).inv ≫ S.fromSpecStalk (W.ι p) := by
      simp only [Category.assoc, hγι]
      rw [morphismRestrict_ι_assoc, hδι]
    have h2 : ((opensIsoOfPreimageEq (specStalkIsoOfMem W p) hQ).inv ≫
          (S.fromSpecStalk (W.ι p) ∣_ V)) ≫ V.ι =
        (W.toScheme.fromSpecStalk p ⁻¹ᵁ GlueingNearPoint.puncturedOpen hcl).ι ≫
          (specStalkIsoOfMem W p).inv ≫ S.fromSpecStalk (W.ι p) := by
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, ← hb, Category.assoc]
    exact (cancel_mono V.ι).mp (h1.trans h2.symm)
  have hequiv := GlueingNearPoint.restrictionFunctorAtPoint_isEquivalence W.toScheme p hcl hqcP
  rw [restrictionFunctorAtPoint_eq_restrictionFunctorOfSquare] at hequiv
  exact restrictionFunctorOfSquare_isEquivalence_of_iso
    (isoPreimageOfLE W V hVW ≪≫ W.toScheme.isoOfEq hPV) (specStalkIsoOfMem W p)
    (opensIsoOfPreimageEq (specStalkIsoOfMem W p) hQ) h
    (morphismRestrict_ι (W.toScheme.fromSpecStalk p) (GlueingNearPoint.puncturedOpen hcl))
    hc' hd' ha hb hequiv

end AlgebraicGeometry

end
