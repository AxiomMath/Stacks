module

public import StacksFrontier.AlgebraicGeometry.CompactOpenLocalization.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.CompactOpenLocalization.StageOpenImmersion

/-!
# The stages of an inverse limit sitting inside an affine open immerse into the fibre products

Let `G` be a cofiltered inverse system of quasi-compact quasi-separated quasi-affine schemes
with affine transition morphisms, let `d` be a limiting cone with quasi-compact vertex, and let
`ψ : d.pt ⟶ X` be an open immersion whose image lies in an affine open `A ⊆ X`.  Write
`B = Γ(X, A)` and `R_k = Γ(G.obj k, ⊤)`, so that `B ⟶ Γ(d.pt, ⊤) = colim_k R_k` and the fibre
products `B_k = B ×_{Γ(d.pt, ⊤)} R_k` are defined.  Then for all `k` far enough along the index,
the composite

    G.obj k ⟶ Spec R_k ⟶ Spec B_k

is an **open immersion**.

This is the paragraph of the Stacks proof of [Stacks, Tag 07RN] that ends *"We conclude that the
morphism `W_i ⟶ Spec(R_i) ⟶ Spec(B_i)` is an open immersion"*, assembled from its three parts:
the elements `g_l ∈ B` with `D(g_l) ⊆ W` covering `W` together with `B_{g_l} = R_{s(g_l)}`
([Stacks, Tag 01P7]) and their lift to a stage, which is
`RingFibreProduct.exists_stage_isOpenImmersion_iSup_basicOpen`; the descent of the cover to a
stage, which is `AlgebraicGeometry.exists_stage_iSup_basicOpen_eq_top`; and the transport of the
resulting open immersion from the union of standard opens onto the stage itself, which is
`AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp'`.

## Main results

* `AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_specMap_snd`: the open immersion
  above, for every stage below some one stage.

## Implementation notes

The presentation `Γ(d.pt, ⊤) = colim_k Γ(G.obj k, ⊤)` is **not** a hypothesis: it is
[Stacks, Tag 01Z0] in Mathlib's form `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`, whose
hypotheses are exactly the ones already assumed here.  Nor is the identification of
`Γ(d.pt, ⊤)` with `Γ(X, ψ ''ᵁ ⊤)` a hypothesis: it is `AlgebraicGeometry.Scheme.Hom.appIso` at
the open immersion `ψ`, so the restriction map `Γ(X, A) ⟶ Γ(d.pt, ⊤)` of the fibre products is
*constructed* here rather than assumed, and the compatibility
`RingFibreProduct.exists_stage_isOpenImmersion_iSup_basicOpen` requires of it holds by
`Iso.hom_inv_id`.

The statement quantifies over all stages below one stage rather than producing a single one,
because [Stacks, Tag 01Z7] is applied to *every* stage of a tail of the index in the step of the
Stacks proof that follows this one.  The extension from one stage to a tail is free: the
covering family is pulled back along the transition morphism, and the hypothesis of
[Stacks, Tag 01Z9] does not mention the stage at all.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **`W_k ⟶ Spec(R_k) ⟶ Spec(B_k)` is an open immersion for every sufficiently large `k`.**

Let `G` be a cofiltered inverse system of quasi-compact quasi-separated quasi-affine schemes
with affine transition morphisms and let `d` be a limiting cone with quasi-compact vertex.  Let
`ψ : d.pt ⟶ X` be an open immersion whose image lies in an affine open `A` of `X`.  Then there
is a stage `j` such that for every stage `k` below `j` the canonical morphism
`G.obj k ⟶ Spec Γ(G.obj k, ⊤)` composed with the projection to the spectrum of the fibre
product `Γ(X, A) ×_{Γ(d.pt, ⊤)} Γ(G.obj k, ⊤)` is an open immersion.

The hypothesis `hWA` is `ψ.opensRange ≤ A` in the spelling the fibre products need; the two are
exchanged by `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`. -/
theorem exists_stage_isOpenImmersion_toSpecΓ_specMap_snd {K : Type u} [Category.{u} K]
    [IsCofiltered K] (G : K ⥤ Scheme.{u})
    [∀ {i j : K} (f : i ⟶ j), IsAffineHom (G.map f)]
    [∀ i, CompactSpace (G.obj i)] [∀ i, QuasiSeparatedSpace (G.obj i)]
    (hqa : ∀ i, (G.obj i).IsQuasiAffine)
    (d : Cone G) (hd : IsLimit d) [CompactSpace d.pt]
    {X : Scheme.{u}} {A : X.Opens} (hA : IsAffineOpen A)
    (ψ : d.pt ⟶ X) [IsOpenImmersion ψ] (hWA : ψ ''ᵁ ⊤ ≤ A) :
    ∃ j : K, ∀ (k : K) (_ : k ⟶ j),
      IsOpenImmersion ((G.obj k).toSpecΓ ≫ Spec.map
        ((RingFibreProduct.fibreProductSystemSnd (Scheme.Γ.mapCocone d.op)
          (X.presheaf.map (homOfLE hWA).op ≫ (ψ.appIso ⊤).hom)).app (op k))) := by
  obtain ⟨hcR⟩ := nonempty_isColimit_Γ_mapCocone G d hd
  have hWc : IsCompact ((ψ ''ᵁ ⊤ : X.Opens) : Set X) :=
    (isCompact_univ (X := d.pt)).image ψ.base.hom.continuous
  have he : Function.Bijective ((ψ.appIso ⊤).inv).hom := ConcreteCategory.bijective_of_isIso _
  have hse : (X.presheaf.map (homOfLE hWA).op ≫ (ψ.appIso ⊤).hom) ≫ (ψ.appIso ⊤).inv
      = X.presheaf.map (homOfLE hWA).op := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨n, g, j, f, -, hgcov, -, hf, hloc, -⟩ :=
    RingFibreProduct.exists_stage_isOpenImmersion_iSup_basicOpen (X := X) (A := A)
      (W := ψ ''ᵁ ⊤) hA hWc hWA (F := G.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone d.op) hcR
      (X.presheaf.map (homOfLE hWA).op ≫ (ψ.appIso ⊤).hom) (ψ.appIso ⊤).inv he hse
  -- The sections `f l` of the stage `j` are the restrictions of the `g l` along `ψ`, so their
  -- basic opens cover the vertex of the limiting cone.
  have hAtop : ⊤ ≤ ψ ⁻¹ᵁ A := by
    refine le_trans ?_ ((Opens.map ψ.base).map (homOfLE hWA)).le
    rw [Scheme.Hom.preimage_image_eq]
  have ht : ∀ l, (d.π.app (unop j)).appTop (f l) = ψ.appLE A ⊤ hAtop (g l) := by
    intro l
    have h0 : (d.π.app (unop j)).appTop (f l)
        = (X.presheaf.map (homOfLE hWA).op ≫ (ψ.appIso ⊤).hom) (g l) := hf l
    rw [h0, CommRingCat.comp_apply, Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE]
  have hcov : ⨆ l, d.pt.basicOpen ((d.π.app (unop j)).appTop (f l)) = ⊤ := by
    simp only [ht, Scheme.basicOpen_appLE, top_inf_eq]
    rw [← Scheme.Hom.preimage_iSup, ← hgcov, Scheme.Hom.preimage_image_eq]
  -- Hence they cover some stage, and then every stage below it.
  obtain ⟨j', fji, hj'⟩ := exists_stage_iSup_basicOpen_eq_top G d hd f hcov
  refine ⟨j', fun k φ => ?_⟩
  have hqak := hqa k
  have hcovk : ⨆ l, (G.obj k).basicOpen ((G.map (φ ≫ fji)).appTop (f l)) = ⊤ := by
    have h1 : ∀ l, (G.obj k).basicOpen ((G.map (φ ≫ fji)).appTop (f l))
        = G.map φ ⁻¹ᵁ (G.obj j').basicOpen ((G.map fji).appTop (f l)) := by
      intro l
      rw [Scheme.preimage_basicOpen_top, G.map_comp, Scheme.Hom.comp_appTop]
      rfl
    simp only [h1]
    rw [← Scheme.Hom.preimage_iSup, hj']
    simp
  refine isOpenImmersion_toSpecΓ_comp' (fun l => (G.map (φ ≫ fji)).appTop (f l)) hcovk _ ?_
  refine RingFibreProduct.isOpenImmersion_iSup_basicOpen_comp_specMap_snd
    (Scheme.Γ.mapCocone d.op) _ (op k) (fun l => (G.map (φ ≫ fji)).appTop (f l)) g
    (fun l => ?_) hloc
  have hw := (Scheme.Γ.mapCocone d.op).w (φ ≫ fji).op
  have h2 : (Scheme.Γ.mapCocone d.op).ι.app (op k) ((G.op ⋙ Scheme.Γ).map (φ ≫ fji).op (f l))
      = (Scheme.Γ.mapCocone d.op).ι.app j (f l) := by
    rw [← CommRingCat.comp_apply, hw]
  exact h2.trans (hf l)

end AlgebraicGeometry

end
