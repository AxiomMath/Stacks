module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibrePowerProjective

/-!
# H-quasi-projectivity of the cover of Stacks 089J over the base

The source `X'` of the Chow cover of [Stacks, Tag 089J] is, by construction, an open subscheme
of a closed subscheme of a finite fibre power over the base of the compactification `Y` of the
chart. If `Y` is H-projective over the base — which is what
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec` produces for
it — then the fibre power is H-projective over the base by
`AlgebraicGeometry.isProjectiveMorphism_overProd_hom`, the closed subscheme is H-projective over
the base, and the open subscheme is H-quasi-projective over the base as soon as it is compact.

Compactness of `X'` is not assumed: `X' = ⋃ᵢ gᵢ⁻¹(W)` is a finite union of preimages of the
chart `W ⊆ Y`, each `gᵢ` is quasi-compact because it is a closed immersion followed by a
projection of a fibre power of proper morphisms, and `W` is the image of the compact chart.

## Main results

* `AlgebraicGeometry.Space.isProjectiveMorphism_overProdObj_hom`: the finite fibre power over
  the base, as an object of the site, is H-projective over the base when its factors are.
* `AlgebraicGeometry.Space.isProjectiveMorphism_chowImageObj_hom`: the scheme-theoretic image
  `Z` of [Stacks, Tag 089J] is H-projective over the base.
* `AlgebraicGeometry.Space.compactSpace_chowCoverObj`: the cover `X'` is a compact space.
* `AlgebraicGeometry.Space.isHQuasiProjective_chowCoverObj_hom`: **the cover `X'` of
  [Stacks, Tag 089J] is H-quasi-projective over the base**, which is the third conjunct of the
  conclusion of that tag.
* `AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom`: **the cover is proper
  and H-quasi-projective over the base**, that is, two of the three conjuncts of the conclusion
  of [Stacks, Tag 089J] with neither assumed. This is
  `AlgebraicGeometry.Space.isProper_chowCoverHom` with its hypothesis `hqp` discharged.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute; H-quasi-projectivity is [Stacks, Tag 01VW], carried by
`AlgebraicGeometry.IsHQuasiProjective`, and nothing about properness or surjectivity of the
cover is touched.

The two hypotheses of the main result are H-projectivity of the compactification over the base
(`AlgebraicGeometry.IsProjectiveMorphism`, [Stacks, Tag 01W8]) and compactness of the étale
chart. Neither mentions `X'`: the first is a property of the scheme `Y` into which the chart is
embedded, produced for it by
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec` out of
[Stacks, Tag 01WA], and the second holds because the chart is affine. In particular neither is
H-quasi-projectivity of `X'`, which is what is proved.

The base is written as the spectrum of a ring because the immersion of `X'` into a projective
space over it is shown to be quasi-compact through quasi-separatedness of that projective space,
which the library has for a spectrum; in [Stacks, Tag 089J] the base is `Spec A`.

## References

* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite fibre power over the base, as an object of the site, is H-projective over the
base when its factors are.** This is
`AlgebraicGeometry.isProjectiveMorphism_overProd_hom` read through
`AlgebraicGeometry.Space.overProdObj_hom`, which says that the structure morphism of the object
of the site *is* the one of the scheme-level product. -/
theorem isProjectiveMorphism_overProdObj_hom {n : ℕ} (Y : Fin (n + 1) → BigFppfOver B S hS)
    (hY : ∀ i, IsProjectiveMorphism (B.inclusion.map (Y i).hom)) :
    IsProjectiveMorphism (B.inclusion.map (overProdObj B S hS Y).hom) := by
  rw [overProdObj_hom]
  exact isProjectiveMorphism_overProd_hom n (fun i ↦ B.inclusion.map (Y i).hom) hY

variable (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)

/-- **The scheme-theoretic image `Z` of Stacks 089J is H-projective over the base.** It is a
closed subscheme of the `(n+1)`-fold fibre power of the compactification over the base, which is
H-projective over the base by
`AlgebraicGeometry.Space.isProjectiveMorphism_overProdObj_hom`. -/
theorem isProjectiveMorphism_chowImageObj_hom
    (hYo : IsProjectiveMorphism (B.inclusion.map Yo.hom)) :
    IsProjectiveMorphism
      (B.inclusion.map (chowImageObj B S hS X Wch c hc hsep Yo j n V e).hom) := by
  rw [show chowImageObj B S hS X Wch c hc hsep Yo j n V e =
      schemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e) from rfl,
    schemeImageObj_hom]
  exact isProjectiveMorphism_isClosedImmersion_comp
    (((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι)
    (B.inclusion.map (overProdObj B S hS (fun _ : Fin (n + 1) ↦ Yo)).hom)
    (isProjectiveMorphism_overProdObj_hom B S hS (fun _ : Fin (n + 1) ↦ Yo) fun _ ↦ hYo)

/-- **Each projection `gᵢ : Z ⟶ Y` of Stacks 089J is quasi-compact.** It is the closed immersion
of the scheme-theoretic image followed by a projection of the fibre power, and that projection
is proper by `AlgebraicGeometry.isProper_overProdπ`. -/
theorem quasiCompact_chowProj
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom)) (i : Fin (n + 1)) :
    AlgebraicGeometry.QuasiCompact (chowProj B S hS X Wch c hc hsep Yo j n V e i) := by
  have hp : ∀ _ : Fin (n + 1), _root_.AlgebraicGeometry.IsProper
      (B.inclusion.map Yo.hom) := fun _ ↦ hYo
  have := hp
  have h1 : _root_.AlgebraicGeometry.IsProper
      (Stacks.Chow.overProdπ (fun _ : Fin (n + 1) ↦ B.inclusion.map Yo.hom) i) :=
    isProper_overProdπ _ i
  have h2 : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map
      (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i)) := by
    rw [overProdObjπ_toScheme]; exact h1
  have := h2
  have h3 : AlgebraicGeometry.QuasiCompact (Scheme.Hom.imageι
      ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) := inferInstance
  have h4 : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i)) := inferInstance
  rw [chowProj_eq]
  exact MorphismProperty.comp_mem (W := @AlgebraicGeometry.QuasiCompact) _ _ h3 h4

variable (hj : _root_.AlgebraicGeometry.IsOpenImmersion
  ((BigFppfOver.toScheme B S hS).map j))

/-- **The open `W ⊆ Y` of Stacks 089J is compact** when the chart is, being the image of the
chart under a continuous map. -/
theorem isCompact_chartOpensRange
    (hWc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Wch)) :
    IsCompact ((chartOpensRange B S hS j hj : ((BigFppfOver.toScheme B S hS).obj Yo).Opens) :
      Set ((BigFppfOver.toScheme B S hS).obj Yo)) := by
  have := hWc
  rw [show ((chartOpensRange B S hS j hj : ((BigFppfOver.toScheme B S hS).obj Yo).Opens) :
      Set ((BigFppfOver.toScheme B S hS).obj Yo)) =
      Set.range ((BigFppfOver.toScheme B S hS).map j).base from
    Scheme.Hom.coe_opensRange _]
  exact isCompact_range ((BigFppfOver.toScheme B S hS).map j).base.hom.continuous

/-- **A finite union of preimages of a compact open under quasi-compact morphisms is a compact
space.** This is `AlgebraicGeometry.Space.unionPreimageObj` of Stacks 089J; its underlying
scheme is the open `⨆ᵢ gᵢ⁻¹(W)`, a finite union of compact sets. -/
theorem compactSpace_unionPreimageObj (Z : BigFppfOver B S hS) {Y : Scheme.{u}} {m : ℕ}
    (g : Fin m → (Z.left.obj ⟶ Y)) (W : Y.Opens)
    (hg : ∀ i, AlgebraicGeometry.QuasiCompact (g i)) (hW : IsCompact (W : Set Y)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (unionPreimageObj B S hS Z g W)) := by
  have h : IsCompact ((unionPreimageOpens B S hS Z g W : Z.left.obj.Opens) :
      Set Z.left.obj) := by
    rw [show ((unionPreimageOpens B S hS Z g W : Z.left.obj.Opens) : Set Z.left.obj) =
        ⋃ i, ((g i ⁻¹ᵁ W : Z.left.obj.Opens) : Set Z.left.obj) from by
      simp [unionPreimageOpens]]
    refine isCompact_iUnion fun i ↦ ?_
    have := hg i
    exact AlgebraicGeometry.QuasiCompact.isCompact_preimage (f := g i) (W : Set Y) W.2 hW
  exact isCompact_iff_compactSpace.mp h

/-- **The cover `X'` of Stacks 089J is a compact space.** It is the finite union of the
preimages `gᵢ⁻¹(W)` of the chart, the `gᵢ` are quasi-compact by
`AlgebraicGeometry.Space.quasiCompact_chowProj` and `W` is compact by
`AlgebraicGeometry.Space.isCompact_chartOpensRange`. -/
theorem compactSpace_chowCoverObj
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom))
    (hWc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Wch)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)) :=
  compactSpace_unionPreimageObj B S hS _ _ _
    (fun i ↦ quasiCompact_chowProj B S hS X Wch c hc hsep Yo j n V e hYo i)
    (isCompact_chartOpensRange B S hS Wch Yo j hj hWc)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (R : CommRingCat.{u}) (hR : B.Contains (Spec R))

/-- **The cover `X'` of Stacks 089J is H-quasi-projective over the base.** This is the third
conjunct of the conclusion of [Stacks, Tag 089J].

By construction `X'` is the open `⨆ᵢ gᵢ⁻¹(W)` of the scheme-theoretic image `Z`, which is a
closed subscheme of the `(n+1)`-fold fibre power of the compactification `Y` over the base. So
its structure morphism to the base is the open immersion of that open followed by the structure
morphism of `Z`, which is H-projective over the base by
`AlgebraicGeometry.Space.isProjectiveMorphism_chowImageObj_hom`; and an immersion with compact
source into a scheme H-projective over the spectrum of a ring is H-quasi-projective by
`AlgebraicGeometry.isHQuasiProjective_of_compactSpace_comp_toSpec`.

Compactness of `X'` is `AlgebraicGeometry.Space.compactSpace_chowCoverObj`, so it is not
assumed. The two hypotheses are H-projectivity of `Y` over the base and compactness of the
chart; neither is a statement about `X'`. -/
theorem isHQuasiProjective_chowCoverObj_hom (X : AlgebraicSpaces B (Spec R) hR)
    (Wch : BigFppfOver B (Spec R) hR) (c : yoneda.obj Wch ⟶ X.obj)
    (hc : IsEtale B (Spec R) hR c) (hsep : IsSeparated B (Spec R) hR c)
    (Yo : BigFppfOver B (Spec R) hR) (j : Wch ⟶ Yo) (n : ℕ)
    (V : BigFppfOver B (Spec R) hR)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B (Spec R) hR X
      (SpacesEtale.diagonalComplement B (Spec R) hR X
        (SpacesEtale.chartObj B (Spec R) hR X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (Spec R) hR).map j))
    (hYo : IsProjectiveMorphism (B.inclusion.map Yo.hom))
    (hWc : CompactSpace ((BigFppfOver.toScheme B (Spec R) hR).obj Wch)) :
    IsHQuasiProjective (B.inclusion.map
      (chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj).hom) := by
  have hXc := compactSpace_chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj
    (isProper_of_isProjectiveMorphism _ hYo) hWc
  have hXc' : CompactSpace
      (unionPreimageOpens B (Spec R) hR (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e)
        (chowProj B (Spec R) hR X Wch c hc hsep Yo j n V e)
        (chartOpensRange B (Spec R) hR j hj)).toScheme := hXc
  have := hXc'
  have hq := isProjectiveMorphism_chowImageObj_hom B (Spec R) hR X Wch c hc hsep Yo j n V e hYo
  rw [show B.inclusion.map (chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj).hom =
      (unionPreimageOpens B (Spec R) hR (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e)
          (chowProj B (Spec R) hR X Wch c hc hsep Yo j n V e)
          (chartOpensRange B (Spec R) hR j hj)).ι ≫
        B.inclusion.map (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e).hom from rfl]
  exact isHQuasiProjective_of_compactSpace_comp_toSpec
    (unionPreimageOpens B (Spec R) hR (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e)
      (chowProj B (Spec R) hR X Wch c hc hsep Yo j n V e)
      (chartOpensRange B (Spec R) hR j hj)).ι
    (B.inclusion.map (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e).hom) hq

/-- **The cover of Stacks 089J is proper, and H-quasi-projective over the base.** Two of the
three conjuncts of the conclusion of [Stacks, Tag 089J], with nothing about either of them
assumed.

Properness is `AlgebraicGeometry.Space.isProper_chowCoverHom`, whose hypothesis `hqp` —
H-quasi-projectivity of the cover over the base — is here discharged by
`AlgebraicGeometry.Space.isHQuasiProjective_chowCoverObj_hom` rather than assumed; its
hypothesis `hYo` is weaker than the H-projectivity of the compactification assumed here, by
[Stacks, Tag 01WC].

The remaining conjunct is surjectivity of `ψ`, which is not proved in this development. No
hypothesis below is
properness, surjectivity, valuative liftability or H-quasi-projectivity of the cover: they are
the data of the construction together with H-projectivity of the compactification, compactness
of the chart and of `V`, the fibre-degree bound of [Stacks, Tag 03JL], and separatedness and
quasi-separatedness conditions. -/
theorem isProper_and_isHQuasiProjective_chowCoverHom (X : AlgebraicSpaces B (Spec R) hR)
    (Wch : BigFppfOver B (Spec R) hR) (c : yoneda.obj Wch ⟶ X.obj)
    (hc : IsEtale B (Spec R) hR c) (hsep : IsSeparated B (Spec R) hR c)
    (Yo : BigFppfOver B (Spec R) hR) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B (Spec R) hR)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B (Spec R) hR X
      (SpacesEtale.diagonalComplement B (Spec R) hR X
        (SpacesEtale.chartObj B (Spec R) hR X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (Spec R) hR).map j))
    (hcs : IsSurjective B (Spec R) hR c)
    (hYo : IsProjectiveMorphism (B.inclusion.map Yo.hom))
    (hWc : CompactSpace ((BigFppfOver.toScheme B (Spec R) hR).obj Wch))
    (hXsep : IsSeparated B (Spec R) hR ((isTerminal_yoneda_obj_base B (Spec R) hR).from X.obj))
    (hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B (Spec R) hR).map
      (chowToOverProd B (Spec R) hR X Wch c hc hsep Yo j n V e)))
    (hVc : CompactSpace ((BigFppfOver.toScheme B (Spec R) hR).obj V))
    (hX'qs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (Spec R) hR).obj
      (chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj)))
    (hmatch : ∀ (K' : Type u) (_ : Field K') (T' : BigFppfOver B (Spec R) hR)
      (_ : (BigFppfOver.toScheme B (Spec R) hR).obj T' ≅ Spec (CommRingCat.of K'))
      (ξ : yoneda.obj T' ⟶ X.obj) (w : Fin (n + 1) → (T' ⟶ Wch)),
      (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
        ∀ v : T' ⟶ Wch, yoneda.map v ≫ c = ξ → ∃ k, v = w k)
    (rho : ∀ i : Fin (n + 1), preimageObj B (Spec R) hR
      (chowImageObj B (Spec R) hR X Wch c hc hsep Yo j n V e)
      (chowProj B (Spec R) hR X Wch c hc hsep Yo j n V e)
      (chartOpensRange B (Spec R) hR j hj) i ⟶ Wch)
    (hrho : ∀ i, chowDenseLift B (Spec R) hR X Wch c hc hsep Yo j n V e hj i ≫ rho i =
      SpacesEtale.diagonalComplementProj B (Spec R) hR X Wch c hc hsep (n + 1) V e i)
    (psi : yoneda.obj (chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj) ⟶ X.obj)
    (hpsi : ∀ i, yoneda.map (chowCoverIncl B (Spec R) hR X Wch c hc hsep Yo j n V e hj i) ≫ psi =
      yoneda.map (rho i) ≫ c)
    (i0 : Fin (n + 1)) :
    IsProper B (Spec R) hR psi ∧
      IsHQuasiProjective
        (B.inclusion.map (chowCoverObj B (Spec R) hR X Wch c hc hsep Yo j n V e hj).hom) :=
  have hqp := isHQuasiProjective_chowCoverObj_hom B R hR X Wch c hc hsep Yo j n V e hj hYo hWc
  ⟨isProper_chowCoverHom B (Spec R) hR X Wch c hc hsep Yo j n V e hj hcs
      (isProper_of_isProjectiveMorphism _ hYo) hXsep hVqc hVc hX'qs hqp hmatch rho hrho psi hpsi
      i0,
    hqp⟩

end AlgebraicGeometry.Space

end
