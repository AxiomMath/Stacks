module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStage
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumOfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Agreement of formal morphisms on the reduction at a finite stage

Let `V = lim Vᵢ` be a cofiltered limit of affine locally Noetherian schemes over `S`, in the
situation of Stacks 0GH8, and let `x̂₁, x̂₂ : V_{i,/Z} ⟶ W` be two morphisms whose restrictions to
`V_{/Z}` agree. The step "agreement of `x̂_{λ,i}|_{Z_λ}`" of the injectivity half of the proof of
**Stacks 0GI5** says that after passing to a later stage they agree on the reduction. The source
argues with the morphisms `Z_λ ⟶ W_red`; here the same is done with `W` itself, which is limit
preserving (`AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_W`), on the base change
`Q ×_{Vᵢ} Vⱼ` of a closed subscheme `Q = Spec (Aᵢ / I)` cut out by `Z`; the reduction of
`V_{j,/Z}` (Stacks 0GB9) factors through it because it is reduced with the same points (Stacks
03JJ).

This is the input that makes the equalizer of the two morphisms a closed immersion, by Stacks
0GHZ (`AlgebraicGeometry.FormalSpace.isClosedImmersion_of_mono_of_reduction_factors`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_map_eq_of_isLimit_baseChange`: two
  sections of `W` over a stage-wise base change that agree in the limit agree at a later stage.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_isClosedImmersion_of_isClosed`: a closed
  subset of an affine object of the site is the image of an affine closed subscheme.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_reduction_comp_eq_of_isLimit`: the
  agreement on the reduction at a later stage.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
* [Stacks Project, Tag 0GHZ](https://stacks.math.columbia.edu/tag/0GHZ)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D}

/-- **Two sections of a limit preserving presheaf over a stage-wise base change that agree in the
limit agree at a later stage.** For a cofiltered limit `V = lim Vᵢ` of affine locally Noetherian
schemes and an affine `q : N ⟶ Vᵢ`, two sections over `N` of a limit preserving presheaf `G`
whose pullbacks to `V ×_{Vᵢ} N` agree have the same pullback to `Vⱼ ×_{Vᵢ} N` for some `j ⟶ i`:
the base change of the limit is again a limit
(`CategoryTheory.Limits.isLimitMapOverBaseChangeCone`). -/
theorem exists_map_eq_of_isLimit_baseChange (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v)
    (hG : LimitPreserving.{u, v, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (i : I)
    {N : BigFppfOver B S hS} (q : N ⟶ (D.obj i).obj)
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (w₁ w₂ : G.obj (op N))
    (h : G.map (pullback.snd (κ.π.app i).hom q).op w₁ =
      G.map (pullback.snd (κ.π.app i).hom q).op w₂) :
    ∃ (j : I) (f : j ⟶ i), G.map (pullback.snd (D.map f).hom q).op w₁ =
      G.map (pullback.snd (D.map f).hom q).op w₂ := by
  let E := D ⋙ ObjectProperty.ι _
  let κ' := (ObjectProperty.ι _).mapCone κ
  have hκ' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone κ') := hκ
  have hlim := isLimitMapOverBaseChangeCone E κ' i q (BigFppfOver.toScheme B S hS) hκ'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)) := hD i
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj N) := hN
  have hstage : ∀ k : Over i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((overBaseChangeDiagram E i q).obj k)) := fun k => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj k.left)) := hD k.left
    exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS)
      (E.map k.hom) q).hom
  have hvert : IsAffine ((BigFppfOver.toScheme B S hS).obj (overBaseChangeCone E κ' i q).pt) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj κ'.pt) := hpt
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (((Functor.const I).obj κ'.pt).obj i)) :=
      hpt
    have : IsAffineHom ((BigFppfOver.toScheme B S hS).map (κ'.π.app i)) :=
      isAffineHom_of_isAffine _
    exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS)
      (κ'.π.app i) q).hom
  obtain ⟨hcol⟩ := hG (Over i) (overBaseChangeDiagram E i q)
    (overBaseChangeCone E κ' i q) hlim hstage hvert
  obtain ⟨k, g, hg⟩ := eventually_eq_of_isColimit_mapCocone G (overBaseChangeDiagram E i q)
    (overBaseChangeCone E κ' i q) hcol (Over.mk (𝟙 i))
    (G.map (pullback.snd (E.map (𝟙 i)) q).op w₁)
    (G.map (pullback.snd (E.map (𝟙 i)) q).op w₂) (by
      have e1 : (overBaseChangeCone E κ' i q).π.app (Over.mk (𝟙 i)) ≫
          pullback.snd (E.map (𝟙 i)) q = pullback.snd (κ'.π.app i) q := pullback.lift_snd _ _ _
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, e1]
      exact h)
  refine ⟨k.left, k.hom, ?_⟩
  have e2 : (CategoryTheory.Limits.overBaseChangeDiagram E i q).map g ≫
      pullback.snd (E.map (𝟙 i)) q = pullback.snd (E.map k.hom) q := pullback.lift_snd _ _ _
  rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, e2] at hg

/-- Every point of the vanishing locus of an ideal `I` of the ring of global sections of an affine
object `V` of the site lies in the image of the closed subscheme `Spec (A / Iⁿ)`, `n ≥ 1`. -/
theorem exists_toScheme_map_adicCompletionQuotientObjHom_eq (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {n : ℕ} (hn : n ≠ 0)
    {y : (BigFppfOver.toScheme B S hS).obj V}
    (hy : y ∈ ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    ∃ z, (BigFppfOver.toScheme B S hS).map (Space.adicCompletionQuotientObjHom B S hS V I n) z =
      y := by
  let X := (BigFppfOver.toScheme B S hS).obj V
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom y
  have hyp : X.isoSpec.inv p = y := by
    show (X.isoSpec.hom ≫ X.isoSpec.inv) y = y
    simp
  have hp : p ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, ⊤)) :=
    (Set.ext_iff.mp (Scheme.isoSpec_inv_preimage_zeroLocus X (I : Set Γ(X, ⊤))) p).mp
      (show X.isoSpec.inv p ∈ X.zeroLocus (I : Set Γ(X, ⊤)) from hyp ▸ hy)
  have hpn : I ^ n ≤ p.asIdeal :=
    (Ideal.pow_le_self hn).trans ((PrimeSpectrum.mem_zeroLocus _ _).mp hp)
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n))) := by
    rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  refine ⟨q, ?_⟩
  have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) q = p := hq
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
    X.isoSpec.inv q).trans ((congrArg X.isoSpec.inv h1).trans hyp)

/-- **A closed subset of an affine object of the site is the image of a closed subscheme.**
For `Z ⊆ |V|` closed, with `V` affine, there is an affine closed subscheme `q : Q ⟶ V` of `V`
(namely `Spec (A / I)` for an ideal `I` cutting out `Z`) whose sections have point-set image in
`Z` and whose image contains every point of `Z`. -/
theorem exists_isClosedImmersion_of_isClosed (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z) :
    ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ V), IsAffine ((BigFppfOver.toScheme B S hS).obj Q) ∧
      Space.HasImageIn B S hS (yoneda.obj V) Z Q q ∧
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) ∧
      ∀ x ∈ Z, ∃ z, (BigFppfOver.toScheme B S hS).map q z = Space.pointsToScheme B S hS V x := by
  obtain ⟨Iid, hI⟩ := Space.exists_ideal_mem_iff_mem_zeroLocus B S hS V hZ
  refine ⟨Space.adicCompletionQuotientObj B S hS V Iid 1,
    Space.adicCompletionQuotientObjHom B S hS V Iid 1, ?_,
    Space.hasImageIn_adicCompletionQuotientObjHom B S hS V Iid hI 1, ?_,
    fun x hx => exists_toScheme_map_adicCompletionQuotientObjHom_eq V Iid one_ne_zero
      ((hI x).mp hx)⟩
  · show IsAffine (Spec _)
    infer_instance
  · show IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Iid ^ 1))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
    infer_instance

/-- A point of a stage lying over a point in the image of a morphism into the base lifts to the
fibre product of the site. -/
theorem exists_toScheme_map_pullback_fst_eq {V' V Q : BigFppfOver B S hS} (φ : V' ⟶ V)
    (q : Q ⟶ V) {y : (BigFppfOver.toScheme B S hS).obj V'}
    {z : (BigFppfOver.toScheme B S hS).obj Q}
    (hyz : (BigFppfOver.toScheme B S hS).map φ y = (BigFppfOver.toScheme B S hS).map q z) :
    ∃ w, (BigFppfOver.toScheme B S hS).map (pullback.fst φ q) w = y := by
  let L := BigFppfOver.toScheme B S hS
  obtain ⟨w₀, hw₀⟩ : y ∈ Set.range (pullback.fst (L.map φ) (L.map q)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨z, hyz.symm⟩
  exact ⟨(PreservesPullback.iso L φ q).inv w₀, (Scheme.Hom.comp_apply _ _ w₀).symm.trans
    ((congrArg (fun k => k w₀) (PreservesPullback.iso_inv_fst L φ q)).trans hw₀)⟩

/-- **Two morphisms `V_{i,/Z} ⟶ W` agreeing in the limit agree on the reduction at a later
stage.** For a cofiltered limit `V = lim Vᵢ` of affine locally Noetherian schemes over `S`, two
morphisms `x̂₁, x̂₂ : V_{i,/Z} ⟶ W` whose restrictions to `V_{/Z}` agree have, for some `j ⟶ i`,
restrictions to `V_{j,/Z}` which agree on its reduction `(V_{j,/Z})_red` (Stacks 0GB9). This is
the step "agreement of `x̂_{λ,i}|_{Z_λ}`" of the injectivity half of the proof of Stacks 0GI5:
`W` is limit preserving, and the reduction factors through the base change to `Vⱼ` of the
closed subscheme `Spec (Aᵢ / I)` cut out by `Z`. -/
theorem exists_reduction_comp_eq_of_isLimit
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (i : I)
    {Z : Set (Space.points B S hS (yoneda.obj (D.obj i).obj))} (hZ : IsClosed Z)
    (x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W)
    (h : Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₂) :
    ∃ (j : I) (f : j ⟶ i),
      FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
          (isAlgebraicSpace_yoneda B S hS (D.obj j).obj)
          (Space.pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' Z)
          (hZ.preimage (Space.continuous_pointsMap B S hS _)) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map f).hom) Z ≫ x₁ =
      FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
          (isAlgebraicSpace_yoneda B S hS (D.obj j).obj)
          (Space.pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' Z)
          (hZ.preimage (Space.continuous_pointsMap B S hS _)) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map f).hom) Z ≫ x₂ := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  obtain ⟨Q, q, hQ, hq, hqci, hqZ⟩ := exists_isClosedImmersion_of_isClosed (D.obj i).obj hZ
  -- the values of a morphism out of `V_{i,/Z}` on sections factoring through `Q`
  have hnat : ∀ (xx : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W)
      {U : BigFppfOver B S hS} (g : U ⟶ Q)
      (hg : Space.HasImageIn B S hS (yoneda.obj (D.obj i).obj) Z U
        ((yoneda.obj (D.obj i).obj).map g.op q)),
      xx.hom.app (op U) (FormalSpace.presheafSection B S hS
          ((yoneda.obj (D.obj i).obj).map g.op q) hg) =
        c.W.obj.map g.op (xx.hom.app (op Q) (FormalSpace.presheafSection B S hS q hq)) := by
    intro xx U g hg
    have e := FormalSpace.presheafSection_map (F := yoneda.obj (D.obj i).obj) (TF := Z) B S hS g
      q hq hg
    rw [← e]
    exact NatTrans.naturality_apply xx.hom g.op _
  have hsec : ∀ {V' : BigFppfOver B S hS} (φ : V' ⟶ (D.obj i).obj) {U : BigFppfOver B S hS}
      (t : U ⟶ V') (r : U ⟶ Q) (htr : t ≫ φ = r ≫ q)
      (ht : Space.HasImageIn B S hS (yoneda.obj V')
        (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z) U t)
      (xx : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W),
      (Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ xx).hom.app (op U)
          (FormalSpace.presheafSection B S hS t ht) =
        c.W.obj.map r.op (xx.hom.app (op Q) (FormalSpace.presheafSection B S hS q hq)) := by
    intro V' φ U t r htr ht xx
    have hr : Space.HasImageIn B S hS (yoneda.obj (D.obj i).obj) Z U
        ((yoneda.obj (D.obj i).obj).map r.op q) :=
      (Space.completionSubfunctor B S hS (yoneda.obj (D.obj i).obj) Z).map r.op hq
    have h2 : (yoneda.map φ).app (op U) t = (yoneda.obj (D.obj i).obj).map r.op q := htr
    have ht' : Space.HasImageIn B S hS (yoneda.obj (D.obj i).obj) Z U
        ((yoneda.map φ).app (op U) t) := by
      rwa [h2]
    have h1 := FormalSpace.completionSheafMap_presheafSection (F := yoneda.obj V')
      (G := yoneda.obj (D.obj i).obj) B S hS (yoneda.map φ) Z t ht ht'
    show xx.hom.app (op U) ((Space.completionSheafMap B S hS (yoneda.map φ) Z).hom.app (op U)
      (FormalSpace.presheafSection B S hS t ht)) = _
    rw [h1]
    have hcongr : ∀ {a b : (yoneda.obj (D.obj i).obj).obj (op U)} (hab : a = b)
        (ha : Space.HasImageIn B S hS (yoneda.obj (D.obj i).obj) Z U a)
        (hb : Space.HasImageIn B S hS (yoneda.obj (D.obj i).obj) Z U b),
        FormalSpace.presheafSection B S hS a ha = FormalSpace.presheafSection B S hS b hb := by
      rintro a b rfl ha hb
      rfl
    have h3 := hcongr h2 ht' hr
    rw [h3]
    exact hnat xx r hr
  -- agreement over the vertex
  let φinf := (κ.π.app i).hom
  have hP : Space.HasImageIn B S hS (yoneda.obj κ.pt.obj)
      (Space.pointsMap B S hS _ (yoneda.map φinf) ⁻¹' Z) (pullback φinf q)
      (pullback.fst φinf q) := by
    refine (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map φinf) Z _ _).2 ?_
    have : (yoneda.map φinf).app (op (pullback φinf q)) (pullback.fst φinf q) =
        (yoneda.obj (D.obj i).obj).map (pullback.snd φinf q).op q :=
      pullback.condition (f := φinf) (g := q)
    rw [this]
    exact (Space.completionSubfunctor B S hS (yoneda.obj (D.obj i).obj) Z).map
      (pullback.snd φinf q).op hq
  have hvert : c.W.obj.map (pullback.snd φinf q).op
        (x₁.hom.app (op Q) (FormalSpace.presheafSection B S hS q hq)) =
      c.W.obj.map (pullback.snd φinf q).op
        (x₂.hom.app (op Q) (FormalSpace.presheafSection B S hS q hq)) := by
    have hc := pullback.condition (f := φinf) (g := q)
    rw [← hsec φinf (pullback.fst φinf q) (pullback.snd φinf q) hc hP x₁,
      ← hsec φinf (pullback.fst φinf q) (pullback.snd φinf q) hc hP x₂, h]
  obtain ⟨j, f, hjf⟩ := exists_map_eq_of_isLimit_baseChange c.W.obj c.limitPreserving_W hκ hD hpt i
    q hQ _ _ hvert
  refine ⟨j, f, ?_⟩
  -- the base change `Q ×_{Vᵢ} Vⱼ`, a closed subspace of `Vⱼ` containing the reduction
  let φ := (D.map f).hom
  have hVj := isAlgebraicSpace_yoneda B S hS (D.obj j).obj
  have hZj : IsClosed (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z) :=
    hZ.preimage (Space.continuous_pointsMap B S hS _)
  have := hqci
  have hci : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (pullback.fst φ q)) := by
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) φ q]
    infer_instance
  have hR := Space.isClosedSubspace_range_yoneda_map B S hS (pullback.fst φ q) hci
  obtain ⟨g, hg⟩ := (Space.exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hVj
      (Space.isClosedSubspace_reducedClosedSubspace B S hS _ hVj _ hZj).1 _ hR
      (Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS _ hVj _ hZj) _).mpr
    (by
      rw [Space.range_pointsMap_ι_reducedClosedSubspace]
      intro x hx
      obtain ⟨z, hz⟩ := hqZ _ hx
      rw [Space.pointsToScheme_pointsMap_yoneda] at hz
      obtain ⟨w', hw'⟩ := exists_toScheme_map_pullback_fst_eq φ q hz.symm
      refine ⟨Space.pointsMap B S hS _ (Subfunctor.toRange (yoneda.map (pullback.fst φ q)))
        ((Space.schemePointsHomeomorph B S hS _).symm w'), ?_⟩
      rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
      apply (Space.schemePointsHomeomorph B S hS _).injective
      rw [Space.schemePointsHomeomorph_apply, Space.schemePointsHomeomorph_apply,
        Space.pointsToScheme_pointsMap_yoneda, ← Space.schemePointsHomeomorph_apply,
        Homeomorph.apply_symm_apply, hw'])
  -- test the two morphisms on the sections of the reduction
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  ext s
  obtain ⟨t, ht⟩ := (g.app U s.down).2
  have hts : t ≫ pullback.fst φ q =
      (Space.reducedClosedSubspace B S hS _ hVj _ hZj).ι.app U s.down :=
    ht.trans (congrArg (fun k => k.app U s.down) hg)
  have htr : (Space.reducedClosedSubspace B S hS _ hVj _ hZj).ι.app U s.down ≫ φ =
      (t ≫ pullback.snd φ q) ≫ q := by
    rw [← hts, Category.assoc, pullback.condition, Category.assoc]
  have hs := Space.hasImageIn_ι_reducedClosedSubspace B S hS hVj _ hZj U.unop s.down
  have key : ∀ xx : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W,
      (FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS hVj _ hZj ≫
          Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ xx).hom.app U s =
        c.W.obj.map t.op (c.W.obj.map (pullback.snd φ q).op
          (xx.hom.app (op Q) (FormalSpace.presheafSection B S hS q hq))) := by
    intro xx
    have e := hsec φ ((Space.reducedClosedSubspace B S hS _ hVj _ hZj).ι.app U s.down)
      (t ≫ pullback.snd φ q) htr hs xx
    rw [← Functor.map_comp_apply, ← op_comp, ← e]
    rfl
  exact (key x₁).trans ((congrArg (c.W.obj.map t.op) hjf).trans (key x₂).symm)

end AlgebraicGeometry.Artin.ContractionSituation

end
