module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteRelativeNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitRelative
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartLocalFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Objects of `Coh_{X/Y}` over a locally Noetherian base come from Noetherian test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation over a scheme `S`, the
standing data of Stacks 08KB, and suppose that `Y` is locally Noetherian. Then every object
`(T, 𝓕)` of `Coh_{X/Y}` is, near every point `t` of `T`, pulled back from an object over a
Noetherian test scheme: there are morphisms `(T, 𝓕) ⟵ (T', 𝓕') ⟶ (T₀, 𝓕₀)` of `Coh_{X/Y}` whose
first morphism of test schemes is étale (hence open) and hits `t`, and whose target has a
Noetherian test scheme.

The proof follows the source's use of limit preservation. Étale locally on `T` the structure
morphism `T ⟶ Y` factors through an affine étale chart `W ⟶ Y`, which is Noetherian because `Y`
is locally Noetherian; on an affine étale neighbourhood `T' = Spec R` of `t` the ring `R` is the
filtered colimit of its finitely generated `Γ(W)`-subalgebras, so `T'` is the limit of the
Noetherian affine schemes `Spec Γ(W)[i]`, all lying over `W`; and the restriction of `(T, 𝓕)` to
`T'` descends to one of them because `Coh_{X/Y} ⟶ Y` is limit preserving on objects (the
relative form of the descent of objects in the proof of Stacks 08KD,
`AlgebraicGeometry.Space.CoherentSituation.exists_coherentHom_stage_of_stage`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_noetherianDescent_of_isLocallyNoetherian`:
  the local descent of objects of `Coh_{X/Y}` to Noetherian test schemes.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Objects of `Coh_{X/Y}` over a locally Noetherian base are étale locally pulled back from
Noetherian test schemes.** If `Y` is locally Noetherian, then for every object `A` of
`Coh_{X/Y}` and every point `t` of its test scheme there are morphisms `A ⟵ A' ⟶ A₀` of
`Coh_{X/Y}` whose first morphism of test schemes is open and hits `t`, and whose target has a
locally Noetherian test scheme. -/
theorem exists_noetherianDescent_of_isLocallyNoetherian
    (hY : IsLocallyNoetherian B S hS D.Y.1)
    (A : CoherentObject D) (t : A.testScheme) :
    ∃ (A' A₀ : CoherentObject D) (p : CoherentHom A' A) (_ : CoherentHom A' A₀)
      (t' : A'.testScheme),
        p.baseScheme t' = t ∧ IsOpenMap p.baseScheme ∧
          _root_.AlgebraicGeometry.IsLocallyNoetherian A₀.testScheme := by
  classical
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨U, f, ι, W, j, e, hfS, hfE, hWaff, hιe, hjopen, hjf, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS D.Y.1 D.Y.2
  obtain ⟨V, ev, i, m, hVaff, hev, ⟨t', ht'⟩, hfac⟩ :=
    exists_affine_etale_nbhd_through_atlas f hfS hfE j hjopen
      (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1 (yonedaEquiv A.T.hom.hom) t
  have hWN : _root_.AlgebraicGeometry.IsLocallyNoetherian (G.obj (W i)) :=
    hY (W i) (yoneda.map (j i) ≫ f) ((isEtale_iff_presheaf_of_yoneda B S hS _).2 (hjf i))
  have := hWaff i
  have : _root_.AlgebraicGeometry.IsNoetherian (G.obj (W i)) := ⟨⟩
  let T' : SchemesOver D.Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map ev ≫ A.T.hom)
  let h : T' ⟶ A.T := CostructuredArrow.homMk ev rfl
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  let A' := pullbackObject' hst A h
  let E := relativeAffineSiteStageDiagram B S hS m
  let c := relativeAffineSiteStageCone B S hS m
  let i₀ : (Finset Γ(G.obj V, ⊤))ᵒᵖ := op ∅
  let gW : (schemeSpaceFunctor B S hS).obj (W i) ⟶ D.Y :=
    ObjectProperty.homMk (yoneda.map (j i) ≫ f)
  let g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i₀)) ⟶
      D.Y :=
    (schemeSpaceFunctor B S hS).map (relativeAffineSiteStageToTarget B S hS m i₀) ≫ gW
  have hg : A'.T.hom = (schemeSpaceFunctor B S hS).map
      (eqToHom rfl ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i₀)) ≫ g := by
    simp only [eqToHom_refl, Category.id_comp, g, ← Category.assoc, ← Functor.map_comp]
    rw [relativeAffineSiteStageCone_π_comp_toTarget B S hS m i₀]
    apply ObjectProperty.hom_ext
    change yoneda.map ev ≫ A.T.hom.hom = yoneda.map m ≫ (yoneda.map (j i) ≫ f)
    apply yonedaEquiv.injective
    exact ((yonedaEquiv_comp _ _).trans (congrArg _ (yonedaEquiv_yoneda_map ev))).trans
      ((yonedaEquiv_naturality _ _).symm.trans (hfac.symm.trans
        ((congrArg (fun y => f.app (op V) (y ≫ j i)) (yonedaEquiv_yoneda_map m).symm).trans
          (yonedaEquiv_comp (yoneda.map m) (yoneda.map (j i) ≫ f)).symm)))
  obtain ⟨k, xi, hxi, q, -⟩ := D.exists_coherentHom_stage_of_stage E c
    (isLimit_relativeAffineSiteStageCone B S hS m) A' rfl g hg
  refine ⟨A', xi, pullbackHom' hst A h, q, t', ht', (G.map ev).isOpenMap, ?_⟩
  have := isNoetherian_relativeAffineSiteStageDiagram_obj B S hS m k.left
  change _root_.AlgebraicGeometry.IsLocallyNoetherian (G.obj xi.T.left)
  rw [hxi]
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
    ((BigAffineFppf.toScheme B S hS).obj (E.obj k.left)))

end AlgebraicGeometry.Space.CoherentSituation

end
