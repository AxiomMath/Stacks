module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteRelativeNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartLocalFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Sections of a limit preserving presheaf over a locally Noetherian base: Noetherian descent

Let `a : F ⟶ Q` be a morphism of presheaves on the big fppf site of `S` which is relatively limit
preserving (Stacks 049J), with `Q` a locally Noetherian algebraic space.  Then every section `s`
of `F` over a scheme `T` of the site is, near every point `t` of `T`, pulled back from a section
over a Noetherian scheme: there are morphisms `T ⟵ T' ⟶ T₀` of the site, the first étale (hence
open) with `t` in its image and `T₀` locally Noetherian, and a section `s₀ ∈ F(T₀)` with
`s|_{T'} = s₀|_{T'}`.

This is the use of limit preservation in the proof of Stacks 0DND: étale locally on `T` the
structure morphism `T ⟶ Q` factors through an affine étale chart `W ⟶ Q`, which is Noetherian
because `Q` is locally Noetherian; on an affine étale neighbourhood `T' = Spec R` of `t` the ring
`R` is the filtered colimit of its finitely generated `Γ(W)`-subalgebras, so `T'` is the limit of
the Noetherian affine schemes `Spec Γ(W)[i]`, all lying over `W`; and the restriction of `s` to
`T'` lies over the point `W ⟶ Q`, so it comes from one of the stages.

## Main results

* `AlgebraicGeometry.Space.exists_noetherianDescent_of_relativelyLimitPreserving`: the local
  descent of sections to Noetherian schemes of the site.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The stages of the relative Noetherian approximation of `m : T ⟶ W`, as a diagram of objects
over `W`. -/
private def relativeAffineSiteStageOverDiagram {T W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (m : T ⟶ W) :
    (Finset Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))ᵒᵖ ⥤ Over W :=
  Over.lift (relativeAffineSiteStageDiagram B S hS m ⋙ BigAffineFppf.inclusion B S hS)
    { app := fun i => relativeAffineSiteStageToTarget B S hS m i
      naturality := fun _ _ f => Over.OverMorphism.ext
        ((relativeAffineSiteStageSchemes_map_toTarget B S hS m f).trans (Category.comp_id _).symm) }

/-- The cone with vertex `m` over the stages of the relative Noetherian approximation of `m`, in
the category of objects over `W`. -/
private def relativeAffineSiteStageOverCone {T W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (m : T ⟶ W) :
    Cone (relativeAffineSiteStageOverDiagram m) :=
  Over.liftCone _ _ ((BigAffineFppf.inclusion B S hS).mapCone
    (relativeAffineSiteStageCone B S hS m)) m
    (fun i => relativeAffineSiteStageCone_π_comp_toTarget B S hS m i)

/-- **Sections of a relatively limit preserving presheaf over a locally Noetherian algebraic space
come étale locally from Noetherian schemes.**  Let `a : F ⟶ Q` be relatively limit preserving,
with `Q` a locally Noetherian algebraic space.  For a section `s` of `F` over a scheme `T` of the
site and a point `t` of `T` there are a morphism `p : T' ⟶ T` which is open on points and hits
`t`, a locally Noetherian scheme `T₀` of the site, a morphism `q : T' ⟶ T₀` and a section `s₀` of
`F` over `T₀` with `F(p)(s) = F(q)(s₀)`. -/
theorem exists_noetherianDescent_of_relativelyLimitPreserving
    {F Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ Q) (hQ : IsAlgebraicSpace B S hS Q)
    (hQN : IsLocallyNoetherian B S hS Q)
    (ha : RelativelyLimitPreserving.{u, u, u, u} B S hS a)
    (T : BigFppfOver B S hS) (s : F.obj (op T)) (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (T' T₀ : BigFppfOver B S hS) (p : T' ⟶ T) (q : T' ⟶ T₀) (s₀ : F.obj (op T₀))
      (t' : (BigFppfOver.toScheme B S hS).obj T'),
        (BigFppfOver.toScheme B S hS).map p t' = t ∧
          IsOpenMap ((BigFppfOver.toScheme B S hS).map p) ∧
          _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₀) ∧
          F.map q.op s₀ = F.map p.op s := by
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨U, f, ι, W, j, e, hfS, hfE, hWaff, hιe, hjopen, hjf, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS Q hQ
  have hcov := (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1
  obtain ⟨V, ev, i, m, hVaff, hev, ht, hfac⟩ :=
    exists_affine_etale_nbhd_through_atlas f hfS hfE j hjopen hcov (a.app (op T) s) t
  -- the chart `W i` is Noetherian
  have hWN : _root_.AlgebraicGeometry.IsLocallyNoetherian (G.obj (W i)) :=
    hQN (W i) (yoneda.map (j i) ≫ f) ((isEtale_iff_presheaf_of_yoneda B S hS _).2 (hjf i))
  have := hWaff i
  have := hVaff
  have := hev
  have : _root_.AlgebraicGeometry.IsNoetherian (G.obj (W i)) := ⟨⟩
  -- the point of `Q` over the chart, and the restriction of `s` to `V`, which lies over it
  let yW : Q.obj (op (W i)) := f.app (op (W i)) (j i)
  have hlies : a.app (op V) (F.map ev.op s) = Q.map m.op yW := by
    rw [NatTrans.naturality_apply, ← hfac]
    exact NatTrans.naturality_apply f m.op (j i)
  let x : (sectionFiber B S hS a (W i) yW).obj (op (relativeAffineSiteStageOverCone m).pt) :=
    ⟨F.map ev.op s, hlies⟩
  -- the stages are affine, and `V` is their limit
  have hlim : IsLimit ((Over.forget (W i) ⋙ G).mapCone (relativeAffineSiteStageOverCone m)) :=
    isLimit_relativeAffineSiteStageCone B S hS m
  have hst : ∀ k, IsAffine ((Over.forget (W i) ⋙ G).obj
      ((relativeAffineSiteStageOverDiagram m).obj k)) := fun k =>
    ((relativeAffineSiteStageDiagram B S hS m).obj k).property
  obtain ⟨hcol⟩ := ha (W i) yW _ _ _ hlim hst hVaff
  obtain ⟨k, y, hy⟩ := exists_eq_map_of_isColimit_mapCocone _ _ _ hcol x
  refine ⟨V, (BigAffineFppf.inclusion B S hS).obj ((relativeAffineSiteStageDiagram B S hS m).obj k),
    ev, (BigAffineFppf.inclusion B S hS).map ((relativeAffineSiteStageCone B S hS m).π.app k),
    y.1, ht.choose, ht.choose_spec, (G.map ev).isOpenMap, ?_, congrArg Subtype.val hy⟩
  have := isNoetherian_relativeAffineSiteStageDiagram_obj B S hS m k
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
    ((BigAffineFppf.toScheme B S hS).obj ((relativeAffineSiteStageDiagram B S hS m).obj k)))

end AlgebraicGeometry.Space

end
