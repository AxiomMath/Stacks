module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartedFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal

/-!
# Sections over affine objects factor étale-locally through a single affine chart

Let `X` be an algebraic space over `S` and `x` a section of `X` over an affine object `TA` of the
big fppf site. Then there are an affine object `T₁` with an étale surjection `T₁ ⟶ TA`, an affine
object `U₀` with an étale morphism `a₀ : h_{U₀} ⟶ X`, and a morphism `T₁ ⟶ U₀` through which `x`
restricted to `T₁` factors. Each point of `TA` has such a neighbourhood through a single affine
summand of an affine coproduct atlas ([Stacks Project, Tag 03FX]); finitely many suffice, and
the coproduct of the neighbourhoods maps to the coproduct of the summands they use.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_nbhd_through_atlas`
* `AlgebraicGeometry.Space.exists_affine_etale_cover_through_affine_chart`

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal Limits

universe u

namespace AlgebraicGeometry.Space


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An affine étale neighbourhood of a point on which a section factors through one summand of
an atlas.** Let `f : h_U ⟶ X` be a representable, surjective, étale atlas whose underlying scheme
is covered by the open immersions `j i : W i ⟶ U`. For a section `x` of `X` over `TA` and a point
`t` of `TA`, there is an affine object `V` étale over `TA` with `t` in its image, a summand
`W i` and a morphism `m : V ⟶ W i` through which `x` restricted to `V` factors. -/
theorem exists_affine_etale_nbhd_through_atlas {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hfS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hfE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    {I : Type u} {W : I → BigFppfOver B S hS} (j : ∀ i, W i ⟶ U)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)))
    {TA : BigFppfOver B S hS} (x : X.obj (op TA)) (t : (BigFppfOver.toScheme B S hS).obj TA) :
    ∃ (V : BigFppfOver B S hS) (ev : V ⟶ TA) (i : I) (m : V ⟶ W i),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Etale ((BigFppfOver.toScheme B S hS).map ev) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map ev) ∧
      f.app _ (m ≫ j i) = X.map ev.op x := by
  let G := BigFppfOver.toScheme B S hS
  let g : yoneda.obj TA ⟶ X := yonedaEquiv.symm x
  let P := hfE.1.pullback g
  let snd : P ⟶ TA := hfE.1.snd g
  let q : yoneda.obj P ⟶ yoneda.obj U := hfE.1.fst g
  have hpb : IsPullback q (yoneda.map snd) f g := hfE.1.isPullback g
  have hsndE : Etale (G.map snd) := hfE.property g q snd hpb
  have hsndS : Function.Surjective (G.map snd).base := (hfS.property g q snd hpb).surj
  obtain ⟨p, hp⟩ := hsndS t
  let q' : P ⟶ U := yoneda.preimage q
  have hq' : yoneda.map q' = q := yoneda.map_preimage q
  obtain ⟨i, w, hw⟩ := hcov (G.map q' p)
  have := hj i
  obtain ⟨Vo, hVo, hpV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (X := G.obj P) (x := p)
    (U := (G.map q') ⁻¹ᵁ (G.map (j i)).opensRange) ⟨w, hw⟩
  have hcont : B.Contains Vo.toScheme := Scheme.size_lt_of_isOpenImmersion Vo.ι P.left.2
  let V : BigFppfOver B S hS := BigFppfOver.mk B S hS hcont (Vo.ι ≫ B.inclusion.map P.hom)
  let vP : V ⟶ P := Over.homMk (ObjectProperty.homMk Vo.ι) (by apply ObjectProperty.hom_ext; rfl)
  have hGvP : G.map vP = Vo.ι := rfl
  have hrange : Set.range (Vo.ι ≫ G.map q') ⊆ Set.range (G.map (j i)) := by
    rintro _ ⟨v, rfl⟩
    exact hVsub v.2
  let mS : Vo.toScheme ⟶ G.obj (W i) :=
    AlgebraicGeometry.IsOpenImmersion.lift (G.map (j i)) (Vo.ι ≫ G.map q') hrange
  have hmS : mS ≫ G.map (j i) = Vo.ι ≫ G.map q' := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hmS' : mS ≫ B.inclusion.map (W i).hom = B.inclusion.map V.hom := by
    have h1 : G.map (j i) ≫ B.inclusion.map U.hom = B.inclusion.map (W i).hom :=
      congrArg B.inclusion.map (Over.w (j i))
    have h2 : G.map q' ≫ B.inclusion.map U.hom = B.inclusion.map P.hom :=
      congrArg B.inclusion.map (Over.w q')
    rw [← h1, ← Category.assoc, hmS, Category.assoc, h2]
    rfl
  obtain ⟨m, hm⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := V) (Y := W i) mS hmS'
  have hmj : m ≫ j i = vP ≫ q' := G.map_injective (by
    rw [G.map_comp, G.map_comp, hm, hGvP]
    exact hmS)
  have hGev : G.map (vP ≫ snd) = Vo.ι ≫ G.map snd := by
    rw [G.map_comp, hGvP]
    rfl
  refine ⟨V, vP ≫ snd, i, m, hVo, ?_, ⟨⟨p, hpV⟩, ?_⟩, ?_⟩
  · rw [hGev]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hsndE
  · rw [hGev]
    exact (congrArg (G.map snd) (rfl : Vo.ι ⟨p, hpV⟩ = p)).trans hp
  · have htaut := app_tautological_section_representing B S hS hpb
    rw [hmj]
    have e1 : f.app (op V) (vP ≫ q') = X.map vP.op (f.app (op P) q') :=
      NatTrans.naturality_apply f vP.op q'
    have e2 : q.app (op P) (𝟙 P) = q' := by rw [← hq']; simp
    rw [e1, ← e2, htaut, op_comp, Functor.map_comp_apply]

/-- Two sections of an algebraic space over a coproduct of the big fppf site agree as soon as
their restrictions to every summand agree. -/
theorem eq_of_map_sigmaIncl_op_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {I : Type*} [Small.{u} I] [B.AdmitsCoproductIndex I]
    {V : I → BigFppfOver B S hS} {a b : X.obj (op (BigFppfOver.sigmaObj B S hS V))}
    (h : ∀ k, X.map (BigFppfOver.sigmaIncl B S hS V k).op a =
      X.map (BigFppfOver.sigmaIncl B S hS V k).op b) : a = b := by
  refine ((isSheaf_iff_isSheaf_of_type _ X).1 hX.isSheaf _
    (BigFppfOver.sieve_sigmaCofan_mem_topology B S hS V)).isSeparatedFor.ext fun _ g hg => ?_
  obtain ⟨_, g', _, ⟨k⟩, rfl⟩ := hg
  have e₁ := congrArg (X.map g'.op) (h k)
  rwa [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply,
    ← op_comp] at e₁

/-- A finite coproduct of affine objects of the big fppf site is affine. -/
theorem isAffine_toScheme_sigmaObj {K : Type u} [Finite K] [B.AdmitsCoproductIndex K]
    {V : K → BigFppfOver B S hS} (h : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (V k))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.sigmaObj B S hS V)) :=
  inferInstanceAs (IsAffine (∐ fun k => (BigFppfOver.toScheme B S hS).obj (V k)))

/-- Morphisms out of the coproduct of a family of the big fppf site are determined by the family of
their restrictions to the summands, which can be prescribed. -/
private theorem exists_sigmaIncl_comp_eq {I : Type*} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (V : I → BigFppfOver B S hS) {Z : BigFppfOver B S hS} (h : ∀ k, V k ⟶ Z) :
    ∃ d : BigFppfOver.sigmaObj B S hS V ⟶ Z, ∀ k, BigFppfOver.sigmaIncl B S hS V k ≫ d = h k :=
  ⟨_, Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS V) h⟩

/-- **A section of an algebraic space over an affine object factors, étale-locally, through one
affine étale chart.** For an algebraic space `X` and a section `x` of `X` over an affine object
`TA` of the site, there are an affine object `T₁` with an étale surjection `w : T₁ ⟶ TA`, an
affine object `U₀` with an étale morphism `a₀ : h_{U₀} ⟶ X`, and a morphism `g : T₁ ⟶ U₀` with
`a₀(g) = x|_{T₁}`. -/
theorem exists_affine_etale_cover_through_affine_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {TA : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj TA)] (x : X.obj (op TA)) :
    ∃ (T₁ U₀ : BigFppfOver B S hS) (w : T₁ ⟶ TA) (g : T₁ ⟶ U₀) (a₀ : yoneda.obj U₀ ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₁) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) ∧
      Etale ((BigFppfOver.toScheme B S hS).map w) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map w) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a₀ ∧
      a₀.app _ g = X.map w.op x := by
  classical
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨U, f, I, W, j, e, hfS, hfE, hWaff, hιe, hjopen, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X hX
  choose V ev i m hVaff hevE hevt hfac using fun t : G.obj TA =>
    exists_affine_etale_nbhd_through_atlas f hfS hfE j hjopen
      (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1 x t
  -- finitely many neighbourhoods suffice
  obtain ⟨s, hs⟩ := (isCompact_univ (X := G.obj TA)).elim_finite_subcover
    (fun t => Set.range (G.map (ev t))) (fun t => (G.map (ev t)).isOpenMap.isOpen_range)
    (fun t _ => Set.mem_iUnion.2 ⟨t, hevt t⟩)
  let K := ↥s
  let Vk : K → BigFppfOver B S hS := fun k => V k.1
  let Wk : K → BigFppfOver B S hS := fun k => W (i k.1)
  let T₁ := BigFppfOver.sigmaObj B S hS Vk
  let U₀ := BigFppfOver.sigmaObj B S hS Wk
  obtain ⟨w, hw⟩ := exists_sigmaIncl_comp_eq Vk fun k => ev k.1
  obtain ⟨g, hg⟩ := exists_sigmaIncl_comp_eq Vk fun k =>
    m k.1 ≫ BigFppfOver.sigmaIncl B S hS Wk k
  obtain ⟨σ, hσ⟩ := exists_sigmaIncl_comp_eq Wk fun k => j (i k.1)
  have hσE : Etale (G.map σ) := by
    refine etale_toScheme_of_sigmaIncl B S hS Wk σ fun k => ?_
    rw [hσ]
    have := hjopen (i k.1)
    infer_instance
  refine ⟨T₁, U₀, w, g, yoneda.map σ ≫ f, isAffine_toScheme_sigmaObj fun k => hVaff k.1,
    isAffine_toScheme_sigmaObj fun k => hWaff (i k.1), ?_, ?_, ?_, ?_⟩
  · refine etale_toScheme_of_sigmaIncl B S hS Vk w fun k => ?_
    rw [hw]
    exact hevE k.1
  · refine ⟨fun t => ?_⟩
    obtain ⟨t', ht's, v, rfl⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
    let k : K := ⟨t', ht's⟩
    refine ⟨(G.map (BigFppfOver.sigmaIncl B S hS Vk k)) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← G.map_comp, hw]
  · exact MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Etale.{u}) σ).2 hσE) hfE
  · refine eq_of_map_sigmaIncl_op_eq hX fun k => ?_
    rw [← NatTrans.naturality_apply, ← Functor.map_comp_apply, ← op_comp, hw]
    change f.app _ ((BigFppfOver.sigmaIncl B S hS Vk k ≫ g) ≫ σ) = _
    rw [hg, Category.assoc, hσ]
    exact hfac k.1

end AlgebraicGeometry.Space

end
