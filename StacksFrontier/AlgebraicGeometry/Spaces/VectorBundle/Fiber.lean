module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Scheme.GlobalEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ResidueFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.LocalModel
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraChartComparison

/-!
# The fibres of a vector bundle are affine spaces

Let `W` be an algebraic space over a scheme `S` in a big fppf site, `ℰ` a finite locally free
`𝒪_W`-module of rank `r` and `p : E = \underline{Spec}_W(Sym(ℰ)) ⟶ W` its vector bundle. For a
point `x` of `W` with residue field `κ(x)`, when `W` is decent, the fibre `E_x = E ×_W Spec κ(x)`
is affine space `𝐀^r_{κ(x)}` over `κ(x)`. This is the hypothesis `X_y ≅ 𝐀^r_{κ(y)}` of
Stacks 0ERG for the projection of a vector bundle, which Stacks 0ERH applies to a line bundle.

The proof is the local computation of the fibre on an étale chart with the same residue field.
By Stacks 0BBP the point `x` has an affine elementary étale neighbourhood `(U, u) ⟶ (W, x)`, with
`κ(x) ≅ κ(u)`, so `E_x` is the fibre of `E ×_W U = Spec Γ(U, Sym(ℰ)) ⟶ U` over `u`. On `U`
itself `ℰ` need not be free, but the comparison `Sym_{𝒪(U)}(ℰ(U)) ⟶ Γ(U, Sym(ℰ))` becomes an
isomorphism after base change to an affine chart `V ⟶ U` on which `ℰ` is free, through a point
`v` above `u`, since `ℰ` and `Sym(ℰ)` are quasi-coherent
(`AlgebraicGeometry.Space.SymAlgSections.bijective_baseChange_chartSymAlgHom`). As `κ(u) ⟶ κ(v)`
is faithfully flat, the fibre ring `κ(u) ⊗ Γ(U, Sym(ℰ))` is `Sym_{κ(u)}(κ(u) ⊗ ℰ(U))`, a
polynomial ring in `r` variables
(`SymmetricAlgebra.exists_isPushout_mvPolynomial_of_bijective_baseChange`).

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_fiber_vectorBundleChartHom`: the fibre of
  `E ×_W U ⟶ U` over a point `u` of an affine chart is `𝐀^r_{κ(u)}`.
* `AlgebraicGeometry.Space.exists_isPullback_vectorBundleProjection_residueFieldMorphism`: for a
  point `x` of a decent algebraic space `W`, the fibre of `p : E ⟶ W` over `Spec κ(x) ⟶ W` is
  represented by a scheme isomorphic over `Spec κ(x)` to `𝐀^r_{κ(x)}`.
* `BaseSpaceDimensionSituation.exists_isPullback_vectorBundleProjection_residueFieldMorphism`:
  the same at the residue field `κ(x)` of a point of a good algebraic space in the situation of
  Stacks 0EDT.

## Implementation notes

Affine space over `κ(x)` is taken on an arbitrary finite index type `n` with `r` elements, in
the universe of the schemes, since `AlgebraicGeometry.AffineSpace` asks for its index type to
live there.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0ERH](https://stacks.math.columbia.edu/tag/0ERH)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 01M1](https://stacks.math.columbia.edu/tag/01M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- **Every point of a chart lies under a point of an affine chart above it trivializing `ℰ` with
rank `r`**, when `ℰ` is finite locally free of rank `r`. -/
theorem exists_trivializing_affine_chart_over (r : ℕ)
    [hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (V₀ : SmallEtale B S hS W.1) (z₀ : chartScheme V₀) :
    ∃ (V : SmallEtale B S hS W.1) (φ : V ⟶ V₀) (ι : Type u) (_ : Finite ι)
      (_ : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
      (_ : ι ≃ Fin r) (z : chartScheme V), IsAffine (chartScheme V) ∧
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS W.1).map φ) z = z₀ := by
  obtain ⟨q, hq, hrank⟩ := hr.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨V, φ, ⟨i, ⟨g⟩⟩, hV, z, hz⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS W.1 (q.coversTop V₀) z₀
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨V, φ, (q.generators i).I, Finite.of_equiv _ (hrank i).some.symm,
    overFreeIsoOfHom B S hS W F g (asIso (q.generators i).π).symm, (hrank i).some, z, hV, hz⟩

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]

/-- **The fibre of `E ×_W U ⟶ U` over a point of an affine chart is affine space over the
residue field**: for `ℰ` of rank `r`, a type `n` with `r` elements, an affine chart `U` and a
point `u` of it, the square formed by `Spec κ(u)[X_i, i ∈ n] ⟶ E ×_W U`, the projections and
`Spec κ(u) ⟶ U` is cartesian. -/
theorem exists_isPullback_fiber_vectorBundleChartHom (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r] {n : Type u} [Finite n]
    (hn : Nat.card n = r)
    (U : SmallEtale B S hS W.1) [hU : IsAffine (chartScheme U)] (u : chartScheme U) :
    ∃ ψ : (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U) →+*
        MvPolynomial n ((chartScheme U).residueField u),
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom MvPolynomial.C))
        ((BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F U))
        ((chartScheme U).fromSpecResidueField u) := by
  classical
  obtain ⟨Q, φ, ι, hι, e, ε, z, hQ, rfl⟩ := exists_trivializing_affine_chart_over B S hS W F r U u
  set φs := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS W.1).map φ) with hφs
  let : Algebra (chartRing B S hS W.1 W.2 U) (chartRing B S hS W.1 W.2 Q) :=
    chartAlgebra (hF := W.2) φ
  let : Algebra (chartRing B S hS W.1 W.2 U) ((chartScheme U).residueField (φs z)) :=
    @RingHom.toAlgebra (chartRing B S hS W.1 W.2 U) ((chartScheme U).residueField (φs z)) _ _
      ((chartScheme U).globalEvaluation (φs z)).hom
  let : Algebra (chartRing B S hS W.1 W.2 Q) ((chartScheme Q).residueField z) :=
    @RingHom.toAlgebra (chartRing B S hS W.1 W.2 Q) ((chartScheme Q).residueField z) _ _
      ((chartScheme Q).globalEvaluation z).hom
  let : Algebra ((chartScheme U).residueField (φs z)) ((chartScheme Q).residueField z) :=
    (φs.residueFieldMap z).hom.toAlgebra
  let : Algebra (chartRing B S hS W.1 W.2 U) ((chartScheme Q).residueField z) :=
    ((algebraMap (chartRing B S hS W.1 W.2 Q) ((chartScheme Q).residueField z)).comp
      (algebraMap (chartRing B S hS W.1 W.2 U) (chartRing B S hS W.1 W.2 Q))).toAlgebra
  have : IsScalarTower (chartRing B S hS W.1 W.2 U) (chartRing B S hS W.1 W.2 Q)
      ((chartScheme Q).residueField z) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (chartRing B S hS W.1 W.2 U) ((chartScheme U).residueField (φs z))
      ((chartScheme Q).residueField z) := IsScalarTower.of_algebraMap_eq fun t =>
    (ConcreteCategory.congr_hom (Scheme.globalEvaluation_naturality φs z) t)
  let := SymAlgSections.chartSymAlgebra B S hS W F U
  have hFq : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} F :=
    SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F
  have hAq := isQuasicoherent_symmetricAlgebraSheaf B S hS W F hFq
  have hbij := SymAlgSections.bijective_chartSymAlgHom B S hS W F Q hQ e
  have hθ := SymAlgSections.bijective_baseChange_chartSymAlgHom B S hS W F φ hU hQ hFq hAq hbij
  obtain ⟨ψ, hpush⟩ := SymmetricAlgebra.exists_isPushout_mvPolynomial_of_bijective_baseChange
    (K := (chartScheme U).residueField (φs z)) (L := (chartScheme Q).residueField z)
    (SymAlgSections.chartSymAlgHom B S hS W F U) hθ
    (SymAlgSections.baseChangeSectionsBasis B S hS W F φ hU hQ hFq e
      (ε.trans (Finite.equivFinOfCardEq hn).symm))
  refine ⟨ψ, ?_⟩
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (chartScheme U).isoSpec.symm (by simp) (by simp) ?_ ?_
  · rw [toScheme_map_affineChartSpecHom, Iso.refl_hom, Category.id_comp, specChartMap]
    rfl
  · have h : Spec.map ((chartScheme U).globalEvaluation (φs z)) =
        (chartScheme U).fromSpecResidueField (φs z) ≫ (chartScheme U).isoSpec.hom :=
      Spec.map_preimage _
    rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    exact (congrArg (· ≫ (chartScheme U).isoSpec.inv) h).trans
      ((Category.assoc _ _ _).trans (by rw [Iso.hom_inv_id, Category.comp_id]))

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- **The fibre of a vector bundle over a point is affine space over the residue field.** Let
`W` be a decent algebraic space, `ℰ` a finite locally free `𝒪_W`-module of rank `r` and
`p : E ⟶ W` its vector bundle. For a point `x` of `W` with residue field `κ(x)`, represented by
the monomorphism `Spec κ(x) ⟶ W`, the fibre `E ×_W Spec κ(x)` is represented by a scheme `T` over
`Spec κ(x)` isomorphic, over `Spec κ(x)`, to affine space `𝐀^r_{κ(x)}` on a type `n` with `r`
elements. -/
theorem exists_isPullback_vectorBundleProjection_residueFieldMorphism (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r] {n : Type u} [Finite n]
    (hn : Nat.card n = r) (hdec : IsDecentSpace B S hS W.1) (x : points B S hS W.1) :
    ∃ (T : BigFppfOver B S hS) (a : yoneda.obj T ⟶ (vectorBundle B S hS W F).obj.left.1)
      (b : T ⟶ (residueFieldRepresentative B S hS W.1 hdec x).1.siteObject B S hS W.1),
      IsPullback a (yoneda.map b) (vectorBundleProjection B S hS W F).hom
          (residueFieldMorphism B S hS W.1 hdec x) ∧
        ∃ e : (BigFppfOver.toScheme B S hS).obj T ≅
            𝔸(n; Spec (.of (residueField B S hS W.1 hdec x))),
          e.hom ≫ 𝔸(n; Spec (.of (residueField B S hS W.1 hdec x))) ↘
              Spec (.of (residueField B S hS W.1 hdec x)) =
            (BigFppfOver.toScheme B S hS).map b := by
  obtain ⟨E, hEaff, -, φ, hφ, g, hgspec, hgsq⟩ :=
    exists_affine_elementaryEtaleNeighborhood' B S hS W.2 hdec x
  let U : SmallEtale B S hS W.1 := etaleChartOfIsEtale B S hS (X := W) E.toSpace E.etale_toSpace
  have : IsAffine (chartScheme U) := hEaff
  obtain ⟨ψ, hpb⟩ := exists_isPullback_fiber_vectorBundleChartHom B S hS W F r hn U E.point
  let ρ : residueFieldObject B S hS E.scheme E.point E.residueField_contained ⟶ U.obj.left :=
    residueFieldMap B S hS E.scheme E.point E.residueField_contained
  let T := pullback (vectorBundleChartHom B S hS W F U) ρ
  -- the residue field comparison is an isomorphism
  have hgIso : IsIso g := by
    have h1 : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
      have : IsIso (CommRingCat.ofHom φ) :=
        (RingEquiv.ofBijective φ hφ).toCommRingCatIso.isIso_hom
      infer_instance
    have h2 : IsIso (B.inclusion.map g.left) := by rw [hgspec]; exact h1
    have h3 : IsIso ((Over.forget _).map g) := isIso_of_fully_faithful B.inclusion g.left
    exact isIso_of_reflects_iso g (Over.forget _)
  -- the cartesian square over the residue field point of the chart
  have hsq₁ := (IsPullback.of_hasPullback (vectorBundleChartHom B S hS W F U) ρ).map yoneda
  have hsq₂ := hsq₁.paste_horiz (isPullback_vectorBundleChart B S hS W F U)
  have hbot : yoneda.map ρ ≫ U.obj.hom = yoneda.map g ≫ residueFieldMorphism B S hS W.1 hdec x :=
    hgsq.symm
  rw [hbot] at hsq₂
  have hsq₃ := hsq₂.paste_vert (IsPullback.of_vert_isIso (f := 𝟙 W.1)
    (snd := yoneda.map g) ⟨by rw [Category.comp_id]⟩)
  rw [Category.comp_id, ← Functor.map_comp] at hsq₃
  refine ⟨T, _, pullback.snd _ _ ≫ g, hsq₃, ?_⟩
  -- the scheme of the fibre
  have hT := (IsPullback.of_hasPullback (vectorBundleChartHom B S hS W F U) ρ).map
    (BigFppfOver.toScheme B S hS)
  let e₁ := hT.isoIsPullback _ _ hpb
  let gs := (BigFppfOver.toScheme B S hS).map g
  have : IsIso gs := Functor.map_isIso _ g
  let e₃ : 𝔸(n; (BigFppfOver.toScheme B S hS).obj
        (residueFieldObject B S hS E.scheme E.point E.residueField_contained)) ≅
      𝔸(n; (BigFppfOver.toScheme B S hS).obj
        ((residueFieldRepresentative B S hS W.1 hdec x).1.siteObject B S hS W.1)) :=
    { hom := AffineSpace.map n gs
      inv := AffineSpace.map n (inv gs)
      hom_inv_id := by rw [← AffineSpace.map_comp, IsIso.hom_inv_id, AffineSpace.map_id]
      inv_hom_id := by rw [← AffineSpace.map_comp, IsIso.inv_hom_id, AffineSpace.map_id] }
  refine ⟨e₁ ≪≫ (AffineSpace.SpecIso n ((chartScheme U).residueField E.point)).symm ≪≫ e₃,
    ?_⟩
  refine (congrArg (fun t => e₁.hom ≫ (AffineSpace.SpecIso n
      ((chartScheme U).residueField E.point)).inv ≫ t) (AffineSpace.map_over (n := n) gs)).trans ?_
  refine (congrArg (fun t => e₁.hom ≫ t) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun t => e₁.hom ≫ t ≫ gs)
    (AffineSpace.SpecIso_inv_over ((chartScheme U).residueField E.point))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ gs) (IsPullback.isoIsPullback_hom_snd _ _ hT hpb)).trans ?_
  exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm

/-- **The fibre of a vector bundle over a point of a good space is affine space over the residue
field.** In the situation of Stacks 0EDT let `W/B` be good, `ℰ` a finite locally free
`𝒪_W`-module of rank `r` and `p : E ⟶ W` its vector bundle. For every point `x` of `W` the fibre
of `p` over `Spec κ(x) ⟶ W` is represented by a scheme isomorphic over `Spec κ(x)` to
`𝐀^r_{κ(x)}`: this is the hypothesis `X_y ≅ 𝐀^r_{κ(y)}` of Stacks 0ERG for `p`. -/
theorem BaseSpaceDimensionSituation.exists_isPullback_vectorBundleProjection_residueFieldMorphism
    (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r] {n : Type u} [Finite n]
    (hn : Nat.card n = r) (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)
    (x : points D.site D.base D.base_mem W.1) :
    ∃ (T : BigFppfOver D.site D.base D.base_mem)
      (a : yoneda.obj T ⟶ (vectorBundle D.site D.base D.base_mem W F).obj.left.1)
      (b : T ⟶ (D.residueFieldRepresentative sW hW x).1.siteObject D.site D.base D.base_mem W.1),
      IsPullback a (yoneda.map b) (vectorBundleProjection D.site D.base D.base_mem W F).hom
          (D.residueFieldMorphism sW hW x) ∧
        ∃ e : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T ≅
            𝔸(n; Spec (.of (D.residueField sW hW x))),
          e.hom ≫ 𝔸(n; Spec (.of (D.residueField sW hW x))) ↘ Spec (.of (D.residueField sW hW x)) =
            (BigFppfOver.toScheme D.site D.base D.base_mem).map b :=
  AlgebraicGeometry.Space.exists_isPullback_vectorBundleProjection_residueFieldMorphism D.site
    D.base D.base_mem W F r hn (D.isDecentSpace_of_isGood sW hW) x

end AlgebraicGeometry.Space

end
