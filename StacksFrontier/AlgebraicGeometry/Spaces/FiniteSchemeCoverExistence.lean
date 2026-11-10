module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverFromModuleHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationQuotientQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentAlgebra

/-!
# Stacks 0GUN: a finite and finitely presented scheme cover, finite étale over a dense open

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` such that `|X|`
has finitely many irreducible components. Stacks 0GUN asserts that

1. there is a surjective finite morphism `f : Y ⟶ X` of finite presentation, with `Y` a scheme,
   which is finite étale over a quasi-compact dense open `U ⊆ X`, and
2. given a surjective étale `V ⟶ X`, `Y` can be chosen so that every point of `Y` has an open
   neighbourhood `W ⊆ Y` such that `W ⟶ X` factors through `V`.

## The argument

Clause (2) is first reduced to an affine chart `c : h_A ⟶ V`, `A` affine, with `h_A ⟶ X`
surjective étale (`AlgebraicGeometry.Space.exists_affine_chart_through`). Stacks 0GUL (2) gives a
surjective integral `π : h_Y ⟶ X` from a scheme, finite étale over a quasi-compact dense open
`U`, factoring Zariski locally through `h_A ⟶ X`. By
`AlgebraicGeometry.Space.exists_finiteSchemeCover_of_moduleHom` it suffices to find a
quasi-coherent module `𝒢` of finite presentation and a morphism `𝒢 ⟶ π_* 𝒪_Y` whose image contains
finitely many prescribed sections over affine étale charts. These sections lie in a quasi-coherent
submodule `𝒩 ⊆ π_* 𝒪_Y` of finite type (the étale extension property of Stacks 0829,
`AlgebraicGeometry.Space.ChartExtensionProperty.exists_forall_mem`), `𝒩` is a quotient of a
module `𝒢` of finite presentation
(`AlgebraicGeometry.Space.exists_epi_of_isFinitePresentationOnSite_of_isFiniteType`), and an
epimorphism of quasi-coherent modules is surjective on affine charts
(`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`).

Clause (1) is clause (2) for the identity of `X`.

In place of the limit argument of the source (Stacks 0GUM, 07SR, 0827, 04AK) the cover is cut
out directly as a closed subspace of finite presentation of `\underline{Spec}_X(Sym 𝒢)`; see
`AlgebraicGeometry.Space.exists_finiteSchemeCover_of_algebraHom`.

## Main results

* `AlgebraicGeometry.Space.exists_isFinitePresentationOnSite_hom_forall_mem_range`: finitely many
  sections of a quasi-coherent module over affine étale charts of a quasi-compact quasi-separated
  algebraic space are reached by a morphism from a module of finite presentation.
* `AlgebraicGeometry.Space.exists_finiteSchemeCover_finiteEtaleOverDenseOpen_and_refining`:
  Stacks 0GUN, both clauses.

## References

* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Finitely many sections over affine charts are reached by a module of finite presentation.**
Let `X` be a quasi-compact and quasi-separated algebraic space and `ℳ` a quasi-coherent
`𝒪_X`-module. Finitely many sections `σ x` of `ℳ` over affine étale charts `T x` of `X` lie in the
image of a morphism `𝒢 ⟶ ℳ` from a quasi-coherent `𝒪_X`-module `𝒢` of finite presentation. -/
theorem exists_isFinitePresentationOnSite_hom_forall_mem_range (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (M : Modules.{u, u} B S hS X hX) (hM : M.IsQuasicoherentOnSite) {α : Type*}
    (t : Finset α) (T : α → SmallEtale B S hS X) (hT : ∀ x, IsAffine (chartScheme (T x)))
    (σ : ∀ x, M.val.obj (op (T x))) :
    ∃ G : Modules.{u, u} B S hS X hX, G.IsQuasicoherentOnSite ∧ G.IsFinitePresentationOnSite ∧
      ∃ γ : G ⟶ M, ∀ x ∈ t, ∃ y, γ.val.app (op (T x)) y = σ x := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX M hM
  obtain ⟨D, hD⟩ := (chartExtensionProperty_id (hX := hX) hZ hXqc hXqs hcart).exists_forall_mem
    hcart t T (fun x => (T x).1.hom) (fun _ => Category.comp_id _) hT σ
  let N := D.toSubmodule M
  have : N.toSheafOfModules.IsFiniteTypeOnSite := D.isFiniteTypeOnSite_toSubmodule hcart
  have hNqc : N.toSheafOfModules.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX _).2
      (D.isCartesianOnAffineCharts_toSubmodule hcart)
  obtain ⟨G, hG, p, hp⟩ := exists_epi_of_isFinitePresentationOnSite_of_isFiniteType B S hS hZ hX
    hXqc hXqs N.toSheafOfModules hNqc
  have hGqc : G.IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite G
  refine ⟨G, hGqc, hG, p ≫ N.ι, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite p hp hGqc hNqc (T x) (hT x)
    ⟨σ x, (ChartSubmodule.mem_toSubmodule D (T x) (σ x)).2 (hD x hx)⟩
  refine ⟨y, ?_⟩
  change (N.ι.val.app (op (T x))) ((p.val.app (op (T x))) y) = σ x
  rw [hy]
  rfl

section Tag

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Clause (2) of Stacks 0GUN for an affine chart.** For a surjective étale `p : h_V ⟶ X` with
`V` affine, there is a finite and finitely presented scheme cover of `X`, finite étale over a
quasi-compact dense open, factoring Zariski locally through `p`. -/
theorem exists_finiteSchemeCover_refining_of_isAffine {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : yoneda.obj V ⟶ X) (hpsurj : IsSurjective B S hS p) (hp : IsEtale B S hS p) :
    ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
      IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U ∧
        FactorsZariskiLocallyThrough B S hS p Y f := by
  obtain ⟨Y, π, U, ⟨hπsurj, hπint, hU, hUqc, hUdense, hπUfin, hπUet⟩, hfac⟩ :=
    (exists_integralSchemeCover_finiteEtaleOverDenseOpen_and_refining B S hS hZ X hX hXqc hXqs
      hcomp).2 (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) p hpsurj hp
  obtain ⟨Vs, Us, hVs, hUs, s, s', h⟩ := exists_finiteSchemeCover_of_moduleHom B S hS hZ ⟨X, hX⟩
    hXqc hXqs π hπint hπsurj U hU hUqc hUdense hπUfin hπUet hV p hp hpsurj hfac
  let Ya : AlgebraicSpaces B S hS := ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩
  let 𝒜 := pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
    Ya ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS)))
  let M : Modules.{u, u} B S hS X hX := AlgebraSheaf.underlyingModule 𝒜
  have hM : M.IsQuasicoherentOnSite :=
    isQuasicoherent_pushforwardAlgebra_of_isAffineHom' B S hS _
      (isAffineHom_of_isIntegralHom π hπint)
  let Tc : {x // x ∈ s} ⊕ {x // x ∈ s'} → SmallEtale B S hS X := Sum.elim (fun _ => Vs) fun _ => Us
  let σ : ∀ x, M.val.obj (op (Tc x)) := fun x => match x with
    | Sum.inl x => x.1
    | Sum.inr x => x.1
  obtain ⟨G, hGqc, hGfp, γ, hγ⟩ := exists_isFinitePresentationOnSite_hom_forall_mem_range B S hS
    hZ hX hXqc hXqs M hM Finset.univ Tc (fun x => match x with
      | Sum.inl _ => hVs
      | Sum.inr _ => hUs) σ
  obtain ⟨Y', f, hf, hfac'⟩ := h G hGqc hGfp γ
    (fun x hx => hγ (Sum.inl ⟨x, hx⟩) (Finset.mem_univ _))
    (fun x hx => hγ (Sum.inr ⟨x, hx⟩) (Finset.mem_univ _))
  exact ⟨Y', f, U, hf, hfac'⟩

/-- **Stacks Project, Tag 0GUN.** Let `X` be a quasi-compact and quasi-separated algebraic
space over a scheme `S` such that `|X|` has finitely many irreducible components. Then

1. there is a surjective, finite and finitely presented morphism `f : h_Y ⟶ X` from the
   presheaf represented by an object `Y` of the big fppf site — a scheme over `S` — and a
   quasi-compact open subspace `U ⊆ X` with dense point set over which `f` is finite étale, and
2. given a surjective étale morphism `p : V ⟶ X` from an algebraic space, such a cover can be
   chosen so that it factors through `p` on a representable open subspace neighbourhood of
   every one of its points.

Clause (2) for `p` is reduced to an affine chart `h_A ⟶ V`, where it is
`AlgebraicGeometry.Space.exists_finiteSchemeCover_refining_of_isAffine`; clause (1) is clause (2)
at the identity of `X`. -/
@[stacks 0GUN]
theorem exists_finiteSchemeCover_finiteEtaleOverDenseOpen_and_refining
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite) :
    (∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
      IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U) ∧
    ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V →
      ∀ p : V ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
        ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
          IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U ∧
            FactorsZariskiLocallyThrough B S hS p Y f := by
  refine (and_iff_right_of_imp fun H => ?_).2 ?_
  · obtain ⟨Y, f, U, hf, -⟩ := H X hX (𝟙 X) (isSurjective_id B S hS X) (isEtale_id B S hS X)
    exact ⟨Y, f, U, hf⟩
  · intro V hV p hp hpe
    obtain ⟨V₀, c, hcsurj, hcet⟩ := hV.exists_atlas
    have hc : IsSurjective B S hS c := isSurjective_of_presheafSurjective B S hS c hcsurj
    have hce : IsEtale B S hS c := isEtale_of_presheaf_etale B S hS hcet
    have hcp : IsSurjective B S hS (c ≫ p) := by
      change Function.Surjective (pointsMap B S hS (yoneda.obj V₀) (c ≫ p))
      rw [pointsMap_comp B S hS (yoneda.obj V₀) c p]
      exact hp.comp hc
    obtain ⟨A, a, b, hAaff, hasurj, haet, hba⟩ := exists_affine_chart_through B S hS hX hXqc V₀
      (c ≫ p) hcp (isEtale_comp B S hS hce hpe)
    obtain ⟨Y, f, U, hf, hfac⟩ :=
      exists_finiteSchemeCover_refining_of_isAffine B S hS hZ hX hXqc hXqs hcomp hAaff a hasurj haet
    refine ⟨Y, f ≫ 𝟙 X, U, by rwa [Category.comp_id], ?_⟩
    exact hfac.comp B S hS (𝟙 X) p (b ≫ c) (by rw [Category.comp_id, ← hba, Category.assoc])

end Tag

end AlgebraicGeometry.Space

end
