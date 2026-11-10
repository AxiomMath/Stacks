module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionFreeChart

/-!
# Reading a rank-one trivialization on the meromorphic sections over a chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `L` be an
`𝒪_F`-module. Over an étale scheme chart `W` on which `L` is free of rank one with generator `e`,
the map `a ↦ a ⊗ e` from the meromorphic functions `𝒦_F(W)` to the meromorphic sections
`𝒦_F(W) ⊗_{𝒪_F(W)} L(W)` of Stacks 0EN5 is bijective.

Freeness of rank one is taken in the form of Stacks 0409's rank clause
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`): over the slice at a chart `V`, `L` is
the colimit of a one-element cofan of copies of the structure sheaf. The cofan injection is then an
isomorphism (`CategoryTheory.Limits.isIso_cofanInj_of_unique`), which over each chart `W` over `V`
is a module isomorphism `𝒪_F(W) ≅ L(W)`. The generators over the charts `W` are the values of the
section of `L` over the slice that `SheafOfModules.unitHomEquiv` attaches to the cofan injection,
so they are compatible with restriction along morphisms of charts over `V`.

Finally, a section of the sheaf `𝒦_F(L)` of Stacks 0EN5 is, on a covering of its chart, the image
of a meromorphic section.

## Main definitions

* `AlgebraicGeometry.Space.siteChart`: an étale scheme chart of `F`, read as an object of the
  underlying category of the small étale ringed site.

## Main results

* `Stacks.bijective_tmul_apply_one`: for a module isomorphic to its base ring with generator
  `ψ 1`, the map `a ↦ a ⊗ ψ 1` out of any module over that ring is bijective.
* `Stacks.bijective_tmul_of_bijective_smul`: the same with the isomorphism presented as
  bijectivity of multiplication by the generator.
* `AlgebraicGeometry.Space.exists_generator_linearEquiv_of_isColimit`: a one-element cofan of
  copies of the structure sheaf whose colimit `L` is over the slice at `V` gives, compatibly
  over all charts `W` over `V`, a generator `e` of `L(W)` which is the image of `1` under a
  linear isomorphism `𝒪_F(W) ≅ L(W)`.
* `AlgebraicGeometry.Space.exists_generator_of_isColimit`: the same generator read on
  meromorphic sections, so that `a ↦ a ⊗ e` is bijective on the meromorphic functions, and
  `AlgebraicGeometry.Space.exists_generator_smul_of_isColimit`: read on regular functions, so
  that `r ↦ r • e` is bijective on `𝒪_F(W)`.
* `AlgebraicGeometry.Space.exists_generator_cover_of_isInvertible` and
  `AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`: the same two over a
  covering family of every chart, for an invertible `L`.
* `AlgebraicGeometry.Space.isLocallySurjective_toSheafify_meromorphicSectionModuleUp`: the
  sheafification map of the presheaf `L ⊗_{𝒪_F} 𝒦_F` of meromorphic sections is locally
  surjective.
* `AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`: a section of
  `𝒦_F(L)` over a chart is, over a covering sieve of that chart, the image of a meromorphic
  section of `L ⊗_{𝒪_F} 𝒦_F`.

## Implementation notes

`AlgebraicGeometry.Space.chartRing` and the module instances on the sections of an `𝒪_F`-module
are keyed on `AlgebraicGeometry.Space.SmallEtale`, while the slice instances of the
sheaves-of-modules API are registered at `(AlgebraicGeometry.Space.smallEtaleRingedSite …).C`. The
two are the same type, but instance search does not unfold
`AlgebraicGeometry.Space.smallEtaleRingedSite`; the binders here are at the `SmallEtale` spelling,
and `AlgebraicGeometry.Space.siteChart` converts to the other.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace Stacks

/-- If `ψ : R ≃ₗ[R] M` then for every `R`-module `K` the map `a ↦ a ⊗ ψ 1` is a bijection of `K`
onto `K ⊗_R M`. -/
theorem bijective_tmul_apply_one {R : Type*} [CommRing R] {K : Type*} [AddCommGroup K]
    [Module R K] {M : Type*} [AddCommGroup M] [Module R M] (ψ : R ≃ₗ[R] M) :
    Function.Bijective fun a : K ↦ a ⊗ₜ[R] ψ 1 := by
  have key : ((TensorProduct.rid R K).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R K) ψ) : K → K ⊗[R] M) =
      fun a : K ↦ a ⊗ₜ[R] ψ 1 := by
    funext a
    change (TensorProduct.congr (LinearEquiv.refl R K) ψ)
      ((TensorProduct.rid R K).symm a) = _
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_tmul]
    rfl
  rw [← key]
  exact LinearEquiv.bijective _

/-- If multiplication by `m : M` is a bijection of `R` onto `M` then for every `R`-module `K` the
map `a ↦ a ⊗ m` is a bijection of `K` onto `K ⊗_R M`. -/
theorem bijective_tmul_of_bijective_smul {R : Type*} [CommRing R] {K : Type*} [AddCommGroup K]
    [Module R K] {M : Type*} [AddCommGroup M] [Module R M] (m : M)
    (h : Function.Bijective fun r : R ↦ r • m) :
    Function.Bijective fun a : K ↦ a ⊗ₜ[R] m := by
  have hone : LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M m) h 1 = m :=
    LinearMap.toSpanSingleton_apply_one R M m
  simpa only [hone] using bijective_tmul_apply_one (K := K)
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M m) h)

end Stacks

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- An étale scheme chart of `F`, read as an object of the underlying category of the small
étale ringed site. -/
abbrev siteChart (V : SmallEtale B S hS F) : (smallEtaleRingedSite B S hS F hF).C := V

/-- **A rank-one trivialization over a chart, as a linear isomorphism of the sections.** Let `L`
be a sheaf of `𝒪_F`-modules which over the slice at an étale scheme chart `V` is the colimit of a
cofan of one copy of the structure sheaf. Then every chart `W` over `V` carries a section `e` of
`L`, compatibly with restriction, which is the image of `1` under a linear isomorphism
`𝒪_F(W) ≅ L(W)`. -/
theorem exists_generator_linearEquiv_of_isColimit (L : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (ι : ∀ _ : Fin 1, SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          (siteChart B S hS F hF V)) ⟶
      L.over (siteChart B S hS F hF V))
    (hc : IsColimit (Cofan.mk (L.over (siteChart B S hS F hF V)) ι)) :
    ∃ e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W),
      (∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
          (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
        ∃ ψ : chartRing B S hS F hF W ≃ₗ[chartRing B S hS F hF W] L.val.obj (op W),
          ψ 1 = e W k := by
  have hiso : IsIso (ι default) := isIso_cofanInj_of_unique ι hc
  refine ⟨fun W k ↦ ((L.over (siteChart B S hS F hF V)).unitHomEquiv
      (ι default)).val (op (Over.mk k)), ?_, ?_⟩
  · intro W W' k g
    exact PresheafOfModules.sections_property
      (M := (L.over (siteChart B S hS F hF V)).val)
      ((L.over (siteChart B S hS F hF V)).unitHomEquiv (ι default))
      (Over.homMk (V := Over.mk k) g rfl : Over.mk (g ≫ k) ⟶ Over.mk k).op
  · intro W k
    exact ⟨((SheafOfModules.evaluation.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
        (siteChart B S hS F hF V)) (op (Over.mk k))).mapIso
      (asIso (ι default))).toLinearEquiv, rfl⟩

/-- **A rank-one trivialization over a chart, read on meromorphic sections.** Let `L` be a
sheaf of `𝒪_F`-modules which over the slice at an étale scheme chart `V` is the colimit of a
cofan of one copy of the structure sheaf. Then every chart `W` over `V` carries a section `e` of
`L`, compatibly with restriction, such that `a ↦ a ⊗ e` is a bijection of the meromorphic
functions `𝒦_F(W)` onto the meromorphic sections `𝒦_F(W) ⊗_{𝒪_F(W)} L(W)` of Stacks 0EN5. -/
theorem exists_generator_of_isColimit (L : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (ι : ∀ _ : Fin 1, SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          (siteChart B S hS F hF V)) ⟶
      L.over (siteChart B S hS F hF V))
    (hc : IsColimit (Cofan.mk (L.over (siteChart B S hS F hF V)) ι)) :
    ∃ e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W),
      (∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
          (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
        Function.Bijective fun x : (meromorphicChartSheaf B S hS F hF).obj.obj (op W) ↦
          (x ⊗ₜ[chartRing B S hS F hF W] e W k :
            (meromorphicSectionModule B S hS F hF L).obj (op W)) := by
  obtain ⟨e, hcompat, hequiv⟩ :=
    exists_generator_linearEquiv_of_isColimit B S hS F hF L V ι hc
  refine ⟨e, hcompat, fun W k ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := hequiv W k
  rw [← hψ]
  exact Stacks.bijective_tmul_apply_one ψ

/-- **A rank-one trivialization over a chart, read on regular functions.** In the situation of
`AlgebraicGeometry.Space.exists_generator_of_isColimit` the generator `e` over a chart `W` over
`V` generates `L(W)` freely over the regular functions: `r ↦ r • e` is a bijection of `𝒪_F(W)`
onto `L(W)`. -/
theorem exists_generator_smul_of_isColimit (L : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (ι : ∀ _ : Fin 1, SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          (siteChart B S hS F hF V)) ⟶
      L.over (siteChart B S hS F hF V))
    (hc : IsColimit (Cofan.mk (L.over (siteChart B S hS F hF V)) ι)) :
    ∃ e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W),
      (∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
          (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k := by
  obtain ⟨e, hcompat, hequiv⟩ :=
    exists_generator_linearEquiv_of_isColimit B S hS F hF L V ι hc
  refine ⟨e, hcompat, fun W k ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := hequiv W k
  convert ψ.bijective using 1
  funext r
  rw [← hψ, ← map_smul ψ r 1, smul_eq_mul, mul_one]

/-- **The sheafification map of the meromorphic sections is locally surjective.** Every section
of the sheaf `𝒦_F(L)` of Stacks 0EN5 over a chart is, on a covering of that chart, the image of
a section of the presheaf `L ⊗_{𝒪_F} 𝒦_F`. -/
theorem isLocallySurjective_toSheafify_meromorphicSectionModuleUp
    (M : Modules.{u, u} B S hS F hF) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F)
        (meromorphicSectionModuleUp B S hS F hF M)) :=
  ((SmallEtale.topology B S hS F).W_toSheafify _).isLocallySurjective

/-- **A section of `𝒦_F(L)` over a chart is a meromorphic section on a covering of that
chart.** For a section `t` of the sheaf of meromorphic sections of Stacks 0EN5 over a chart `V`
there is a covering sieve `T` of `V` such that over every member `W ⟶ V` of `T` the restriction
of `t` is the image of an element of `L(W) ⊗_{𝒪_F(W)} 𝒦_F(W)`. -/
theorem exists_eval_toMeromorphicSectionSheaf_sieve_mem (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (t : (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ SmallEtale.topology B S hS F V ∧
      ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ V), T k →
        ∃ y : (meromorphicSectionModule B S hS F hF M).obj (op W),
          toMeromorphicSectionSheaf B S hS F hF M W y =
            ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map k.op).hom t := by
  refine ⟨Presheaf.imageSieve (toSheafify (SmallEtale.topology B S hS F)
      (meromorphicSectionModuleUp B S hS F hF M)) t,
    (isLocallySurjective_toSheafify_meromorphicSectionModuleUp B S hS F hF M).imageSieve_mem t,
    ?_⟩
  intro W k hk
  obtain ⟨y, hy⟩ := hk
  exact ⟨y.down, hy⟩

section Invertible

variable (X : AlgebraicSpaces B S hS)

/-- **An invertible module is, over a covering family of every chart, free of rank one with a
generator compatible with restriction.** Let `L` be an invertible module on `X`. Every chart `U`
of `X` has a covering family `V i ⟶ U` such that over every chart `W` over a member `V i` there
is a section `e` of `L`, compatible with restriction, for which `a ↦ a ⊗ e` is a bijection of the
meromorphic functions `𝒦_X(W)` onto the meromorphic sections `𝒦_X(W) ⊗_{𝒪_X(W)} L(W)`. -/
theorem exists_generator_cover_of_isInvertible (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS X.1) (a : ∀ i, V i ⟶ U),
      Sieve.ofArrows V a ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ i, ∃ e : (W : SmallEtale B S hS X.1) → (W ⟶ V i) → L.val.obj (op W),
        (∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V i) (g : W' ⟶ W),
            (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
        ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V i),
          Function.Bijective fun x : (meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W) ↦
            (x ⊗ₜ[chartRing B S hS X.1 X.2 W] e W k :
              (meromorphicSectionModule B S hS X.1 X.2 L).obj (op W)) := by
  obtain ⟨I, V, a, hcov, hfree⟩ :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X L hL U
  refine ⟨I, V, a, hcov, fun i ↦ ?_⟩
  obtain ⟨ι, ⟨hc⟩⟩ := hfree i
  exact exists_generator_of_isColimit B S hS X.1 X.2 L (V i) ι hc

/-- **An invertible module is, over a covering family of every chart, free of rank one with a
generator compatible with restriction, read on regular functions.** Let `L` be an invertible
module on `X`. Every chart `U` of `X` has a covering family `V i ⟶ U` such that over every chart
`W` over a member `V i` there is a section `e` of `L`, compatible with restriction, for which
`r ↦ r • e` is a bijection of `𝒪_X(W)` onto `L(W)`. -/
theorem exists_generator_cover_smul_of_isInvertible (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS X.1) (a : ∀ i, V i ⟶ U),
      Sieve.ofArrows V a ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ i, ∃ e : (W : SmallEtale B S hS X.1) → (W ⟶ V i) → L.val.obj (op W),
        (∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V i) (g : W' ⟶ W),
            (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
        ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V i),
          Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k := by
  obtain ⟨I, V, a, hcov, hfree⟩ :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X L hL U
  refine ⟨I, V, a, hcov, fun i ↦ ?_⟩
  obtain ⟨ι, ⟨hc⟩⟩ := hfree i
  exact exists_generator_smul_of_isColimit B S hS X.1 X.2 L (V i) ι hc

end Invertible

end AlgebraicGeometry.Space

end
