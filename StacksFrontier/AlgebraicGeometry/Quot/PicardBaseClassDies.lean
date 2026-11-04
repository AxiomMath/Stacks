module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra

/-!
# A Picard class pulled back from the test scheme dies in the relative Picard functor

In Situation 0D25 — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` — let `T` be a
test scheme over `B`.  The sequence of Stacks 0D27 is

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)`,

the first arrow pullback along `f_T : X_T ⟶ T` and the second the canonical map into the fppf
sheafification.  This file proves that the composite of the two arrows is zero, with no
hypothesis on `f`: every invertible module `N` on the small étale site of `T` is trivial after
pullback along an étale covering family of test schemes, so the class of `f_T^*N` agrees with the
trivial class on a covering sieve, and hence in the sheafification.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.picardClassMap_eq_of_forall` and
  `AlgebraicGeometry.Space.PicardSituation.exists_forall_of_picardClassMap_eq`: two Picard
  classes on `X_T` have the same image in `Pic_{X/B}(T)` exactly when they agree after pullback
  along the members of a covering sieve of `T`.
* `AlgebraicGeometry.Space.PicardSituation.ofArrows_mem_fppfTopology_of_etale`: a jointly
  surjective family of étale morphisms of test schemes generates an fppf covering sieve.
* `AlgebraicGeometry.Space.PicardSituation.exists_mem_fppfTopology_picardPullback_eq_zero`:
  **a Picard class of a test scheme `T` dies on an fppf covering sieve of `T`**.
* `AlgebraicGeometry.Space.PicardSituation.picardClassMap_basePicardPullback`: **the composite
  `Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` is zero.**

## Implementation notes

Local triviality comes from the étale rank-one free locus: an invertible module on an algebraic
space is free of rank one over an étale neighbourhood of every point
(`AlgebraicGeometry.Space.mem_etaleRankOneFreeLocus_of_isInvertibleModule`).  The neighbourhood
is an algebraic space; one of its étale scheme charts through the point is a scheme of the site
with an étale morphism to `T`, and the points of the represented algebraic space of a scheme are
the points of the scheme (`AlgebraicGeometry.Space.pointsEquivScheme`), so these charts form a
jointly surjective étale family of test schemes, which generates an fppf covering sieve.

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-! ### Equality in the sheafification -/

/-- Two Picard classes on `X_T` which agree after pullback along every member of a covering sieve
of `T` have the same image in `Pic_{X/B}(T)`: the relative Picard functor is separated. -/
theorem picardClassMap_eq_of_forall {T : s.SchemesOver} (x y : s.picardAt T) {R : Sieve T}
    (hR : R ∈ s.fppfTopology T)
    (h : ∀ ⦃U : s.SchemesOver⦄ (g : U ⟶ T), R.arrows g → s.picardMap g x = s.picardMap g y) :
    s.picardClassMap T x = s.picardClassMap T y := by
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 s.isSheaf_picardFunctor R hR).isSeparatedFor
  refine hsep.ext fun U g hg => ?_
  have key : ∀ z : s.picardAt T, s.picardFunctor.map g.op (s.picardClassMap T z) =
      s.picardClassMap U (s.picardMap g z) := fun z =>
    (ConcreteCategory.congr_hom (s.toPicardFunctor.naturality g.op) z).symm
  show s.picardFunctor.map g.op (s.picardClassMap T x) =
    s.picardFunctor.map g.op (s.picardClassMap T y)
  rw [key, key, h g hg]

/-- Two Picard classes on `X_T` with the same image in `Pic_{X/B}(T)` agree after pullback along
every member of some covering sieve of `T`: the canonical map into a sheafification is locally
injective. -/
theorem exists_forall_of_picardClassMap_eq {T : s.SchemesOver} (x y : s.picardAt T)
    (h : s.picardClassMap T x = s.picardClassMap T y) :
    ∃ R ∈ s.fppfTopology T,
      ∀ ⦃U : s.SchemesOver⦄ (g : U ⟶ T), R.arrows g → s.picardMap g x = s.picardMap g y := by
  have hW : s.fppfTopology.W (toSheafify s.fppfTopology s.picardPresheaf) :=
    GrothendieckTopology.W_toSheafify _ _
  have hinj := GrothendieckTopology.W.isLocallyInjective (A := Type (u + 1)) hW
  exact ⟨_, hinj.equalizerSieve_mem (X := Opposite.op T) x y h, fun _ _ hg => hg⟩

/-! ### Étale covering families of test schemes -/

/-- **A jointly surjective family of étale morphisms of test schemes generates an fppf covering
sieve.** -/
theorem ofArrows_mem_fppfTopology_of_etale {T : s.SchemesOver} {I : Type (u + 1)}
    (U : I → s.SchemesOver) (g : ∀ i, U i ⟶ T)
    (hetale : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (g i).left))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T.left,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i).left)) :
    Sieve.ofArrows U g ∈ s.fppfTopology T := by
  refine Functor.mem_restrictedTopology_of_functorPushforward_mem
    (F := CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base) ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.ofArrows_mem_topology_of_etale B S hS (fun i => (U i).left)
      (fun i => (g i).left) hetale hcov)
  rintro _ _ ⟨_, w, _, ⟨i⟩, rfl⟩
  exact (Sieve.functorPushforward (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
    (Sieve.ofArrows U g)).downward_closed
      (Sieve.image_mem_functorPushforward
        (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base) (Sieve.ofArrows U g)
        (Sieve.ofArrows_mk _ _ i)) w

/-! ### An invertible module on a test scheme is trivial on an étale covering family -/

/-- **A Picard class of a test scheme dies on an étale neighbourhood of every point.**  For every
point `t` of a test scheme `T` there is an étale morphism `γ : U ⟶ T` of schemes of the site
whose image contains `t` and along which the given class pulls back to zero. -/
theorem exists_etale_picardPullback_eq_zero (T : s.SchemesOver) (y : s.basePicardAt T)
    (t : (BigFppfOver.toScheme B S hS).obj T.left) :
    ∃ (U : BigFppfOver B S hS) (γ : U ⟶ T.left) (v : (BigFppfOver.toScheme B S hS).obj U),
      Etale ((BigFppfOver.toScheme B S hS).map γ) ∧ (BigFppfOver.toScheme B S hS).map γ v = t ∧
      picardPullback ((schemeSpaceFunctor B S hS).map γ) y = 0 := by
  obtain ⟨N, hN, rfl⟩ := exists_picardClass (s.baseSpaceAt T) y
  let x := (pointsEquivScheme B S hS T.left).symm t
  obtain ⟨V, a, ha, ⟨w, hw⟩, ⟨e⟩⟩ :=
    mem_etaleRankOneFreeLocus_of_isInvertibleModule (s.baseSpaceAt T) N hN x
  obtain ⟨Uc, p, hp⟩ := exists_chart_point B S hS V.1 V.2 w
  let c : yoneda.obj Uc.obj.left ⟶ yoneda.obj T.left := Uc.obj.hom ≫ a.hom
  let γ : Uc.obj.left ⟶ T.left := Yoneda.fullyFaithful.preimage c
  have hγ : yoneda.map γ = c := Yoneda.fullyFaithful.map_preimage c
  refine ⟨Uc.obj.left, γ, pointsEquivScheme B S hS Uc.obj.left p, ?_, ?_, ?_⟩
  · apply etale_of_isEtale_yoneda_map
    rw [hγ]
    exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2 Uc.property) ha
  · apply (pointsEquivScheme B S hS T.left).symm.injective
    rw [← pointsMap_yoneda_map_symm, Equiv.symm_apply_apply, hγ]
    have h₁ := congrFun (pointsMap_comp B S hS (yoneda.obj Uc.obj.left) Uc.obj.hom a.hom) p
    simp only [Function.comp_apply] at h₁
    exact h₁.trans ((congrArg _ hp).trans hw)
  · have hsq : (schemeSpaceFunctor B S hS).map γ =
        (ObjectProperty.homMk Uc.obj.hom :
          (schemeSpaceFunctor B S hS).obj Uc.obj.left ⟶ V) ≫ a :=
      ObjectProperty.hom_ext _ hγ
    rw [hsq, picardPullback_comp, picardPullback_picardClass,
      (picardClass_eq_zero_iff _ _ _).2 ⟨e⟩, picardPullback_zero]

/-- **A Picard class of a test scheme dies on an fppf covering sieve.**  For every Picard class
`y` of a test scheme `T` over the base there is a covering sieve of `T` along each member of
which `y` pulls back to zero. -/
theorem exists_mem_fppfTopology_picardPullback_eq_zero (T : s.SchemesOver)
    (y : s.basePicardAt T) :
    ∃ R ∈ s.fppfTopology T, ∀ ⦃U : s.SchemesOver⦄ (g : U ⟶ T), R.arrows g →
      picardPullback ((schemeSpaceFunctor B S hS).map g.left) y = 0 := by
  choose U γ v hγe hγv hγ0 using s.exists_etale_picardPullback_eq_zero T y
  let U' : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj T.left) → s.SchemesOver :=
    fun t => CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (γ t.down) ≫ T.hom)
  let g' : ∀ t, U' t ⟶ T := fun t => CostructuredArrow.homMk (γ t.down) rfl
  refine ⟨Sieve.ofArrows U' g', s.ofArrows_mem_fppfTopology_of_etale U' g'
    (fun t => hγe t.down) (fun t => ⟨ULift.up t, v t, hγv t⟩), ?_⟩
  rintro W _ ⟨Z, w, _, ⟨t⟩, rfl⟩
  rw [CostructuredArrow.comp_left, Functor.map_comp, picardPullback_comp]
  show picardPullback _ (picardPullback ((schemeSpaceFunctor B S hS).map (γ t.down)) y) = 0
  rw [hγ0, picardPullback_zero]

/-- **The composite `Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` of Stacks 0D27 is zero.**  A class
pulled back from `T` has the same image in the relative Picard functor as the trivial class.
No hypothesis on `f` is needed. -/
theorem picardClassMap_basePicardPullback (T : s.SchemesOver) (y : s.basePicardAt T) :
    s.picardClassMap T (s.basePicardPullback T y) = s.picardClassMap T 0 := by
  obtain ⟨R, hR, hR0⟩ := s.exists_mem_fppfTopology_picardPullback_eq_zero T y
  refine s.picardClassMap_eq_of_forall _ _ hR fun U g hg => ?_
  rw [picardMap_eq, basePicardPullback, ← picardPullback_comp, baseChangeMap_comp_inclusion,
    picardPullback_comp, hR0 g hg, picardPullback_zero, picardPullback_zero]

end PicardSituation

end AlgebraicGeometry.Space

end
