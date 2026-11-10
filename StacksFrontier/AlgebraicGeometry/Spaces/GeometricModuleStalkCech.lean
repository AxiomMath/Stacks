module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorFibreInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkLocalization
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingPullbackDatum

/-!
# Čech separation and glueing of a geometric stalk

Let `x̄` be a geometric point of an algebraic space `X`, `N₀` a small étale neighbourhood of
`x̄` and `g₁, …, g_r` regular functions on its chart, with germs `fᵢ ∈ 𝒪_{X, x̄}`.  This file
carries the two halves of exactness of `M → ∏ M[1/fᵢ] ⇉ ∏ M[1/fᵢfⱼ]` — separation
(`FormalGlueing.CechSeparated`) and glueing (`FormalGlueing.CechGlueingElementary`) — from the
sections of an `𝒪_X`-module over the affine neighbourhoods lying over `N₀` to its geometric
stalk.  The stalkwise proof of Stacks 0AF0 needs them for the stalk of `j_*ℋ` at a point of
`Z`, where they hold chartwise because the basic opens `D(gᵢ)` cover the part of the chart
lying over `U = X ∖ Z`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_forall_of_eventually`: finitely many properties of
  refinements, each stable under further refinement and each eventually true, hold together
  on one affine refinement.
* `AlgebraicGeometry.Space.cechSeparated_geometricModuleStalk`: separation passes to the stalk.
* `AlgebraicGeometry.Space.cechGlueingElementary_geometricModuleStalk`: glueing passes to the
  stalk.

## Implementation notes

Every element of the stalk and every relation in it is represented over one neighbourhood, and
the finitely many refinements are made successively rather than by a cone over a finite diagram:
`exists_affine_forall_of_eventually` only ever refines the neighbourhood reached so far, so no two
parallel maps of neighbourhoods have to be equalized.  Restriction of sections is
`AlgebraicGeometry.Space.nbhdRestrict`, an additive map with its target type fixed, so that the
scalar actions on both sides are found by instance search.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- **Finitely many eventual properties hold together.**  If each of finitely many properties of
refinements of `N₁` is stable under further refinement and holds after refining any given one,
then all of them hold on one refinement with affine chart. -/
theorem exists_affine_forall_of_eventually {ι : Type*} [Finite ι] (N₁ : SmallEtaleNeighborhood x)
    (P : ι → ∀ M : SmallEtaleNeighborhood x, (M ⟶ N₁) → Prop)
    (hstab : ∀ i (M M' : SmallEtaleNeighborhood x) (e' : M' ⟶ M) (e : M ⟶ N₁),
      P i M e → P i M' (e' ≫ e))
    (hev : ∀ i (M : SmallEtaleNeighborhood x) (e : M ⟶ N₁),
      ∃ (M' : SmallEtaleNeighborhood x) (e' : M' ⟶ M), P i M' (e' ≫ e)) :
    ∃ (M : SmallEtaleNeighborhood x) (e : M ⟶ N₁), IsAffine (chartScheme M.chart) ∧
      ∀ i, P i M e := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, ∃ (M : SmallEtaleNeighborhood x) (e : M ⟶ N₁), ∀ i ∈ s, P i M e := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₁, 𝟙 N₁, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨M, e, he⟩ := ih
      obtain ⟨M', e', he'⟩ := hev a M e
      refine ⟨M', e' ≫ e, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact he'
      · exact hstab i M M' e' e (he i hi)
  obtain ⟨M, e, he⟩ := key Finset.univ
  obtain ⟨M', e', hM'⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x M
  exact ⟨M', e' ≫ e, hM', fun i => hstab i M M' e' e (he i (Finset.mem_univ i))⟩

/-- Finitely many sections with zero germ all vanish on one affine refinement. -/
private theorem exists_affine_map_eq_zero_of_germ_eq_zero {ι : Type*} [Finite ι]
    (F : Modules.{u, u} B S hS X.1 X.2) (N₁ : SmallEtaleNeighborhood x)
    (s : ι → F.val.obj (op N₁.chart))
    (h : ∀ i, geometricModuleStalkGerm B S hS X x F N₁ (s i) = 0) :
    ∃ (M : SmallEtaleNeighborhood x) (e : M ⟶ N₁), IsAffine (chartScheme M.chart) ∧
      ∀ i, F.val.map e.hom.op (s i) = 0 := by
  refine exists_affine_forall_of_eventually B S hS X x N₁
    (fun i M e => F.val.map e.hom.op (s i) = 0)
    (fun i M M' e' e (hP : F.val.map e.hom.op _ = 0) => by
      rw [← map_comp_apply_neighborhood B S hS X.2 F e' e, hP]
      exact map_zero (ConcreteCategory.hom (F.val.map e'.hom.op)))
    (fun i M e => ?_)
  have h0 : geometricModuleStalkGerm B S hS X x F M (F.val.map e.hom.op (s i)) = 0 := by
    rw [geometricModuleStalkGerm_map, h]
  obtain ⟨M', e', he'⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x F M _).1 h0
  refine ⟨M', e', ?_⟩
  rw [← map_comp_apply_neighborhood B S hS X.2 F e' e]
  exact he'

variable {X x}

/-- Restricting `g ^ k • s` along a refinement is restricting `s` and the restricted `g`. -/
theorem map_pow_smul_neighborhood (F : Modules.{u, u} B S hS X.1 X.2)
    {N₀ M M' : SmallEtaleNeighborhood x} (d : M ⟶ N₀) (e : M' ⟶ M)
    (a : chartRing B S hS X.1 X.2 N₀.chart) (k : ℕ) (s : F.val.obj (op M.chart)) :
    F.val.map e.hom.op ((chartRestrict (hF := X.2) d.hom a) ^ k • s) =
      (chartRestrict (hF := X.2) (e ≫ d).hom a) ^ k •
        (show F.val.obj (op M'.chart) from F.val.map e.hom.op s) := by
  refine (PresheafOfModules.map_smul F.val e.hom.op _ s).trans ?_
  congr 1
  change chartRestrict (hF := X.2) e.hom ((chartRestrict (hF := X.2) d.hom a) ^ k) = _
  rw [map_pow, show (e ≫ d).hom = e.hom ≫ d.hom from rfl, chartRestrict_comp]
  rfl

variable (X x)

/-- **Čech separation passes to the geometric stalk.**  If over every affine neighbourhood `M`
lying over `N₀` a section of `F` killed by powers of all the restricted `gᵢ` vanishes, then an
element of `F_x̄` killed by powers of all the germs of the `gᵢ` vanishes. -/
theorem cechSeparated_geometricModuleStalk (F : Modules.{u, u} B S hS X.1 X.2)
    (N₀ : SmallEtaleNeighborhood x) {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 N₀.chart)
    (h : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      ∀ s : F.val.obj (op M.chart),
        (∀ i, ∃ k : ℕ, (chartRestrict (hF := X.2) d.hom (g i)) ^ k • s = 0) → s = 0) :
    FormalGlueing.CechSeparated (fun i ↦ etaleLocalRingGerm B S hS X.1 x (op N₀) (g i))
      (geometricModuleStalk B S hS X x F) := by
  intro n hn
  obtain ⟨N, t, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F n
  obtain ⟨M₀, c, d₀, -⟩ := exists_affine_smallEtaleNeighborhood_over_two B S hS X x N N₀
  set s₀ : F.val.obj (op M₀.chart) := F.val.map c.hom.op t
  have hs₀ : geometricModuleStalkGerm B S hS X x F M₀ s₀ =
      geometricModuleStalkGerm B S hS X x F N t := geometricModuleStalkGerm_map B S hS X x F c t
  choose k hk using hn
  obtain ⟨M, e, hM, hP⟩ := exists_affine_map_eq_zero_of_germ_eq_zero B S hS X x F M₀
    (fun i => (chartRestrict (hF := X.2) d₀.hom (g i)) ^ k i • s₀) fun i => by
      rw [germ_pow_smul_germ, hs₀]
      exact hk i
  have hzero : F.val.map e.hom.op s₀ = 0 := by
    refine h M (e ≫ d₀) hM _ fun i => ⟨k i, ?_⟩
    rw [← map_pow_smul_neighborhood B S hS F d₀ e]
    exact hP i
  rw [← hs₀, ← geometricModuleStalkGerm_map B S hS X x F e, hzero]
  exact map_zero (geometricModuleStalkGerm B S hS X x F M)

variable {X x}

/-- The germ of a regular function, as a ring homomorphism out of `chartRing`. -/
noncomputable abbrev neighborhoodGerm (M : SmallEtaleNeighborhood x) :
    chartRing B S hS X.1 X.2 M.chart →+* etaleLocalRing B S hS X.1 x :=
  etaleLocalRingGerm B S hS X.1 x (op M)

/-- The germ of the restriction of a regular function along a morphism of neighbourhoods equals
the germ of the function itself. -/
theorem chartGerm_chartRestrict {N₀ M : SmallEtaleNeighborhood x} (d : M ⟶ N₀)
    (a : chartRing B S hS X.1 X.2 N₀.chart) :
    neighborhoodGerm B S hS M (chartRestrict (hF := X.2) d.hom a) = neighborhoodGerm B S hS N₀ a :=
  etaleLocalRingGerm_chartRestrict (hF := X.2) d a

/-- Taking germs of sections is compatible with scalar multiplication by regular functions. -/
theorem germ_smul_chart (F : Modules.{u, u} B S hS X.1 X.2) (M : SmallEtaleNeighborhood x)
    (a : chartRing B S hS X.1 X.2 M.chart) (s : F.val.obj (op M.chart)) :
    geometricModuleStalkGerm B S hS X x F M (a • s) =
      neighborhoodGerm B S hS M a • geometricModuleStalkGerm B S hS X x F M s :=
  geometricModuleStalkGerm_smul B S hS X x F M a s

/-- Restriction of sections along a morphism of neighbourhoods, with its target type fixed. -/
noncomputable def nbhdRestrict (F : Modules.{u, u} B S hS X.1 X.2)
    {M M' : SmallEtaleNeighborhood x} (e : M' ⟶ M) :
    F.val.obj (op M.chart) →+ F.val.obj (op M'.chart) :=
  (F.val.map e.hom.op).hom.toAddMonoidHom

/-- Restriction of sections along a morphism of neighbourhoods is semilinear over the
restriction of regular functions. -/
theorem nbhdRestrict_smul (F : Modules.{u, u} B S hS X.1 X.2)
    {M M' : SmallEtaleNeighborhood x} (e : M' ⟶ M)
    (a : chartRing B S hS X.1 X.2 M.chart) (s : F.val.obj (op M.chart)) :
    nbhdRestrict B S hS F e (a • s) =
      chartRestrict (hF := X.2) e.hom a • nbhdRestrict B S hS F e s :=
  PresheafOfModules.map_smul F.val e.hom.op a s

/-- The restriction of `a • s` along a morphism of neighbourhoods is the restriction of `a`
acting on the restriction of `s`. -/
theorem map_smul_neighborhood (F : Modules.{u, u} B S hS X.1 X.2)
    {M M' : SmallEtaleNeighborhood x} (e : M' ⟶ M)
    (a : chartRing B S hS X.1 X.2 M.chart) (s : F.val.obj (op M.chart)) :
    F.val.map e.hom.op (a • s) =
      chartRestrict (hF := X.2) e.hom a •
        (show F.val.obj (op M'.chart) from F.val.map e.hom.op s) :=
  PresheafOfModules.map_smul F.val e.hom.op a s

variable (X x)

/-- **Čech glueing passes to the geometric stalk.**  If over every affine neighbourhood `M`
lying over `N₀` the sections of `F` glue along the restricted `gᵢ`, then `F_x̄` glues along the
germs of the `gᵢ`. -/
theorem cechGlueingElementary_geometricModuleStalk (F : Modules.{u, u} B S hS X.1 X.2)
    (N₀ : SmallEtaleNeighborhood x) {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 N₀.chart)
    (h : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      FormalGlueing.CechGlueingElementary (fun i ↦ chartRestrict (hF := X.2) d.hom (g i))
        (F.val.obj (op M.chart))) :
    FormalGlueing.CechGlueingElementary (fun i ↦ etaleLocalRingGerm B S hS X.1 x (op N₀) (g i))
      (geometricModuleStalk B S hS X x F) := by
  classical
  intro k n hn
  have hrep : ∀ i, ∃ (Ni : SmallEtaleNeighborhood x) (t : F.val.obj (op Ni.chart)),
      geometricModuleStalkGerm B S hS X x F Ni t = n i :=
    fun i => geometricModuleStalkGerm_jointly_surjective B S hS X x F (n i)
  choose Ni t ht using hrep
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨M₁, e₁, -, hP₁⟩ := exists_affine_forall_of_eventually B S hS X x N₀
    (fun i M e => ∃ s : F.val.obj (op M.chart), geometricModuleStalkGerm B S hS X x F M s = n i)
    (fun i M M' e' e ⟨s, hs⟩ => ⟨F.val.map e'.hom.op s,
      (geometricModuleStalkGerm_map B S hS X x F e' s).trans hs⟩)
    (fun i M e => by
      obtain ⟨M', a, b, -⟩ := IsCofilteredOrEmpty.cone_objs M (Ni i)
      exact ⟨M', a, F.val.map b.hom.op (t i),
        (geometricModuleStalkGerm_map B S hS X x F b (t i)).trans (ht i)⟩)
  choose t₁ ht₁ using hP₁
  set G : Fin r → chartRing B S hS X.1 X.2 M₁.chart :=
    fun i => chartRestrict (hF := X.2) e₁.hom (g i)
  have hG : ∀ i, neighborhoodGerm B S hS M₁ (G i) =
      etaleLocalRingGerm B S hS X.1 x (op N₀) (g i) :=
    fun i => chartGerm_chartRestrict B S hS e₁ (g i)
  let rel : Fin r → Fin r → ℕ → F.val.obj (op M₁.chart) := fun i j l =>
    (G i * G j) ^ l • ((G j) ^ k • t₁ i - (G i) ^ k • t₁ j)
  have hrel : ∀ i j l, geometricModuleStalkGerm B S hS X x F M₁ (rel i j l) =
      (etaleLocalRingGerm B S hS X.1 x (op N₀) (g i) *
          etaleLocalRingGerm B S hS X.1 x (op N₀) (g j)) ^ l •
        ((etaleLocalRingGerm B S hS X.1 x (op N₀) (g j)) ^ k • n i -
          (etaleLocalRingGerm B S hS X.1 x (op N₀) (g i)) ^ k • n j) := by
    intro i j l
    simp only [rel, germ_smul_chart, map_sub, map_pow, map_mul, hG, ht₁]
  choose l hl using hn
  obtain ⟨M₂, e₂, hM₂, hP₂⟩ := exists_affine_map_eq_zero_of_germ_eq_zero B S hS X x F M₁
    (fun p : Fin r × Fin r => rel p.1 p.2 (l p.1 p.2)) fun p => by
      rw [hrel]
      exact hl p.1 p.2
  set G' : Fin r → chartRing B S hS X.1 X.2 M₂.chart :=
    fun i => chartRestrict (hF := X.2) (e₂ ≫ e₁).hom (g i)
  have hG' : ∀ i, chartRestrict (hF := X.2) e₂.hom (G i) = G' i := by
    intro i
    change chartRestrict (hF := X.2) e₂.hom (chartRestrict (hF := X.2) e₁.hom (g i)) =
      chartRestrict (hF := X.2) (e₂.hom ≫ e₁.hom) (g i)
    rw [chartRestrict_comp]
    rfl
  let n' : Fin r → F.val.obj (op M₂.chart) := fun i => F.val.map e₂.hom.op (t₁ i)
  obtain ⟨m, hm⟩ := h M₂ (e₂ ≫ e₁) hM₂ k n' (by
    intro i j
    refine ⟨l i j, ?_⟩
    have h2 : nbhdRestrict B S hS F e₂ (rel i j (l i j)) = 0 := hP₂ (i, j)
    simp only [rel, nbhdRestrict_smul, map_sub, map_pow, map_mul, hG'] at h2
    exact h2)
  refine ⟨geometricModuleStalkGerm B S hS X x F M₂ m, fun i => ?_⟩
  obtain ⟨l', hl'⟩ := hm i
  refine ⟨l', ?_⟩
  have hn2 : ∀ i, geometricModuleStalkGerm B S hS X x F M₂ (n' i) = n i := fun i =>
    (geometricModuleStalkGerm_map B S hS X x F e₂ (t₁ i)).trans (ht₁ i)
  have h3 := congrArg (geometricModuleStalkGerm B S hS X x F M₂) hl'
  simp only [germ_smul_chart, map_sub, map_pow, hn2, map_zero, chartGerm_chartRestrict] at h3
  exact h3

end AlgebraicGeometry.Space

end
