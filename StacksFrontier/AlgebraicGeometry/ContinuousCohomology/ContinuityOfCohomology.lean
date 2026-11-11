module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InflationDelta

/-!
# Continuity of the cohomology of a profinite group with finite coefficients

Let `G` be a profinite group and `R` a finite ring. For every `n`, the cohomology of `G` with
coefficients in a finite discrete `R`-module is the colimit of the cohomology of the finite
quotients `G ⧸ U` along the inflation maps:

* every class of `Hⁿ(G, X)`, `X` a module over `G ⧸ U`, is inflated from some `G ⧸ V`, `V ≤ U`
  (`Stacks.ContinuousCohomology.InflationSurjective`);
* a class of `Hⁿ(G ⧸ U, X)` which dies in `Hⁿ(G, X)` dies in some `Hⁿ(G ⧸ V, X)`
  (`Stacks.ContinuousCohomology.InflationInjective`).

Both are proved together by induction on `n`
(`Stacks.ContinuousCohomology.inflationSurjective_and_inflationInjective`), by dimension shifting
along effacing monomorphisms: `Hⁿ(G, -)` and `Hⁿ(G ⧸ U, -)` are elementwise effaceable on finite
modules, a finite module is acted on trivially by an open normal subgroup and so descends to a
finite quotient (`Stacks.ContinuousCohomology.descend`), and inflation commutes with the
connecting morphisms.

## Main definitions

* `Stacks.ContinuousCohomology.ActsTrivially`, `Stacks.ContinuousCohomology.descend`.
* `Stacks.ContinuousCohomology.InflationSurjective`,
  `Stacks.ContinuousCohomology.InflationInjective`.

## Main results

* `Stacks.ContinuousCohomology.inflationSurjective_and_inflationInjective`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe w

namespace Stacks.ContinuousCohomology

open scoped Stacks.DiscreteModuleTopology

section Descent

variable (R : Type) [Ring R] {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open normal subgroup acts trivially on `X`. -/
def ActsTrivially (U : OpenNormalSubgroup G) (X : FiniteTypeContinuousModule.{0, w, w} R G) :
    Prop :=
  ∀ g ∈ U, X.obj.obj.obj.ρ g = 1

/-- **Descent** of a finite module on which `U` acts trivially to a module over `G ⧸ U`. -/
def descend (U : OpenNormalSubgroup G) (X : FiniteTypeContinuousModule.{0, w, w} R G)
    (hX : ActsTrivially R U X) : FiniteTypeContinuousModule.{0, w, w} R (G ⧸ (U : Subgroup G)) :=
  ⟨⟨⟨⟨X.obj.obj.obj.V, QuotientGroup.lift (U : Subgroup G) X.obj.obj.obj.ρ hX⟩,
      (Action.isContinuous_def _).2 <| by
        rw [continuous_prod_of_discrete_right]
        exact fun _ ↦ continuous_of_discreteTopology⟩, ⟨rfl⟩⟩, X.property⟩

/-- Restricting the descended module back to `G` gives the original module. -/
theorem res_descend (U : OpenNormalSubgroup G) (X : FiniteTypeContinuousModule.{0, w, w} R G)
    (hX : ActsTrivially R U X) :
    (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk U)).obj (descend R U X hX) = X := rfl

/-- A finite module is acted on trivially by some open normal subgroup. -/
theorem exists_actsTrivially (X : FiniteTypeContinuousModule.{0, w, w} R G) :
    ∃ U : OpenNormalSubgroup G, ActsTrivially R U X := by
  obtain ⟨H, hn, ho, hH⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType R G X
  exact ⟨⟨⟨H, ho⟩, hn⟩, hH⟩

omit [IsTopologicalGroup G] in
/-- A smaller subgroup acts trivially as well. -/
theorem ActsTrivially.mono {U V : OpenNormalSubgroup G}
    {X : FiniteTypeContinuousModule.{0, w, w} R G}
    (hU : ActsTrivially R U X) (h : V ≤ U) : ActsTrivially R V X :=
  fun g hg ↦ hU g (h hg)

end Descent

section Res

variable (R : Type) [Ring R] {Γ Γ' : Type w} [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ']

/-- Restriction is faithful. -/
instance faithful_finiteTypeContinuousModuleRes (φ : Γ' →ₜ* Γ) :
    (finiteTypeContinuousModuleRes.{0, w, w} R φ).Faithful where
  map_injective {_ _} _ _ h := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (ObjectProperty.hom_ext _ (Action.hom_ext _ _ (congrArg (fun k ↦ k.hom.hom.hom.hom) h))))

/-- **A `Γ'`-equivariant map between restrictions along a surjection is `Γ`-equivariant.** -/
def resPreimage (φ : Γ' →ₜ* Γ) (hφ : Function.Surjective φ)
    {X Y : FiniteTypeContinuousModule.{0, w, w} R Γ}
    (f : (finiteTypeContinuousModuleRes.{0, w, w} R φ).obj X ⟶
      (finiteTypeContinuousModuleRes.{0, w, w} R φ).obj Y) : X ⟶ Y :=
  ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R Γ _ _).symm
    ⟨f.hom.hom.hom.hom.hom, fun g x ↦ by
      obtain ⟨g', rfl⟩ := hφ g
      exact (Stacks.GroupCohomology.homEquiv R Γ' _ _ f.hom).2 g' x⟩)

/-- Restriction of `resPreimage f` is `f`. -/
theorem res_map_resPreimage (φ : Γ' →ₜ* Γ) (hφ : Function.Surjective φ)
    {X Y : FiniteTypeContinuousModule.{0, w, w} R Γ}
    (f : (finiteTypeContinuousModuleRes.{0, w, w} R φ).obj X ⟶
      (finiteTypeContinuousModuleRes.{0, w, w} R φ).obj Y) :
    (finiteTypeContinuousModuleRes.{0, w, w} R φ).map (resPreimage R φ hφ f) = f :=
  rfl

end Res

/-- Enough injectives for continuous discrete modules at the module universe of the group,
pinned. -/
local instance (priority := 3000) enoughInjectives_continuousModule_continuity (Λ : Type)
    [Ring Λ] (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, w, w} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, w, 0} Λ G

section Elements

variable {R : Type} [Ring R] [Finite R]
  {Γ Γ' : Type w} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']

/-- Restriction along `φ` preserves finite limits (instance form). -/
local instance (φ : Γ' →ₜ* Γ) :
    PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteLimits_finiteTypeContinuousModuleRes φ

/-- Restriction along `φ` preserves finite colimits (instance form). -/
local instance (φ : Γ' →ₜ* Γ) :
    PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteColimits_finiteTypeContinuousModuleRes φ

variable [TotallyDisconnectedSpace Γ] (φ : Γ' →ₜ* Γ)

/-- Inflation is natural, on elements. -/
theorem inflation_naturality_apply (n : ℕ) {X Y : FiniteTypeContinuousModule.{0, w, w} R Γ}
    (f : X ⟶ Y) (x : ((cohomologyDelta R Γ).functor n).obj X) :
    ((inflation R φ).app n).app Y (((cohomologyDelta R Γ).functor n).map f x) =
      ((cohomologyDelta R Γ').functor n).map ((finiteTypeContinuousModuleRes.{0, w, w} R φ).map f)
        (((inflation R φ).app n).app X x) :=
  ConcreteCategory.congr_hom (((inflation R φ).app n).naturality f) x

/-- Inflation commutes with the connecting morphisms, on elements. -/
theorem inflation_δ_apply {S : ShortComplex (FiniteTypeContinuousModule.{0, w, w} R Γ)}
    (hS : S.ShortExact) (n : ℕ) (z : ((cohomologyDelta R Γ).functor n).obj S.X₃) :
    ((inflation R φ).app (n + 1)).app S.X₁ ((cohomologyDelta R Γ).δ hS n z) =
      (cohomologyDelta R Γ').δ (hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R φ)) n
        (((inflation R φ).app n).app S.X₃ z) :=
  (ConcreteCategory.congr_hom ((inflation R φ).comm hS n) z).symm

end Elements

section Continuity

variable (R : Type) [Ring R] [Finite R] {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Restriction along a quotient map preserves finite limits (instance form). -/
local instance {Γ Γ' : Type w} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']
    (φ : Γ' →ₜ* Γ) :
    PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteLimits_finiteTypeContinuousModuleRes φ

/-- Restriction along a quotient map preserves finite colimits (instance form). -/
local instance {Γ Γ' : Type w} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']
    (φ : Γ' →ₜ* Γ) :
    PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteColimits_finiteTypeContinuousModuleRes φ

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The quotient map is surjective. -/
theorem quotientMk_surjective (U : OpenNormalSubgroup G) : Function.Surjective (quotientMk U) :=
  QuotientGroup.mk_surjective

omit [TotallyDisconnectedSpace G] in
/-- Inflating to `G ⧸ V` and then to `G` is inflating to `G`, on elements. -/
theorem inflation_quotientMk_quotientMap_apply {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ)
    (X : FiniteTypeContinuousModule.{0, w, w} R (G ⧸ (U : Subgroup G)))
    (y : ((cohomologyDelta R (G ⧸ (U : Subgroup G))).functor n).obj X) :
    ((inflation R (quotientMk V)).app n).app
        ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap h)).obj X)
        (((inflation R (quotientMap h)).app n).app X y) =
      ((inflation R (quotientMk U)).app n).app X y :=
  ConcreteCategory.congr_hom (congrArg (fun η ↦ (η.app n).app X)
    (inflation_comp_self R (quotientMap h) (quotientMk V))) y

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The quotient maps compose. -/
theorem quotientMap_quotientMap {U V W : OpenNormalSubgroup G} (h : V ≤ U) (h' : W ≤ V)
    (g : G ⧸ (W : Subgroup G)) : quotientMap h (quotientMap h' g) = quotientMap (h'.trans h) g := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

omit [TotallyDisconnectedSpace G] in
/-- Inflating to `G ⧸ V` and then to `G ⧸ W` is inflating to `G ⧸ W`, on elements. -/
theorem inflation_quotientMap_quotientMap_apply {U V W : OpenNormalSubgroup G} (h : V ≤ U)
    (h' : W ≤ V) (n : ℕ) (X : FiniteTypeContinuousModule.{0, w, w} R (G ⧸ (U : Subgroup G)))
    (y : ((cohomologyDelta R (G ⧸ (U : Subgroup G))).functor n).obj X) :
    ((cohomologyDelta R (G ⧸ (W : Subgroup G))).functor n).map
        ((resComparison R (quotientMap h) (quotientMap h') (quotientMap (h'.trans h))
          (quotientMap_quotientMap h h')).app X)
        (((inflation R (quotientMap h')).app n).app
          ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap h)).obj X)
          (((inflation R (quotientMap h)).app n).app X y)) =
      ((inflation R (quotientMap (h'.trans h))).app n).app X y :=
  ConcreteCategory.congr_hom (congrArg (fun η ↦ (η.app n).app X)
    (inflation_comp R (quotientMap h) (quotientMap h') (quotientMap (h'.trans h))
      (quotientMap_quotientMap h h'))) y

/-- `H^•(G, -)` is elementwise effaceable. -/
instance elementwiseEffaceable_cohomologyDelta (Γ : Type w) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    (cohomologyDelta R Γ).ElementwiseEffaceable :=
  elementwiseEffaceable_restrictedCohomologyDelta R _ Topology.IsInducing.id

/-- Surjectivity onto `Hⁿ(G, X)` from the finite quotients. -/
def InflationSurjective (n : ℕ) : Prop :=
  ∀ (U : OpenNormalSubgroup G) (X : FiniteTypeContinuousModule.{0, w, w} R (G ⧸ (U : Subgroup G)))
    (x : ((cohomologyDelta R G).functor n).obj
      ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk U)).obj X)),
    ∃ (V : OpenNormalSubgroup G) (h : V ≤ U)
      (y : ((cohomologyDelta R (G ⧸ (V : Subgroup G))).functor n).obj
        ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap h)).obj X)),
      ((inflation R (quotientMk V)).app n).app _ y = x

/-- A class of a finite quotient dying in `G` dies in a smaller finite quotient. -/
def InflationInjective (n : ℕ) : Prop :=
  ∀ (U : OpenNormalSubgroup G) (X : FiniteTypeContinuousModule.{0, w, w} R (G ⧸ (U : Subgroup G)))
    (y : ((cohomologyDelta R (G ⧸ (U : Subgroup G))).functor n).obj X),
    ((inflation R (quotientMk U)).app n).app X y = 0 →
      ∃ (V : OpenNormalSubgroup G) (h : V ≤ U), ((inflation R (quotientMap h)).app n).app X y = 0

omit [TotallyDisconnectedSpace G] in
/-- Degree zero of `Stacks.ContinuousCohomology.InflationSurjective`: inflation is bijective. -/
theorem inflationSurjective_zero : InflationSurjective R (G := G) 0 := by
  intro U X x
  obtain ⟨y, hy⟩ := (bijective_inflation_app_zero R (quotientMk U) (quotientMk_surjective U)
    ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap (le_refl U))).obj X)).2 x
  exact ⟨U, le_refl U, y, hy⟩

omit [TotallyDisconnectedSpace G] in
/-- Degree zero of `Stacks.ContinuousCohomology.InflationInjective`. -/
theorem inflationInjective_zero : InflationInjective R (G := G) 0 := by
  intro U X y hy
  have hy0 : y = 0 := (bijective_inflation_app_zero R (quotientMk U) (quotientMk_surjective U)
    X).1 (hy.trans (map_zero _).symm)
  exact ⟨U, le_refl U, by rw [hy0, map_zero]⟩

open CategoryTheory.DeltaFunctor.ElementwiseEffaceable in
/-- **Surjectivity in degree `n + 1`.** A class `x ∈ Hⁿ⁺¹(G, X)` dies in some finite `I`; an open
normal subgroup `W` acts trivially on `I`, so the effacing sequence descends to `G ⧸ W`, `x` is
the connecting image of a class of degree `n`, which is inflated from some `G ⧸ V` by
surjectivity in degree `n`, and inflation commutes with the connecting morphisms. -/
theorem inflationSurjective_succ {n : ℕ} (ih : InflationSurjective R (G := G) n) :
    InflationSurjective R (G := G) (n + 1) := by
  intro U X x
  obtain ⟨I', ι', hι', hx⟩ := DeltaFunctor.ElementwiseEffaceable.exists_mono
    (F := cohomologyDelta R G) x
  obtain ⟨W₀, hW₀⟩ := exists_actsTrivially R I'
  let W : OpenNormalSubgroup G := W₀ ⊓ U
  have hWU : W ≤ U := inf_le_right
  have hI' : ActsTrivially R W I' := hW₀.mono R inf_le_left
  let I := descend R W I' hI'
  let Y := (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hWU)).obj X
  let ι : Y ⟶ I := resPreimage R (quotientMk W) (quotientMk_surjective W) ι'
  have : Mono ι := (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk W)).mono_of_mono_map hι'
  have hS := shortExact_effSeq ι
  have hT := hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk W))
  obtain ⟨q, hq⟩ := exists_δ_eq (F := cohomologyDelta R G) hT x hx
  obtain ⟨V, hVW, q', hq'⟩ := ih W (cokernel ι) q
  have hS₂ := hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hVW))
  let y₀ := (cohomologyDelta R (G ⧸ (V : Subgroup G))).δ hS₂ n q'
  let c := (resComparison R (quotientMap hWU) (quotientMap hVW) (quotientMap (hVW.trans hWU))
    (quotientMap_quotientMap hWU hVW)).app X
  refine ⟨V, hVW.trans hWU, ((cohomologyDelta R (G ⧸ (V : Subgroup G))).functor (n + 1)).map c y₀,
    ?_⟩
  have hc : ((cohomologyDelta R G).functor (n + 1)).map
      ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk V)).map c) = 𝟙 _ :=
    ((cohomologyDelta R G).functor (n + 1)).map_id _
  refine (inflation_naturality_apply (quotientMk V) (n + 1) c y₀).trans ?_
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  refine (inflation_δ_apply (quotientMk V) hS₂ n q').trans ?_
  exact (congrArg ((cohomologyDelta R G).δ hT n) hq').trans hq

omit [TotallyDisconnectedSpace G] in
open CategoryTheory.DeltaFunctor.ElementwiseEffaceable in
/-- **Injectivity in degree `n + 1`.** A class `y` of `G ⧸ U` dying in `G` is a connecting image
`δ z` for an effacing sequence over `G ⧸ U`; the inflation of `z` comes from the middle term by
exactness, hence by surjectivity in degree `n` from some `G ⧸ V`, and injectivity in degree `n`
makes `z` itself come from the middle term over a smaller `G ⧸ W`, where `y` then dies. -/
theorem inflationInjective_succ {n : ℕ} (hS' : InflationSurjective R (G := G) n)
    (hJ : InflationInjective R (G := G) n) : InflationInjective R (G := G) (n + 1) := by
  intro U X y hy
  obtain ⟨I, ι, hι, hyι⟩ := DeltaFunctor.ElementwiseEffaceable.exists_mono
    (F := cohomologyDelta R (G ⧸ (U : Subgroup G))) y
  have hS := shortExact_effSeq ι
  obtain ⟨z, hz⟩ := exists_δ_eq (F := cohomologyDelta R (G ⧸ (U : Subgroup G))) hS y hyι
  have h1 : (cohomologyDelta R G).δ
      (hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk U))) n
      (((inflation R (quotientMk U)).app n).app _ z) = 0 :=
    (inflation_δ_apply (quotientMk U) hS n z).symm.trans ((congrArg _ hz).trans hy)
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).1 ((cohomologyDelta R G).exact_δ₁
    (hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMk U))) n) _ h1
  obtain ⟨V, hVU, b, hb⟩ := hS' U I a
  let τ : ((cohomologyDelta R (G ⧸ (U : Subgroup G))).functor n).obj (cokernel ι) ⟶
      ((cohomologyDelta R (G ⧸ (V : Subgroup G))).functor n).obj
        ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hVU)).obj (cokernel ι)) :=
    ((inflation R (quotientMap hVU)).app n).app (cokernel ι)
  let gV := ((cohomologyDelta R (G ⧸ (V : Subgroup G))).functor n).map
    ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hVU)).map (cokernel.π ι))
  have hc : ((inflation R (quotientMk V)).app n).app _ (gV b - τ z) = 0 := by
    rw [map_sub, sub_eq_zero]
    refine (inflation_naturality_apply (quotientMk V) n _ b).trans ?_
    refine (congrArg _ hb).trans ?_
    refine ha.trans ?_
    exact (inflation_quotientMk_quotientMap_apply R hVU n _ z).symm
  obtain ⟨W, hWV, hc'⟩ := hJ V _ _ hc
  rw [map_sub, sub_eq_zero] at hc'
  refine ⟨W, hWV.trans hVU, ?_⟩
  rw [← inflation_quotientMap_quotientMap_apply R hVU hWV]
  have hS₁ := hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hVU))
  have h2 : ((inflation R (quotientMap hWV)).app (n + 1)).app _
      (((inflation R (quotientMap hVU)).app (n + 1)).app X y) = 0 := by
    rw [← hz]
    refine (congrArg _ (inflation_δ_apply (quotientMap hVU) hS n z)).trans ?_
    refine (inflation_δ_apply (quotientMap hWV) hS₁ n _).trans ?_
    refine (congrArg _ hc'.symm).trans ?_
    refine (congrArg _ (inflation_naturality_apply (quotientMap hWV) n _ b)).trans ?_
    exact ConcreteCategory.congr_hom ((cohomologyDelta R (G ⧸ (W : Subgroup G))).map_g_δ
      (hS₁.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hWV))) n)
      (((inflation R (quotientMap hWV)).app n).app
        ((finiteTypeContinuousModuleRes.{0, w, w} R (quotientMap hVU)).obj I) b)
  rw [h2]
  exact map_zero _

/-- **Continuity of cohomology**, in all degrees: every class of `Hⁿ(G, X)` is inflated from a
finite quotient, and a class of a finite quotient which dies in `G` dies in a smaller finite
quotient. -/
theorem inflationSurjective_and_inflationInjective (n : ℕ) :
    InflationSurjective R (G := G) n ∧ InflationInjective R (G := G) n := by
  induction n with
  | zero => exact ⟨inflationSurjective_zero R, inflationInjective_zero R⟩
  | succ n ih => exact ⟨inflationSurjective_succ R ih.1, inflationInjective_succ R ih.1 ih.2⟩

end Continuity

end Stacks.ContinuousCohomology

end
