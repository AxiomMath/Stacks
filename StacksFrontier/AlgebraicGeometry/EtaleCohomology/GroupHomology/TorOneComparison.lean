module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.TorOneChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompletedTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.AugmentationSquareNotClosed
public import StacksCore.Tactic.StacksAttribute

/-!
# `Tor₁^{Λ[[G]]}(Λ, Λ)` and the completed `Tor`

Let `Λ` be a finite ring and `G` a profinite group. Item (1) of the notes on homology of
[Stacks, Section 03VI] identifies `H_i(G, M)` with `Tor_i^{Λ[[G]]}(M, Λ)`. The library proves the
completed form `H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)` (`homologyIsoLimitTor`). This file compares,
in degree one and for `M = Λ`, the abstract `Tor` over the ring `Λ[[G]]`, the left derived functor
of the coinvariants of `Λ[[G]]`-modules, with the completed one:

* the change-of-rings maps `Tor₁^{Λ[[G]]}(Λ, Λ) → Tor₁^{Λ[G/U]}(Λ, Λ)` along `Λ[[G]] → Λ[G/U]`
  (`completedTorChangeOfRings`, `torOneLeg`) form a cone over the completed `Tor` diagram
  `torDiagram` (`torOneCone`), whose transition maps are the change-of-rings maps
  `torChangeOfRings`;
* under `Tor₁ = I / I²` (`torOneMk`) these maps are `I / I² → I_U / I_U²`
  (`torOneLeg_torOneTrivialMk`, `torDiagram_map_torOneLevelMk`);
* hence the induced map `Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ)` (`torOneLimitMap`) is
  surjective for every profinite `G` (`torOneLimitMap_surjective`) and injective when `G` is
  topologically finitely generated (`torOneLimitMap_injective`), by
  `exists_mem_ker_augmentation_eval_sub_mem` and `mem_augmentationIdealSq_iff_forall_eval_mem`.

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `completedTorChangeOfRings π`: `Tor_•^{Λ[[G]]}(res_π -, Λ) ⟶ Tor_•^{Λ[Q]}(-, Λ)` for
  `π : G → Q`, `G` compact and `Q` finite discrete.
* `torOneTrivial Λ G`: `Tor₁^{Λ[[G]]}(Λ, Λ)`.
* `torOneCone`, `torOneLimitMap`.
* `torOneIsoLimit`, `torOneIsoHomology`:
  `Tor₁^{Λ[[G]]}(Λ, Λ) ≅ lim_U Tor₁^{Λ[G/U]}(Λ, Λ) ≅ H₁(G, Λ)` for `G` topologically finitely
  generated.
* `mapCoeff`: change of coefficients `R[[G]] → S[[G]]`.

## Main results

* `torOneLimitMap_surjective`, `torOneLimitMap_injective`, `bijective_torOneLimitMap`.
* `not_injective_torOneLimitMap_piZMod`: for `G = (ℤ/p)^ℕ` and `Λ = 𝔽_p` the map is not injective.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.CategoryHomology MonoidAlgebra

universe w

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

section CompletedChangeOfRings

variable {Λ : Type} [Ring Λ] [Finite Λ] {Q : Type w} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]
  {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (π : G →ₜ* Q)

omit [Finite Λ] [CompactSpace Q] [DiscreteTopology Q] [CompactSpace G] in
/-- On the restriction of `Y` along `π`, `a ∈ Λ[[G]]` acts as `π(a) ∈ Λ[[Q]]` acts on `Y` viewed
over `Q`. -/
theorem smul_resCompleted (Y : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (a : CompletedGroupAlgebra (ULift.{w} Λ) G) (y : Y.obj.obj.obj.V) :
    (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from
        (a • (show (resCompleted π).obj Y from y))) =
      map (π : G →* Q) π.continuous a •
        (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from y) := by
  have h5 : map ((ContinuousMonoidHom.id Q : Q →ₜ* Q) : Q →* Q)
      (ContinuousMonoidHom.id Q).continuous (map (π : G →* Q) π.continuous a) =
      map (π : G →* Q) π.continuous a :=
    (map_congr _ continuous_id rfl _).trans (map_id _)
  exact (finiteTypeCompletedAction_res π Y a y).trans
    ((congrArg (fun b => finiteTypeCompletedAction Y b y) h5.symm).trans
      (finiteTypeCompletedAction_res (ContinuousMonoidHom.id Q) Y _ y).symm)

/-- `y ↦ [y]`, from `res_π Y` to the `Λ[[Q]]`-coinvariants of `Y`, a map of `Λ[[G]]`-modules. -/
def coinvariantsChangeOfRingsHom (Y : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    (resCompleted π).obj Y ⟶
      (ModuleCat.restrictScalars
        (augmentation : CompletedGroupAlgebra (ULift.{w} Λ) G →+* ULift.{w} Λ)).obj
        ((coinvariantsFunctor (ULift.{w} Λ) Q).obj
          ((resCompleted (ContinuousMonoidHom.id Q)).obj Y)) :=
  ModuleCat.ofHom (X := (resCompleted π).obj Y)
    (Y := (ModuleCat.restrictScalars
        (augmentation : CompletedGroupAlgebra (ULift.{w} Λ) G →+* ULift.{w} Λ)).obj
        ((coinvariantsFunctor (ULift.{w} Λ) Q).obj
          ((resCompleted (ContinuousMonoidHom.id Q)).obj Y)))
    { toFun := fun y => coinvariantsMk _ _
        (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from y)
      map_add' := fun y y' => coinvariantsMk_add _ _ _ _
      map_smul' := fun a y => by
        refine (congrArg (coinvariantsMk _ _) (smul_resCompleted π Y a y)).trans ?_
        refine (coinvariantsMk_smul _ _ _ _).trans ?_
        exact congrArg (fun c => c • coinvariantsMk (ULift.{w} Λ) Q
          (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from y))
          (augmentation_map _ _ a) }

/-- **The projection of coinvariants** `Λ ⊗_{Λ[[G]]} res_π Y → Λ ⊗_{Λ[[Q]]} Y`, `[y] ↦ [y]`,
naturally in `Y`. -/
def coinvariantsChangeOfRings :
    resCompleted π ⋙ coinvariantsFunctor (ULift.{w} Λ) G ⟶
      resCompleted (ContinuousMonoidHom.id Q) ⋙ coinvariantsFunctor (ULift.{w} Λ) Q where
  app Y := coinvariantsLift _ _ (coinvariantsChangeOfRingsHom π Y)
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl

omit [Finite Λ] [CompactSpace Q] [DiscreteTopology Q] [CompactSpace G] in
/-- The projection of coinvariants on representatives. -/
theorem coinvariantsChangeOfRings_app_mk (Y : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (y : Y.obj.obj.obj.V) :
    ((coinvariantsChangeOfRings π).app Y).hom
        (coinvariantsMk _ _ (show (resCompleted π).obj Y from y)) =
      coinvariantsMk _ _ (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from y) :=
  rfl

/-- The degree-zero part of `completedTorChangeOfRings`: the projection of coinvariants, read on
`Tor₀ = Λ ⊗ -`. -/
def completedTorChangeOfRingsZero :
    ((finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ)).functor 0 ⟶
      (torDelta Λ Q).functor 0 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (resCompleted π)
        (coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedZeroIsoSelf.hom ≫
      coinvariantsChangeOfRings π ≫
        Functor.whiskerLeft (resCompleted (ContinuousMonoidHom.id Q))
          (coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedZeroIsoSelf.inv) (uliftRestrict Λ)

/-- **The change-of-rings map `Tor_i^{Λ[[G]]}(res_π M, Λ) ⟶ Tor_i^{Λ[Q]}(M, Λ)`** along
`Λ[[G]] → Λ[Q]`, for a compact group `G` and a continuous homomorphism `π : G → Q` to a finite
discrete group, as a morphism of homological δ-functors on finite modules with `Q`-action: the
unique one which is the projection of coinvariants in degree zero. For `G` finite discrete it is
`torChangeOfRings`. -/
def completedTorChangeOfRings :
    (finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ) ⟶ torDelta Λ Q :=
  haveI := isUniversal_torDelta Λ Q
  HomologicalDeltaFunctor.IsUniversal.lift (H := torDelta Λ Q) (completedTorChangeOfRingsZero π)

/-- **`completedTorChangeOfRings` is the projection of coinvariants in degree zero.** -/
theorem isCoinvariantsProjection_completedTorChangeOfRings :
    IsCoinvariantsProjection π (completedTorChangeOfRings (Λ := Λ) π) := by
  intro Y k
  have h0 : (completedTorChangeOfRings (Λ := Λ) π).app 0 = completedTorChangeOfRingsZero π :=
    haveI := isUniversal_torDelta Λ Q
    HomologicalDeltaFunctor.IsUniversal.lift_app_zero (H := torDelta Λ Q) _
  rw [h0]
  have e2 := congrArg (fun f => ModuleCat.Hom.hom f (coinvariantsMk _ _
      (show (resCompleted π).obj Y from k)))
    ((coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedZeroIsoSelf.inv_hom_id_app
      ((resCompleted π).obj Y))
  exact congrArg (fun z => (((coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedZeroIsoSelf.inv.app
    ((resCompleted (ContinuousMonoidHom.id Q)).obj Y)).hom
      (((coinvariantsChangeOfRings π).app Y).hom z))) e2

end CompletedChangeOfRings

section Squares

variable {R : Type w} [Ring R]

/-- A map of group algebras induced by a group homomorphism preserves the augmentation. -/
theorem finiteAugmentation_mapDomainRingHom {H K : Type*} [Group H] [Group K] (f : H →* K)
    (z : MonoidAlgebra R H) :
    finiteAugmentation K (mapDomainRingHom R f z) = finiteAugmentation H z := by
  have h : (finiteAugmentation K).comp (mapDomainRingHom R f) = finiteAugmentation H :=
    MonoidAlgebra.ringHom_ext (fun a => by simp)
      (fun g => by simp)
  exact DFunLike.congr_fun h z

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `(G/U)/⊥ → G/U`. -/
abbrev quotientBotLift (U : OpenNormalSubgroup G) :
    (G ⧸ (U : Subgroup G)) ⧸ (botOpenNormalSubgroup (G ⧸ (U : Subgroup G)) :
      Subgroup (G ⧸ (U : Subgroup G))) →* G ⧸ (U : Subgroup G) :=
  QuotientGroup.lift _ (MonoidHom.id _) fun _ hx => (MonoidHom.mem_ker).2 (Subgroup.mem_bot.1 hx)

/-- `Λ[G/U] → Λ[(G/U)/⊥] → Λ[G/U]` is the identity. -/
theorem mapDomainRingHom_quotientMapAlgebra_quotientMk (U : OpenNormalSubgroup G)
    (h : ∀ g ∈ U, (quotientMk U : G →* G ⧸ (U : Subgroup G)) g ∈
      botOpenNormalSubgroup (G ⧸ (U : Subgroup G)))
    (z : MonoidAlgebra R (G ⧸ (U : Subgroup G))) :
    mapDomainRingHom R (quotientBotLift U)
      (quotientMapAlgebra (quotientMk U : G →* G ⧸ (U : Subgroup G)) h z) = z := by
  have hs : ∀ (g : G) (a : R),
      mapDomainRingHom R (quotientBotLift U)
        (quotientMapAlgebra (quotientMk U : G →* G ⧸ (U : Subgroup G)) h
          (single (g : G ⧸ (U : Subgroup G)) a)) = single (g : G ⧸ (U : Subgroup G)) a := by
    intro g a
    rw [quotientMapAlgebra_single]
    exact mapDomain_single
  have key : (mapDomainRingHom R (quotientBotLift U)).comp
      (quotientMapAlgebra (quotientMk U : G →* G ⧸ (U : Subgroup G)) h) = RingHom.id _ := by
    refine MonoidAlgebra.ringHom_ext (fun a => ?_) (fun q => ?_)
    · have := hs 1 a
      rw [QuotientGroup.mk_one] at this
      exact this
    · induction q using QuotientGroup.induction_on with
      | H g => exact hs g 1
  exact DFunLike.congr_fun key z

variable [Finite R] [CompactSpace G]

/-- **The square of the augmentation ideal of `Λ[[G/U]] = Λ[G/U]`**: the image of `y ∈ Λ[[G]]` in
`Λ[[G/U]]` lies in its `I²` exactly when the image of `y` in `Λ[G/U]` lies in `I_U²`. -/
theorem map_quotientMk_mem_augmentationIdealSq_iff (U : OpenNormalSubgroup G)
    (y : CompletedGroupAlgebra R G) :
    map (quotientMk U : G →* G ⧸ (U : Subgroup G)) (quotientMk U).continuous y ∈
        augmentationIdealSq R (G ⧸ (U : Subgroup G)) ↔
      eval U y ∈ finiteAugmentationIdealSq R (G ⧸ (U : Subgroup G)) := by
  have hU : ∀ g ∈ U, (quotientMk U : G →* G ⧸ (U : Subgroup G)) g ∈
      botOpenNormalSubgroup (G ⧸ (U : Subgroup G)) :=
    fun g hg => Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff g).2 hg)
  constructor
  · intro hy
    have h1 := eval_mem_finiteAugmentationIdealSq (botOpenNormalSubgroup _) hy
    have e := eval_map (Λ := R) (quotientMk U : G →* G ⧸ (U : Subgroup G))
      (quotientMk U).continuous hU y
    have h2 : quotientMapAlgebra (quotientMk U : G →* G ⧸ (U : Subgroup G)) hU (eval U y) ∈
        finiteAugmentationIdealSq R _ := by
      rw [← e]
      exact h1
    rw [← mapDomainRingHom_quotientMapAlgebra_quotientMk U hU (eval U y)]
    exact map_mem_sq_ker _ (fun z => finiteAugmentation_mapDomainRingHom _ z) h2
  · intro hy
    refine (mem_augmentationIdealSq_iff_forall_eval_mem (ι := G ⧸ (U : Subgroup G)) (g := id)
      ?_ _).2 fun V => ?_
    · rw [Set.range_id, Subgroup.closure_univ, Subgroup.coe_top]
      exact dense_univ
    · have hV := map_mem_of_mem_comapSubgroup (quotientMk U : G →* G ⧸ (U : Subgroup G))
        (quotientMk U).continuous V
      have hUV : U ≤ comapSubgroup (quotientMk U : G →* G ⧸ (U : Subgroup G))
          (quotientMk U).continuous V := fun g hg => by
        have h1 : (quotientMk U : G →* G ⧸ (U : Subgroup G)) g = 1 :=
          (QuotientGroup.eq_one_iff g).2 hg
        change (quotientMk U : G →* G ⧸ (U : Subgroup G)) g ∈ V
        rw [h1]
        exact one_mem V
      have e := eval_map (Λ := R) (quotientMk U : G →* G ⧸ (U : Subgroup G))
        (quotientMk U).continuous hV y
      have h2 : quotientMapAlgebra (quotientMk U : G →* G ⧸ (U : Subgroup G)) hV
          (eval (comapSubgroup (quotientMk U : G →* G ⧸ (U : Subgroup G))
            (quotientMk U).continuous V) y) ∈ finiteAugmentationIdealSq R _ := by
        rw [← quotientAlgebraMap_eval hUV]
        exact map_mem_sq_ker _ (fun z => finiteAugmentation_mapDomainRingHom _ z)
          (quotientAlgebraMap_mem_finiteAugmentationIdealSq hUV hy)
      rw [← e] at h2
      exact h2

omit [Finite R] in
/-- `Λ[[G]] → Λ[[G/U]]` is surjective. -/
theorem exists_map_quotientMk_eq (U : OpenNormalSubgroup G)
    (z : CompletedGroupAlgebra R (G ⧸ (U : Subgroup G))) :
    ∃ y, map (quotientMk U : G →* G ⧸ (U : Subgroup G)) (quotientMk U).continuous y = z := by
  classical
  let := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  refine ⟨∑ q : G ⧸ (U : Subgroup G), const (coeffAt z q) * of q.out, ?_⟩
  rw [map_sum]
  conv_rhs => rw [eq_sum_const_mul_of z]
  exact Finset.sum_congr rfl fun q _ => (map_mul _ _ _).trans
    (congrArg₂ (· * ·) (CompletedGroupAlgebra.map_const _ _ _)
      ((CompletedGroupAlgebra.map_of _ _ _).trans (congrArg of (QuotientGroup.out_eq' q))))

end Squares

section Coefficients

variable {R S : Type*} [Ring R] [Ring S] {G : Type*} [Group G] [TopologicalSpace G]

/-- **Change of coefficients** `R[[G]] → S[[G]]` along a ring map `φ : R → S`, levelwise. -/
def mapCoeff (φ : R →+* S) : CompletedGroupAlgebra R G →+* CompletedGroupAlgebra S G :=
  (RingHom.pi fun U => (MonoidAlgebra.mapRingHom _ φ).comp (eval U)).codRestrict _
    fun x U V h => by
      change quotientAlgebraMap S h (MonoidAlgebra.mapRingHom _ φ (eval U x)) =
        MonoidAlgebra.mapRingHom _ φ (eval V x)
      rw [← quotientAlgebraMap_eval h x]
      exact DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom φ _).symm (eval U x)

/-- The components of `mapCoeff φ x` are the images of those of `x`. -/
theorem eval_mapCoeff (φ : R →+* S) (U : OpenNormalSubgroup G) (x : CompletedGroupAlgebra R G) :
    eval U (mapCoeff φ x) = MonoidAlgebra.mapRingHom _ φ (eval U x) :=
  rfl

omit [TopologicalSpace G] in
/-- Change of coefficients commutes with the augmentation of a group algebra. -/
theorem finiteAugmentation_mapRingHom (φ : R →+* S) (z : MonoidAlgebra R G) :
    finiteAugmentation G (MonoidAlgebra.mapRingHom G φ z) = φ (finiteAugmentation G z) := by
  have h : (finiteAugmentation G).comp (MonoidAlgebra.mapRingHom G φ) =
      φ.comp (finiteAugmentation G) :=
    MonoidAlgebra.ringHom_ext (fun a => by simp) (fun g => by simp)
  exact DFunLike.congr_fun h z

/-- A ring map sending `ker ε` into `ker ε'` sends the square of `ker ε` into that of `ker ε'`. -/
theorem map_mem_sq_ker_of_map_mem_ker {T T' : Type*} [Ring T] [Ring T'] {ε : R →+* T}
    {ε' : S →+* T'} (φ : R →+* S) (hφ : ∀ x, ε x = 0 → ε' (φ x) = 0) {z : R}
    (hz : z ∈ ((RingHom.ker ε).restrictScalars ℤ) ^ 2) :
    φ z ∈ ((RingHom.ker ε').restrictScalars ℤ) ^ 2 := by
  rw [pow_two] at hz ⊢
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun x y hx hy => ?_
  · rw [map_mul]
    exact Submodule.mul_mem_mul (hφ a ha) (hφ b hb)
  · rw [map_add]
    exact add_mem hx hy

/-- Change of coefficients twice along mutually inverse maps is the identity. -/
theorem mapCoeff_mapCoeff (φ : R →+* S) (ψ : S →+* R) (h : ∀ a, ψ (φ a) = a)
    (x : CompletedGroupAlgebra R G) : mapCoeff ψ (mapCoeff φ x) = x := by
  refine ext fun U => ?_
  have hc : ψ.comp φ = RingHom.id R := RingHom.ext h
  rw [eval_mapCoeff, eval_mapCoeff, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hc,
    MonoidAlgebra.mapRingHom_id, RingHom.id_apply]

/-- Change of coefficients commutes with the augmentation. -/
theorem augmentation_mapCoeff [IsTopologicalGroup G] (φ : R →+* S) (x : CompletedGroupAlgebra R G) :
    augmentation (mapCoeff φ x) = φ (augmentation x) := by
  rw [augmentation_eq topSubgroup, augmentation_eq topSubgroup, eval_mapCoeff,
    finiteAugmentation_mapRingHom]

end Coefficients

section Comparison

variable (Λ : Type) [Ring Λ] [Finite Λ] (G : Type w) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ)`**: the left derived functor of the coinvariants of `Λ[[G]]`-modules in
degree one, at the trivial module `Λ` (`finiteTypeGroupHomology` in degree one at `Λ`). -/
abbrev torOneTrivial : ModuleCat.{w} Λ :=
  (uliftRestrict Λ).obj (((finiteTypeGroupHomology (Λ := Λ) (ContinuousMonoidHom.id G)).functor
    1).obj (trivialFiniteTypeModule Λ G))

/-- `a ↦ a · 1`, the surjection `Λ[[G]] → Λ` with kernel the augmentation ideal. -/
def trivialAugmentationHom :
    ModuleCat.of (CompletedGroupAlgebra (ULift.{w} Λ) G) (CompletedGroupAlgebra (ULift.{w} Λ) G) ⟶
      (finiteTypeCompletedModule Λ G).obj (trivialFiniteTypeModule Λ G) :=
  ModuleCat.ofHom (Y := (finiteTypeCompletedModule Λ G).obj (trivialFiniteTypeModule Λ G))
    (LinearMap.toSpanSingleton _ _ (trivialGenerator Λ G))

variable {Λ G}

omit [Finite Λ] [CompactSpace G] in
/-- `a ↦ ε(a) · 1`. -/
theorem trivialAugmentationHom_apply (a : CompletedGroupAlgebra (ULift.{w} Λ) G) :
    (trivialAugmentationHom Λ G).hom a =
      ((augmentation a).down • trivialGenerator Λ G) :=
  finiteTypeCompletedAction_of_forall_eq_one _ (trivialFiniteTypeModule_ρ Λ G) a _

omit [Finite Λ] [CompactSpace G] in
/-- `a ↦ a · 1` is surjective. -/
theorem trivialAugmentationHom_surjective :
    Function.Surjective (trivialAugmentationHom Λ G).hom := fun y => by
  obtain ⟨c, rfl⟩ := (bijective_smul_trivialFiniteTypeModule Λ G).2 y
  exact ⟨const (ULift.up c), by rw [trivialAugmentationHom_apply, augmentation_const]⟩

omit [Finite Λ] [CompactSpace G] in
/-- The kernel of `a ↦ a · 1` is the augmentation ideal. -/
theorem ker_trivialAugmentationHom :
    LinearMap.ker (trivialAugmentationHom Λ G).hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra (ULift.{w} Λ) G →+* ULift.{w} Λ) := by
  ext a
  rw [LinearMap.mem_ker, trivialAugmentationHom_apply, RingHom.mem_ker]
  constructor
  · intro h
    exact ULift.ext ((bijective_smul_trivialFiniteTypeModule Λ G).1
      (h.trans (show (0 : (trivialFiniteTypeModule Λ G).obj.obj.obj.V) =
        (0 : Λ) • trivialGenerator Λ G from (zero_smul Λ _).symm)))
  · intro h
    rw [h]
    change (0 : Λ) • trivialGenerator Λ G = 0
    exact zero_smul Λ _

/-- **The surjection `I → Tor₁^{Λ[[G]]}(Λ, Λ)`**, `x ↦ [x]`, of kernel `I²`
(`torOneMk_eq_zero_iff`). -/
abbrev torOneTrivialMk : augmentationIdealModule (ULift.{w} Λ) G →+ torOneTrivial Λ G :=
  torOneMk (trivialAugmentationHom Λ G) trivialAugmentationHom_surjective
    ker_trivialAugmentationHom

omit [Finite Λ] [CompactSpace G] in
/-- `G ⧸ U` acts trivially on the descent of `Λ`. -/
theorem descendU_trivial_ρ (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G))
    (q : G ⧸ (U.1 : Subgroup G)) : (descendU U).obj.obj.obj.ρ q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H g => exact trivialFiniteTypeModule_ρ Λ G g

omit [Finite Λ] [CompactSpace G] in
/-- The descent of `Λ` is free of rank one on `1`. -/
theorem bijective_smul_descendU (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G)) :
    Function.Bijective fun c : Λ =>
      c • (show (descendU U).obj.obj.obj.V from trivialGenerator Λ G) :=
  bijective_smul_trivialFiniteTypeModule Λ G

/-- Every open normal subgroup acts trivially on `Λ`. -/
def trivialSubgroupOf (U : OpenNormalSubgroup G) :
    TrivialSubgroup Λ (trivialFiniteTypeModule Λ G) :=
  ⟨U, fun g _ => trivialFiniteTypeModule_ρ Λ G g⟩

/-- `Tor₁^{Λ[[G/U]]}(Λ, Λ) = I_U / I_U²` at a finite level: the class of `c ∈ I_U`. -/
abbrev torOneLevelMk (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G)) :
    augmentationIdealModule (ULift.{w} Λ) (G ⧸ (U.1 : Subgroup G)) →+
      (torDiagram Λ (trivialFiniteTypeModule Λ G) 1).obj U :=
  trivialTorOneMk (ContinuousMonoidHom.id _) (descendU U) (trivialGenerator Λ G)
    (bijective_smul_descendU U) (descendU_trivial_ρ U)

/-- **The change-of-rings map `Tor₁^{Λ[[G]]}(Λ, Λ) → Tor₁^{Λ[G/U]}(Λ, Λ)`** along
`Λ[[G]] → Λ[G/U]` (`completedTorChangeOfRings`). -/
def torOneLeg (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G)) :
    torOneTrivial Λ G ⟶ (torDiagram Λ (trivialFiniteTypeModule Λ G) 1).obj U :=
  ((completedTorChangeOfRings (Λ := Λ) (quotientMk U.1)).app 1).app (descendU U)

/-- **The change of rings `Tor₁^{Λ[[G]]}(Λ, Λ) → Tor₁^{Λ[G/U]}(Λ, Λ)` is `I/I² → I_U/I_U²`**:
it sends the class of `x ∈ I` to the class of its image in `Λ[[G/U]] = Λ[G/U]`. -/
theorem torOneLeg_torOneTrivialMk (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G))
    (x : augmentationIdealModule (ULift.{w} Λ) G) :
    (torOneLeg U).hom (torOneTrivialMk x) =
      torOneLevelMk U (augmentationIdealMap (quotientMk U.1) x) := by
  have hp : trivialProjection (quotientMk U.1) (descendU U) (trivialGenerator Λ G)
      (bijective_smul_descendU U) = trivialAugmentationHom Λ G :=
    ModuleCat.hom_ext (LinearMap.ext fun a =>
      (trivialProjection_apply (quotientMk U.1) (descendU U) (trivialGenerator Λ G)
        (bijective_smul_descendU U) (descendU_trivial_ρ U) a).trans
        (trivialAugmentationHom_apply a).symm)
  have hmk : torOneTrivialMk (Λ := Λ) (G := G) = trivialTorOneMk (quotientMk U.1) (descendU U)
      (trivialGenerator Λ G) (bijective_smul_descendU U) (descendU_trivial_ρ U) :=
    (torOneMk_congr _ _ _ hp.symm _ _)
  rw [hmk]
  exact app_one_trivialTorOneMk (quotientMk U.1) (descendU U) (trivialGenerator Λ G)
    (bijective_smul_descendU U) (descendU_trivial_ρ U) _
    (isCoinvariantsProjection_completedTorChangeOfRings _) x

omit [Finite Λ] [CompactSpace G] in
/-- The images in `Λ[[G/V]]` and then `Λ[[G/U]]` are the image in `Λ[[G/U]]`. -/
theorem augmentationIdealMap_quotientMap_augmentationIdealMap {U V : OpenNormalSubgroup G}
    (h : V ≤ U) (x : augmentationIdealModule (ULift.{w} Λ) G) :
    augmentationIdealMap (quotientMap h) (augmentationIdealMap (quotientMk V) x) =
      augmentationIdealMap (quotientMk U) x :=
  Subtype.ext ((map_map _ _ _ _ _).trans (map_congr _ _ (MonoidHom.ext fun _ => rfl) _))

/-- **The transition maps of the completed `Tor` diagram are `I_V/I_V² → I_U/I_U²`.** -/
theorem torDiagram_map_torOneLevelMk {V U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G)}
    (f : V ⟶ U) (c : augmentationIdealModule (ULift.{w} Λ) (G ⧸ (V.1 : Subgroup G))) :
    ((torDiagram Λ (trivialFiniteTypeModule Λ G) 1).map f).hom (torOneLevelMk V c) =
      torOneLevelMk U (augmentationIdealMap (quotientMap (show V.1 ≤ U.1 from leOfHom f)) c) := by
  have hu : trivialProjection (ContinuousMonoidHom.id _) (descendU V) (trivialGenerator Λ G)
        (bijective_smul_descendU V) ≫
        (resCompleted (ContinuousMonoidHom.id _)).map
          (descendTransition Λ (trivialFiniteTypeModule Λ G) (leOfHom f)) =
      trivialProjection (quotientMap (show V.1 ≤ U.1 from leOfHom f)) (descendU U)
        (trivialGenerator Λ G) (bijective_smul_descendU U) :=
    ModuleCat.hom_ext (LinearMap.ext fun a =>
      (congrArg ((resCompleted (ContinuousMonoidHom.id _)).map
          (descendTransition Λ (trivialFiniteTypeModule Λ G) (leOfHom f))).hom
        (trivialProjection_apply _ (descendU V) _ (bijective_smul_descendU V)
          (descendU_trivial_ρ V) a)).trans
      (trivialProjection_apply (quotientMap (show V.1 ≤ U.1 from leOfHom f)) (descendU U) _
        (bijective_smul_descendU U) (descendU_trivial_ρ U) a).symm)
  have h1 := leftDerived_map_torOneMk _
    (trivialProjection_surjective (ContinuousMonoidHom.id _) (descendU V) (trivialGenerator Λ G)
      (bijective_smul_descendU V) (descendU_trivial_ρ V))
    (ker_trivialProjection (ContinuousMonoidHom.id _) (descendU V) (trivialGenerator Λ G)
      (bijective_smul_descendU V) (descendU_trivial_ρ V))
    (trivialProjection_surjective (quotientMap (show V.1 ≤ U.1 from leOfHom f)) (descendU U)
      (trivialGenerator Λ G) (bijective_smul_descendU U) (descendU_trivial_ρ U))
    (ker_trivialProjection (quotientMap (show V.1 ≤ U.1 from leOfHom f)) (descendU U)
      (trivialGenerator Λ G) (bijective_smul_descendU U) (descendU_trivial_ρ U)) _ hu c
  rw [torDiagram_map]
  exact (congrArg (((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f))).app 1).app
    (descendU U)).hom h1).trans
    (torChangeOfRings_app_one_trivialTorOneMk Λ _ (descendU U) (trivialGenerator Λ G)
      (bijective_smul_descendU U) (descendU_trivial_ρ U) c)

variable (Λ G) in
/-- **The cone of change-of-rings maps** `Tor₁^{Λ[[G]]}(Λ, Λ) → Tor₁^{Λ[G/U]}(Λ, Λ)` over the
completed `Tor` diagram. -/
def torOneCone : Cone (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) where
  pt := torOneTrivial Λ G
  π :=
    { app := torOneLeg
      naturality := fun V U f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro t
        obtain ⟨x, rfl⟩ := torOneMk_surjective _ trivialAugmentationHom_surjective
          ker_trivialAugmentationHom t
        exact (torOneLeg_torOneTrivialMk U x).trans
          ((congrArg (torOneLevelMk U) (augmentationIdealMap_quotientMap_augmentationIdealMap
            (show V.1 ≤ U.1 from leOfHom f) x)).symm.trans
            ((torDiagram_map_torOneLevelMk f _).symm.trans
              (congrArg ((torDiagram Λ _ 1).map f).hom (torOneLeg_torOneTrivialMk V x).symm))) }

variable (Λ G) in
/-- **The change-of-rings map `Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ)`**, induced by the
change of rings along `Λ[[G]] → Λ[G/U]` for every open normal subgroup `U`. -/
def torOneLimitMap : torOneTrivial Λ G ⟶ limit (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) :=
  limit.lift _ (torOneCone Λ G)

/-- The components of `torOneLimitMap` are the change-of-rings maps. -/
theorem torOneLimitMap_π (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G))
    (t : torOneTrivial Λ G) :
    (limit.π (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) U).hom
        ((torOneLimitMap Λ G).hom t) = (torOneLeg U).hom t :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (limit.lift_π (torOneCone Λ G) U)) t

/-- The class of `x ∈ I` vanishes in `Tor₁^{Λ[G/U]}(Λ, Λ)` exactly when the image of `x` in
`Λ[G/U]` lies in `I_U²`. -/
theorem torOneLeg_torOneTrivialMk_eq_zero_iff
    (U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G))
    (x : augmentationIdealModule (ULift.{w} Λ) G) :
    (torOneLeg U).hom (torOneTrivialMk x) = 0 ↔
      eval U.1 (x : CompletedGroupAlgebra (ULift.{w} Λ) G) ∈
        finiteAugmentationIdealSq (ULift.{w} Λ) (G ⧸ (U.1 : Subgroup G)) := by
  rw [torOneLeg_torOneTrivialMk]
  exact (torOneMk_eq_zero_iff _ _ _ _).trans (map_quotientMk_mem_augmentationIdealSq_iff U.1 _)

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ)` is injective** for `G` topologically
finitely generated: `I²` is closed in `Λ[[G]]`. -/
theorem torOneLimitMap_injective {ι : Type*} [Finite ι] {g : ι → G}
    (hg : Dense (Subgroup.closure (Set.range g) : Set G)) :
    Function.Injective (torOneLimitMap Λ G).hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨x, rfl⟩ := torOneMk_surjective _ trivialAugmentationHom_surjective
    ker_trivialAugmentationHom t
  refine (torOneMk_eq_zero_iff _ _ _ x).2
    ((mem_augmentationIdealSq_iff_forall_eval_mem hg _).2 fun U => ?_)
  refine (torOneLeg_torOneTrivialMk_eq_zero_iff (trivialSubgroupOf U) x).1 ?_
  exact (torOneLimitMap_π (trivialSubgroupOf U) _).symm.trans
    ((congrArg _ ht).trans (map_zero _))

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ)` is surjective**, for every profinite `G`:
a compatible family of classes in the `I_U / I_U²` lifts, by compactness. -/
theorem torOneLimitMap_surjective : Function.Surjective (torOneLimitMap Λ G).hom := by
  intro z
  have hrep : ∀ U : TrivialSubgroup Λ (trivialFiniteTypeModule Λ G),
      ∃ y : augmentationIdealModule (ULift.{w} Λ) G,
        (torOneLeg U).hom (torOneTrivialMk y) =
          (limit.π (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) U).hom z := by
    intro U
    obtain ⟨c, hc⟩ := torOneMk_surjective _ (trivialProjection_surjective _ (descendU U)
      (trivialGenerator Λ G) (bijective_smul_descendU U) (descendU_trivial_ρ U))
      (ker_trivialProjection _ (descendU U) (trivialGenerator Λ G) (bijective_smul_descendU U)
        (descendU_trivial_ρ U)) ((limit.π (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) U).hom z)
    obtain ⟨y, hy⟩ := exists_map_quotientMk_eq U.1
      (c : CompletedGroupAlgebra (ULift.{w} Λ) (G ⧸ (U.1 : Subgroup G)))
    have hy0 : y ∈ RingHom.ker
        (augmentation : CompletedGroupAlgebra (ULift.{w} Λ) G →+* ULift.{w} Λ) :=
      (augmentation_map _ _ y).symm.trans ((congrArg augmentation hy).trans c.2)
    refine ⟨⟨y, hy0⟩, ?_⟩
    have e : augmentationIdealMap (quotientMk U.1) ⟨y, hy0⟩ = c := Subtype.ext hy
    exact (torOneLeg_torOneTrivialMk U _).trans ((congrArg (torOneLevelMk U) e).trans hc)
  choose y hy using hrep
  have hcompat : ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V),
      quotientAlgebraMap (ULift.{w} Λ) h
          (eval U (y (trivialSubgroupOf U) : CompletedGroupAlgebra (ULift.{w} Λ) G)) -
        eval V (y (trivialSubgroupOf V) : CompletedGroupAlgebra (ULift.{w} Λ) G) ∈
          finiteAugmentationIdealSq (ULift.{w} Λ) (G ⧸ (V : Subgroup G)) := by
    intro U V h
    have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (limit.w (torDiagram Λ (trivialFiniteTypeModule Λ G) 1)
        (homOfLE h : trivialSubgroupOf U ⟶ trivialSubgroupOf V))) z
    have e2 := congrArg ((torDiagram Λ (trivialFiniteTypeModule Λ G) 1).map
      (homOfLE h : trivialSubgroupOf U ⟶ trivialSubgroupOf V)).hom (hy (trivialSubgroupOf U))
    have e3 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((torOneCone Λ G).w
      (homOfLE h : trivialSubgroupOf U ⟶ trivialSubgroupOf V)))
      (torOneTrivialMk (y (trivialSubgroupOf U)))
    have e4 : (torOneLeg (trivialSubgroupOf V)).hom
        (torOneTrivialMk (y (trivialSubgroupOf U) - y (trivialSubgroupOf V))) = 0 :=
      ((congrArg (torOneLeg (trivialSubgroupOf V)).hom (map_sub _ _ _)).trans
        (map_sub _ _ _)).trans (sub_eq_zero.2
          (e3.symm.trans (e2.trans (e1.trans (hy (trivialSubgroupOf V)).symm))))
    have e5 := (torOneLeg_torOneTrivialMk_eq_zero_iff (trivialSubgroupOf V) _).1 e4
    rw [quotientAlgebraMap_eval h, ← map_sub]
    exact e5
  obtain ⟨x, hx0, hx⟩ := exists_mem_ker_augmentation_eval_sub_mem
    (fun U => eval U (y (trivialSubgroupOf U) : CompletedGroupAlgebra (ULift.{w} Λ) G))
    (fun U => (augmentation_eq U _).symm.trans (y (trivialSubgroupOf U)).2) hcompat
  refine ⟨torOneTrivialMk ⟨x, hx0⟩, Concrete.limit_ext _ _ _ fun U => ?_⟩
  refine (torOneLimitMap_π U _).trans ((sub_eq_zero.1 ?_).trans (hy U))
  refine ((map_sub _ _ _).symm.trans (congrArg (torOneLeg U).hom (map_sub _ _ _).symm)).trans ?_
  refine (torOneLeg_torOneTrivialMk_eq_zero_iff U _).2 ?_
  have := hx U.1
  rw [← map_sub] at this
  exact this

/-- **Stacks Project, Section 03VI, notes on homology (1), in degree one with `M = Λ`, for the
abstract `Tor`.** For a finite ring `Λ` and a profinite group `G` topologically generated by
finitely many elements, the change-of-rings map
`Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ)` (`torOneLimitMap`) is bijective. Here
`Tor_•^{Λ[[G]]}(-, Λ)` is the left derived functor of the coinvariants of `Λ[[G]]`-modules and the
limit is the completed `Tor` of `torDiagram`, which is `H₁(G, Λ)` (`homologyIsoLimitTor`,
`torOneIsoHomology`). Surjectivity holds for every profinite `G` (`torOneLimitMap_surjective`);
injectivity fails for `G = (ℤ/p)^ℕ` (`not_injective_torOneLimitMap_piZMod`). -/
@[stacks 03VI "Notes on Homology (1) in degree one with M = Λ, for G topologically finitely
generated: the change-of-rings map Tor₁^{Λ[[G]]}(Λ, Λ) → lim_U Tor₁^{Λ[G/U]}(Λ, Λ) is bijective,
Tor over Λ[[G]] being the left derived functor of the coinvariants"]
theorem bijective_torOneLimitMap {ι : Type*} [Finite ι] {g : ι → G}
    (hg : Dense (Subgroup.closure (Set.range g) : Set G)) :
    Function.Bijective (torOneLimitMap Λ G).hom :=
  ⟨torOneLimitMap_injective hg, torOneLimitMap_surjective⟩

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ) ≅ lim_U Tor₁^{Λ[G/U]}(Λ, Λ)`** by the change-of-rings maps, for `G`
topologically finitely generated. -/
def torOneIsoLimit {ι : Type*} [Finite ι] {g : ι → G}
    (hg : Dense (Subgroup.closure (Set.range g) : Set G)) :
    torOneTrivial Λ G ≅ limit (torDiagram Λ (trivialFiniteTypeModule Λ G) 1) :=
  (LinearEquiv.ofBijective (torOneLimitMap Λ G).hom (bijective_torOneLimitMap hg)).toModuleIso

/-- The isomorphism `torOneIsoLimit` is `torOneLimitMap`. -/
theorem torOneIsoLimit_hom {ι : Type*} [Finite ι] {g : ι → G}
    (hg : Dense (Subgroup.closure (Set.range g) : Set G)) :
    (torOneIsoLimit hg).hom = torOneLimitMap Λ G :=
  rfl

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ) ≅ H₁(G, Λ)`** for a profinite group `G` topologically generated by
finitely many elements and a finite ring `Λ`: `torOneIsoLimit` followed by
`H₁(G, Λ) ≅ lim_U Tor₁^{Λ[G/U]}(Λ, Λ)` (`homologyIsoLimitTor`). Here `H₁(G, Λ) = H¹(G, Λ^∨)^∨`. -/
def torOneIsoHomology [TotallyDisconnectedSpace G] {ι : Type*} [Finite ι] {g : ι → G}
    (hg : Dense (Subgroup.closure (Set.range g) : Set G)) :
    torOneTrivial Λ G ≅
      ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor 1).obj
        (trivialFiniteTypeModule Λ G) :=
  torOneIsoLimit hg ≪≫ (homologyIsoLimitTor Λ (trivialFiniteTypeModule Λ G) 1).symm

end Comparison

section Counterexample

variable (p : ℕ) [Fact p.Prime]

/-- **The change-of-rings map `Tor₁^{𝔽_p[[G]]}(𝔽_p, 𝔽_p) → lim_U Tor₁^{𝔽_p[G/U]}(𝔽_p, 𝔽_p)` is
not injective for `G = (ℤ/p)^ℕ`**: the element `f = Σ_t (e_{2t} - 1)(e_{2t+1} - 1)` of
`exists_forall_eval_mem_and_not_mem_augmentationIdealSq` lies in `I_U²` at every finite level but
not in `I²`, so its class in `Tor₁ = I / I²` is non-zero with zero image. So the identification of
the abstract `Tor₁^{Λ[[G]]}(Λ, Λ)` with `H₁(G, Λ)` by change of rings fails without finite
generation. -/
theorem not_injective_torOneLimitMap_piZMod :
    ¬ Function.Injective (torOneLimitMap (ZMod p) (ℕ → Multiplicative (ZMod p))).hom := by
  intro hinj
  obtain ⟨f, hf0, hfU, hfnot⟩ := exists_forall_eval_mem_and_not_mem_augmentationIdealSq p
  let φ : ZMod p →+* ULift.{0} (ZMod p) := ULift.ringEquiv.symm.toRingHom
  let ψ : ULift.{0} (ZMod p) →+* ZMod p := ULift.ringEquiv.toRingHom
  have hf'0 : mapCoeff φ f ∈ RingHom.ker (augmentation : CompletedGroupAlgebra (ULift.{0} (ZMod p))
      (ℕ → Multiplicative (ZMod p)) →+* ULift.{0} (ZMod p)) := by
    rw [RingHom.mem_ker, augmentation_mapCoeff, hf0, map_zero]
  let x : augmentationIdealModule (ULift.{0} (ZMod p)) (ℕ → Multiplicative (ZMod p)) :=
    ⟨mapCoeff φ f, hf'0⟩
  have hx : torOneTrivialMk x ≠ 0 := by
    intro h
    have h1 := (torOneMk_eq_zero_iff _ _ _ x).1 h
    apply hfnot
    have h2 := map_mem_sq_ker_of_map_mem_ker (mapCoeff ψ)
      (fun y hy => by rw [augmentation_mapCoeff, hy, map_zero]) h1
    rwa [mapCoeff_mapCoeff φ ψ (fun _ => rfl)] at h2
  have hz : (torOneLimitMap (ZMod p) (ℕ → Multiplicative (ZMod p))).hom (torOneTrivialMk x) =
      (torOneLimitMap (ZMod p) (ℕ → Multiplicative (ZMod p))).hom 0 := by
    refine Concrete.limit_ext _ _ _ fun U => ?_
    refine (torOneLimitMap_π U _).trans (((torOneLeg_torOneTrivialMk_eq_zero_iff U x).2 ?_).trans
      ((torOneLimitMap_π U 0).trans (map_zero _)).symm)
    exact map_mem_sq_ker_of_map_mem_ker (MonoidAlgebra.mapRingHom _ φ)
      (fun z hz => by rw [finiteAugmentation_mapRingHom, hz, map_zero]) (hfU U.1)
  exact hx (hinj hz)

end Counterexample

end Stacks.GroupHomology
