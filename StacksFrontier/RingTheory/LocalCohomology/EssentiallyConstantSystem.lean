module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Biproducts
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Defs
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerSystems

/-!
# Essential constancy of a local cohomology system

Let `A` be a Noetherian local ring and let `(Fₙ)` be an inverse system of finite `A`-modules.
If a finite `A`-module `M` maps to `lim Fₙ` so that the induced map from `Hⁱ_𝔪(M)` to
`lim Hⁱ_𝔪(Fₙ)` is an isomorphism, then the inverse system `(Hⁱ_𝔪(Fₙ))` is essentially constant.

The system is Mittag-Leffler because each of its terms is Artinian, so the image of each
projection from the limit is the stable part of the corresponding term, and the kernels of the
projections stabilize because the limit is Artinian too. From some index on, the projection is
injective and its image is the image of a transition map, which splits the system off the limit
and exhibits it as essentially constant.

That splitting argument uses the Artinian hypothesis only to produce an index beyond which the
projections are injective, and it produces an essential-constancy witness for the limit cone it
is handed. Both observations are recorded in the criterion the above specializes: a
Mittag-Leffler inverse system of modules whose limit injects into its terms from some index on
is essentially constant with value that limit, with respect to the given limit cone. That
criterion is the reduction step of [Stacks, Tag 0EIE], which derives essential constancy of
`{Hⁱ_T(M/IⁿM)}` from the Mittag-Leffler property, the identification of `Hⁱ_T(M)` with the
inverse limit of the system, and the injectivity of `Hⁱ_T(M) → Hⁱ_T(M/IⁿM)` for `n ≫ 0`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyModuleFunctor` — local cohomology supported at the
  maximal ideal, in a fixed degree, as a functor on modules.

## Main results

* `Stacks.LocalCohomology.isEssentiallyConstantWith_of_isMittagLeffler_of_eventually_injective`
  — a Mittag-Leffler inverse system of modules whose limit injects into its terms from some
  index on is essentially constant with value that limit.
* `Stacks.LocalCohomology.isEssentiallyConstantWith_of_isMittagLeffler_of_isArtinian` — the same
  conclusion with the eventual injectivity replaced by the descending chain condition on the
  point of the limit cone, which supplies it.
* `Stacks.LocalCohomology.isEssentiallyConstantInverseSystem_localCohomology` — the essential
  constancy criterion.

## Implementation notes

"With value `Hⁱ_𝔪(M)`" is expressed by the assumed isomorphism onto the inverse limit, through
Mathlib's canonical comparison `CategoryTheory.Limits.limit.post`, and the conclusion is the
standard predicate for an essentially constant inverse system. The combinatorics of the
Mittag-Leffler argument is carried out on `DirInvSystem`, the `ℕ`-indexed inverse system of
underlying modules.

## References

* [Stacks Project, Tag 0EHB](https://stacks.math.columbia.edu/tag/0EHB)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

section

open Opposite

/-- The subobject image of a transition map, read as a submodule, is the range of the
corresponding linear map. -/
private theorem transitionImage_subobjectModule
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    (i k : ℕ) (h : i ≤ k) :
    ModuleCat.subobjectModule (F.obj (op i))
        (transitionImage F i k h) =
      LinearMap.range (ModuleCat.homEquiv (F.map (homOfLE h).op)) := by
  have heq :
      Subobject.mk (image.ι (F.map (homOfLE h).op)) =
        Subobject.mk (ModuleCat.ofHom
          (ModuleCat.homEquiv (F.map (homOfLE h).op)).range.subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange _)
      (ModuleCat.imageIsoRange_hom_subtype _)
  rw [transitionImage, heq]
  exact (ModuleCat.subobjectModule (F.obj (op i))).apply_symm_apply _

/-- The `ℕ`-indexed inverse system of underlying modules of an inverse system in `ModuleCat A`. -/
private noncomputable def moduleTower
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) :
    DirInvSystem (fun n : ℕ => F.obj (op n)) where
  φ := fun {i j} h => ModuleCat.homEquiv (F.map (homOfLE h).op)
  φ_self i x := by simp [ModuleCat.homEquiv]
  φ_comp := by
    intro i j k hij hjk x
    change (F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op) x =
      (F.map (homOfLE (hij.trans hjk)).op) x
    rw [← Functor.map_comp]
    congr 1

/-- A Mittag-Leffler inverse system of modules has a Mittag-Leffler tower of underlying modules. -/
private theorem moduleTower_mittagLeffler
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    (hML : IsMittagLefflerCategorical F) :
    (moduleTower F).IsMittagLeffler := by
  intro i
  obtain ⟨c, hic, hstable⟩ := hML i
  refine ⟨c, hic, fun k hck => ?_⟩
  have heq := congrArg (ModuleCat.subobjectModule (F.obj (op i))) (hstable k hck)
  rw [transitionImage_subobjectModule, transitionImage_subobjectModule] at heq
  exact congrArg SetLike.coe heq

/-- The fibre condition over a chosen element `x₀` at index `i₀`: below `i₀` an element must be
the image of `x₀`, above `i₀` it must be stable and map to `x₀`. -/
public def towerFiberProp {A : ℕ → Type*}
    (S : DirInvSystem A) (i₀ : ℕ) (x₀ : A i₀) (i : ℕ) (x : A i) : Prop :=
  if h : i ≤ i₀ then x = S.φ h x₀
  else S.Stable x ∧ S.φ (Nat.le_of_lt (Nat.lt_of_not_ge h)) x = x₀

/-- The fibre condition is preserved by the transition maps of the tower. -/
private theorem towerFiberProp_map {A : ℕ → Type*}
    (S : DirInvSystem A) (i₀ : ℕ) (x₀ : A i₀)
    {i k : ℕ} (hik : i ≤ k) {x : A k} (hx : towerFiberProp S i₀ x₀ k x) :
    towerFiberProp S i₀ x₀ i (S.φ hik x) := by
  by_cases hi : i ≤ i₀
  · by_cases hk : k ≤ i₀
    · have hx' : x = S.φ hk x₀ := by simpa [towerFiberProp, hk] using hx
      have hval : S.φ hik x = S.φ hi x₀ := by simpa [hx'] using S.φ_comp hik hk x₀
      simpa [towerFiberProp, hi] using hval
    · have hx' : S.Stable x ∧ S.φ (Nat.le_of_not_ge hk) x = x₀ := by
        simpa [towerFiberProp, hk] using hx
      have hki : i₀ ≤ k := Nat.le_of_not_ge hk
      have hcomp := S.φ_comp hi hki x
      rw [hx'.2] at hcomp
      simpa [towerFiberProp, hi] using hcomp.symm
  · have hi₀ : i₀ ≤ i := Nat.le_of_not_ge hi
    have hk : ¬ k ≤ i₀ := fun h => hi (le_trans hik h)
    have hk₀ : i₀ ≤ k := hi₀.trans hik
    have hx' : S.Stable x ∧ S.φ hk₀ x = x₀ := by
      simpa [towerFiberProp, hk] using hx
    have hcomp := S.φ_comp hi₀ hik x
    rw [hx'.2] at hcomp
    have hval : S.Stable (S.φ hik x) ∧ S.φ hi₀ (S.φ hik x) = x₀ :=
      ⟨DirInvSystem.Stable.map S hik hx'.1, hcomp⟩
    simpa [towerFiberProp, hi] using hval

/-- For a Mittag-Leffler tower and a stable element, the transition maps between the fibres over
that element are surjective. -/
private theorem towerFiber_transition_surjective {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀)
    {i k : ℕ} (hik : i ≤ k) :
    Function.Surjective (fun z : {x : A k // towerFiberProp S i₀ x₀ k x} =>
      (⟨S.φ hik z.1, towerFiberProp_map S i₀ x₀ hik z.2⟩ :
        {x : A i // towerFiberProp S i₀ x₀ i x})) := by
  intro z
  by_cases hi : i ≤ i₀
  · have hz : z.1 = S.φ hi x₀ := by simpa [towerFiberProp, hi] using z.2
    by_cases hk : k ≤ i₀
    · exact ⟨⟨S.φ hk x₀, by simp [towerFiberProp, hk]⟩,
        Subtype.ext (by simpa [hz] using S.φ_comp hik hk x₀)⟩
    · have h₀k : i₀ ≤ k := Nat.le_of_not_ge hk
      obtain ⟨y, hys, hmap⟩ := S.stable_surjective hML h₀k hx₀
      refine ⟨⟨y, by simp [towerFiberProp, hk, hys, hmap]⟩, ?_⟩
      apply Subtype.ext
      calc
        S.φ hik y = S.φ hi (S.φ h₀k y) := (S.φ_comp hi h₀k y).symm
        _ = S.φ hi x₀ := by rw [hmap]
        _ = z.1 := hz.symm
  · have hi₀ : i₀ ≤ i := Nat.le_of_not_ge hi
    have hz : S.Stable z.1 ∧ S.φ hi₀ z.1 = x₀ := by
      simpa [towerFiberProp, hi] using z.2
    obtain ⟨y, hys, hmap⟩ := S.stable_surjective hML hik hz.1
    have h₀k : i₀ ≤ k := hi₀.trans hik
    have hbase : S.φ h₀k y = x₀ :=
      calc
        S.φ h₀k y = S.φ hi₀ (S.φ hik y) := (S.φ_comp hi₀ hik y).symm
        _ = S.φ hi₀ z.1 := by rw [hmap]
        _ = x₀ := hz.2
    have hyprop : towerFiberProp S i₀ x₀ k y := by
      have hk : ¬ k ≤ i₀ := fun h => hi (le_trans hik h)
      simpa [towerFiberProp, hk] using And.intro hys hbase
    exact ⟨⟨y, hyprop⟩, Subtype.ext hmap⟩

/-- The inverse system of fibres over a chosen element of a tower. -/
private noncomputable def towerFiberSystem {A : ℕ → Type*}
    (S : DirInvSystem A) (i₀ : ℕ) (x₀ : A i₀) :
    DirInvSystem (fun i => {x : A i // towerFiberProp S i₀ x₀ i x}) where
  φ := fun {_ _} hik x => ⟨S.φ hik x.1, towerFiberProp_map S i₀ x₀ hik x.2⟩
  φ_self i x := Subtype.ext (S.φ_self i x.1)
  φ_comp _ _ _ hij hjk x := Subtype.ext (S.φ_comp hij hjk x.1)

/-- The fibre system over a stable element of a Mittag-Leffler tower is Mittag-Leffler. -/
private theorem towerFiberSystem_mittagLeffler {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀) :
    (towerFiberSystem S i₀ x₀).IsMittagLeffler :=
  fun i => ⟨i, le_rfl, fun _ hik =>
    (Set.range_eq_univ.mpr (towerFiber_transition_surjective S hML i₀ x₀ hx₀ hik)).trans
      (Set.range_eq_univ.mpr (towerFiber_transition_surjective S hML i₀ x₀ hx₀ le_rfl)).symm⟩

/-- Every fibre over a stable element of a Mittag-Leffler tower is nonempty. -/
private theorem towerFiberSystem_nonempty {A : ℕ → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (i₀ : ℕ) (x₀ : A i₀) (hx₀ : S.Stable x₀) (i : ℕ) :
    Nonempty {x : A i // towerFiberProp S i₀ x₀ i x} := by
  by_cases hi : i ≤ i₀
  · exact ⟨⟨S.φ hi x₀, by simp [towerFiberProp, hi]⟩⟩
  · obtain ⟨x, hx, hmap⟩ := S.stable_surjective hML (Nat.le_of_not_ge hi) hx₀
    exact ⟨⟨x, by simpa [towerFiberProp, hi] using And.intro hx hmap⟩⟩

/-- A stable element of a term of a Mittag-Leffler system is the image of an element of the
point of any limit cone. -/
private theorem exists_conePoint_with_projection_of_stable
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hML : IsMittagLefflerCategorical F) (j : ℕ) {x : F.obj (op j)}
    (hx : (moduleTower F).Stable x) :
    ∃ z : ToType c.pt, c.π.app (op j) z = x := by
  let S := moduleTower F
  let T := towerFiberSystem S j x
  have hS := moduleTower_mittagLeffler hML
  obtain ⟨a, ha⟩ := T.nonempty_limit_of_isMittagLeffler
    (towerFiberSystem_mittagLeffler S hS j x hx) (towerFiberSystem_nonempty S hS j x hx)
  let sec : (F ⋙ forget (ModuleCat.{v} A)).sections :=
    ⟨fun n => (a n.unop).1, by
      intro n m f
      let h : m.unop ≤ n.unop := leOfHom f.unop
      show S.φ h ((a n.unop).1) = (a m.unop).1
      exact congrArg Subtype.val (ha h)⟩
  let L := isLimitOfPreserves (forget (ModuleCat.{v} A)) hc
  refine ⟨(Types.isLimitEquivSections L).symm sec, ?_⟩
  have hj : (a j).1 = x := by
    have heq : (a j).1 = S.φ (le_rfl : j ≤ j) x := by
      simpa [towerFiberProp, T] using (a j).2
    rwa [S.φ_self j x] at heq
  simpa [L, sec] using (Types.isLimitEquivSections_symm_apply L sec (op j)).trans hj

/-- A stable element of a term of a Mittag-Leffler system is the image of an element of the
inverse limit. -/
private theorem exists_limit_with_projection_of_stable
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    (hML : IsMittagLefflerCategorical F) (j : ℕ) {x : F.obj (op j)}
    (hx : (moduleTower F).Stable x) :
    ∃ z : ToType (limit F), limit.π F (op j) z = x :=
  exists_conePoint_with_projection_of_stable (limit.isLimit F) hML j hx

/-- The projections of a cone over an inverse system are compatible with the transition maps. -/
private theorem cone_projection_compat
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} (c : Cone F)
    {a b : ℕ} (hab : a ≤ b) (z : ToType c.pt) :
    (ModuleCat.homEquiv (F.map (homOfLE hab).op))
        ((ModuleCat.homEquiv (c.π.app (op b))) z) =
      (ModuleCat.homEquiv (c.π.app (op a))) z :=
  congrArg (fun f => ModuleCat.homEquiv f z) (c.w (homOfLE hab).op)

/-- The projections from the inverse limit are compatible with the transition maps. -/
private theorem limit_projection_compat
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    {a b : ℕ} (hab : a ≤ b) (z : ToType (limit F)) :
    (ModuleCat.homEquiv (F.map (homOfLE hab).op))
        ((ModuleCat.homEquiv (limit.π F (op b))) z) =
      (ModuleCat.homEquiv (limit.π F (op a))) z :=
  cone_projection_compat (limit.cone F) hab z

/-- For a Mittag-Leffler system, the image of the projection from the point of a limit cone to a
term is exactly the stable part of that term. -/
private theorem conePoint_projection_range_eq_stable
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hML : IsMittagLefflerCategorical F) (j : ℕ) :
    Set.range (ModuleCat.homEquiv (c.π.app (op j))) =
      {x : F.obj (op j) | (moduleTower F).Stable x} := by
  ext x
  refine ⟨?_, exists_conePoint_with_projection_of_stable hc hML j⟩
  rintro ⟨z, rfl⟩ k hjk
  exact ⟨(ModuleCat.homEquiv (c.π.app (op k))) z, cone_projection_compat c hjk z⟩

/-- For a Mittag-Leffler system, the image of the projection from the inverse limit to a term is
exactly the stable part of that term. -/
private theorem projection_range_eq_stable
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    (hML : IsMittagLefflerCategorical F) (j : ℕ) :
    Set.range (ModuleCat.homEquiv (limit.π F (op j))) =
      {x : F.obj (op j) | (moduleTower F).Stable x} :=
  conePoint_projection_range_eq_stable (limit.isLimit F) hML j

/-- If the point of a limit cone is Artinian, its projections to the terms are injective from
some index on, because their kernels form a descending chain. -/
private theorem eventually_injective_cone_projection
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hArt : IsArtinian A (ToType c.pt)) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      Function.Injective (ModuleCat.homEquiv (c.π.app (op m))) := by
  let p : ∀ n : ℕ, ToType c.pt →ₗ[A] F.obj (op n) :=
    fun n => ModuleCat.homEquiv (c.π.app (op n))
  let K : ℕ →o (Submodule A (ToType c.pt))ᵒᵈ :=
    { toFun := fun n => OrderDual.toDual (LinearMap.ker (p n))
      monotone' := by
        intro a b hab
        show LinearMap.ker (p b) ≤ LinearMap.ker (p a)
        intro z hz
        rw [LinearMap.mem_ker] at hz ⊢
        have hcp := cone_projection_compat c hab z
        change (ModuleCat.homEquiv (F.map (homOfLE hab).op)) (p b z) = p a z at hcp
        simpa [hz] using hcp.symm }
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes K
  have hker : ∀ m : ℕ, n ≤ m → LinearMap.ker (p n) = LinearMap.ker (p m) :=
    fun m hnm => OrderDual.toDual.injective (hn m hnm)
  have hbot : LinearMap.ker (p n) = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have hp : ∀ m : ℕ, p m z = 0 := by
      intro m
      by_cases hnm : n ≤ m
      · rw [hker m hnm] at hz
        exact LinearMap.mem_ker.mp hz
      · have hmn : m ≤ n := Nat.le_of_not_ge hnm
        have hcp := cone_projection_compat c hmn z
        change (ModuleCat.homEquiv (F.map (homOfLE hmn).op)) (p n z) = p m z at hcp
        rw [LinearMap.mem_ker.mp hz, map_zero] at hcp
        exact hcp.symm
    have hlim := isLimitOfPreserves (forget (ModuleCat.{v} A)) hc
    have hsections : (Types.isLimitEquivSections hlim) z =
        (Types.isLimitEquivSections hlim) (0 : ToType c.pt) := by
      apply Subtype.ext
      funext m
      simp only [Types.isLimitEquivSections_apply]
      show (p m.unop) z = (p m.unop) 0
      rw [hp m.unop, map_zero]
    exact (Types.isLimitEquivSections hlim).injective hsections
  refine ⟨n, fun m hnm => ?_⟩
  apply LinearMap.ker_eq_bot.mp
  rw [← hker m hnm, hbot]

/-- A linear map factors through an injective map with the same range. -/
private noncomputable def linearMapFactorThroughInjective
    {A : Type u} [CommRing A] {L M N : Type v}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (p : L →ₗ[A] N) (hp : Function.Injective p) (t : M →ₗ[A] N)
    (hR : LinearMap.range t = LinearMap.range p) : M →ₗ[A] L := by
  let e : L ≃ₗ[A] LinearMap.range p := LinearEquiv.ofInjective p hp
  let q : M →ₗ[A] LinearMap.range p :=
    LinearMap.codRestrict (LinearMap.range p) t (by
      intro x
      rw [← hR]
      exact ⟨x, rfl⟩)
  exact e.symm.toLinearMap.comp q

/-- The factorization through an injective map recovers the original map. -/
private theorem linearMapFactorThroughInjective_spec
    {A : Type u} [CommRing A] {L M N : Type v}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (p : L →ₗ[A] N) (hp : Function.Injective p) (t : M →ₗ[A] N)
    (hR : LinearMap.range t = LinearMap.range p) :
    p.comp (linearMapFactorThroughInjective p hp t hR) = t := by
  ext x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective p hp).apply_symm_apply
    ⟨t x, hR ▸ LinearMap.mem_range_self t x⟩)

/-- If the inverse limit is Artinian, the projections to the terms are injective from some index
on, because their kernels form a descending chain. -/
private theorem eventually_injective_limit_projection
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    (hArt : IsArtinian A (ToType (limit F))) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      Function.Injective (ModuleCat.homEquiv (limit.π F (op m))) :=
  eventually_injective_cone_projection (limit.isLimit F) hArt

/-- For a Mittag-Leffler system, the ranges of the transition maps into a fixed term eventually
agree with the image of the projection from the point of a limit cone. -/
private theorem exists_eventually_transition_range_eq_conePoint_projection
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hML : IsMittagLefflerCategorical F) (j : ℕ) :
    ∃ b : ℕ, ∃ hjb : j ≤ b, ∀ k, ∀ hbk : b ≤ k,
      Set.range (ModuleCat.homEquiv (F.map (homOfLE (hjb.trans hbk)).op)) =
        Set.range (ModuleCat.homEquiv (c.π.app (op j))) := by
  let S := moduleTower F
  have hS := moduleTower_mittagLeffler hML
  obtain ⟨b, hjb, hstable⟩ := hS j
  refine ⟨b, hjb, fun k hbk => ?_⟩
  calc
    Set.range (ModuleCat.homEquiv (F.map (homOfLE (hjb.trans hbk)).op)) =
        Set.range (ModuleCat.homEquiv (F.map (homOfLE hjb).op)) := by
          simpa [S, moduleTower] using hstable k hbk
    _ = {x : F.obj (op j) | S.Stable x} := (S.stable_eq_range hjb hstable).symm
    _ = Set.range (ModuleCat.homEquiv (c.π.app (op j))) :=
      (conePoint_projection_range_eq_stable hc hML j).symm

/-- For a Mittag-Leffler system, the ranges of the transition maps into a fixed term eventually
agree with the image of the projection from the limit. -/
private theorem exists_eventually_transition_range_eq_projection
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    (hML : IsMittagLefflerCategorical F) (j : ℕ) :
    ∃ c : ℕ, ∃ hjc : j ≤ c, ∀ k, ∀ hck : c ≤ k,
      Set.range (ModuleCat.homEquiv (F.map (homOfLE (hjc.trans hck)).op)) =
        Set.range (ModuleCat.homEquiv (limit.π F (op j))) :=
  exists_eventually_transition_range_eq_conePoint_projection (limit.isLimit F) hML j

/-- **A Mittag-Leffler inverse system of modules whose limit injects into its terms from some
index on is essentially constant with value that limit.** Let `F : ℕᵒᵖ ⥤ ModuleCat A` be
Mittag-Leffler, let `c` be a limit cone on `F`, and suppose the projection `c.pt ⟶ F_m` is
injective for every `m ≥ n`. Then `F` is essentially constant with value `c.pt`, with respect to
`c` itself.

*Argument.* For a Mittag-Leffler system the image of `c.pt → F_n` is the stable part of `F_n`,
hence equals the range of the transition map `F_i → F_n` for `i` large. So that transition map
factors through the injection `c.pt → F_n`, which yields `σ : F_i → c.pt` with
`(c.pt → F_n) ∘ σ = (F_i → F_n)`; precomposing with `c.pt → F_i` and cancelling the injection
`c.pt → F_n` gives `σ ∘ (c.pt → F_i) = id`. For cofinality at an index `j ≤ n` the two
composites agree after the transition `F_n → F_j`; for `j > n` one lifts the transition
`F_k → F_j` through `c.pt → F_j`, available for `k` large by the same stable-image description,
and identifies the lift with `σ` applied to the transition `F_k → F_i` by cancelling
`c.pt → F_n`. -/
public theorem isEssentiallyConstantWith_of_isMittagLeffler_of_eventually_injective
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hML : IsMittagLefflerCategorical F) {n : ℕ}
    (hninj : ∀ m : ℕ, n ≤ m → Function.Injective (ModuleCat.homEquiv (c.π.app (op m)))) :
    ∃ (j : ℕᵒᵖ) (σ : F.obj j ⟶ c.pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith F c j σ := by
  let p (m : ℕ) : ToType c.pt →ₗ[A] F.obj (op m) := ModuleCat.homEquiv (c.π.app (op m))
  let t {a b : ℕ} (h : a ≤ b) : F.obj (op b) →ₗ[A] F.obj (op a) :=
    ModuleCat.homEquiv (F.map (homOfLE h).op)
  have hpn : Function.Injective (p n) := hninj n le_rfl
  obtain ⟨i, hni, hstable⟩ :=
    exists_eventually_transition_range_eq_conePoint_projection hc hML n
  have hrange : LinearMap.range (t hni) = LinearMap.range (p n) :=
    SetLike.coe_injective (hstable i le_rfl)
  let sₗ : F.obj (op i) →ₗ[A] ToType c.pt :=
    linearMapFactorThroughInjective (p n) hpn (t hni) hrange
  have hfactor_apply (y : F.obj (op i)) : p n (sₗ y) = t hni y :=
    LinearMap.congr_fun (linearMapFactorThroughInjective_spec (p n) hpn (t hni) hrange) y
  have tcomp {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) (x : F.obj (op d)) :
      t hab (t hbd x) = t (hab.trans hbd) x := (moduleTower F).φ_comp hab hbd x
  have pcomp {a b : ℕ} (hab : a ≤ b) (z : ToType c.pt) :
      t hab (p b z) = p a z := cone_projection_compat c hab z
  refine ⟨op i, ModuleCat.ofHom sₗ, ?_, ?_⟩
  · ext z
    exact hpn ((hfactor_apply _).trans (pcomp hni z))
  · intro j
    let jn := j.unop
    obtain ⟨cj, hjcj, hstabj⟩ :=
      exists_eventually_transition_range_eq_conePoint_projection hc hML jn
    let k := max i cj
    have hik : i ≤ k := le_max_left _ _
    have hckj : cj ≤ k := le_max_right _ _
    have hjk : jn ≤ k := hjcj.trans hckj
    have hnk : n ≤ k := hni.trans hik
    refine ⟨op k, op (homOfLE hik), op (homOfLE hjk), ?_⟩
    apply ModuleCat.hom_ext
    ext x
    show t hjk x = p jn (sₗ (t hik x))
    by_cases hjn : jn ≤ n
    · calc
        t hjk x = t hjn (t hnk x) := (tcomp hjn hnk x).symm
        _ = t hjn (t hni (t hik x)) := by rw [tcomp hni hik]
        _ = t hjn (p n (sₗ (t hik x))) := by rw [hfactor_apply]
        _ = p jn (sₗ (t hik x)) := pcomp hjn _
    · have hnj : n ≤ jn := Nat.le_of_not_ge hjn
      obtain ⟨z, hz⟩ : t hjk x ∈ Set.range (p jn) := hstabj k hckj ▸ ⟨x, rfl⟩
      have hzs : z = sₗ (t hik x) := hpn (
        calc
          p n z = t hnj (p jn z) := (pcomp hnj z).symm
          _ = t hnj (t hjk x) := by rw [hz]
          _ = t hnk x := tcomp hnj hjk x
          _ = t hni (t hik x) := (tcomp hni hik x).symm
          _ = p n (sₗ (t hik x)) := (hfactor_apply _).symm)
      rw [← hz, hzs]

/-- **A Mittag-Leffler inverse system of modules whose limit cone has Artinian point is
essentially constant with value that point**, with respect to that very cone. The eventual
injectivity asked for by
`Stacks.LocalCohomology.isEssentiallyConstantWith_of_isMittagLeffler_of_eventually_injective`
is free here: the kernels of the projections `c.pt ⟶ F_m` form a descending chain in `c.pt`, so
they stabilize, and their intersection is zero because `c` is a limit cone. -/
public theorem isEssentiallyConstantWith_of_isMittagLeffler_of_isArtinian
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} {c : Cone F} (hc : IsLimit c)
    (hML : IsMittagLefflerCategorical F) (hArt : IsArtinian A (ToType c.pt)) :
    ∃ (j : ℕᵒᵖ) (σ : F.obj j ⟶ c.pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith F c j σ :=
  let ⟨_, hninj⟩ := eventually_injective_cone_projection hc hArt
  isEssentiallyConstantWith_of_isMittagLeffler_of_eventually_injective hc hML hninj

/-- A Mittag-Leffler inverse system of modules with Artinian inverse limit is essentially
constant. -/
private theorem essentiallyConstant_of_artinian_limit
    {A : Type u} [CommRing A] {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} [HasLimit F]
    (hML : IsMittagLefflerCategorical F)
    (hArt : IsArtinian A (ToType (limit F))) :
    CategoryTheory.IsEssentiallyConstantInverseSystem F := by
  obtain ⟨j, σ, hj⟩ := isEssentiallyConstantWith_of_isMittagLeffler_of_isArtinian
    (limit.isLimit F) hML hArt
  exact (CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantPro_iff_op F).mp
    ⟨limit.cone F, j, σ, hj⟩

end

/-- Local cohomology with support in the maximal ideal, in degree `i`, as a
functor on modules. -/
public noncomputable def localCohomologyModuleFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (i : ℤ) :
    CategoryTheory.Functor (ModuleCat.{v} A) (ModuleCat.{v} A) :=
  DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
    Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) ⋙
    (Dualizing.derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _)).ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} A) i

/-- **Stacks 0EHB.** If the canonical map from the local cohomology of a finite
module to the inverse limit of the local cohomology of a countable inverse
system of finite modules is an isomorphism, that local cohomology system is
essentially constant. -/
@[stacks 0EHB]
public theorem isEssentiallyConstantInverseSystem_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : CategoryTheory.Functor ℕᵒᵖ (ModuleCat.{v} A))
    (hF : ∀ n, Module.Finite A (F.obj n))
    (M : ModuleCat.{v} A) [Module.Finite A M] (i : ℤ)
    [HasLimit F] [HasLimit (F ⋙ localCohomologyModuleFunctor A i)]
    (f : M ⟶ limit F)
    (_ : IsIso ((localCohomologyModuleFunctor A i).map f ≫
      limit.post F (localCohomologyModuleFunctor A i))) :
    CategoryTheory.IsEssentiallyConstantInverseSystem
      (F ⋙ localCohomologyModuleFunctor A i) := by
  let H : ModuleCat.{v} A ⥤ ModuleCat.{v} A := localCohomologyModuleFunctor A i
  have hML : IsMittagLefflerCategorical (F ⋙ H) := by
    simpa [H, localCohomologyModuleFunctor] using
      isMittagLeffler_localCohomology A F hF i
  have hArtM : IsArtinian A (ToType (H.obj M)) :=
    isArtinian_localCohomology_maximalIdeal A M i
  let e : H.obj M ⟶ limit (F ⋙ H) := H.map f ≫ limit.post F H
  have : IsIso e := ‹IsIso ((localCohomologyModuleFunctor A i).map f ≫
    limit.post F (localCohomologyModuleFunctor A i))›
  exact essentiallyConstant_of_artinian_limit hML
    (isArtinian_of_surjective (ToType (H.obj M)) (ModuleCat.homEquiv e)
      ((ModuleCat.epi_iff_surjective e).mp inferInstance))

end Stacks.LocalCohomology

end
