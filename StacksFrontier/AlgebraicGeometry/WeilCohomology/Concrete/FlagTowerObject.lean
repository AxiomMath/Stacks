module

public import StacksFrontier.AlgebraicGeometry.FlagTower.ChowPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Grassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective

/-!
# Towers of projective bundles as smooth projective schemes

Let `X` be a smooth projective scheme over a field `k` and `ℰ` a finite locally free module of
constant rank `r` on `X`. The tower `Stacks.FlagTower.tower m ℰ ⟶ X` of `m ≤ r` projective
bundles of successive tautological kernels is a composite of projections of projective bundles
`𝐏(ℰ_j) ⟶ X_j` of modules of rank `r - j ≥ 1`. Each of them is a morphism of smooth projective
schemes over `k` (`Stacks.WeilCohomology.SmoothProjectiveScheme.bundleProj`), so the tower is a
composite of such morphisms, up to the identity of the underlying schemes
(`Stacks.FlagTower.towerHom_succ`).

## Main definitions

* `Stacks.FlagTower.towerObj`, `Stacks.FlagTower.towerHom`: the tower as a morphism of smooth
  projective schemes over `k`.
* `Stacks.FlagTower.grassmannianOver`: the Grassmannian `G(l, n)_X` over a smooth projective `X`,
  with its identification `Stacks.FlagTower.grassmannianOverHom` with `X × G(l, n)_k`.

## Main results

* `Stacks.FlagTower.towerHom_succ`: the tower of length `m + 1` is the tower of length `m` over
  `𝐏(ℰ)` followed by `𝐏(ℰ) ⟶ X`.
* `Stacks.FlagTower.exists_relativeDimension_towerObj`: it is equidimensional if `X` is.

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow Stacks.WeilCohomology

universe u

namespace Stacks.FlagTower

variable {k : Type u} [Field k]

/-- The source of a proper morphism to a quasi-compact quasi-separated scheme is again so. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_isProper {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsProper f] [CompactSpace Z] [QuasiSeparatedSpace Z] :
    CompactSpace Y ∧ QuasiSeparatedSpace Y :=
  ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_isProper f⟩

/-- **The projection of the tower of projective bundles is projective**: a composite of
projections of projective bundles of finite locally free modules. -/
theorem isProjective_tower (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [CompactSpace X]
    [QuasiSeparatedSpace X] : IsProjective (tower m E).2 := by
  induction m generalizing X with
  | zero => exact isProjective_id X
  | succ m ih =>
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isProper (bundleProj E)
    exact IsProjective.comp (@ih _ (kernel (bundleTautological E))
      (isFiniteLocallyFree_kernel_bundleTautological E) _ _) (isProjective_bundleProj E)

/-- **The projection of the tower of `m ≤ r` projective bundles of a module of constant rank `r`
is smooth**: each layer is the projective bundle of a module of rank `r - j ≥ 1`. -/
theorem smooth_tower (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r) :
    Smooth (tower m E).2 := by
  induction m generalizing X r with
  | zero => exact inferInstanceAs (Smooth (𝟙 X))
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r' : ℕ, r = r' + 1 := ⟨r - 1, by omega⟩
    have := hE
    have := smooth_bundleProj E r
    have := @ih _ (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E)
      r (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)
    exact inferInstanceAs (Smooth ((kernelTower m E).2 ≫ bundleProj E))

/-- **The projection of the tower of `m ≤ r` projective bundles of a module of constant rank
`r` has a relative dimension**, the sum of those of its layers. -/
theorem exists_relativeDimension_tower_snd (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r) :
    ∃ N : ℕ, RelativeDimension (tower m E).2 N := by
  induction m generalizing X r with
  | zero => exact ⟨0, relativeDimension_of_isIso (𝟙 X)⟩
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r' : ℕ, r = r' + 1 := ⟨r - 1, by omega⟩
    have := hE
    have := locallyOfFiniteType_bundleProj E r
    obtain ⟨N, hN⟩ := @ih _ (kernel (bundleTautological E))
      (isFiniteLocallyFree_kernel_bundleTautological E) r
      (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)
    have hL : LocallyOfFiniteType (@tower m _ (kernel (bundleTautological E))
        (isFiniteLocallyFree_kernel_bundleTautological E)).2 :=
      (@isProper_tower m _ (kernel (bundleTautological E))
        (isFiniteLocallyFree_kernel_bundleTautological E)).toLocallyOfFiniteType
    have hS := @smooth_tower m _ (kernel (bundleTautological E))
      (isFiniteLocallyFree_kernel_bundleTautological E) r
      (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)
    exact ⟨N + r, @RelativeDimension.comp_of_flat _ _ _ _ (bundleProj E) hL _ inferInstance _ _ hN
      (relativeDimension_bundleProj E r)⟩

/-- **The tower over an equidimensional base is equidimensional**: if `s : X ⟶ S` has relative
dimension `d`, then `Y ⟶ X ⟶ S` has some relative dimension, `Y` the top of the tower of `m ≤ r`
projective bundles of a module of constant rank `r`. -/
theorem exists_relativeDimension_tower (m : ℕ) {X S : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r)
    (s : X ⟶ S) [LocallyOfFiniteType s] {d : ℕ} (hs : RelativeDimension s d) :
    ∃ e : ℕ, RelativeDimension ((tower m E).2 ≫ s) e := by
  have := smooth_tower m E r hE hm
  obtain ⟨N, hN⟩ := exists_relativeDimension_tower_snd m E r hE hm
  exact ⟨N + d, RelativeDimension.comp_of_flat _ s hN hs⟩

/-- A smooth projective scheme over `k` is quasi-compact and quasi-separated. -/
theorem compactSpace_and_quasiSeparatedSpace_of_isProjective
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s) :
    CompactSpace Y ∧ QuasiSeparatedSpace Y := by
  have := hp.isProper
  exact compactSpace_and_quasiSeparatedSpace_of_isProper s

/-- **The tower of `m` projective bundles of successive tautological kernels**, for a module `ℰ`
finite locally free of constant rank `r ≥ m` on a smooth projective scheme `s : Y ⟶ Spec k`, as
a smooth projective scheme over `k`: the top of `Stacks.FlagTower.tower m ℰ` with
`Y' ⟶ Y ⟶ Spec k`. -/
def towerObj
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r) :
    (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := (compactSpace_and_quasiSeparatedSpace_of_isProjective s hp).1
  haveI := (compactSpace_and_quasiSeparatedSpace_of_isProjective s hp).2
  SmoothProjectiveScheme.mk ((tower m E).2 ≫ s)
    (haveI := smooth_tower m E r hE hm; inferInstance)
    (IsProjective.comp (isProjective_tower m E) hp)

/-- The projection of the tower, as a morphism of smooth projective schemes over `k`. -/
def towerHom
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r) :
    towerObj s hp m E r hE hm ⟶ SmoothProjectiveScheme.mk s inferInstance hp :=
  SmoothProjectiveScheme.homMk (tower m E).2 rfl

/-- `towerObj` is equidimensional over an equidimensional base. -/
theorem exists_relativeDimension_towerObj
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r)
    {d : ℕ} (hs : RelativeDimension s d) :
    ∃ e : ℕ, RelativeDimension (towerObj s hp m E r hE hm).obj.hom e :=
  exists_relativeDimension_tower m E r hE hm s hs

/-- The structure morphism of the first layer `𝐏(ℰ) ⟶ Y ⟶ Spec k` is projective. -/
theorem isProjective_bundleProj_comp_spec
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    IsProjective (bundleProj E ≫ s) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have := (compactSpace_and_quasiSeparatedSpace_of_isProjective s hp).1
  have := (compactSpace_and_quasiSeparatedSpace_of_isProjective s hp).2
  IsProjective.comp (isProjective_bundleProj E) hp

/-- The structure morphism of the first layer `𝐏(ℰ) ⟶ Y ⟶ Spec k` is smooth. -/
theorem smooth_bundleProj_comp_spec
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (_hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    Smooth (bundleProj E ≫ s) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have := smooth_bundleProj E r
  inferInstance

/-- The first layer `𝐏(ℰ)` with its structure morphism `𝐏(ℰ) ⟶ Y ⟶ Spec k`. -/
abbrev bundleBase {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    (SmoothProjectiveScheme k).FullSubcategory :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  haveI := smooth_bundleProj_comp_spec s hp E r
  SmoothProjectiveScheme.mk (bundleProj E ≫ s) inferInstance
    (isProjective_bundleProj_comp_spec s hp E r)

/-- `bundleBase` is the projective bundle `𝐏(ℰ)` of `Y`, by the identity of the scheme. -/
def bundleBaseHom {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    bundleBase s hp E r ⟶
      SmoothProjectiveScheme.bundle (SmoothProjectiveScheme.mk s inferInstance hp) E r :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.homMk (𝟙 (bundle E)) (Category.id_comp (bundleProj E ≫ s))

/-- The inverse of `bundleBaseHom`. -/
def bundleBaseInv {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    SmoothProjectiveScheme.bundle (SmoothProjectiveScheme.mk s inferInstance hp) E r ⟶
      bundleBase s hp E r :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.homMk (𝟙 (bundle E)) (Category.id_comp (bundleProj E ≫ s))

/-- `bundleBaseInv` is a left inverse of `bundleBaseHom`. -/
theorem bundleBaseHom_inv {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    bundleBaseHom s hp E r ≫ bundleBaseInv s hp E r = 𝟙 _ :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.hom_ext' (Category.id_comp (𝟙 (bundle E)))

/-- `bundleBaseInv` is a right inverse of `bundleBaseHom`. -/
theorem bundleBaseInv_hom {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    bundleBaseInv s hp E r ≫ bundleBaseHom s hp E r = 𝟙 _ :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.hom_ext' (Category.id_comp (𝟙 (bundle E)))

/-- The tower of length `m` over the first layer `𝐏(ℰ)`, on the tautological kernel. -/
abbrev kernelTowerObj {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) : (SmoothProjectiveScheme k).FullSubcategory :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  haveI := smooth_bundleProj_comp_spec s hp E r
  @towerObj _ _ _ (bundleProj E ≫ s) _ (isProjective_bundleProj_comp_spec s hp E r) m
    (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E) r
    (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)

/-- Its projection to `𝐏(ℰ)`. -/
abbrev kernelTowerHom {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) : kernelTowerObj s hp m E r hm ⟶ bundleBase s hp E r :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  haveI := smooth_bundleProj_comp_spec s hp E r
  @towerHom _ _ _ (bundleProj E ≫ s) _ (isProjective_bundleProj_comp_spec s hp E r) m
    (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E) r
    (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)

/-- The tower of length `m + 1` over `Y` is the tower of length `m` over `𝐏(ℰ)`: the identity of
the underlying scheme, read with the two structure morphisms to `Spec k`. -/
def towerSuccHom {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    towerObj s hp (m + 1) E (r + 1) hE hm ⟶ kernelTowerObj s hp m E r hm :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have h : 𝟙 (tower (m + 1) E).1 ≫ (kernelTower m E).2 ≫ bundleProj E ≫ s =
      (tower (m + 1) E).2 ≫ s :=
    (Category.id_comp _).trans (Category.assoc (kernelTower m E).2 (bundleProj E) s).symm
  SmoothProjectiveScheme.homMk (𝟙 (tower (m + 1) E).1) h

/-- The inverse of `towerSuccHom`. -/
def towerSuccInv {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    kernelTowerObj s hp m E r hm ⟶ towerObj s hp (m + 1) E (r + 1) hE hm :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have h : 𝟙 (tower (m + 1) E).1 ≫ (tower (m + 1) E).2 ≫ s =
      (kernelTower m E).2 ≫ bundleProj E ≫ s :=
    (Category.id_comp _).trans (Category.assoc (kernelTower m E).2 (bundleProj E) s)
  SmoothProjectiveScheme.homMk (𝟙 (tower (m + 1) E).1) h

/-- `towerSuccInv` is a left inverse of `towerSuccHom`. -/
theorem towerSuccHom_inv {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) : towerSuccHom s hp m E r hm ≫ towerSuccInv s hp m E r hm = 𝟙 _ :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.hom_ext' (Category.id_comp (𝟙 (tower (m + 1) E).1))

/-- `towerSuccInv` is a right inverse of `towerSuccHom`. -/
theorem towerSuccInv_hom {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) : towerSuccInv s hp m E r hm ≫ towerSuccHom s hp m E r hm = 𝟙 _ :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  SmoothProjectiveScheme.hom_ext' (Category.id_comp (𝟙 (tower (m + 1) E).1))

/-- **The projection of the tower of length `m + 1` is the projection of the tower of length
`m` over `𝐏(ℰ)` followed by `𝐏(ℰ) ⟶ Y`.** -/
theorem towerHom_succ {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (hp : IsProjective s)
    (m : ℕ) (E : Y.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hm : m + 1 ≤ r + 1) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    towerHom s hp (m + 1) E (r + 1) hE hm = towerSuccHom s hp m E r hm ≫
      kernelTowerHom s hp m E r hm ≫ bundleBaseHom s hp E r ≫
        SmoothProjectiveScheme.bundleProj (SmoothProjectiveScheme.mk s inferInstance hp) E r := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  refine SmoothProjectiveScheme.hom_ext' ?_
  have h : 𝟙 (tower (m + 1) E).1 ≫ (kernelTower m E).2 ≫ 𝟙 (bundle E) ≫ bundleProj E =
      (tower (m + 1) E).2 := by
    rw [Category.id_comp, Category.id_comp]
    rfl
  exact h.symm

/-! ### The Grassmannian over `X` -/

section Grassmannian

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ)

/-- **The Grassmannian `G(l, n)_X` of a smooth projective scheme `X` over `k`**, as a smooth
projective scheme over `k`: `G(l, n)_X ⟶ X` is smooth and projective (Stacks 089U, 089V). -/
def grassmannianOver : (SmoothProjectiveScheme k).FullSubcategory :=
  SmoothProjectiveScheme.mk
    ((Grassmannian.schemeOver.over l n ((SmoothProjectiveScheme.toScheme k).obj X)).hom ≫
      X.obj.hom) inferInstance
    (IsProjective.comp (Grassmannian.isProjective_schemeOver l n _)
      (SmoothProjectiveScheme.isProjective X))

/-- The projection `G(l, n)_X ⟶ X`. -/
def grassmannianOverProj : grassmannianOver X l n ⟶ X :=
  SmoothProjectiveScheme.homMk
    (Grassmannian.schemeOver.over l n ((SmoothProjectiveScheme.toScheme k).obj X)).hom rfl

/-- The inverse of `productGrassmannianIso` followed by the first projection to `X` is the
projection `G(l, n)_X ⟶ X`. -/
theorem productGrassmannianIso_inv_fst :
    (productGrassmannianIso k X l n).inv ≫
        pullback.fst X.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom =
      (Grassmannian.schemeOver.over l n ((SmoothProjectiveScheme.toScheme k).obj X)).hom := by
  rw [Iso.inv_comp_eq]
  exact (productGrassmannianIso_hom_fst k X l n).symm

/-- The identification `G(l, n)_X ≅ X × G(l, n)_k` of smooth projective schemes over `k`
(`Stacks.FlagTower.productGrassmannianIso`). -/
def grassmannianOverHom : grassmannianOver X l n ⟶
    SmoothProjectiveScheme.prod X (SmoothProjectiveScheme.grassmannian k l n) :=
  SmoothProjectiveScheme.homMk (productGrassmannianIso k X l n).inv
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.obj.hom) (productGrassmannianIso_inv_fst X l n)))

/-- The inverse of `grassmannianOverHom`. -/
def grassmannianOverInv :
    SmoothProjectiveScheme.prod X (SmoothProjectiveScheme.grassmannian k l n) ⟶
      grassmannianOver X l n :=
  SmoothProjectiveScheme.homMk (productGrassmannianIso k X l n).hom
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.obj.hom) (productGrassmannianIso_hom_fst k X l n)))

/-- `grassmannianOverInv` is a left inverse of `grassmannianOverHom`. -/
theorem grassmannianOverHom_inv : grassmannianOverHom X l n ≫ grassmannianOverInv X l n = 𝟙 _ :=
  SmoothProjectiveScheme.hom_ext' (Iso.inv_hom_id _)

/-- `grassmannianOverInv` is a right inverse of `grassmannianOverHom`. -/
theorem grassmannianOverInv_hom : grassmannianOverInv X l n ≫ grassmannianOverHom X l n = 𝟙 _ :=
  SmoothProjectiveScheme.hom_ext' (Iso.hom_inv_id _)

/-- The identification `G(l, n)_X ≅ X × G(l, n)_k` is over `X`. -/
theorem grassmannianOverHom_fst :
    grassmannianOverHom X l n ≫
        SmoothProjectiveScheme.fst X (SmoothProjectiveScheme.grassmannian k l n) =
      grassmannianOverProj X l n :=
  SmoothProjectiveScheme.hom_ext' (productGrassmannianIso_inv_fst X l n)

end Grassmannian

end Stacks.FlagTower

end
