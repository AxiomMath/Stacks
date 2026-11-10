module

public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

/-!
# The adic replacement of an extension of an adic system by an essentially constant one

Let `R` be a commutative ring, `I ⊆ R` an ideal, and let

`0 → Qₙ → Pₙ → Cₙ → 0`

be a short exact sequence of inverse systems of `R`-modules, indexed by `n ∈ ℕ`, in which the
term `Pₙ` is annihilated by `I^{n+1}`. Assume that `(Qₙ)` is a quotient of an `R`-module `M`:
the maps `M → Qₙ` are surjective, every compatible family in `(Qₙ)` comes from `M`, and their
kernels contain a fixed submodule `H` annihilated by a power of `I`, intersect to `H`, and
eventually lie in `H + I^{n+1} M` for every `n`. Assume finally that `(Cₙ)` is essentially
constant.

Writing `M''` for the module of compatible families in `(Pₙ)`, this file proves that
`{M''/I^{n+1}M''}` is pro-isomorphic to `(Pₙ)`, compatibly with the maps from `M`, and that the
induced maps `M/I^{n+1}M → M''/I^{n+1}M''` have kernels and cokernels annihilated by a fixed power
of `I`.

## Main definitions

* `InverseSequence.ProIso.ofProZero` — the pro-isomorphism attached to a map of inverse systems
  of modules whose kernels and cokernels are pro-zero.
* `Stacks.AdicSystem.compatibleFamilies` — the module of compatible families of an inverse
  system of modules, which is its inverse limit.
* `Stacks.AdicSystem.adicQuotientTower` — the inverse system `n ↦ M/I^{n+1}M`.
* `Stacks.AdicSystem.ExtensionData` — the data and hypotheses described above.
* `Stacks.AdicSystem.ExtensionData.replacementProIso` — the pro-isomorphism between `(Pₙ)` and
  `{M''/I^{n+1}M''}`.

## Main results

* `Stacks.AdicSystem.ExtensionData.replacementProIso_φ_μ` — the pro-isomorphism carries the
  maps `M → Pₙ` to the maps `M → M''/I^{n+1}M''`.
* `Stacks.AdicSystem.ExtensionData.smul_eq_zero_of_quotientMap_eq_zero` and
  `Stacks.AdicSystem.ExtensionData.smul_mem_range_quotientMap` — the kernels and cokernels of
  `M/I^{n+1}M → M''/I^{n+1}M''` are annihilated by a fixed power of `I`.
* `Stacks.AdicSystem.ExtensionData.finite_adicQuotient` — each `M''/I^{n+1}M''` is a finite
  `R`-module when `R` is Noetherian and the `Pₙ` are finite.
* `Stacks.AdicSystem.ExtensionData.map_comp_replacementProIso_φ` — the pro-isomorphism is
  compatible with a map of inverse systems `(Fₙ) ⟶ (Pₙ)` through which the maps `M → Pₙ` factor.
* `Stacks.AdicSystem.ExtensionData.smul_eq_zero_of_levelsMap_eq_zero` and
  `Stacks.AdicSystem.ExtensionData.smul_mem_range_levelsMap` — the same annihilation statements
  for the comparison `Fₙ → M''/I^{n+1}M''` out of a system `Fₙ = M/I^{n+1}M` of levels of `M`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Pro-isomorphisms from pro-zero kernels and cokernels -/

namespace InverseSequence.ProIso

variable {R : Type u} [CommRing R] {X Y : ℕᵒᵖ ⥤ ModuleCat.{u} R} (f : X ⟶ Y)

/-- The kernels of a map of inverse systems of modules are *pro-zero* when every element of the
kernel at a sufficiently high level dies at a given level. -/
public def KernelsProZero : Prop :=
  ∀ n : ℕ, ∃ m, ∃ h : n ≤ m, ∀ x, f.app (op m) x = 0 → tr X h x = 0

/-- The cokernels of a map of inverse systems of modules are *pro-zero* when the image of a
sufficiently high level lies in the image of the map at a given level. -/
public def CokernelsProZero : Prop :=
  ∀ n : ℕ, ∃ m, ∃ h : n ≤ m, ∀ y, ∃ x, f.app (op n) x = tr Y h y

variable {f}

/-- A map of inverse systems commutes with the transition maps. -/
theorem app_tr (f : X ⟶ Y) {n m : ℕ} (h : n ≤ m) (x : X.obj (op m)) :
    f.app (op n) (tr X h x) = tr Y h (f.app (op m) x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, tr, tr, f.naturality]

/-- The composite of two transition maps is the transition map. -/
theorem tr_tr (Z : ℕᵒᵖ ⥤ ModuleCat.{u} R) {k n m : ℕ} (h : k ≤ n)
    (h' : n ≤ m) (x : Z.obj (op m)) : tr Z h (tr Z h' x) = tr Z (h.trans h') x := by
  rw [← ConcreteCategory.comp_apply, ProIso.tr_trans]

/-- If the kernel of `f` at level `m` dies at level `n`, so does the kernel at any level
`m' ≥ m`. -/
theorem kernelsProZero_mono {n m m' : ℕ} (h : n ≤ m) (hm' : m ≤ m')
    (hm : ∀ x, f.app (op m) x = 0 → tr X h x = 0) :
    ∀ x, f.app (op m') x = 0 → tr X (h.trans hm') x = 0 := fun x hx => by
  rw [← tr_tr X h hm']
  exact hm _ (by rw [app_tr, hx, map_zero])

/-- If the image of level `m` of `Y` at level `n` lies in the image of `f`, so does the image of
any level `m' ≥ m`. -/
theorem cokernelsProZero_mono {n m m' : ℕ} (h : n ≤ m) (hm' : m ≤ m')
    (hm : ∀ y, ∃ x, f.app (op n) x = tr Y h y) :
    ∀ y, ∃ x, f.app (op n) x = tr Y (h.trans hm') y := fun y =>
  (hm (tr Y hm' y)).imp fun _ hx => hx.trans (tr_tr Y h hm' y)

/-- The function `n ↦ max (b 0, …, b n, n)`, a monotone function dominating both `b` and the
identity. -/
def monotoneBound (b : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup b ⊔ n

/-- `monotoneBound b` dominates `b`. -/
theorem le_monotoneBound (b : ℕ → ℕ) (n : ℕ) : b n ≤ monotoneBound b n :=
  le_sup_of_le_left (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n)))

/-- `monotoneBound b` dominates the identity. -/
theorem self_le_monotoneBound (b : ℕ → ℕ) (n : ℕ) : n ≤ monotoneBound b n := le_sup_right

/-- `monotoneBound b` is monotone. -/
theorem monotone_monotoneBound (b : ℕ → ℕ) : Monotone (monotoneBound b) := fun _ _ h =>
  sup_le_sup (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ h))) h

variable (hk : KernelsProZero f) (hc : CokernelsProZero f)

/-- A monotone choice of level, for each `n`, whose kernel under `f` dies at level `n`. -/
def kerBound (n : ℕ) : ℕ := monotoneBound (fun n => (hk n).choose) n

/-- `kerBound hk n` is at least `n`. -/
theorem le_kerBound (n : ℕ) : n ≤ kerBound hk n := self_le_monotoneBound _ n

/-- The kernel of `f` at level `kerBound hk n` dies at level `n`. -/
theorem kerBound_spec (n : ℕ) :
    ∀ x, f.app (op (kerBound hk n)) x = 0 → tr X (le_kerBound hk n) x = 0 :=
  kernelsProZero_mono (hk n).choose_spec.choose (le_monotoneBound (fun n => (hk n).choose) n)
    (hk n).choose_spec.choose_spec

/-- A monotone choice of level, for each `n`, whose image at level `n` lies in the image of
`f`. -/
def cokBound (n : ℕ) : ℕ := monotoneBound (fun n => (hc n).choose) n

/-- `cokBound hc n` is at least `n`. -/
theorem le_cokBound (n : ℕ) : n ≤ cokBound hc n := self_le_monotoneBound _ n

/-- The image of level `cokBound hc n` of `Y` at level `n` lies in the image of `f`. -/
theorem cokBound_spec (n : ℕ) :
    ∀ y, ∃ x, f.app (op n) x = tr Y (le_cokBound hc n) y :=
  cokernelsProZero_mono (hc n).choose_spec.choose (le_monotoneBound (fun n => (hc n).choose) n)
    (hc n).choose_spec.choose_spec

/-- The level `cokBound hc (kerBound hk n)`, the source level of the inverse map to level `n`. -/
abbrev invLevel (n : ℕ) : ℕ := cokBound hc (kerBound hk n)

/-- `invLevel hk hc n` is at least `n`. -/
theorem le_invLevel (n : ℕ) : n ≤ invLevel hk hc n :=
  (le_kerBound hk n).trans (le_cokBound hc _)

/-- `invLevel hk hc` is monotone. -/
theorem monotone_invLevel : Monotone (invLevel hk hc) :=
  (monotone_monotoneBound _).comp (monotone_monotoneBound _)

/-- The image of an element of `Y` at level `invLevel hk hc n` in level `kerBound hk n` lies in
the range of `f`. -/
theorem invMap_range (n : ℕ) (y : Y.obj (op (invLevel hk hc n))) :
    (tr Y (le_cokBound hc (kerBound hk n))).hom y ∈
      LinearMap.range (f.app (op (kerBound hk n))).hom := by
  obtain ⟨x, hx⟩ := cokBound_spec hc (kerBound hk n) y
  exact ⟨x, hx⟩

/-- The kernel of `f` at level `kerBound hk n` lies in the kernel of the transition map to level
`n`. -/
theorem invMap_ker (n : ℕ) :
    LinearMap.ker (f.app (op (kerBound hk n))).hom ≤
      LinearMap.ker (tr X (le_kerBound hk n)).hom :=
  fun x hx => kerBound_spec hk n x hx

/-- The linear map `Y_{β n} → X_n` inverting `f` up to refinement: lift the image of `y` at the
kernel level through `f`, then drop to level `n`. -/
def invMapLinear (n : ℕ) : Y.obj (op (invLevel hk hc n)) →ₗ[R] X.obj (op n) :=
  ((LinearMap.ker (f.app (op (kerBound hk n))).hom).liftQ (tr X (le_kerBound hk n)).hom
      (invMap_ker hk n)).comp
    ((LinearMap.quotKerEquivRange (f.app (op (kerBound hk n))).hom).symm.toLinearMap.comp
      ((tr Y (le_cokBound hc (kerBound hk n))).hom.codRestrict _ (invMap_range hk hc n)))

/-- The map `Y_{β n} → X_n` inverting `f` up to refinement. -/
def invMap (n : ℕ) : Y.obj (op (invLevel hk hc n)) ⟶ X.obj (op n) :=
  ModuleCat.ofHom (invMapLinear hk hc n)

/-- `invMap hk hc n y` is the image at level `n` of any `x` with `f x` equal to the image of `y`
at level `kerBound hk n`. -/
theorem invMap_eq (n : ℕ) (y : Y.obj (op (invLevel hk hc n))) (x : X.obj (op (kerBound hk n)))
    (hx : f.app (op (kerBound hk n)) x = tr Y (le_cokBound hc _) y) :
    invMap hk hc n y = tr X (le_kerBound hk n) x := by
  set e := LinearMap.quotKerEquivRange (f.app (op (kerBound hk n))).hom
  have he : e.symm ((tr Y (le_cokBound hc (kerBound hk n))).hom.codRestrict _
      (invMap_range hk hc n) y) = Submodule.Quotient.mk x := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    ext
    simp only [e, LinearMap.quotKerEquivRange_apply_mk, LinearMap.codRestrict_apply]
    exact hx.symm
  have key : invMapLinear hk hc n y =
      (LinearMap.ker (f.app (op (kerBound hk n))).hom).liftQ (tr X (le_kerBound hk n)).hom
        (invMap_ker hk n) (e.symm ((tr Y (le_cokBound hc (kerBound hk n))).hom.codRestrict _
          (invMap_range hk hc n) y)) := rfl
  change invMapLinear hk hc n y = _
  rw [key, he]
  rfl

/-- **A map of inverse systems of modules with pro-zero kernels and cokernels is a
pro-isomorphism.** The pro-isomorphism goes from the target to the source; its backward maps are
the components of `f`. -/
public def ofProZero : ProIso Y X where
  α := invLevel hk hc
  β := id
  αmono := monotone_invLevel hk hc
  βmono := monotone_id
  αle := le_invLevel hk hc
  βle := fun _ => le_rfl
  φ := invMap hk hc
  ψ := fun n => f.app (op n)
  φnat := by
    intro m m' h
    ext y
    obtain ⟨x', hx'⟩ := cokBound_spec hc (kerBound hk m') y
    obtain ⟨x, hx⟩ := cokBound_spec hc (kerBound hk m) (tr Y (monotone_invLevel hk hc h) y)
    change invMap hk hc m (tr Y _ y) = tr X h (invMap hk hc m' y)
    rw [invMap_eq hk hc m _ x hx, invMap_eq hk hc m' y x' hx']
    have hkm : kerBound hk m ≤ kerBound hk m' := monotone_monotoneBound _ h
    have hzero : f.app (op (kerBound hk m)) (x - tr X hkm x') = 0 := by
      rw [map_sub, hx, app_tr, hx', tr_tr, tr_tr, sub_self]
    have := kerBound_spec hk m _ hzero
    rw [map_sub, sub_eq_zero] at this
    rw [this, tr_tr, tr_tr]
  ψnat h := f.naturality (homOfLE h).op
  ψφ := by
    intro m
    ext y
    obtain ⟨x, hx⟩ := cokBound_spec hc (kerBound hk m) y
    change f.app (op m) (invMap hk hc m y) = tr Y _ y
    rw [invMap_eq hk hc m y x hx, app_tr, hx, tr_tr]
  φψ := by
    intro m
    ext x
    obtain ⟨x', hx'⟩ := cokBound_spec hc (kerBound hk m) (f.app (op (invLevel hk hc m)) x)
    change invMap hk hc m (f.app (op (invLevel hk hc m)) x) = tr X _ x
    rw [invMap_eq hk hc m _ x' hx']
    have hzero : f.app (op (kerBound hk m)) (x' - tr X (le_cokBound hc _) x) = 0 := by
      rw [map_sub, hx', app_tr, sub_self]
    have := kerBound_spec hk m _ hzero
    rw [map_sub, sub_eq_zero] at this
    rw [this, tr_tr]

/-- The forward map of `ofProZero hk hc` at level `n` sends `y` to the image at level `n` of any
`x` with `f x` equal to the image of `y` at level `kerBound hk n`. -/
theorem ofProZero_φ_eq (n : ℕ) (y : Y.obj (op ((ofProZero hk hc).α n)))
    (x : X.obj (op (kerBound hk n)))
    (hx : f.app (op (kerBound hk n)) x = tr Y (le_cokBound hc _) y) :
    (ofProZero hk hc).φ n y = tr X (le_kerBound hk n) x :=
  invMap_eq hk hc n y x hx

end InverseSequence.ProIso

/-! ### Compatible families and the adic quotient tower -/

namespace Stacks.AdicSystem

open InverseSequence InverseSequence.ProIso

variable {R : Type u} [CommRing R]

/-- The module of compatible families of an inverse system of modules: its inverse limit. -/
public def compatibleFamilies (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    Submodule R (∀ n : ℕ, P.obj (op n)) where
  carrier := {x | ∀ (n m : ℕ) (h : n ≤ m), tr P h (x m) = x n}
  add_mem' {x y} hx hy n m h := by
    simp only [Pi.add_apply, map_add, hx n m h, hy n m h]
  zero_mem' n m h := by simp
  smul_mem' a x hx n m h := by
    simp only [Pi.smul_apply, map_smul, hx n m h]

/-- The projection of the inverse limit onto the `n`-th term. -/
public def compatibleFamiliesπ (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) :
    compatibleFamilies P →ₗ[R] P.obj (op n) :=
  (LinearMap.proj n).comp (compatibleFamilies P).subtype

/-- The projection `compatibleFamiliesπ P n` takes the `n`-th component. -/
@[simp]
public theorem compatibleFamiliesπ_apply (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (x : compatibleFamilies P) : compatibleFamiliesπ P n x = x.1 n :=
  rfl

/-- The transition maps send the components of a compatible family to one another. -/
theorem tr_compatibleFamilies (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) (x : compatibleFamilies P) {n m : ℕ}
    (h : n ≤ m) : tr P h (x.1 m) = x.1 n :=
  x.2 n m h

/-- A family of elements with compatible successive transitions is compatible. -/
theorem mem_compatibleFamilies_of_succ (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) (x : ∀ n : ℕ, P.obj (op n))
    (hx : ∀ n, tr P (Nat.le_succ n) (x (n + 1)) = x n) : x ∈ compatibleFamilies P := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base => rw [ProIso.tr_refl]; rfl
  | succ m hnm ih =>
    rw [← ih, ← hx m, tr_tr P hnm (Nat.le_succ m)]

variable (I : Ideal R)

/-- For `n ≤ m`, `I^{m+1}N ⊆ I^{n+1}N`. -/
theorem pow_succ_smul_top_le (N : Type u) [AddCommGroup N] [Module R N] {n m : ℕ} (h : n ≤ m) :
    I ^ (m + 1) • (⊤ : Submodule R N) ≤
      (I ^ (n + 1) • (⊤ : Submodule R N)).comap LinearMap.id := by
  rw [Submodule.comap_id]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-- The transition map `N/I^{m+1}N → N/I^{n+1}N` for `n ≤ m`. -/
def adicQuotientMap (N : Type u) [AddCommGroup N] [Module R N] {n m : ℕ} (h : n ≤ m) :
    (N ⧸ (I ^ (m + 1) • (⊤ : Submodule R N))) →ₗ[R] N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N)) :=
  Submodule.mapQ _ _ LinearMap.id (pow_succ_smul_top_le I N h)

/-- The inverse system `n ↦ N/I^{n+1}N` of an `R`-module `N`. -/
public def adicQuotientTower (N : Type u) [AddCommGroup N] [Module R N] :
    ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (N ⧸ (I ^ (n.unop + 1) • (⊤ : Submodule R N)))
  map {m n} g := ModuleCat.ofHom (adicQuotientMap I N (leOfHom g.unop))
  map_id _ := ModuleCat.hom_ext (Submodule.mapQ_id _)
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    simp [adicQuotientMap]

/-- The transition map `N/I^{m+1}N → N/I^{n+1}N` sends the class of `x` to the class of `x`. -/
theorem adicQuotientMap_mk (N : Type u) [AddCommGroup N] [Module R N] {n m : ℕ} (h : n ≤ m)
    (x : N) : adicQuotientMap I N h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  rfl

/-- The transition maps of `adicQuotientTower I N` are the maps `adicQuotientMap I N`. -/
theorem tr_adicQuotientTower (N : Type u) [AddCommGroup N] [Module R N] {n m : ℕ} (h : n ≤ m)
    (q : (adicQuotientTower I N).obj (op m)) :
    tr (adicQuotientTower I N) h q = adicQuotientMap I N h q :=
  rfl

/-! ### The extension data -/

/-- An inverse system `(Pₙ)` with `Pₙ` annihilated by `I^{n+1}`, and compatible maps
`μₙ : M → Pₙ` out of an `R`-module `M` such that

* the kernels of the `μₙ` contain a submodule `H` annihilated by a power of `I`, their
  intersection is `H`, and for every `n` some kernel lies in `H + I^{n+1} M`,
* every compatible family with components in the images of the `μₙ` comes from `M`.

The images of the `μₙ` form the subsystem `(Qₙ)`, and the quotients `Pₙ/Qₙ` form the system
`ExtensionData.quotientSystem`. -/
public structure ExtensionData (P : ℕᵒᵖ ⥤ ModuleCat.{u} R) (M : Type u) [AddCommGroup M]
    [Module R M] where
  /-- The maps `M → Pₙ`. -/
  μ : ∀ n : ℕ, M →ₗ[R] P.obj (op n)
  /-- The maps `μₙ` are compatible with the transition maps. -/
  μ_tr : ∀ {n m : ℕ} (h : n ≤ m) (x : M), tr P h (μ m x) = μ n x
  /-- `Pₙ` is annihilated by `I^{n+1}`. -/
  ann : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (P.obj (op n))) = ⊥
  /-- The common part of the kernels. -/
  H : Submodule R M
  /-- The exponent of a power of `I` annihilating `H`. -/
  e : ℕ
  /-- `H` is annihilated by `I^e`. -/
  ann_H : I ^ e • H = ⊥
  /-- `H` lies in the kernel of every `μₙ`. -/
  le_ker : ∀ n : ℕ, H ≤ LinearMap.ker (μ n)
  /-- The level at which the kernels have shrunk into `H + I^{n+1} M`. -/
  kerLevel : ℕ → ℕ
  /-- The kernel of `μ (kerLevel n)` lies in `H + I^{n+1} M`. -/
  ker_le : ∀ n : ℕ, LinearMap.ker (μ (kerLevel n)) ≤ H ⊔ I ^ (n + 1) • (⊤ : Submodule R M)
  /-- The intersection of the kernels of the `μₙ` is contained in `H`. -/
  iInf_ker_le : ∀ x : M, (∀ n, μ n x = 0) → x ∈ H
  /-- A compatible family with components in the images of the `μₙ` comes from `M`. -/
  lift : ∀ x ∈ compatibleFamilies P, (∀ n, x n ∈ LinearMap.range (μ n)) →
    ∃ m : M, ∀ n, μ n m = x n

namespace ExtensionData

variable {I} {P : ℕᵒᵖ ⥤ ModuleCat.{u} R} {M : Type u} [AddCommGroup M] [Module R M]
  (D : ExtensionData I P M)

/-- The transition maps of `P` carry the image of `μₘ` into the image of `μₙ`. -/
theorem tr_range {n m : ℕ} (h : n ≤ m) :
    LinearMap.range (μ D m) ≤ (LinearMap.range (μ D n)).comap (tr P h).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, (D.μ_tr h x).symm⟩

/-- The quotient system `Pₙ/Qₙ`, `Qₙ` the image of `μₙ`. -/
public def quotientSystem : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (P.obj n ⧸ LinearMap.range (D.μ n.unop))
  map {m n} g := ModuleCat.ofHom <|
    Submodule.mapQ _ _ (P.map g).hom (D.tr_range (leOfHom g.unop))
  map_id n := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    simp only [Functor.map_comp, ModuleCat.hom_comp]
    rfl

/-- The transition maps of the quotient system are induced by those of `P`. -/
theorem tr_quotientSystem_mk {n m : ℕ} (h : n ≤ m) (y : P.obj (op m)) :
    tr D.quotientSystem h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (tr P h y) :=
  rfl

/-- The quotient maps `Pₙ → Pₙ/Qₙ`. -/
public def toQuotient (n : ℕ) : P.obj (op n) →ₗ[R] D.quotientSystem.obj (op n) :=
  Submodule.mkQ _

/-- The kernel of `Pₙ → Pₙ/Qₙ` is the image of `μₙ`. -/
theorem toQuotient_eq_zero_iff (n : ℕ) (y : P.obj (op n)) :
    D.toQuotient n y = 0 ↔ y ∈ LinearMap.range (D.μ n) :=
  Submodule.Quotient.mk_eq_zero _

/-- The quotient maps `Pₙ → Pₙ/Qₙ` are surjective. -/
theorem toQuotient_surjective (n : ℕ) : Function.Surjective (D.toQuotient n) :=
  Submodule.mkQ_surjective _

/-- The quotient maps `Pₙ → Pₙ/Qₙ` commute with the transition maps. -/
theorem tr_toQuotient {n m : ℕ} (h : n ≤ m) (y : P.obj (op m)) :
    tr D.quotientSystem h (D.toQuotient m y) = D.toQuotient n (tr P h y) :=
  rfl

/-- The map `M → lim P`. -/
public def ι : M →ₗ[R] compatibleFamilies P where
  toFun m := ⟨fun n => D.μ n m, fun n k h => D.μ_tr h m⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The `n`-th component of `ι m` is `μₙ m`. -/
@[simp]
theorem ι_apply_coe (m : M) (n : ℕ) : (D.ι m).1 n = D.μ n m :=
  rfl

/-- A compatible family whose images in the quotient system all vanish comes from `M`. -/
theorem mem_range_ι_of_toQuotient_eq_zero (x : compatibleFamilies P)
    (hx : ∀ n, D.toQuotient n (x.1 n) = 0) : x ∈ LinearMap.range D.ι := by
  obtain ⟨m, hm⟩ := D.lift x.1 x.2 fun n => (D.toQuotient_eq_zero_iff n _).1 (hx n)
  exact ⟨m, Subtype.ext (funext hm)⟩

include D in
/-- The `n`-th term of `P` is annihilated by `I^{n+1}`. -/
theorem smul_eq_zero {n : ℕ} {a : R} (ha : a ∈ I ^ (n + 1)) (y : P.obj (op n)) : a • y = 0 := by
  have : a • y ∈ I ^ (n + 1) • (⊤ : Submodule R (P.obj (op n))) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [D.ann n] at this

/-- The `n`-th term of the quotient system is annihilated by `I^{n+1}`. -/
theorem smul_quotient_eq_zero {n : ℕ} {a : R} (ha : a ∈ I ^ (n + 1))
    (z : D.quotientSystem.obj (op n)) : a • z = 0 := by
  obtain ⟨y, rfl⟩ := D.toQuotient_surjective n z
  rw [← map_smul, D.smul_eq_zero ha, map_zero]

/-! #### Consequences of the essential constancy of the quotient system -/

section EssentiallyConstant

variable {c : Cone D.quotientSystem} {i : ℕ} {s : D.quotientSystem.obj (op i) ⟶ c.pt}
  (hc : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith D.quotientSystem c
    (op i) s)

include hc

omit hc in
/-- The projections of the cone point commute with the transition maps to level `0`. -/
theorem cone_π_eq (n : ℕ) (z : c.pt) :
    tr D.quotientSystem (Nat.zero_le n) (c.π.app (op n) z) = c.π.app (op 0) z := by
  rw [← c.w (homOfLE (Nat.zero_le n)).op]
  rfl

/-- The retraction `s` undoes the projection of the cone point at level `i`. -/
private theorem s_π_apply (z : c.pt) : s (c.π.app (op i) z) = z := by
  simpa using congrArg (fun g => g.hom z) hc.retraction

/-- Every compatible family in the quotient system is the image of a point of the value. -/
theorem eq_π_s (y : ∀ n, D.quotientSystem.obj (op n))
    (hy : ∀ n m (h : n ≤ m), tr D.quotientSystem h (y m) = y n) (n : ℕ) :
    c.π.app (op n) (s (y i)) = y n := by
  obtain ⟨k, σ, τ, hk⟩ := hc.cofinal (op n)
  have h1 := congrArg (fun g => g.hom (y k.unop)) hk
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
  have hσ : D.quotientSystem.map σ (y k.unop) = y i := hy i k.unop (leOfHom σ.unop)
  have hτ : D.quotientSystem.map τ (y k.unop) = y n := hy n k.unop (leOfHom τ.unop)
  rw [← hτ]
  change _ = (D.quotientSystem.map τ).hom (y k.unop)
  rw [h1]
  change c.π.app (op n) (s (y i)) = c.π.app (op n) (s (D.quotientSystem.map σ (y k.unop)))
  rw [hσ]

/-- The projections of the value are injective from the retraction level on. -/
theorem π_injective {n : ℕ} (hn : i ≤ n) : Function.Injective (c.π.app (op n)) := by
  intro z w hzw
  have hi : c.π.app (op i) z = c.π.app (op i) w := by
    have hw := c.w (homOfLE hn).op
    rw [← hw]
    change (D.quotientSystem.map _) (c.π.app (op n) z) = (D.quotientSystem.map _) _
    exact congrArg _ hzw
  rw [← s_π_apply D hc z, ← s_π_apply D hc w, hi]

/-- If a compatible family of `P` dies in the quotient at some level beyond the retraction
level, it dies in the quotient at every level. -/
theorem toQuotient_eq_zero_of_level (x : compatibleFamilies P) {m : ℕ} (hm : i ≤ m)
    (hx : D.toQuotient m (x.1 m) = 0) (n : ℕ) : D.toQuotient n (x.1 n) = 0 := by
  have hy : ∀ n m (h : n ≤ m),
      tr D.quotientSystem h (D.toQuotient m (x.1 m)) = D.toQuotient n (x.1 n) :=
    fun n m h => by rw [D.tr_toQuotient, tr_compatibleFamilies]
  have hyi : D.toQuotient i (x.1 i) = 0 := by
    rw [← hy i m hm, hx, map_zero]
  rw [← D.eq_π_s hc (fun n => D.toQuotient n (x.1 n)) hy n, hyi, map_zero, map_zero]

/-- The value is annihilated by `I^{i+1}`. -/
theorem smul_pt_eq_zero {a : R} (ha : a ∈ I ^ (i + 1)) (z : c.pt) : a • z = 0 := by
  rw [← s_π_apply D hc (a • z), map_smul, D.smul_quotient_eq_zero ha, map_zero]

/-- A power of `I` carries `lim P` into the image of `M`. -/
theorem smul_mem_range_ι {a : R} (ha : a ∈ I ^ (i + 1)) (x : compatibleFamilies P) :
    a • x ∈ LinearMap.range D.ι := by
  refine D.mem_range_ι_of_toQuotient_eq_zero _ ?_
  refine D.toQuotient_eq_zero_of_level hc (a • x) le_rfl ?_
  change D.toQuotient i (a • x.1 i) = 0
  rw [map_smul, D.smul_quotient_eq_zero ha]

end EssentiallyConstant

/-! #### Lifting points of a cone over the quotient system to `lim P` -/

section Lift

variable (c : Cone D.quotientSystem)

/-- The projections of a cone over the quotient system commute with the transition maps. -/
theorem tr_cone_π {n m : ℕ} (h : n ≤ m) (z : c.pt) :
    tr D.quotientSystem h (c.π.app (op m) z) = c.π.app (op n) z := by
  rw [← c.w (homOfLE h).op]
  rfl

/-- A lift to `Pₙ` of the `n`-th projection of a cone point extends to a lift to `Pₙ₊₁` of the
`(n+1)`-st projection mapping to it. -/
theorem exists_lift_succ (z : c.pt) (n : ℕ) (y : P.obj (op n))
    (hy : D.toQuotient n y = c.π.app (op n) z) :
    ∃ y' : P.obj (op (n + 1)), D.toQuotient (n + 1) y' = c.π.app (op (n + 1)) z ∧
      tr P (Nat.le_succ n) y' = y := by
  obtain ⟨w, hw⟩ := D.toQuotient_surjective (n + 1) (c.π.app (op (n + 1)) z)
  have h0 : D.toQuotient n (tr P (Nat.le_succ n) w - y) = 0 := by
    rw [map_sub, ← D.tr_toQuotient, hw, hy, D.tr_cone_π c, sub_self]
  obtain ⟨m, hm⟩ := (D.toQuotient_eq_zero_iff n _).1 h0
  refine ⟨w - D.μ (n + 1) m, ?_, ?_⟩
  · rw [map_sub, hw, (D.toQuotient_eq_zero_iff _ _).2 ⟨m, rfl⟩, sub_zero]
  · rw [map_sub, D.μ_tr, hm, sub_sub_cancel]

/-- A compatible sequence of lifts of the projections of a point of the cone. -/
noncomputable def liftSeq (z : c.pt) :
    (n : ℕ) → {y : P.obj (op n) // D.toQuotient n y = c.π.app (op n) z}
  | 0 => ⟨(D.toQuotient_surjective 0 (c.π.app (op 0) z)).choose,
      (D.toQuotient_surjective 0 (c.π.app (op 0) z)).choose_spec⟩
  | n + 1 => ⟨(D.exists_lift_succ c z n (liftSeq z n).1 (liftSeq z n).2).choose,
      (D.exists_lift_succ c z n (liftSeq z n).1 (liftSeq z n).2).choose_spec.1⟩

/-- Successive terms of `liftSeq` are compatible under the transition maps. -/
theorem tr_liftSeq (z : c.pt) (n : ℕ) :
    tr P (Nat.le_succ n) (D.liftSeq c z (n + 1)).1 = (D.liftSeq c z n).1 :=
  (D.exists_lift_succ c z n (D.liftSeq c z n).1 (D.liftSeq c z n).2).choose_spec.2

/-- **Points of a cone over the quotient system lift to `lim P`.** -/
theorem exists_lift (z : c.pt) :
    ∃ x : compatibleFamilies P, ∀ n, D.toQuotient n (x.1 n) = c.π.app (op n) z :=
  ⟨⟨fun n => (D.liftSeq c z n).1,
      mem_compatibleFamilies_of_succ P _ fun n => D.tr_liftSeq c z n⟩,
    fun n => (D.liftSeq c z n).2⟩

end Lift

/-! #### The comparison map and its kernels and cokernels -/

include D in
/-- `I^{n+1} lim P` lies in the kernel of the projection `lim P → Pₙ`. -/
theorem pow_smul_top_le_ker (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)) ≤
      LinearMap.ker (compatibleFamiliesπ P n) := by
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  simp only [LinearMap.mem_ker, map_smul, compatibleFamiliesπ_apply]
  exact D.smul_eq_zero ha _

/-- The comparison `lim P / I^{n+1} lim P → Pₙ`. -/
public def comparisonApp (n : ℕ) :
    (adicQuotientTower I (compatibleFamilies P)).obj (op n) ⟶ P.obj (op n) :=
  ModuleCat.ofHom ((I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P))).liftQ
    (compatibleFamiliesπ P n) (D.pow_smul_top_le_ker n))

/-- The comparison sends the class of a compatible family to its `n`-th component. -/
theorem comparisonApp_mk (n : ℕ) (x : compatibleFamilies P) :
    D.comparisonApp n (Submodule.Quotient.mk x) = x.1 n :=
  rfl

/-- The comparison map `{lim P / I^{n+1} lim P} → (Pₙ)` of inverse systems. -/
public def comparison : adicQuotientTower I (compatibleFamilies P) ⟶ P where
  app n := D.comparisonApp n.unop
  naturality m n g := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    exact (tr_compatibleFamilies P x (leOfHom g.unop)).symm

/-- The comparison map sends the class of a compatible family to its `n`-th component. -/
theorem comparison_app_mk (n : ℕ) (x : compatibleFamilies P) :
    D.comparison.app (op n) (Submodule.Quotient.mk x) = x.1 n :=
  rfl

/-- The map `M → lim P` carries `I^k M` into `I^k lim P`. -/
theorem ι_pow_smul_top_le (k : ℕ) :
    (I ^ k • (⊤ : Submodule R M)).map D.ι ≤ I ^ k • (⊤ : Submodule R (compatibleFamilies P)) := by
  rw [Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- The map `M/I^{n+1}M → lim P / I^{n+1} lim P` induced by `M → lim P`. -/
public def quotientMap (n : ℕ) :
    (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) →ₗ[R]
      (compatibleFamilies P ⧸ (I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)))) :=
  Submodule.mapQ _ _ D.ι (fun x hx => D.ι_pow_smul_top_le (n + 1) ⟨x, hx, rfl⟩)

/-- `quotientMap` sends the class of `m` to the class of `ι m`. -/
theorem quotientMap_mk (n : ℕ) (m : M) :
    D.quotientMap n (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.ι m) :=
  rfl

section EssentiallyConstant

variable {c : Cone D.quotientSystem} {i : ℕ} {s : D.quotientSystem.obj (op i) ⟶ c.pt}
  (hc : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith D.quotientSystem c
    (op i) s)

include hc

omit hc in
/-- The kernels of the `μₙ` decrease with `n`. -/
theorem ker_mono {n m : ℕ} (h : n ≤ m) : LinearMap.ker (D.μ m) ≤ LinearMap.ker (D.μ n) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← D.μ_tr h, hx, map_zero]

/-- A compatible family of `P` vanishing at a level beyond the retraction level and beyond the
kernel level of `n` lies in `I^{n+1} lim P`. -/
theorem mem_pow_smul_of_eq_zero (x : compatibleFamilies P) {n m : ℕ} (hm : i ≤ m)
    (hmn : D.kerLevel n ≤ m) (hx : x.1 m = 0) :
    x ∈ I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)) := by
  obtain ⟨m₀, rfl⟩ := D.mem_range_ι_of_toQuotient_eq_zero x
    (D.toQuotient_eq_zero_of_level hc x hm (by rw [hx, map_zero]))
  have hker : m₀ ∈ LinearMap.ker (D.μ (D.kerLevel n)) := D.ker_mono hmn hx
  obtain ⟨h, hh, r, hr, rfl⟩ := Submodule.mem_sup.1 (D.ker_le n hker)
  have hιh : D.ι h = 0 := Subtype.ext (funext fun k => D.le_ker k hh)
  rw [map_add, hιh, zero_add]
  exact D.ι_pow_smul_top_le (n + 1) ⟨r, hr, rfl⟩

/-- **The kernels of the comparison are pro-zero.** -/
theorem kernelsProZero_comparison : KernelsProZero D.comparison := by
  intro n
  refine ⟨n + D.kerLevel n + i, by omega, fun q hq => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (I ^ (n + D.kerLevel n + i + 1) • (⊤ : Submodule R (compatibleFamilies P))) q
  change Submodule.Quotient.mk x = (0 : _ ⧸ _)
  rw [Submodule.Quotient.mk_eq_zero]
  exact D.mem_pow_smul_of_eq_zero hc (n := n) (m := n + D.kerLevel n + i) x (by omega)
    (by omega) hq

/-- **The cokernels of the comparison are pro-zero.** -/
theorem cokernelsProZero_comparison : CokernelsProZero D.comparison := by
  intro n
  obtain ⟨k, σ, τ, hk⟩ := hc.cofinal (op n)
  refine ⟨k.unop, leOfHom τ.unop, fun y => ?_⟩
  set z : c.pt := s (D.quotientSystem.map σ (D.toQuotient k.unop y)) with hz
  have hyz : D.toQuotient n (tr P (leOfHom τ.unop) y) = c.π.app (op n) z := by
    have h1 := congrArg (fun g => g.hom (D.toQuotient k.unop y)) hk
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [← D.tr_toQuotient]
    exact h1
  obtain ⟨x₁, hx₁⟩ := D.exists_lift c z
  have h0 : D.toQuotient n (tr P (leOfHom τ.unop) y - x₁.1 n) = 0 := by
    rw [map_sub, hyz, hx₁, sub_self]
  obtain ⟨m, hm⟩ := (D.toQuotient_eq_zero_iff n _).1 h0
  refine ⟨Submodule.Quotient.mk (x₁ + D.ι m), ?_⟩
  change (x₁ + D.ι m).1 n = _
  simp only [Submodule.coe_add, Pi.add_apply, ι_apply_coe, hm, add_sub_cancel]

/-- **The pro-isomorphism `(Pₙ) ≅ {lim P / I^{n+1} lim P}`.** -/
public def replacementProIso : ProIso P (adicQuotientTower I (compatibleFamilies P)) :=
  ofProZero (D.kernelsProZero_comparison hc) (D.cokernelsProZero_comparison hc)

/-- The backward maps of the pro-isomorphism are the comparison maps. -/
theorem replacementProIso_ψ (n : ℕ) : (D.replacementProIso hc).ψ n = D.comparison.app (op n) :=
  rfl

/-- **The pro-isomorphism carries the maps `M → Pₙ` to the maps `M → lim P / I^{n+1} lim P`.** -/
theorem replacementProIso_φ_μ (n : ℕ) (m : M) :
    (D.replacementProIso hc).φ n (D.μ ((D.replacementProIso hc).α n) m) =
      Submodule.Quotient.mk (D.ι m) := by
  refine (ofProZero_φ_eq _ _ n _ (Submodule.Quotient.mk (D.ι m)) ?_).trans rfl
  change D.μ _ m = tr P _ (D.μ _ m)
  rw [D.μ_tr]

/-- **The cokernels of `M/I^{n+1}M → lim P / I^{n+1} lim P` are annihilated by `I^{i+1}`.** -/
theorem smul_mem_range_quotientMap (n : ℕ) {a : R} (ha : a ∈ I ^ (i + 1))
    (q : compatibleFamilies P ⧸ (I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)))) :
    a • q ∈ LinearMap.range (D.quotientMap n) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨m, hm⟩ := D.smul_mem_range_ι hc ha x
  exact ⟨Submodule.Quotient.mk m, by rw [quotientMap_mk, hm]; rfl⟩

omit hc in
/-- The kernel of `M → lim P` is `H`. -/
theorem mem_of_ι_eq_zero (x : M) (hx : D.ι x = 0) : x ∈ D.H :=
  D.iInf_ker_le x fun n => congrArg (fun z : compatibleFamilies P => z.1 n) hx

/-- **The kernels of `M/I^{n+1}M → lim P / I^{n+1} lim P` are annihilated by a fixed power of
`I`.** -/
theorem smul_eq_zero_of_quotientMap_eq_zero (n : ℕ) {a : R}
    (ha : a ∈ I ^ (D.e + (i + 1))) (q : M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))
    (hq : D.quotientMap n q = 0) : a • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  have hx : D.ι x ∈ I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)) :=
    (Submodule.Quotient.mk_eq_zero _).1 hq
  change Submodule.Quotient.mk (a • x) = (0 : _ ⧸ _)
  rw [Submodule.Quotient.mk_eq_zero]
  rcases lt_or_ge (n + 1) (i + 1) with hsmall | hlarge
  · exact Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (by omega) ha) Submodule.mem_top
  · have hle : I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)) ≤
        (I ^ (n + 1 - (i + 1)) • (⊤ : Submodule R M)).map D.ι := by
      have hsplit : I ^ (n + 1) = I ^ (n + 1 - (i + 1)) * I ^ (i + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, Submodule.mul_smul, Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_
      refine Submodule.smul_le.2 fun b hb y _ => ?_
      obtain ⟨m, hm⟩ := D.smul_mem_range_ι hc hb y
      exact ⟨m, Submodule.mem_top, hm⟩
    obtain ⟨r, hr, hrx⟩ := hle hx
    have hH : x - r ∈ D.H := D.mem_of_ι_eq_zero (x - r) (by rw [map_sub, hrx, sub_self])
    have hxeq : x = (x - r) + r := by abel
    rw [hxeq, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · have : a • (x - r) = 0 := by
        have ha' : a ∈ I ^ D.e := Ideal.pow_le_pow_right (by omega) ha
        have := Submodule.smul_mem_smul ha' hH
        rwa [D.ann_H] at this
      rw [this]
      exact Submodule.zero_mem _
    · have ha' : a ∈ I ^ (i + 1) := Ideal.pow_le_pow_right (by omega) ha
      have := Submodule.smul_mem_smul ha' hr
      rw [← Submodule.mul_smul, ← pow_add] at this
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) this

/-- **The terms `lim P / I^{n+1} lim P` are finite** when the terms of `P` are finite over a
Noetherian ring. -/
theorem finite_adicQuotient [IsNoetherianRing R] (hP : ∀ n, Module.Finite R (P.obj (op n)))
    (n : ℕ) : Module.Finite R
      (compatibleFamilies P ⧸ (I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)))) := by
  obtain ⟨m, hnm, hker⟩ := D.kernelsProZero_comparison hc n
  let g := (D.comparison.app (op m)).hom
  have : Module.Finite R (_ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange g).symm
  refine Module.Finite.of_surjective
    ((LinearMap.ker g).liftQ (adicQuotientMap I (compatibleFamilies P) hnm) hker) fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), rfl⟩

end EssentiallyConstant

/-! #### The comparison out of a system of levels of `M` -/

section Levels

variable (Fm : ℕᵒᵖ ⥤ ModuleCat.{u} R) (π : ∀ n : ℕ, M →ₗ[R] Fm.obj (op n))
  (hπ_tr : ∀ {n m : ℕ} (h : n ≤ m) (x : M), tr Fm h (π m x) = π n x)
  (hπ_surj : ∀ n, Function.Surjective (π n))
  (hπ_ker : ∀ n, LinearMap.ker (π n) = I ^ (n + 1) • (⊤ : Submodule R M))

include hπ_ker in
/-- The kernel of `πₙ` lies in the kernel of `M → lim P / I^{n+1} lim P`. -/
theorem levelsKer_le (n : ℕ) : LinearMap.ker (π n) ≤
    LinearMap.ker ((I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P))).mkQ.comp D.ι) := by
  rw [hπ_ker]
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact D.ι_pow_smul_top_le (n + 1) ⟨x, hx, rfl⟩

/-- The map `Fₙ = M/I^{n+1}M → lim P / I^{n+1} lim P`. -/
public def levelsMapApp (n : ℕ) :
    Fm.obj (op n) →ₗ[R]
      (compatibleFamilies P ⧸ (I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)))) :=
  ((LinearMap.ker (π n)).liftQ _ (D.levelsKer_le Fm π hπ_ker n)).comp
    (LinearMap.quotKerEquivOfSurjective (π n) (hπ_surj n)).symm.toLinearMap

/-- `levelsMapApp` sends `πₙ x` to the class of `ι x`. -/
theorem levelsMapApp_π (n : ℕ) (x : M) :
    D.levelsMapApp Fm π hπ_surj hπ_ker n (π n x) = Submodule.Quotient.mk (D.ι x) := by
  have : (LinearMap.quotKerEquivOfSurjective (π n) (hπ_surj n)).symm (π n x) =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [levelsMapApp, LinearMap.comp_apply, LinearEquiv.coe_coe, this,
    Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]

include hπ_tr in
/-- **The comparison out of the levels of `M`**, as a map of inverse systems. -/
public def levelsMap : Fm ⟶ adicQuotientTower I (compatibleFamilies P) where
  app n := ModuleCat.ofHom (D.levelsMapApp Fm π hπ_surj hπ_ker n.unop)
  naturality {m n} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ_surj m.unop y
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    have h1 : Fm.map f (π m.unop x) = π n.unop x := by
      rw [hf]; exact hπ_tr (leOfHom f.unop) x
    change D.levelsMapApp Fm π hπ_surj hπ_ker n.unop (Fm.map f (π m.unop x)) =
      adicQuotientMap I _ (leOfHom f.unop) (D.levelsMapApp Fm π hπ_surj hπ_ker m.unop (π m.unop x))
    rw [h1, D.levelsMapApp_π, D.levelsMapApp_π]
    rfl

/-- The comparison out of the levels sends `πₙ x` to the class of `ι x`. -/
theorem levelsMap_app_π (n : ℕ) (x : M) :
    (D.levelsMap Fm π hπ_tr hπ_surj hπ_ker).app (op n) (π n x) = Submodule.Quotient.mk (D.ι x) :=
  D.levelsMapApp_π Fm π hπ_surj hπ_ker n x

variable {c : Cone D.quotientSystem} {i : ℕ} {s : D.quotientSystem.obj (op i) ⟶ c.pt}
  (hc : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith D.quotientSystem c
    (op i) s)

/-- **Compatibility of the pro-isomorphism with a map of inverse systems `κ : (Fₙ) ⟶ (Pₙ)` through
which the maps `M → Pₙ` factor.** -/
public theorem map_comp_replacementProIso_φ (κ : Fm ⟶ P)
    (hκ : ∀ n x, κ.app (op n) (π n x) = D.μ n x) (n : ℕ) :
    κ.app (op ((D.replacementProIso hc).α n)) ≫ (D.replacementProIso hc).φ n =
      Fm.map (homOfLE ((D.replacementProIso hc).αle n)).op ≫
        (D.levelsMap Fm π hπ_tr hπ_surj hπ_ker).app (op n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hπ_surj ((D.replacementProIso hc).α n) y
  change (D.replacementProIso hc).φ n (κ.app (op _) (π _ x)) =
    (D.levelsMap Fm π hπ_tr hπ_surj hπ_ker).app (op n) (tr Fm _ (π _ x))
  rw [hκ, D.replacementProIso_φ_μ hc n x, hπ_tr, D.levelsMap_app_π]

include hc in
/-- The kernels of the comparison out of the levels are annihilated by a fixed power of `I`. -/
public theorem smul_eq_zero_of_levelsMap_eq_zero (n : ℕ) {a : R}
    (ha : a ∈ I ^ (D.e + (i + 1))) (q : Fm.obj (op n))
    (hq : (D.levelsMap Fm π hπ_tr hπ_surj hπ_ker).app (op n) q = 0) : a • q = 0 := by
  obtain ⟨x, rfl⟩ := hπ_surj n q
  have h0 : D.quotientMap n (Submodule.Quotient.mk x) = 0 := by
    rwa [quotientMap_mk, ← D.levelsMap_app_π Fm π hπ_tr hπ_surj hπ_ker n x]
  have := D.smul_eq_zero_of_quotientMap_eq_zero hc n ha _ h0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hπ_ker n] at this
  rw [← map_smul]
  exact this

include hc in
/-- The cokernels of the comparison out of the levels are annihilated by `I^{i+1}`. -/
public theorem smul_mem_range_levelsMap (n : ℕ) {a : R} (ha : a ∈ I ^ (i + 1))
    (q : compatibleFamilies P ⧸ (I ^ (n + 1) • (⊤ : Submodule R (compatibleFamilies P)))) :
    a • q ∈ LinearMap.range ((D.levelsMap Fm π hπ_tr hπ_surj hπ_ker).app (op n)).hom := by
  obtain ⟨p, hp⟩ := D.smul_mem_range_quotientMap hc n ha q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ p
  exact ⟨π n x, (D.levelsMap_app_π Fm π hπ_tr hπ_surj hπ_ker n x).trans hp⟩

end Levels

end ExtensionData

end Stacks.AdicSystem
