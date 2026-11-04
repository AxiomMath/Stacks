module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.CompactFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Germ
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule

/-!
# Enriques–Severi–Zariski: vanishing of `Γ(X, ℱ ⊗ ℒ^{⊗ n})` for `n ≪ 0`

[Stacks, Tag 0FD7]. Let `k` be a field, let `X` be a proper scheme over `k`, let `ℒ` be an ample
invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. If `Ass(ℱ)` contains no closed
points then `Γ(X, ℱ ⊗ ℒ^{⊗ n}) = 0` for `n ≪ 0`.

## Main results

* `Stacks.EnriquesSeveriZariski.eq_zero_of_forall_mem_range_chain`: a global section of a twist
  divisible by every power of the chosen ample section is zero.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_eq_zero_sections_descend`: the descent along one
  arithmetic progression.
* `Stacks.EnriquesSeveriZariski.forall_le_eq_zero_sections_twist`: **[Stacks, Tag 0FD7]** on the
  sections themselves.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_isZero_globalSectionsOverField_twist`:
  **[Stacks, Tag 0FD7]**, the vanishing as an assertion about the `k`-vector space
  `Γ(X, ℱ ⊗ ℒ^{⊗ n})`.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_isZero_cohomologyOverField_zero_twist`:
  **[Stacks, Tag 0FD7]**, the same vanishing in degree-zero cohomology.
* `Stacks.EnriquesSeveriZariski.twistedGradedModuleTwistIso`: the comparison with the twist of
  the graded twisted-cohomology machinery, which is an isomorphism and not an equality.
* `…_twistedGradedModuleTwist`: **[Stacks, Tag 0FD7]** at that spelling, in global sections and
  in degree-zero cohomology.

## The proof, and why it is not the source's

The source proves 0FD7 by the dévissage [Stacks, Tag 01YM] applied to the property "every
section of `ℱ ⊗ ℒ^{⊗ n}` has support consisting only of closed points", verifying 01YM's three
closure conditions and using asymptotic Riemann–Roch [Stacks, Tag 0BJ8] on the integral closed
subschemes that the dévissage produces. The route taken here is shorter and uses neither the
dévissage nor asymptotic Riemann–Roch; it needs only [Stacks, Tag 09NV], [Stacks, Tag 0BUG] and
the Krull intersection theorem.

`Ass(ℱ)` is a finite set (`AlgebraicGeometry.associatedPoints_finite`) of non-closed points. By
[Stacks, Tag 09NV] there are `e > 0` and `σ ∈ Γ(X, ℒ^{⊗ e})` whose nonvanishing locus `X_σ` is
affine and contains `Ass(ℱ)`. Multiplication by `σ` is then injective on
`Γ(X, ℱ ⊗ ℒ^{⊗ n})` for every `n`, because a section with vanishing germs at every associated
point is zero and `σ` is a unit at every associated point.

Fix a degree `m`. The images of the `j`-fold multiplications by `σ` form a decreasing sequence
of subspaces of the finite dimensional space `Γ(X, ℱ ⊗ ℒ^{⊗ m})`, so they are constant from some
index `J` on; every section in that stable image is then divisible by every power of `σ`. A
section divisible by `σ^j` has germ in `𝔪_y^j · (ℱ ⊗ ℒ^{⊗ n})_y` at every `y` where `σ`
vanishes, so by Krull its germ there is zero: the support of such a section is a closed subset
of `X` contained in the affine open `X_σ`. A point of a closed subset of `X_σ` has its closure
inside an affine open, so it is a closed point of `X` by
`Stacks.EnriquesSeveriZariski.isClosed_singleton_of_closure_subset_of_isAffineOpen`, which is
where [Stacks, Tag 0BUG] enters. Since `Ass(ℱ ⊗ ℒ^{⊗ n}) = Ass(ℱ)` contains no closed point,
such a section has vanishing germs at every associated point, hence is zero.

So the stable image is zero; since multiplication by `σ^j` is injective on global sections, the
twist in degree `m - j·e` has no nonzero global section for every `j ≥ J`. Applying this at
`m = 0, -1, …, -(e-1)` covers every sufficiently negative integer.

## Implementation notes

The descent is organized by the explicit sequence
`Stacks.EnriquesSeveriZariski.descend e m j = m - j * e`, written as a recursion so that
`descend e m (j + 1) = descend e m j - e` holds by `rfl`; that makes the chain of multiplication
maps `Stacks.EnriquesSeveriZariski.chain` definable with no transport, each step composing on
the left.

**Two spellings of the twist.** The ample theory of this repository twists by
`AlgebraicGeometry.SheafOfModules.tensorPow`, the iterated tensor product of
[Stacks, Tag 01CU], and that is the spelling used here, because
`Stacks.Divisors.associatedPoints_tensorObj_eq_of_isInvertible`,
`AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible` and
[Stacks, Tag 09NV] are all stated at it. The graded twisted-cohomology machinery twists by
`Stacks.SheafOfModules.TensorPower.tensorPower` instead, the image of the structure sheaf under
a power of the autoequivalence `- ⊗ ℒ`. These are not the same object: the tensor products
agree definitionally but the tensor powers do not, and
`Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow` compares them by an isomorphism.
`Stacks.EnriquesSeveriZariski.twistedGradedModuleTwistIso` lifts that comparison to the twists,
and the statement is restated across it.

`Ass(ℱ ⊗ ℒ^{⊗ n}) = Ass(ℱ)` is
`Stacks.Divisors.associatedPoints_tensorObj_eq_of_isInvertible`, the tensor factor being
invertible; it is the one place where the hypothesis is used for the twist rather than for `ℱ`,
and it is why the source's hypothesis on `ℱ` alone suffices.

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.EnriquesSeveriZariski

/-! ### The descending chain of multiplication maps -/

/-- The integer `m - j * e`, defined by recursion on `j`. -/
def descend (e : ℕ) (m : ℤ) : ℕ → ℤ
  | 0 => m
  | j + 1 => descend e m j - e

/-- `descend e m 0 = m`. -/
@[simp] theorem descend_zero (e : ℕ) (m : ℤ) : descend e m 0 = m := rfl

/-- `descend e m (j + 1) = descend e m j - e`. -/
@[simp] theorem descend_succ (e : ℕ) (m : ℤ) (j : ℕ) :
    descend e m (j + 1) = descend e m j - e :=
  rfl

/-- `descend e m j = m - j * e`. -/
theorem descend_eq (e : ℕ) (m : ℤ) (j : ℕ) : descend e m j = m - j * e := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descend_succ, ih]
    push_cast
    ring

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- Multiplication by `σ`, read as a map down one step of the chain: it goes from the twist in
degree `n - e` to the twist in degree `n`. -/
def mulSectionDown {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤))
    (F : X.Modules) (n : ℤ) : twist L F (n - e) ⟶ twist L F n :=
  mulSection L σ F (n - e) ≫ eqToHom (congrArg (twist L F) (by ring))

/-- The `j`-fold multiplication by `σ`, from degree `descend e m j` up to degree `m`. -/
def chain {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (m : ℤ) :
    (j : ℕ) → (twist L F (descend e m j) ⟶ twist L F m)
  | 0 => 𝟙 _
  | j + 1 => mulSectionDown L σ F (descend e m j) ≫ chain σ F m j

/-- The `0`-fold multiplication by `σ` is the identity. -/
@[simp] theorem chain_zero {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤))
    (F : X.Modules) (m : ℤ) : chain L σ F m 0 = 𝟙 _ :=
  rfl

/-- The `(j + 1)`-fold multiplication by `σ` is one multiplication by `σ` from degree
`descend e m (j + 1)` to degree `descend e m j`, followed by the `j`-fold one. -/
@[simp] theorem chain_succ {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤))
    (F : X.Modules) (m : ℤ) (j : ℕ) :
    chain L σ F m (j + 1) = mulSectionDown L σ F (descend e m j) ≫ chain L σ F m j :=
  rfl

/-! ### The stalk behaviour of the chain -/

/-- Injectivity on stalks is stable under composition. -/
private theorem injective_stalkLinearMap_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C)
    (y : X) (hu : Function.Injective (AlgebraicGeometry.stalkLinearMap A B u y))
    (hv : Function.Injective (AlgebraicGeometry.stalkLinearMap B C v y)) :
    Function.Injective (AlgebraicGeometry.stalkLinearMap A C (u ≫ v) y) := fun a b hab =>
  hu (hv (by simpa only [AlgebraicGeometry.Scheme.Modules.stalkLinearMap_comp] using hab))

/-- Composing with an `eqToHom` on the right changes neither injectivity on stalks nor the
submodule the stalk map lands in. -/
private theorem injective_stalkLinearMap_comp_eqToHom {A B C : X.Modules} (u : A ⟶ B)
    (h : B = C) (y : X) (hu : Function.Injective (AlgebraicGeometry.stalkLinearMap A B u y)) :
    Function.Injective (AlgebraicGeometry.stalkLinearMap A C (u ≫ eqToHom h) y) := by
  subst h
  simpa using hu

private theorem range_stalkLinearMap_comp_eqToHom_le {A B C : X.Modules} (u : A ⟶ B)
    (h : B = C) (y : X) {I : Ideal (X.presheaf.stalk y)}
    (hu : LinearMap.range (AlgebraicGeometry.stalkLinearMap A B u y) ≤
      I • (⊤ : Submodule (X.presheaf.stalk y) (B.presheaf.stalk y))) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap A C (u ≫ eqToHom h) y) ≤
      I • (⊤ : Submodule (X.presheaf.stalk y) (C.presheaf.stalk y)) := by
  subst h
  simpa using hu

/-- The ideal multiples the stalk maps land in compose. -/
private theorem range_stalkLinearMap_comp_le {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C)
    (y : X) {I J : Ideal (X.presheaf.stalk y)}
    (hu : LinearMap.range (AlgebraicGeometry.stalkLinearMap A B u y) ≤
      I • (⊤ : Submodule (X.presheaf.stalk y) (B.presheaf.stalk y)))
    (hv : LinearMap.range (AlgebraicGeometry.stalkLinearMap B C v y) ≤
      J • (⊤ : Submodule (X.presheaf.stalk y) (C.presheaf.stalk y))) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap A C (u ≫ v) y) ≤
      I • (J • (⊤ : Submodule (X.presheaf.stalk y) (C.presheaf.stalk y))) := by
  rintro z ⟨a, rfl⟩
  rw [AlgebraicGeometry.Scheme.Modules.stalkLinearMap_comp]
  have h2 := Submodule.mem_map_of_mem
    (f := AlgebraicGeometry.stalkLinearMap B C v y) (hu ⟨a, rfl⟩)
  rw [Submodule.map_smul'', Submodule.map_top] at h2
  exact Submodule.smul_mono le_rfl hv h2

/-- Peeling one power of the maximal ideal. -/
private theorem maximalIdeal_smul_pow_smul {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] (j : ℕ) (N : Submodule R M) :
    (IsLocalRing.maximalIdeal R) • ((IsLocalRing.maximalIdeal R ^ j) • N) =
      (IsLocalRing.maximalIdeal R ^ (j + 1)) • N := by
  rw [pow_succ', mul_smul]

/-- Where `σ` does not vanish, one step of the chain is injective on stalks. -/
theorem injective_stalkLinearMap_mulSectionDown {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (n : ℤ) {y : X}
    (hy : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    Function.Injective
      (AlgebraicGeometry.stalkLinearMap _ _ (mulSectionDown L σ F n) y) :=
  injective_stalkLinearMap_comp_eqToHom _ _ y
    (injective_stalkLinearMap_mulSection L σ F (n - e) hy)

/-- Where `σ` vanishes, one step of the chain lands in the maximal ideal times the stalk. -/
theorem range_stalkLinearMap_mulSectionDown_le {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (n : ℤ) {y : X}
    (hy : y ∉ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap _ _ (mulSectionDown L σ F n) y) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
        (⊤ : Submodule (X.presheaf.stalk y) ((twist L F n).presheaf.stalk y)) :=
  range_stalkLinearMap_comp_eqToHom_le _ _ y
    (range_stalkLinearMap_mulSection_le L σ F (n - e) hy)

/-- Where `σ` does not vanish, the whole chain is injective on stalks. -/
theorem injective_stalkLinearMap_chain {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (m : ℤ) (j : ℕ) {y : X}
    (hy : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    Function.Injective (AlgebraicGeometry.stalkLinearMap _ _ (chain L σ F m j) y) := by
  induction j with
  | zero =>
    exact fun a b hab =>
      (AlgebraicGeometry.Scheme.Modules.stalkLinearMap_id (twist L F m) y a).symm.trans
        (hab.trans (AlgebraicGeometry.Scheme.Modules.stalkLinearMap_id (twist L F m) y b))
  | succ j ih =>
    rw [chain_succ]
    exact injective_stalkLinearMap_comp _ _ y
      (injective_stalkLinearMap_mulSectionDown L σ F (descend e m j) hy) ih

/-- Where `σ` vanishes, the `j`-fold chain lands in the `j`-th power of the maximal ideal times
the stalk. -/
theorem range_stalkLinearMap_chain_le {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (m : ℤ) (j : ℕ) {y : X}
    (hy : y ∉ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap _ _ (chain L σ F m j) y) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ j) •
        (⊤ : Submodule (X.presheaf.stalk y) ((twist L F m).presheaf.stalk y)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [chain_succ, ← maximalIdeal_smul_pow_smul]
    exact range_stalkLinearMap_comp_le _ _ y
      (range_stalkLinearMap_mulSectionDown_le L σ F (descend e m j) hy) ih

/-! ### The twist of a coherent module -/

/-- The twist of a coherent module by a tensor power of an invertible module is coherent. -/
theorem isCoherent_twist [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (n : ℤ) :
    (twist L F n).IsCoherent :=
  AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
    (Stacks.Ample.tensorPowModule X L n)

/-- **`Ass(ℱ ⊗ ℒ^{⊗ n}) = Ass(ℱ)`**, the tensor factor being invertible. -/
theorem associatedPoints_twist (F : X.Modules) (n : ℤ) :
    Stacks.Divisors.associatedPoints (twist L F n) = Stacks.Divisors.associatedPoints F :=
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L n) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L n
  Stacks.Divisors.associatedPoints_tensorObj_eq_of_isInvertible F
    (Stacks.Ample.tensorPowModule X L n)

/-! ### Injectivity of multiplication on global sections -/

section Noetherian

variable [IsLocallyNoetherian X]

/-- A global section of a twist of a coherent module is zero once its germs vanish at the
associated points of the module. -/
private theorem eq_zero_of_forall_germ_associatedPoints_twist (F : X.Modules) [F.IsCoherent]
    (n : ℤ) (t : Γ(twist L F n, ⊤))
    (h : ∀ (x : X) (hx : x ∈ (⊤ : X.Opens)), x ∈ Stacks.Divisors.associatedPoints F →
      (twist L F n).presheaf.germ ⊤ x hx t = 0) :
    t = 0 :=
  have : (twist L F n).IsCoherent := isCoherent_twist L F n
  have : (twist L F n).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero (twist L F n) ⊤ t
    fun x hx hxa => h x hx (by rwa [associatedPoints_twist] at hxa)

/-- **Multiplication along the chain is injective on global sections.** A section killed by the
chain has vanishing germ at every associated point, because `σ` does not vanish there, and a
section with vanishing germs at the associated points is zero. -/
theorem injective_app_top_chain {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) [F.IsCoherent]
    (hAss : Stacks.Divisors.associatedPoints F ⊆
      (Stacks.AmpleTheory.powNonvanishingOpen X L e σ : Set X))
    (m : ℤ) (j : ℕ) :
    Function.Injective ((chain L σ F m j).app (⊤ : X.Opens)) := by
  intro a b hab
  have happ : (chain L σ F m j).val.app (op (⊤ : X.Opens)) (a - b) = 0 :=
    (map_sub _ a b).trans (sub_eq_zero.mpr hab)
  refine sub_eq_zero.1 (eq_zero_of_forall_germ_associatedPoints_twist L F _ (a - b)
    fun x hxtop hx => ?_)
  refine injective_stalkLinearMap_chain L σ F m j (hAss hx) ?_
  exact (AlgebraicGeometry.stalkLinearMap_germ _ _ (chain L σ F m j) ⊤ x hxtop (a - b)).trans
    ((congrArg _ happ).trans ((map_zero _).trans (map_zero _).symm))

/-! ### A section divisible by every power of `σ` -/

/-- **A global section of a twist divisible by every power of `σ` is zero.** Its germ vanishes at
every point where `σ` vanishes, by the Krull intersection theorem, so its support — a closed
subset of `X` — lies inside the affine open `X_σ`; a point of such a set has its closure inside
an affine open, hence is a closed point, and `Ass(ℱ ⊗ ℒ^{⊗ m}) = Ass(ℱ)` contains none. -/
theorem eq_zero_of_forall_mem_range_chain (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤))
    (haff : IsAffineOpen (Stacks.AmpleTheory.powNonvanishingOpen X L e σ))
    (F : X.Modules) [F.IsCoherent]
    (hAss : ∀ x : X, x ∈ Stacks.Divisors.associatedPoints F → ¬ IsClosed ({x} : Set X))
    (m : ℤ) (t : Γ(twist L F m, ⊤))
    (ht : ∀ j : ℕ, ∃ u : Γ(twist L F (descend e m j), ⊤),
      (chain L σ F m j).app (⊤ : X.Opens) u = t) :
    t = 0 := by
  have hcm : (twist L F m).IsCoherent := isCoherent_twist L F m
  have : (twist L F m).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have hoff : ∀ y : X, y ∉ Stacks.AmpleTheory.powNonvanishingOpen X L e σ →
      (twist L F m).presheaf.germ ⊤ y (Opens.mem_top y) t = 0 := by
    intro y hy
    refine eq_zero_of_forall_mem_maximalIdeal_pow_smul (twist L F m) y _ fun j => ?_
    obtain ⟨u, hu⟩ := ht j
    have hu' : (chain L σ F m j).val.app (op (⊤ : X.Opens)) u = t := hu
    rw [← hu', ← AlgebraicGeometry.stalkLinearMap_germ _ _ (chain L σ F m j) ⊤ y
      (Opens.mem_top y) u]
    exact range_stalkLinearMap_chain_le L σ F m j hy ⟨_, rfl⟩
  have hsupp : germSupport (twist L F m) t ⊆
      (Stacks.AmpleTheory.powNonvanishingOpen X L e σ : Set X) := fun y hy =>
    of_not_not fun hcon => hy (hoff y hcon)
  refine eq_zero_of_forall_germ_associatedPoints_twist L F m t fun x _ hx => ?_
  by_contra hcon
  exact hAss x hx
    (isClosed_singleton_of_closure_subset_of_isAffineOpen k f haff
      (((isClosed_germSupport (twist L F m) t).closure_subset_iff.2
        (Set.singleton_subset_iff.2 hcon)).trans hsupp))

/-! ### The descent -/

/-- **The descent.** Along the arithmetic progression of step `e` through `m`, the twist has no
nonzero global section from some level on.

The ranges of the chains inside the finite dimensional space `Γ(X, ℱ ⊗ ℒ^{⊗ m})` form a
decreasing sequence of subspaces, hence are constant from some level `J` on; a section in that
stable range is divisible by every power of `σ`, hence zero, so the stable range is zero; and the
chain is injective on global sections, so the twist in degree `descend e m j` has no nonzero
global section for every `j ≥ J`. -/
theorem exists_forall_le_eq_zero_sections_descend (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤))
    (haff : IsAffineOpen (Stacks.AmpleTheory.powNonvanishingOpen X L e σ))
    (F : X.Modules) [F.IsCoherent]
    (hsub : Stacks.Divisors.associatedPoints F ⊆
      (Stacks.AmpleTheory.powNonvanishingOpen X L e σ : Set X))
    (hAss : ∀ x : X, x ∈ Stacks.Divisors.associatedPoints F → ¬ IsClosed ({x} : Set X))
    (m : ℤ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ t : Γ(twist L F (descend e m j), ⊤), t = 0 := by
  classical
  have hcm : (twist L F m).IsCoherent := isCoherent_twist L F m
  have hfd : FiniteDimensional k (globalSectionsOverField k f (twist L F m)) :=
    finiteDimensional_globalSectionsOverField k f (twist L F m)
  set W : ℕ → Submodule k (globalSectionsOverField k f (twist L F m)) := fun j =>
    LinearMap.range ((globalSectionsFunctor k f).map (chain L σ F m j)).hom
  have hWanti : ∀ j : ℕ, W (j + 1) ≤ W j := by
    intro j
    rintro z ⟨a, rfl⟩
    refine ⟨((globalSectionsFunctor k f).map (mulSectionDown L σ F (descend e m j))).hom a, ?_⟩
    simp only [chain_succ]
    rfl
  have hWanti' : Antitone W := antitone_nat_of_succ_le hWanti
  have hn : ∀ j : ℕ, Module.finrank k (W (j + 1)) ≤ Module.finrank k (W j) :=
    fun j => Submodule.finrank_mono (hWanti j)
  obtain ⟨J, hJ⟩ :=
    exists_eventually_eq_of_antitone (d := fun j => Module.finrank k (W j)) hn
  have hWeq : ∀ j : ℕ, J ≤ j → W j = W J := fun j hj =>
    Submodule.eq_of_le_of_finrank_eq (hWanti' hj) (hJ j hj)
  have hWJ : W J = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro t htmem
    refine eq_zero_of_forall_mem_range_chain L k f σ haff F hAss m t fun j => ?_
    rcases le_or_gt J j with hj | hj
    · exact (hWeq j hj).symm.le htmem
    · exact hWanti' (le_of_lt hj) htmem
  refine ⟨J, fun j hj t => ?_⟩
  have hmem : (chain L σ F m j).app (⊤ : X.Opens) t ∈ W j := ⟨t, rfl⟩
  have hzero := (Submodule.eq_bot_iff _).1 hWJ _ ((hWeq j hj).le hmem)
  exact injective_app_top_chain L σ F hsub m j (hzero.trans (map_zero _).symm)

end Noetherian

/-! ### Tag 0FD7 -/

/-- **[Stacks, Tag 0FD7], on global sections.** Let `k` be a field, let `X` be a proper scheme
over `k`, let `ℒ` be an ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. If
`Ass(ℱ)` contains no closed points then `Γ(X, ℱ ⊗ ℒ^{⊗ n}) = 0` for all `n ≪ 0`. -/
@[stacks 0FD7 "the vanishing stated on the global sections themselves"]
theorem forall_le_eq_zero_sections_twist (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsCoherent]
    (hAss : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Stacks.Divisors.associatedPoints F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ → ∀ t : Γ(twist L F n, ⊤), t = 0 := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨e, he, σ, haff, hsub, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (AlgebraicGeometry.associatedPoints_finite F) ⊤ (by simp)
  choose J hJ using fun i : ℕ => exists_forall_le_eq_zero_sections_descend L k f σ haff F hsub
    (fun x hx hcl => hAss x hcl hx) (-(i : ℤ))
  refine exists_forall_le_of_forall_residue he
    (fun n => ∀ t : Γ(twist L F n, ⊤), t = 0) J fun i _ j hij => ?_
  rw [← descend_eq]
  exact hJ i j hij

/-- **[Stacks, Tag 0FD7].** Let `k` be a field, let `X` be a proper scheme over `k`, let `ℒ` be
an ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. If `Ass(ℱ)` contains no
closed points then

`Γ(X, ℱ ⊗_{𝒪_X} ℒ^{⊗ n}) = 0`

for all `n ≪ 0`, as an assertion about the `k`-vector space of global sections. -/
@[stacks 0FD7]
theorem exists_forall_le_isZero_globalSectionsOverField_twist (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules)
    [F.IsCoherent]
    (hAss : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Stacks.Divisors.associatedPoints F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ → IsZero (globalSectionsOverField k f (twist L F n)) := by
  obtain ⟨n₀, hn₀⟩ := forall_le_eq_zero_sections_twist L k f hL F hAss
  refine ⟨n₀, fun n hn => ?_⟩
  have hsub : Subsingleton (globalSectionsOverField k f (twist L F n)) :=
    ⟨fun a b => by rw [hn₀ n hn a, hn₀ n hn b]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **[Stacks, Tag 0FD7], in degree-zero cohomology.** The same vanishing read through the
derived functor computing `H⁰`, which is the form the twisted-cohomology consumers of 0FD7 ask
for. -/
@[stacks 0FD7 "the vanishing stated on degree-zero cohomology"]
theorem exists_forall_le_isZero_cohomologyOverField_zero_twist (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules)
    [F.IsCoherent]
    (hAss : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Stacks.Divisors.associatedPoints F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ → IsZero (cohomologyOverField k f (twist L F n) 0) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_forall_le_isZero_globalSectionsOverField_twist L k f hL F hAss
  exact ⟨n₀, fun n hn => (hn₀ n hn).of_iso (cohomologyOverFieldZeroIso k f (twist L F n))⟩

/-! ### The twisted-graded-module spelling of the twist -/

/-- **The two spellings of the twist are isomorphic, not equal.**
`Stacks.Cohomology.TwistedGradedModule.twist X ℒ ℱ n` tensors `ℱ` with
`Stacks.SheafOfModules.TensorPower.tensorPower`, the image of the structure sheaf under the
`n`-th power of the autoequivalence `- ⊗ ℒ`, while `Stacks.EnriquesSeveriZariski.twist` tensors
with `AlgebraicGeometry.SheafOfModules.tensorPow`, the iterated tensor product of
[Stacks, Tag 01CU]. The two tensor PRODUCTS agree definitionally — that much was checked — but
the two tensor POWERS are different constructions, and the comparison between them is
`Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`, which is an isomorphism and not an
equality. -/
noncomputable def twistedGradedModuleTwistIso (F : X.Modules) (n : ℤ) :
    Stacks.Cohomology.TwistedGradedModule.twist X L F n ≅ twist L F n :=
  Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (Iso.refl F)
    (Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n)

/-- **[Stacks, Tag 0FD7] at the twisted-graded-module spelling of the twist**, which is the
spelling the graded twisted-cohomology machinery is typed against. -/
@[stacks 0FD7 "the vanishing at the twisted-graded-module spelling of the twist"]
theorem exists_forall_le_isZero_globalSectionsOverField_twistedGradedModuleTwist (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L)
    (F : X.Modules) [F.IsCoherent]
    (hAss : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Stacks.Divisors.associatedPoints F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ →
      IsZero (globalSectionsOverField k f
        (Stacks.Cohomology.TwistedGradedModule.twist X L F n)) := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_isZero_globalSectionsOverField_twist L k f hL F hAss
  exact ⟨n₀, fun n hn => (hn₀ n hn).of_iso
    ((globalSectionsFunctor k f).mapIso (twistedGradedModuleTwistIso L F n))⟩

/-- **[Stacks, Tag 0FD7] at the twisted-graded-module spelling, in degree-zero cohomology.** -/
@[stacks 0FD7 "the vanishing at the twisted-graded-module spelling, in degree-zero cohomology"]
theorem exists_forall_le_isZero_cohomologyOverField_zero_twistedGradedModuleTwist (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L)
    (F : X.Modules) [F.IsCoherent]
    (hAss : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Stacks.Divisors.associatedPoints F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ →
      IsZero (cohomologyOverField k f
        (Stacks.Cohomology.TwistedGradedModule.twist X L F n) 0) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_forall_le_isZero_globalSectionsOverField_twistedGradedModuleTwist L k f hL F hAss
  exact ⟨n₀, fun n hn => (hn₀ n hn).of_iso
    (cohomologyOverFieldZeroIso k f (Stacks.Cohomology.TwistedGradedModule.twist X L F n))⟩

end Stacks.EnriquesSeveriZariski

end
