module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernKMap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedPowerSumVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyLocalized

/-!
# Additive maps out of `K₀` and the localized Chern character map

Let `D` be a pretriangulated category and `A` an abelian group. A function `f` from the objects of
`D` to `A` which is *additive along distinguished triangles*, `f(Y) = f(X) + f(Z)` for every
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`, kills the defining relations of `K₀(D)` (Stacks 0FCN)
and so extends to a homomorphism `K₀(D) ⟶ A` with `[X] ↦ f(X)`, the only one.

This is the construction of the map of Stacks 0FET. Let `(S, δ)` be the base situation of
chapter 42, let `X` be locally of finite type over `S` with quasi-compact irreducible components,
let `i : Z ⟶ X` be a closed immersion, and let `D_{Z,perf}(𝒪_X)` be the perfect complexes whose
cohomology sheaves are supported on `Z` (Remark 0FEP). A supported perfect `E` vanishes on
`X ∖ Z`, so `(X, Z, E)` is an instance of Situation 0GUJ through the finiteness alternative on the
irreducible components, and has a localized Chern character (Definition 0FB5, Remark 0GUK)

  `ch(Z ⟶ X, E) = ∑_p P_p(Z ⟶ X, E)/p! ∈ ∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`.

Lemma 0FBE says that this is additive along distinguished triangles of `D_{Z,perf}(𝒪_X)`: a
distinguished triangle of `D_{Z,perf}(𝒪_X)` is one of perfect objects of `D(𝒪_X)` vanishing on
`X ∖ Z`, and condition (b) of Lemma 0FBD holds since the irreducible components of `X` are
quasi-compact. So "extending additively" is the map

  `ch(Z ⟶ X, -) : K₀(D_{Z,perf}(𝒪_X)) ⟶ ∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`,   `[E] ↦ ch(Z ⟶ X, E)`.

If `X` is quasi-compact, the localized power sums `P_p(Z ⟶ X, E)` vanish for `p ≫ 0`, so the map
takes values in `A^*(Z ⟶ X) ⊗ 𝐐 = ⨁_p A^p(Z ⟶ X) ⊗ 𝐐`, the last sentence of Stacks 0FET.

Finally, Stacks 0FB7 for these classes: if `Z ⊆ Z' ⊆ X` are closed and `E` is supported on `Z`,
then `P_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ P_p(Z ⟶ X, E)`.

## Main definitions

* `CategoryTheory.Pretriangulated.K0.lift` — the homomorphism `K₀(D) ⟶ A` of a function additive
  along distinguished triangles.
* `Stacks.Chow.supportedPerfectData` — the data `(X, Z, E)` of Situation 0GUJ for a supported
  perfect object `E`.
* `Stacks.Chow.supportedLocalizedChernChar` — `ch(Z ⟶ X, E)` for `E ∈ D_{Z,perf}(𝒪_X)`.
* `Stacks.Chow.localizedChernCharKMap` — `ch(Z ⟶ X, -)` on `K₀(D_{Z,perf}(𝒪_X))`.
* `Stacks.Chow.localizedChernCharKMapDirectSum` — for `X` quasi-compact, the same map with values
  in `⨁_p A^p(Z ⟶ X) ⊗ 𝐐`.

## Main results

* `CategoryTheory.Pretriangulated.K0.lift_cls`, `CategoryTheory.Pretriangulated.K0.lift_unique`.
* `Stacks.Chow.supportedLocalizedChernChar_triangle` — Stacks 0FBE for distinguished triangles of
  `D_{Z,perf}(𝒪_X)`.
* `Stacks.Chow.localizedChernCharKMap_cls` — `[E] ↦ ch(Z ⟶ X, E)`.
* `Stacks.Chow.exists_localizedChernCharKMap_eq_zero` — for `X` quasi-compact, every value has
  only finitely many nonzero components.
* `Stacks.Chow.coe_localizedChernCharKMapDirectSum` — the two maps agree.
* `Stacks.Chow.supportedLocalizedPowerSum_eq_bivariantProperPushforward` — Stacks 0FB7 for the
  classes of supported perfect objects.

## Implementation notes

The objectwise class `Stacks.Chow.supportedLocalizedChernChar` is that of Remark 0GUK
(`Stacks.Chow.LocalizedChernData.localizedChernChar`), which in Situation 0GUJ is the class of
Definition 0FB5 (`Stacks.Chow.supportedLocalizedChernChar_eq_localizedChernChar`). The
multiplicativity `ch(Z ⟶ X, α β) = ch(Z ⟶ X, α) ch(Z ⟶ X, β)` of Remark 0FET (Lemma 0FBF) is
`Stacks.Chow.localizedChernCharKMap_mul`, which needs the product of Remark 0FDN on
`K₀(D_{Z,perf}(𝒪_X))`.

## References

* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0FCN](https://stacks.math.columbia.edu/tag/0FCN)
* [Stacks Project, Tag 0FBE](https://stacks.math.columbia.edu/tag/0FBE)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.K0

universe v u w

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] {A : Type w} [AddCommGroup A]

/-- **The homomorphism `K₀(D) ⟶ A` of a function `f` additive along distinguished triangles**,
`f(Y) = f(X) + f(Z)` for every distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`: the lift of `f` to the
free abelian group on the objects of `D` kills the relations `[Y] - [X] - [Z]`, so it descends to
`K₀(D)`, with `[X] ↦ f(X)` (`CategoryTheory.Pretriangulated.K0.lift_cls`). -/
def lift (f : D → A) (hf : ∀ T ∈ distTriang D, f T.obj₂ = f T.obj₁ + f T.obj₃) : K0 D →+ A :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) fun x hx ↦ by
    refine (AddSubgroup.closure_le (K := (FreeAbelianGroup.lift f).ker)).2 ?_ hx
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, hf T hT]
    abel

/-- The value of `CategoryTheory.Pretriangulated.K0.lift` on a class: `[X] ↦ f(X)`. -/
@[simp]
theorem lift_cls (f : D → A) (hf : ∀ T ∈ distTriang D, f T.obj₂ = f T.obj₁ + f T.obj₃) (X : D) :
    lift f hf (cls X) = f X :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **Uniqueness**: `CategoryTheory.Pretriangulated.K0.lift` is the only homomorphism `K₀(D) ⟶ A`
with `[X] ↦ f(X)`. -/
theorem lift_unique (f : D → A) (hf : ∀ T ∈ distTriang D, f T.obj₂ = f T.obj₁ + f T.obj₃)
    (φ : K0 D →+ A) (hφ : ∀ X : D, φ (cls X) = f X) : φ = lift f hf :=
  hom_ext fun X ↦ by rw [hφ, lift_cls]

end CategoryTheory.Pretriangulated.K0

open AlgebraicGeometry

namespace Stacks.Chow

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section Data

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The data of Situation 0GUJ for a supported perfect object**: for `E ∈ D_{Z,perf}(𝒪_X)`, the
scheme `X`, the closed subscheme `Z`, the object `E` and the degree `0`; condition (2) holds since
`E` vanishes on `X ∖ Z` (`AlgebraicGeometry.supportedPerfect_isZero_derivedPullback_compl`). -/
abbrev supportedPerfectData (E : supportedPerfectDerivedCategory i) : LocalizedChernData.{u} where
  base := C
  X := X
  a := a
  Z := Z
  i := i
  E := E.obj
  p := 0
  perfect := E.property.1
  restriction := Or.inl (supportedPerfect_isZero_derivedPullback_compl i E)

variable {i}

/-- A supported perfect object vanishes off its support: the first alternative of condition (2) of
Situation 0GUJ. -/
theorem supportedPerfectData_isZeroOnComplement (E : supportedPerfectDerivedCategory i) :
    (supportedPerfectData C a i E).IsZeroOnComplement :=
  LocalizedChernData.isZeroOnComplement_of_supportedPerfect _ E rfl

/-- If the irreducible components of `X` are quasi-compact, the data of a supported perfect object
are an instance of Situation 0GUJ, through the second finiteness alternative. -/
abbrev supportedPerfectSituation (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)
    (E : supportedPerfectDerivedCategory i) : LocalizedSituation.{u} where
  toLocalizedChernData := supportedPerfectData C a i E
  finiteness := Or.inr (Or.inl hX)

/-- **The localized Chern character `ch(Z ⟶ X, E) ∈ ∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐` of a supported
perfect object** `E ∈ D_{Z,perf}(𝒪_X)`, for `X` with quasi-compact irreducible components: the
class of Remark 0GUK (Definition 0FB5 (1)), `E` vanishing off `Z`. -/
def supportedLocalizedChernChar (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)
    (E : supportedPerfectDerivedCategory i) (p : ℕ) :
    TensorProduct ℤ ℚ (BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl (p : ℤ)) :=
  (supportedPerfectData C a i E).localizedChernChar
    (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj
          E.property.1)
    (supportedPerfectData_isZeroOnComplement C a E) p

/-- `ch_p(Z ⟶ X, E) = P_p(Z ⟶ X, E)/p!`. -/
theorem supportedLocalizedChernChar_apply (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)
    (E : supportedPerfectDerivedCategory i) (p : ℕ) :
    supportedLocalizedChernChar C a hX E p = ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
      (supportedPerfectData C a i E).localizedPowerSum
        (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj
          E.property.1)
        (supportedPerfectData_isZeroOnComplement C a E) p :=
  rfl

/-- In Situation 0GUJ the localized Chern character of a supported perfect object is that of
Definition 0FB5. -/
theorem supportedLocalizedChernChar_eq_localizedChernChar
    (hX : ∀ T ∈ irreducibleComponents X, IsCompact T) (E : supportedPerfectDerivedCategory i)
    (p : ℕ) :
    supportedLocalizedChernChar C a hX E p =
      (supportedPerfectSituation C a hX E).localizedChernChar
        (supportedPerfectData_isZeroOnComplement C a E) p :=
  (supportedPerfectSituation C a hX E).localizedChernChar_toLocalizedChernData _ p

/-- **The last sentence of Stacks 0FET, objectwise.** If `X` is quasi-compact,
`ch_p(Z ⟶ X, E) = 0` for all large `p`. -/
theorem exists_supportedLocalizedChernChar_eq_zero [CompactSpace X]
    (hX : ∀ T ∈ irreducibleComponents X, IsCompact T) (E : supportedPerfectDerivedCategory i) :
    ∃ N, ∀ p ≥ N, supportedLocalizedChernChar C a hX E p = 0 :=
  LocalizedChernData.exists_localizedChernChar_eq_zero (D := supportedPerfectData C a i E)
    (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj
          E.property.1)
    (supportedPerfectData_isZeroOnComplement C a E)

/-- **Stacks 0FBE for supported perfect objects.** Let `X` have quasi-compact irreducible
components and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of `D_{Z,perf}(𝒪_X)`. Then
`ch(Z ⟶ X, E₂) = ch(Z ⟶ X, E₁) + ch(Z ⟶ X, E₃)`: the triangle is a distinguished triangle of
perfect objects of `D(𝒪_X)` vanishing on `X ∖ Z`, and condition (b) of Stacks 0FBD holds
(`Stacks.Chow.LocalizedChernData.localizedChernChar_triangle`). -/
theorem supportedLocalizedChernChar_triangle (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)
    (T : Triangle (supportedPerfectDerivedCategory i))
    (hT : T ∈ distTriang (supportedPerfectDerivedCategory i)) :
    supportedLocalizedChernChar C a hX T.obj₂ =
      supportedLocalizedChernChar C a hX T.obj₁ + supportedLocalizedChernChar C a hX T.obj₃ :=
  funext fun p ↦ (supportedPerfectData C a i T.obj₁).localizedChernChar_triangle
    T.obj₁.property.1 T.obj₂.property.1 T.obj₃.property.1 _ _ _ hT
    (supportedPerfect_isZero_derivedPullback_compl i T.obj₁)
    (supportedPerfect_isZero_derivedPullback_compl i T.obj₃) (Or.inr (Or.inr (Or.inl hX))) p

end Data

section KMap

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **The localized Chern character map of Stacks 0FET**
`ch(Z ⟶ X, -) : K₀(D_{Z,perf}(𝒪_X)) ⟶ ∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`, for `X` with quasi-compact
irreducible components: `[E] ↦ ch(Z ⟶ X, E)`, extended additively. It is well defined because the
localized Chern character is additive along distinguished triangles (Lemma 0FBE,
`Stacks.Chow.supportedLocalizedChernChar_triangle`). -/
@[stacks 0FET]
def localizedChernCharKMap :
    K0 (supportedPerfectDerivedCategory i) →+
      ∀ p : ℕ, TensorProduct ℤ ℚ (BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl
        (p : ℤ)) :=
  K0.lift (supportedLocalizedChernChar C a hX) (supportedLocalizedChernChar_triangle C a hX)

/-- The localized Chern character map on a class: `[E] ↦ ch(Z ⟶ X, E)`. -/
@[simp, stacks 0FET "localized_chern_character_k_map: the generator [E] is sent to \
  ch(Z → X, E), and the map is the additive extension"]
theorem localizedChernCharKMap_cls (E : supportedPerfectDerivedCategory i) :
    localizedChernCharKMap C a hX (K0.cls E) = supportedLocalizedChernChar C a hX E :=
  K0.lift_cls _ _ E

/-- The localized Chern character map is the only additive map with `[E] ↦ ch(Z ⟶ X, E)`. -/
theorem localizedChernCharKMap_unique
    (φ : K0 (supportedPerfectDerivedCategory i) →+
      ∀ p : ℕ, TensorProduct ℤ ℚ (BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl
        (p : ℤ)))
    (hφ : ∀ E, φ (K0.cls E) = supportedLocalizedChernChar C a hX E) :
    φ = localizedChernCharKMap C a hX :=
  K0.lift_unique _ _ φ hφ

end KMap

/-! ### Values in `A^*(Z ⟶ X) ⊗ 𝐐` on a quasi-compact scheme -/

section DirectSum

/-- A function on `ℕ` vanishing from `N` on, as an element of the direct sum. -/
theorem coe_dfinsuppMk_range {M : ℕ → Type*} [∀ p, AddCommMonoid (M p)] (f : ∀ p, M p) (N : ℕ)
    (hf : ∀ p ≥ N, f p = 0) :
    ⇑(DFinsupp.mk (Finset.range N) fun p ↦ f p : DirectSum ℕ M) = f := by
  funext p
  rw [DFinsupp.mk_apply]
  split_ifs with hp
  · rfl
  · exact (hf p (by simpa using hp)).symm

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] [CompactSpace X]
  (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- `ch(Z ⟶ X, E)` as an element of `A^*(Z ⟶ X) ⊗ 𝐐 = ⨁_p A^p(Z ⟶ X) ⊗ 𝐐`, for `X`
quasi-compact. -/
def supportedLocalizedChernCharDirectSum (E : supportedPerfectDerivedCategory i) :
    DirectSum ℕ fun p : ℕ ↦
      TensorProduct ℤ ℚ (BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl (p : ℤ)) :=
  DFinsupp.mk (Finset.range (exists_supportedLocalizedChernChar_eq_zero C a hX E).choose)
    fun p ↦ supportedLocalizedChernChar C a hX E p

/-- The components of `Stacks.Chow.supportedLocalizedChernCharDirectSum` are those of
`ch(Z ⟶ X, E)`. -/
@[simp]
theorem coe_supportedLocalizedChernCharDirectSum (E : supportedPerfectDerivedCategory i) :
    ⇑(supportedLocalizedChernCharDirectSum C a hX E) = supportedLocalizedChernChar C a hX E :=
  coe_dfinsuppMk_range _ _ (exists_supportedLocalizedChernChar_eq_zero C a hX E).choose_spec

/-- The class in `⨁_p A^p(Z ⟶ X) ⊗ 𝐐` is additive along distinguished triangles. -/
theorem supportedLocalizedChernCharDirectSum_add (T : Triangle (supportedPerfectDerivedCategory i))
    (hT : T ∈ distTriang (supportedPerfectDerivedCategory i)) :
    supportedLocalizedChernCharDirectSum C a hX T.obj₂ =
      supportedLocalizedChernCharDirectSum C a hX T.obj₁ +
        supportedLocalizedChernCharDirectSum C a hX T.obj₃ :=
  DFunLike.coe_injective (by
    rw [DFinsupp.coe_add, coe_supportedLocalizedChernCharDirectSum,
      coe_supportedLocalizedChernCharDirectSum, coe_supportedLocalizedChernCharDirectSum,
      supportedLocalizedChernChar_triangle C a hX T hT])

/-- **The last sentence of Stacks 0FET: the localized Chern character map with values in
`A^*(Z ⟶ X) ⊗ 𝐐`** for `X` quasi-compact,
`K₀(D_{Z,perf}(𝒪_X)) ⟶ ⨁_p A^p(Z ⟶ X) ⊗ 𝐐`, `[E] ↦ ch(Z ⟶ X, E)`. Its components are those of
`Stacks.Chow.localizedChernCharKMap` (`Stacks.Chow.coe_localizedChernCharKMapDirectSum`). -/
def localizedChernCharKMapDirectSum :
    K0 (supportedPerfectDerivedCategory i) →+
      DirectSum ℕ fun p : ℕ ↦
        TensorProduct ℤ ℚ (BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl (p : ℤ)) :=
  K0.lift (supportedLocalizedChernCharDirectSum C a hX)
    (supportedLocalizedChernCharDirectSum_add C a hX)

/-- The value of `Stacks.Chow.localizedChernCharKMapDirectSum` on a class. -/
@[simp]
theorem localizedChernCharKMapDirectSum_cls (E : supportedPerfectDerivedCategory i) :
    localizedChernCharKMapDirectSum C a hX (K0.cls E) =
      supportedLocalizedChernCharDirectSum C a hX E :=
  K0.lift_cls _ _ E

/-- **The two forms of the localized Chern character map agree**: the components of
`Stacks.Chow.localizedChernCharKMapDirectSum` are those of `Stacks.Chow.localizedChernCharKMap`. -/
theorem coe_localizedChernCharKMapDirectSum (x : K0 (supportedPerfectDerivedCategory i)) :
    ⇑(localizedChernCharKMapDirectSum C a hX x) = localizedChernCharKMap C a hX x := by
  have h : (DFinsupp.coeFnAddMonoidHom.comp (localizedChernCharKMapDirectSum C a hX (i := i))) =
      localizedChernCharKMap C a hX :=
    K0.hom_ext fun E ↦ by
      rw [AddMonoidHom.comp_apply, DFinsupp.coeFnAddMonoidHom_apply,
        localizedChernCharKMapDirectSum_cls, coe_supportedLocalizedChernCharDirectSum,
        localizedChernCharKMap_cls]
  exact DFunLike.congr_fun h x

/-- If `X` is quasi-compact, the localized Chern character map takes values in `A^*(Z ⟶ X) ⊗ 𝐐`:
every value has only finitely many nonzero components. -/
@[stacks 0FET "localized_chern_character_k_finite_support: for X quasi-compact the image lies \
  in A^*(Z → X) ⊗ Q, every value having finitely many nonzero components"]
theorem exists_localizedChernCharKMap_eq_zero (x : K0 (supportedPerfectDerivedCategory i)) :
    ∃ N, ∀ p ≥ N, localizedChernCharKMap C a hX x p = 0 := by
  classical
  refine ⟨(localizedChernCharKMapDirectSum C a hX x).support.sup id + 1, fun p hp ↦ ?_⟩
  rw [← coe_localizedChernCharKMapDirectSum C a hX x, ← DFinsupp.notMem_support_iff]
  intro hmem
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

end DirectSum

/-! ### A larger closed subscheme -/

section LargerClosed

variable (C : ChowSituation.{u}) {X Z Z' : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X} [IsClosedImmersion i'] {j : Z ⟶ Z'}
  [IsClosedImmersion j] (hj : j ≫ i' = i) (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **Stacks 0FB7 for supported perfect objects.** Let `Z ⊆ Z' ⊆ X` be closed, with
`j : Z ⟶ Z'`, and let `E` be a perfect object supported on `Z`, read as `E'` in
`D_{Z',perf}(𝒪_X)`. Then `P_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ P_p(Z ⟶ X, E)` in `A^p(Z' ⟶ X)`, with `∘`
as in Stacks 0EPK. -/
theorem supportedLocalizedPowerSum_eq_bivariantProperPushforward
    (E : supportedPerfectDerivedCategory i) (E' : supportedPerfectDerivedCategory i')
    (hE : E'.obj = E.obj) (p : ℕ) :
    (supportedPerfectData C a i' E').localizedPowerSum
        (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E'.obj
          E'.property.1)
        (supportedPerfectData_isZeroOnComplement C a E') p =
      bivariantProperPushforwardOfInvertible C (i ≫ a) (i' ≫ a) a j i'
        (by rw [← Category.assoc, hj]) rfl p
        (((supportedPerfectData C a i E).localizedPowerSum
          (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj
          E.property.1)
          (supportedPerfectData_isZeroOnComplement C a E) p).congrHom hj.symm (by rw [hj])) := by
  obtain ⟨E₁, hE₁⟩ := E'
  obtain ⟨E₀, hE₀⟩ := E
  dsimp only at hE
  subst hE hj
  have key := LocalizedSituation.localizedPowerSum_withLargerClosed
    (S := supportedPerfectSituation C a hX ⟨E₁, hE₀⟩) (i' := i') (j := j) (hj := rfl)
    (supportedPerfectData_isZeroOnComplement C a ⟨E₁, hE₀⟩) p
  rw [(supportedPerfectSituation C a hX ⟨E₁, hE₀⟩).localizedPowerSum_toLocalizedChernData]
  exact ((supportedPerfectSituation C a hX ⟨E₁, hE₁⟩).localizedPowerSum_toLocalizedChernData
    (supportedPerfectData_isZeroOnComplement C a ⟨E₁, hE₁⟩) p).trans key

end LargerClosed

end Stacks.Chow

end
