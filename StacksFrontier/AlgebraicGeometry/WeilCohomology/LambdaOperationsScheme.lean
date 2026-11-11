module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceAsImage
public import StacksFrontier.AlgebraicGeometry.Modules.WedgeDegreeZeroMono
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# The lambda operations on `K₀(Vect(X))` of every scheme

Let `X` be a scheme. `StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations` constructs
the operations `λ^r : K₀(Vect(X)) → K₀(Vect(X))` of Stacks Tag 0FIC out of the single relation

`[⋀ⁿ ℱ] = ∑_{i = 0}^{n} [⋀ⁱ ℰ] [⋀^{n - i} 𝒢]`

along a short exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free `𝒪_X`-modules, which it
records as `AlgebraicGeometry.VectorBundleKZero.ExteriorPowersData`. **This file proves that
relation on every scheme** (`exteriorPowersData`), following the source: the short exact sequence
is a two-step filtration of `ℱ`, which induces on `⋀ⁿ ℱ` the filtration

`Fᵖ(⋀ⁿ ℱ) = im(⋀ᵖ ℰ ⊗ ⋀^{n - p} ℱ ⟶ ⋀ⁿ ℱ)`,  `p = 0, …, n`,

with subquotients `⋀ᵖ ℰ ⊗ ⋀^{n - p} 𝒢`. With the relation in hand, Tag 0FIC is stated with no
hypothesis and with the compatibility with pullback read against the pullback ring map
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` (`exists_lambdaOperations_pullbackRingHom`).

## The argument

The filtration and its graded pieces are those of
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` and
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece`, applied to the short exact sequence
at hand. Three facts about them are used, each of which needs the sequence to split locally — which
it does, the quotient `𝒢` being finite locally free
(`AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree`):

* `F⁰ = ⋀ⁿ ℱ` (`SheafOfModules.epi_prodWedgeHom_zero_left`, no splitting needed);
* for `p + 1 + m = n`, `Fᵖ / Fᵖ⁺¹ ≅ ⋀ᵖ ℰ ⊗ ⋀^{m + 1} 𝒢`
  (`SheafOfModules.cokernelOfLEIsoExteriorGraded` and
  `SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split`);
* `Fⁿ ≅ ⋀ⁿ ℰ ⊗ ⋀⁰ ℱ ≅ ⋀ⁿ ℰ`, the wedge-product morphism being a monomorphism at complementary
  degree zero (`SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split`).

Finite local freeness of the steps is then proved by induction on `p`: `Fᵖ⁺¹` is the kernel of the
epimorphism `Fᵖ ⟶ Fᵖ / Fᵖ⁺¹` between finite locally free modules. The relation in `K₀(Vect(X))`
is the telescoping sum of the classes of the short exact sequences
`0 → Fᵖ⁺¹ → Fᵖ → ⋀ᵖ ℰ ⊗ ⋀^{n - p} 𝒢 → 0`, the class of a tensor product being the product of the
classes (Tag 0FDK).

## Main results

* `AlgebraicGeometry.VectorBundleKZero.classOf_exteriorPower_shortExact_of_isFiniteLocallyFree`:
  **the filtration relation** `[⋀ⁿ ℱ] = ∑ [⋀ⁱ ℰ] [⋀^{n - i} 𝒢]`.
* `AlgebraicGeometry.VectorBundleKZero.exteriorPowersData`: the geometric input of Tag 0FIC holds
  on every scheme.
* `AlgebraicGeometry.VectorBundleKZero.lambdaOperation_add`:
  `λ^r(a + b) = ∑_{i ≤ r} λ^i(a) λ^{r - i}(b)`.
* `AlgebraicGeometry.VectorBundleKZero.exists_lambdaOperations_pullbackRingHom`: **Tag 0FIC**,
  with no hypothesis.

## References

* [Stacks Project, Tag 0FIC](https://stacks.math.columbia.edu/tag/0FIC)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FiniteLocallyFree

attribute [local instance] SheafOfModules.monoidalSheaves
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X : Scheme.{u}} {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)

/-- **A short exact sequence of `𝒪_X`-modules with finite locally free quotient splits over an
open neighbourhood of every point**, in the open-subspace spelling of restriction that the
globalized comparisons of the wedge filtration consume. -/
@[ega "0 5.4.9" "EGA 0, special case"]
theorem exists_nonempty_splitting_openSubspaceShortComplex
    (hS : (ShortComplex.mk f g w).ShortExact)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (_root_.SheafOfModules.openSubspaceShortComplex
      (X := X.toRingedSpace) U (T := ShortComplex.mk f g w)).Splitting := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (ShortComplex.mk f g w).X₃ := isFiniteLocallyFree_toSheaf hG
  exact (Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree _ hS x).imp
    fun U h => ⟨h.1, h.2.map fun sp =>
      _root_.SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor U sp⟩

/-- The `(p, q)` wedge-product morphism `⋀ᵖ ℰ ⊗ ⋀^q ℱ ⟶ ⋀^{p+q} ℱ` along `f` and the identity of
`ℱ`, for the chosen packages of exterior algebras. -/
abbrev exteriorFiltrationWedgeHom (p q : ℕ) :=
  _root_.SheafOfModules.prodWedgeHom (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ F)
    (SheafOfModules.algebras _ F) f (𝟙 F) p q

/-- The image of `exteriorFiltrationWedgeHom f p q`, the step `Fᵖ` of the filtration of
`⋀^{p+q} ℱ`, as a subobject. -/
abbrev exteriorFiltrationStepSubobject (p q : ℕ) :=
  @imageSubobject X.Modules _ _ _ (exteriorFiltrationWedgeHom f p q)
    (HasImages.has_image (exteriorFiltrationWedgeHom f p q))

/-- The step `Fᵖ = im(⋀ᵖ ℰ ⊗ ⋀^q ℱ ⟶ ⋀^{p+q} ℱ)` of the filtration of `⋀^{p+q} ℱ`. -/
abbrev exteriorFiltrationStep (p q : ℕ) : X.Modules :=
  Subobject.underlying.obj (exteriorFiltrationStepSubobject f p q)

variable {f g w}

/-- Along an isomorphism `M ≅ N`, finite local freeness of `N` gives that of `M` and equality of
the classes. -/
private theorem isFiniteLocallyFree_and_classOf_eq_of_iso {M N : X.Modules} (e : M ≅ N)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M ∧ classOf X M = classOf X N :=
  have h := @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ e.symm hN
  ⟨h, classOf_eq_of_iso e h⟩

/-- **One step of the filtration.** In total degree `n = k + 1 + m`, if `Fᵏ` is finite locally free
then so is `Fᵏ⁺¹`, and `[Fᵏ] = [Fᵏ⁺¹] + [⋀ᵏ ℰ] [⋀^{m+1} 𝒢]`: the quotient `Fᵏ / Fᵏ⁺¹` is
`⋀ᵏ ℰ ⊗ ⋀^{m+1} 𝒢`. -/
theorem exteriorFiltrationStep_succ (k m : ℕ) (hS : (ShortComplex.mk f g w).ShortExact)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (ih : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (exteriorFiltrationStep f k (1 + m))) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (exteriorFiltrationStep f (k + 1) m) ∧
      classOf X (exteriorFiltrationStep f k (1 + m)) =
        classOf X (exteriorFiltrationStep f (k + 1) m) +
        classOf X (Scheme.Modules.exteriorPower E (k : ℤ)) *
          classOf X (Scheme.Modules.exteriorPower G ((m + 1 : ℕ) : ℤ)) := by
  have hle := _root_.SheafOfModules.imageSubobject_prodWedgeHom_succ_le
    (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ F) f k m
  have hiso := _root_.SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split
    (T := ShortComplex.mk f g w)
    (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ G) (SheafOfModules.algebras _ F)
    hS.exact hS.epi_g k m (exists_nonempty_splitting_openSubspaceShortComplex f g w hS hG)
  let e := _root_.SheafOfModules.cokernelOfLEIsoExteriorGraded
    (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ F) f k m ≪≫
    (@asIso _ _ _ _ (_root_.SheafOfModules.exteriorGradedQuotientComparison
      (T := ShortComplex.mk f g w)
      (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ G) (SheafOfModules.algebras _ F)
      hS.exact hS.epi_g k m) hiso).symm
  let c := imageSubobjectCompIso (exteriorFiltrationWedgeHom f k (1 + m))
    (eqToHom (congrArg (SheafOfModules.algebras _ F).exterior.piece
      (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))
  let S := ShortComplex.mk (Subobject.ofLE _ _ hle) (cokernel.π (Subobject.ofLE _ _ hle))
    (cokernel.condition _)
  have hSE : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hEk := Scheme.Modules.isFiniteLocallyFree_exteriorPower E k hE
  have hGm := Scheme.Modules.isFiniteLocallyFree_exteriorPower G (m + 1) hG
  have hT := @isFiniteLocallyFree_tensorObj X _ _ hEk hGm
  obtain ⟨h2, hc2⟩ := isFiniteLocallyFree_and_classOf_eq_of_iso c ih
  obtain ⟨h3, hc3⟩ := isFiniteLocallyFree_and_classOf_eq_of_iso e hT
  have h1 : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁ :=
    isFiniteLocallyFree_ofSheaf (isFiniteLocallyFree_X₁_of_shortExact hSE
      (isFiniteLocallyFree_toSheaf h2) (isFiniteLocallyFree_toSheaf h3))
  have hcl := @classOf_shortExact X _ _ _ S.f S.g hSE.mono_f hSE.epi_g S.zero h1 h2 h3 hSE.exact
  refine ⟨h1, ?_⟩
  calc classOf X (exteriorFiltrationStep f k (1 + m)) = classOf X S.X₂ :=
        hc2.symm
    _ = classOf X S.X₁ + classOf X S.X₃ := hcl
    _ = classOf X (exteriorFiltrationStep f (k + 1) m) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X
          (Scheme.Modules.exteriorPower E (k : ℤ))
          (Scheme.Modules.exteriorPower G ((m + 1 : ℕ) : ℤ))) := by
      rw [hc3]; rfl
    _ = _ := by rw [classOf_mul _ _ hEk hGm]

/-- **The last step of the filtration** is `Fⁿ ≅ ⋀ⁿ ℰ ⊗ ⋀⁰ ℱ ≅ ⋀ⁿ ℰ`: it is finite locally free and
`[Fⁿ] = [⋀ⁿ ℰ]`. -/
theorem exteriorFiltrationStep_zero_right (n : ℕ) (hS : (ShortComplex.mk f g w).ShortExact)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (exteriorFiltrationStep f n 0) ∧
      classOf X (exteriorFiltrationStep f n 0) =
        classOf X (Scheme.Modules.exteriorPower E (n : ℤ)) := by
  have hmono : Mono (exteriorFiltrationWedgeHom f n 0) :=
    _root_.SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split (T := ShortComplex.mk f g w)
      (SheafOfModules.algebras _ E) (SheafOfModules.algebras _ F) n 0 rfl
      (exists_nonempty_splitting_openSubspaceShortComplex f g w hS hG)
  let c : exteriorFiltrationStep f n 0 ≅ _ :=
    imageSubobjectIso (exteriorFiltrationWedgeHom f n 0) ≪≫
    imageMonoIsoSource (exteriorFiltrationWedgeHom f n 0)
  have hEn := Scheme.Modules.isFiniteLocallyFree_exteriorPower E n hE
  have hF0 := isFiniteLocallyFree_exteriorPower_zero X F
  have hT := @isFiniteLocallyFree_tensorObj X _ _ hEn hF0
  obtain ⟨h, hc⟩ := isFiniteLocallyFree_and_classOf_eq_of_iso c hT
  refine ⟨h, hc.trans ?_⟩
  calc _ = classOf X (Scheme.Modules.tensorObjRingedSpace X
        (Scheme.Modules.exteriorPower E (n : ℤ)) (Scheme.Modules.exteriorPower F 0)) := rfl
    _ = _ := by rw [← classOf_mul _ _ hEn hF0, classOf_exteriorPower_zero, mul_one]

/-- **The first step of the filtration** is all of `⋀ⁿ ℱ`: it is finite locally free and
`[F⁰] = [⋀ⁿ ℱ]`. -/
theorem exteriorFiltrationStep_zero_left (n : ℕ)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (exteriorFiltrationStep f 0 n) ∧
      classOf X (exteriorFiltrationStep f 0 n) =
        classOf X (Scheme.Modules.exteriorPower F (n : ℤ)) := by
  have h₁ : Epi (C := X.Modules) (exteriorFiltrationWedgeHom f 0 n) :=
    _root_.SheafOfModules.epi_prodWedgeHom_zero_left _ _ f n
  have h₂ : Epi (C := X.Modules) (exteriorFiltrationStepSubobject f 0 n).arrow :=
    @epi_of_epi_fac X.Modules _ _ _ _ _ _ _ h₁
      (imageSubobject_arrow_comp (exteriorFiltrationWedgeHom f 0 n))
  have : IsIso (C := X.Modules) (exteriorFiltrationStepSubobject f 0 n).arrow :=
    @isIso_of_mono_of_epi X.Modules _ _ _ _ _ (Subobject.arrow_mono _) h₂
  let c : exteriorFiltrationStep f 0 n ≅ Scheme.Modules.exteriorPower F (n : ℤ) :=
    asIso (exteriorFiltrationStepSubobject f 0 n).arrow ≪≫
      eqToIso (congrArg (fun j : ℕ => (SheafOfModules.algebras _ F).exteriorPower j)
        (Nat.zero_add n))
  exact isFiniteLocallyFree_and_classOf_eq_of_iso c
    (Scheme.Modules.isFiniteLocallyFree_exteriorPower F n hF)

/-- **The filtration relation of Tag 0FIC.** Along a short exact sequence
`0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules on a scheme,
`[⋀ⁿ ℱ] = ∑_{i = 0}^{n} [⋀ⁱ ℰ] [⋀^{n - i} 𝒢]` in `K₀(Vect(X))`. -/
@[sga "6 V 2.2.1" "special case"]
theorem classOf_exteriorPower_shortExact_of_isFiniteLocallyFree (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) (n : ℕ) :
    classOf X (Scheme.Modules.exteriorPower F (n : ℤ)) =
      ∑ i ∈ Finset.range (n + 1),
        classOf X (Scheme.Modules.exteriorPower E (i : ℤ)) *
          classOf X (Scheme.Modules.exteriorPower G ((n - i : ℕ) : ℤ)) := by
  have hS : (ShortComplex.mk f g w).ShortExact := { exact := hex }
  have key : ∀ k, k ≤ n →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (exteriorFiltrationStep f k (n - k)) ∧
        classOf X (Scheme.Modules.exteriorPower F (n : ℤ)) =
          (∑ i ∈ Finset.range k,
            classOf X (Scheme.Modules.exteriorPower E (i : ℤ)) *
              classOf X (Scheme.Modules.exteriorPower G ((n - i : ℕ) : ℤ))) +
          classOf X (exteriorFiltrationStep f k (n - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, Finset.sum_range_zero, zero_add]
      exact ⟨(exteriorFiltrationStep_zero_left n hF).1,
        (exteriorFiltrationStep_zero_left n hF).2.symm⟩
    | succ k ih =>
      intro hk
      obtain ⟨h₁, h₂⟩ := ih (by omega)
      obtain ⟨m, hm⟩ : ∃ m, n - k = 1 + m := ⟨n - k - 1, by omega⟩
      rw [hm] at h₁ h₂
      obtain ⟨h₃, h₄⟩ := exteriorFiltrationStep_succ k m hS hE hG h₁
      rw [show n - (k + 1) = m by omega, Finset.sum_range_succ, h₂, h₄,
        show n - k = m + 1 by omega]
      exact ⟨h₃, by abel⟩
  obtain ⟨-, h⟩ := key n le_rfl
  rw [h, Nat.sub_self, (exteriorFiltrationStep_zero_right n hS hE hG).2, Finset.sum_range_succ,
    Nat.sub_self]
  simp

/-- **The geometric input of Tag 0FIC holds on every scheme**: its single field is
`classOf_exteriorPower_shortExact_of_isFiniteLocallyFree`. -/
@[sga "6 V 2.2.1" "special case"]
theorem exteriorPowersData (X : Scheme.{u}) : ExteriorPowersData X :=
  ⟨fun f g w hE hF hG hmono hepi hex n =>
    classOf_exteriorPower_shortExact_of_isFiniteLocallyFree f g w hE hF hG hmono hepi hex n⟩

/-- `λ^r(a + b) = ∑_{i ≤ r} λ^i(a) λ^{r - i}(b)`: the total class `c` turns sums into products. -/
theorem lambdaOperation_add (h : ExteriorPowersData X) (r : ℕ) (a b : VectorBundleKZero X) :
    lambdaOperation h r (a + b) =
      ∑ i ∈ Finset.range (r + 1), lambdaOperation h i a * lambdaOperation h (r - i) b := by
  simp only [lambdaOperation, map_add, toMul_add, Units.val_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **Stacks Project, Tag 0FIC.** Let `X` be a scheme. There are maps
`λ^r : K₀(Vect(X)) → K₀(Vect(X))` which send `[ℰ]` to `[⋀^r ℰ]` when `ℰ` is a finite locally free
`𝒪_X`-module and which are compatible with pullbacks: for every morphism of schemes `f : Y ⟶ X`,
`λ^r ∘ f^* = f^* ∘ λ^r`, where `f^*` is the pullback ring map `pullbackRingHom f`.

The family is `X ↦ lambdaOperation (exteriorPowersData X)`, so nothing is assumed: the filtration
relation the construction consumes is `exteriorPowersData`, and the pullback map is the one
constructed in `StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback`. -/
@[stacks 0FIC "there exist maps `λ^r : K₀(Vect(X)) → K₀(Vect(X))`, `r : ℕ`, for every scheme \
  `X`, with `λ^r [ℰ] = [⋀^r ℰ]` for each finite locally free `𝒪_X`-module `ℰ` and \
  `λ^r (f^* a) = f^* (λ^r a)` for every morphism `f : Y ⟶ X`, `f^*` being `pullbackRingHom f`",
  sga "6 X 1.2" "clause (1.2.1)"]
theorem exists_lambdaOperations_pullbackRingHom :
    ∃ lam : ∀ X : Scheme.{u}, ℕ → VectorBundleKZero X → VectorBundleKZero X,
      (∀ (X : Scheme.{u}) (r : ℕ) (E : X.Modules),
          IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
            lam X r (classOf X E) = classOf X (Scheme.Modules.exteriorPower E (r : ℤ))) ∧
        (∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (r : ℕ) (a : VectorBundleKZero X),
          lam Y r (pullbackRingHom f a) = pullbackRingHom f (lam X r a)) :=
  ⟨fun X => lambdaOperation (exteriorPowersData X),
    fun X r E hE => lambdaOperation_classOf (exteriorPowersData X) r E hE,
    fun {_X Y} f r a => lambdaOperation_pullback f (exteriorPowersData Y) (exteriorPowersData _)
      (pullbackRingHom f) (pullbackRingHom_classOf f) (isFiniteLocallyFree_pullback f) r a⟩

end AlgebraicGeometry.VectorBundleKZero

end
