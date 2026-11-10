module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `μ_n ≅ 𝐙/n𝐙` on the small étale site of a scheme over an algebraically closed field

Let `k` be an algebraically closed field, let `X` be a `k`-scheme and let `n ≥ 1` be invertible
in `k`. Then the sheaf `μ_n` of `n`-th roots of unity on Mathlib's small étale site of `X`,
`Stacks.Kummer.rootsOfUnitySheaf X n`, is isomorphic, as a sheaf of abelian groups with
coefficients in `AddCommGrpCat.{max (u + 1) v}`, to the constant sheaf with value `𝐙/n𝐙`.

The isomorphism is **not canonical**: it is induced by a group isomorphism `𝐙/n𝐙 ≅ μ_n(k)`, and
there are `φ(n)` of those. This is the sense in which [Stacks, Tag 03RQ] calls the resulting
identifications of `H^q_étale(X, 𝐙/n𝐙)` noncanonical.

## The argument

A choice of isomorphism `𝐙/n𝐙 ≅ μ_n(k)` turns each residue class `j` into a root of unity
`ζ^j ∈ k`, hence through the structure morphism into an invertible global function on every
étale `X`-scheme. This is a map from the constant presheaf with value `𝐙/n𝐙` to `μ_n`, and it is
locally bijective, so it becomes an isomorphism after sheafification.

*Local injectivity.* Two distinct classes give roots of unity whose difference is a unit of `k`;
if the two constants agree on an étale `X`-scheme `T`, then `1 = 0` on `T`, so `T` is empty and
covered by the empty family.

*Local surjectivity.* A root of unity `w` in the global functions of a `k`-scheme is Zariski
locally one of the `n` constants: Lagrange interpolation on the `n` roots of `Xⁿ - 1` writes
`w = ∑ ν e_ν` for a complete family of orthogonal idempotents `e_ν`, and on the basic open of an
`e_ν` with invertible germ the section `w` restricts to `ν`. An open cover of an étale
`X`-scheme is a covering family of the small étale site.

## Main definitions

* `AlgebraicGeometry.zmodAddEquivRootsOfUnity`: a (noncanonical) isomorphism `𝐙/n𝐙 ≅ μ_n(k)`.
* `Stacks.Kummer.constToRoots`: the comparison from the constant presheaf to `μ_n`.
* `Stacks.Kummer.constantSheafIsoRootsOfUnitySheaf`: **`𝐙/n𝐙 ≅ μ_n` on `X_étale`.**

## Implementation notes

The ring-theoretic lemmas of the namespace `AlgebraicGeometry.ConstantRootsOfUnity` (the choice
of roots of unity and the Zariski-local constancy of a root of unity) serve the comparison on
Mathlib's small étale site at the étale coefficient universe.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-- **A (noncanonical) isomorphism `𝐙/n𝐙 ≅ μ_n(k)`** for `k` algebraically closed and `n ≥ 1`
invertible in `k`: both groups are cyclic of order `n`. -/
def zmodAddEquivRootsOfUnity (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n)
    (hnk : IsUnit (n : k)) :
    ZMod n ≃+ Additive (rootsOfUnity n k) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (n : k) := ⟨hnk.ne_zero⟩
  apply addEquivOfAddCyclicCardEq
  change Nat.card (ZMod n) = Nat.card (rootsOfUnity n k)
  rw [Nat.card_zmod, HasEnoughRootsOfUnity.natCard_rootsOfUnity]

namespace ConstantRootsOfUnity

/-- The root of unity of `k` attached to a residue class by
`AlgebraicGeometry.zmodAddEquivRootsOfUnity`. -/
def zeta (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))
    (j : ZMod n) : kˣ :=
  ((Additive.toMul (zmodAddEquivRootsOfUnity k n hn hnk j) : rootsOfUnity n k) : kˣ)

/-- Distinct residue classes give distinct roots of unity. -/
theorem zeta_injective (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n)
    (hnk : IsUnit (n : k)) :
    Function.Injective (fun j : ZMod n => ((zeta k n hn hnk j : kˣ) : k)) := fun _ _ h =>
  (zmodAddEquivRootsOfUnity k n hn hnk).injective
    (Additive.toMul.injective (Subtype.ext (Units.ext h)))

/-- Every `n`-th root of unity of `k` is attached to a residue class. -/
theorem exists_zeta_eq (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n)
    (hnk : IsUnit (n : k)) {x : k} (hx : x ^ n = 1) :
    ∃ j : ZMod n, ((zeta k n hn hnk j : kˣ) : k) = x := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hxu : (Units.mk0 x hx0) ∈ rootsOfUnity n k := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hx)
  refine ⟨(zmodAddEquivRootsOfUnity k n hn hnk).symm
    (Additive.ofMul (⟨Units.mk0 x hx0, hxu⟩ : rootsOfUnity n k)), ?_⟩
  change (((Additive.toMul ((zmodAddEquivRootsOfUnity k n hn hnk)
    ((zmodAddEquivRootsOfUnity k n hn hnk).symm
      (Additive.ofMul (⟨Units.mk0 x hx0, hxu⟩ : rootsOfUnity n k)))) :
      rootsOfUnity n k) : kˣ) : k) = x
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- A scheme whose ring of global functions has `1 = 0` is empty. -/
theorem isEmpty_of_one_eq_zero {Y : Scheme.{u}} (h : (1 : Γ(Y, ⊤)) = 0) : IsEmpty Y := by
  refine ⟨fun y => ?_⟩
  have h1 : (1 : Y.presheaf.stalk y) = 0 := by
    have h2 := congrArg (Y.presheaf.germ ⊤ y trivial).hom h
    rwa [map_one, map_zero] at h2
  exact one_ne_zero h1

/-- A ring receiving a homomorphism from a field which kills a nonzero element is zero. -/
theorem one_eq_zero_of_map_eq_zero {K R : Type u} [Field K] [CommRing R]
    (θ : K →+* R) {x : K} (hx : x ≠ 0) (h : θ x = 0) : (1 : R) = 0 := by
  rw [← map_one θ, ← mul_inv_cancel₀ hx, map_mul, h, zero_mul]

/-- **A root of unity in the global functions of a `k`-scheme is Zariski locally one of the `n`
constants.** Lagrange interpolation on the `n` roots of `Xⁿ - 1` in `k` writes `w` as a
combination `∑ ν · e_ν` of a complete family of orthogonal idempotents, and on the basic open
`D(e_ν)` around a point where `e_ν` has invertible germ the section `w` restricts to the
constant `ν`. -/
theorem exists_basicOpen_res_eq_const
    {k : Type u} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (Y : Scheme.{u}) (φ : k →+* Γ(Y, ⊤)) (w : Γ(Y, ⊤)) (hw : w ^ n = 1) (y : Y) :
    ∃ (V : Y.Opens) (ξ : k), y ∈ V ∧ ξ ^ n = 1 ∧
      (Y.presheaf.map (homOfLE (le_top (a := V))).op).hom w =
        (Y.presheaf.map (homOfLE (le_top (a := V))).op).hom (φ ξ) := by
  classical
  set S : Finset k := Polynomial.nthRootsFinset n (1 : k) with hSdef
  have hinj : Set.InjOn (id : k → k) S := fun a _ b _ h => h
  have hcard : S.card = n := hζ.card_nthRootsFinset
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hcard]; exact hn
  set ev : Polynomial k →+* Γ(Y, ⊤) := Polynomial.eval₂RingHom φ w with hev
  have hevX : ev Polynomial.X = w := by simp [hev]
  have hev0 : ev (Polynomial.X ^ n - 1) = 0 := by
    rw [map_sub, map_pow, hevX, map_one, hw, sub_self]
  set e : k → Γ(Y, ⊤) := fun ν => ev (Lagrange.basis S id ν) with hedef
  have hsum : ∑ ν ∈ S, e ν = 1 := by
    rw [hedef, ← map_sum, Lagrange.sum_basis hinj hSne, map_one]
  have hdvd : ∀ ν ∈ S, ∀ μ ∈ S, ν ≠ μ →
      (Polynomial.X ^ n - 1 : Polynomial k) ∣
        Lagrange.basis S id ν * Lagrange.basis S id μ := by
    intro ν hν μ hμ hne
    have hbase : ∀ σ ∈ S, Lagrange.basis S id σ =
        (∏ j ∈ S.erase σ, Polynomial.C (σ - j)⁻¹) *
          ∏ j ∈ S.erase σ, (Polynomial.X - Polynomial.C j) := by
      intro σ _
      rw [Lagrange.basis, ← Finset.prod_mul_distrib]
      rfl
    have hprod : (Polynomial.X ^ n - 1 : Polynomial k) =
        ∏ ν ∈ S, (Polynomial.X - Polynomial.C ν) :=
      Polynomial.X_pow_sub_one_eq_prod hn hζ
    have hν' : ν ∈ S.erase μ := Finset.mem_erase.2 ⟨hne, hν⟩
    have h1 : (Polynomial.X ^ n - 1 : Polynomial k) ∣
        (∏ j ∈ S.erase μ, (Polynomial.X - Polynomial.C j)) *
          ∏ j ∈ S.erase ν, (Polynomial.X - Polynomial.C j) := by
      rw [hprod, ← Finset.mul_prod_erase S _ hν]
      exact mul_dvd_mul (Finset.dvd_prod_of_mem _ hν') dvd_rfl
    rw [hbase ν hν, hbase μ hμ]
    have h2 : ((∏ j ∈ S.erase ν, Polynomial.C (ν - j)⁻¹) *
          ∏ j ∈ S.erase ν, (Polynomial.X - Polynomial.C j)) *
        ((∏ j ∈ S.erase μ, Polynomial.C (μ - j)⁻¹) *
          ∏ j ∈ S.erase μ, (Polynomial.X - Polynomial.C j)) =
        ((∏ j ∈ S.erase ν, Polynomial.C (ν - j)⁻¹) *
          ∏ j ∈ S.erase μ, Polynomial.C (μ - j)⁻¹) *
        ((∏ j ∈ S.erase μ, (Polynomial.X - Polynomial.C j)) *
          ∏ j ∈ S.erase ν, (Polynomial.X - Polynomial.C j)) := by
      ring
    rw [h2]
    exact Dvd.dvd.mul_left h1 _
  have horth : ∀ ν ∈ S, ∀ μ ∈ S, ν ≠ μ → e ν * e μ = 0 := by
    intro ν hν μ hμ hne
    obtain ⟨q, hq⟩ := hdvd ν hν μ hμ hne
    rw [hedef, ← map_mul, hq, map_mul, hev0, zero_mul]
  have hwsum : w = ∑ ν ∈ S, φ ν * e ν := by
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hn.ne' : 1 ≤ n) with h1 | h2
    · have hn1 : n = 1 := h1.symm
      have hS1 : S = {1} := by
        apply Finset.eq_singleton_iff_unique_mem.2
        refine ⟨(Polynomial.mem_nthRootsFinset hn 1).2 (by simp), ?_⟩
        intro x hx
        have := (Polynomial.mem_nthRootsFinset hn 1).1 hx
        rwa [hn1, pow_one] at this
      have hw1 : w = 1 := by rw [← pow_one w, ← hn1]; exact hw
      have hone : ∑ ν ∈ S, φ ν * e ν = 1 := by
        rw [hS1]
        simp only [Finset.sum_singleton, map_one, one_mul]
        have h := hsum
        rw [hS1] at h
        simpa using h
      rw [hw1, hone]
    · have hdeg : (Polynomial.X : Polynomial k).degree < S.card := by
        rw [hcard, Polynomial.degree_X]
        exact_mod_cast h2
      have hXint : (Polynomial.X : Polynomial k) =
          Lagrange.interpolate S id (fun ν => Polynomial.X.eval (id ν)) :=
        Lagrange.eq_interpolate hinj hdeg
      have h := congrArg ev hXint
      rw [hevX] at h
      rw [h, Lagrange.interpolate_apply, map_sum]
      refine Finset.sum_congr rfl ?_
      intro ν _
      rw [map_mul]
      simp [hedef, hev]
  have hexists : ∃ ν ∈ S, y ∈ Y.basicOpen (e ν) := by
    by_contra hc
    simp only [not_exists, not_and] at hc
    have hone : (1 : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      have hg := congrArg (Y.presheaf.germ ⊤ y trivial).hom hsum
      rw [map_sum, map_one] at hg
      rw [← hg]
      refine Ideal.sum_mem _ ?_
      intro ν hν
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hc ν hν ((Y.mem_basicOpen_top (e ν) y).2 hu)
    exact mem_nonunits_iff.1
      ((IsLocalRing.mem_maximalIdeal (1 : Y.presheaf.stalk y)).1 hone) isUnit_one
  obtain ⟨ν, hν, hyν⟩ := hexists
  refine ⟨Y.basicOpen (e ν), ν, hyν,
    (Polynomial.mem_nthRootsFinset hn 1).1 hν, ?_⟩
  set V := Y.basicOpen (e ν) with hV
  set ρ : Γ(Y, ⊤) →+* Γ(Y, V) :=
    (Y.presheaf.map (homOfLE (le_top (a := V))).op).hom with hρ
  have hunit : IsUnit (ρ (e ν)) := Y.toRingedSpace.isUnit_res_basicOpen (U := ⊤) (e ν)
  have hidem : e ν * e ν = e ν := by
    have h : e ν * ∑ μ ∈ S, e μ = e ν * e ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_single_of_mem ν hν ?_
      intro μ hμ hne
      exact horth ν hν μ hμ (Ne.symm hne)
    rw [hsum, mul_one] at h
    exact h.symm
  have hρν : ρ (e ν) = 1 := by
    have h2 : ρ (e ν) * ρ (e ν) = ρ (e ν) * 1 := by
      rw [mul_one, ← map_mul, hidem]
    exact hunit.mul_left_cancel h2
  have hρμ : ∀ μ ∈ S, μ ≠ ν → ρ (e μ) = 0 := by
    intro μ hμ hne
    have h : ρ (e μ) = ρ (e μ) * ρ (e ν) := by rw [hρν, mul_one]
    rw [h, ← map_mul, horth μ hμ ν hν hne, map_zero]
  rw [hwsum, map_sum]
  refine (Finset.sum_eq_single_of_mem ν hν ?_).trans ?_
  · intro μ hμ hne
    rw [map_mul, hρμ μ hμ hne, mul_zero]
  · rw [map_mul, hρν, mul_one]

/-- The form of `AlgebraicGeometry.ConstantRootsOfUnity.exists_basicOpen_res_eq_const` used on
the small étale site: a morphism landing in the open where `w` is the constant `ξ` pulls `w`
back to that constant. -/
theorem exists_open_pullback_eq_const
    {k : Type u} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (Y : Scheme.{u}) (φ : k →+* Γ(Y, ⊤)) (w : Γ(Y, ⊤)) (hw : w ^ n = 1) (y : Y) :
    ∃ (V : Y.Opens) (ξ : k), y ∈ V ∧ ξ ^ n = 1 ∧
      ∀ (Z : Scheme.{u}) (ψ : Z ⟶ Y), (∀ z : Z, ψ z ∈ V) →
        (Scheme.Γ.map ψ.op).hom w = (Scheme.Γ.map ψ.op).hom (φ ξ) := by
  obtain ⟨V, ξ, hyV, hξ, hres⟩ := exists_basicOpen_res_eq_const hn hζ Y φ w hw y
  refine ⟨V, ξ, hyV, hξ, fun Z ψ hψ => ?_⟩
  have he : (ψ ⁻¹ᵁ (⊤ : Y.Opens)) ≤ ψ ⁻¹ᵁ V := fun z _ => hψ z
  have key : Scheme.Γ.map ψ.op =
      Y.presheaf.map (homOfLE (le_top (a := V))).op ≫ ψ.appLE V (ψ ⁻¹ᵁ ⊤) he := by
    rw [Scheme.Hom.map_appLE, Scheme.Γ_map_op, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [key]
  change (ψ.appLE V (ψ ⁻¹ᵁ ⊤) he).hom ((Y.presheaf.map _).hom w) = _
  rw [hres]
  rfl

end ConstantRootsOfUnity

end AlgebraicGeometry

namespace Stacks.Kummer

open AlgebraicGeometry AlgebraicGeometry.ConstantRootsOfUnity

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))

/-- The structure homomorphism of the base field into the global functions of an étale
`X`-scheme. -/
def structHom (U : X.Etale) : k →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.hom ≫ f).appTop).hom

omit [IsAlgClosed k] in
/-- The structure homomorphisms are compatible with restriction along morphisms of the small
étale site. -/
theorem structHom_naturality {U V : X.Etale} (g : V ⟶ U) (x : k) :
    g.left.appTop.hom (structHom k f U x) = structHom k f V x := by
  simp only [structHom, ← MorphismProperty.Over.w g, Category.assoc, Scheme.Hom.comp_appTop]
  rfl

/-- The constant roots of unity, as an additive homomorphism from `𝐙/n𝐙` (raised to the étale
coefficient universe) to the sections of `𝐆_m` over an étale `X`-scheme. -/
def constToUnitsApp (U : X.Etale) :
    ULift.{max (u + 1) v} (ZMod n) →+
      ToType ((multiplicativeSheaf.{u, v} X).obj.obj (op U)) :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (MonoidHom.toAdditive
      ((Units.map (structHom k f U).toMonoidHom).comp (rootsOfUnity n k).subtype))).comp
    ((zmodAddEquivRootsOfUnity k n hn hnk).toAddMonoidHom.comp
      (AddEquiv.ulift (α := ZMod n)).toAddMonoidHom)

/-- The value of `Stacks.Kummer.constToUnitsApp` is the constant root of unity. -/
theorem constToUnitsApp_eq (U : X.Etale) (j : ZMod n) :
    constToUnitsApp.{u, v} k f n hn hnk U (ULift.up j) =
      ofUnit (Units.map (structHom k f U).toMonoidHom (zeta k n hn hnk j)) :=
  rfl

/-- The comparison from the constant presheaf with value `𝐙/n𝐙` to `𝐆_m`, sending a residue
class to the corresponding constant root of unity. -/
def constToUnits :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))) ⟶
      (multiplicativeSheaf.{u, v} X).obj where
  app U := AddCommGrpCat.ofHom (constToUnitsApp.{u, v} k f n hn hnk U.unop)
  naturality U V g := by
    ext ⟨j⟩
    change constToUnitsApp.{u, v} k f n hn hnk V.unop (ULift.up j) =
      (multiplicativeSheaf.{u, v} X).obj.map g (constToUnitsApp.{u, v} k f n hn hnk U.unop
        (ULift.up j))
    rw [constToUnitsApp_eq, constToUnitsApp_eq, ← Quiver.Hom.op_unop g, map_ofUnit]
    congr 1
    ext
    exact (structHom_naturality k f g.unop _).symm

/-- The constant roots of unity are killed by the `n`-th power map, so the comparison to `𝐆_m`
factors through `μ_n`. -/
theorem constToUnits_comp_powMap :
    constToUnits.{u, v} k f n hn hnk ≫ (powMap.{u, v} X n).hom = 0 := by
  ext U ⟨j⟩
  change n • (constToUnitsApp.{u, v} k f n hn hnk U.unop (ULift.up j)) = 0
  rw [← map_nsmul]
  have hx : (n • (ULift.up j : ULift.{max (u + 1) v} (ZMod n))) = 0 := by
    apply ULift.ext
    change n • j = (0 : ZMod n)
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [hx, map_zero]

/-- **The comparison from the constant presheaf with value `𝐙/n𝐙` to `μ_n`**, sending a residue
class to the corresponding constant root of unity. -/
def constToRoots :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))) ⟶
      (rootsOfUnitySheaf.{u, v} X n).obj :=
  kernel.lift ((sheafToPresheaf _ _).map (powMap.{u, v} X n))
      (constToUnits.{u, v} k f n hn hnk) (constToUnits_comp_powMap.{u, v} k f n hn hnk) ≫
    (PreservesKernel.iso (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (powMap.{u, v} X n)).inv

/-- The comparison to `μ_n` followed by the inclusion `μ_n ⟶ 𝐆_m` is the comparison to `𝐆_m`. -/
theorem constToRoots_comp_ι :
    constToRoots.{u, v} k f n hn hnk ≫ (rootsOfUnityι.{u, v} X n).hom =
      constToUnits.{u, v} k f n hn hnk := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
  let p := powMap.{u, v} X n
  have h1 : (PreservesKernel.iso E p).inv ≫ E.map (kernel.ι p) = kernel.ι (E.map p) := by
    rw [Iso.inv_comp_eq, PreservesKernel.iso_hom]
    exact (kernelComparison_comp_ι p E).symm
  change (kernel.lift (E.map p) (constToUnits.{u, v} k f n hn hnk)
      (constToUnits_comp_powMap.{u, v} k f n hn hnk) ≫
      (PreservesKernel.iso E p).inv) ≫ E.map (kernel.ι p) = _
  rw [Category.assoc, h1]
  exact kernel.lift_ι _ _ _

/-- A section of `μ_n` is determined by the invertible global function underlying it. -/
theorem rootsOfUnityι_app_injective (U : X.Etale) :
    Function.Injective ((rootsOfUnityι.{u, v} X n).hom.app (op U)) := fun _ _ hab =>
  (rootsOfUnitySection_bijective.{u, v} X n (op U)).injective (Subtype.ext (congrArg
    (fun z : ToType ((multiplicativeSheaf.{u, v} X).obj.obj (op U)) => Additive.toMul z.down) hab))

/-- Two residue classes with the same constant root of unity on an étale `X`-scheme agree
locally: distinct classes give roots of unity whose difference is a unit of `k`, so they can
only agree over an empty object, which is covered by the empty family. -/
theorem constToUnits_isLocallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constToUnits.{u, v} k f n hn hnk) := by
  refine ⟨fun {T} a b hab => ?_⟩
  obtain rfl | hab' := eq_or_ne a b
  · simp
  · have hne : ((zeta k n hn hnk a.down : kˣ) : k) -
        ((zeta k n hn hnk b.down : kˣ) : k) ≠ 0 := fun h =>
      hab' (ULift.ext (zeta_injective k n hn hnk (sub_eq_zero.1 h)))
    have hval : structHom k f T.unop ((zeta k n hn hnk a.down : kˣ) : k) =
        structHom k f T.unop ((zeta k n hn hnk b.down : kˣ) : k) :=
      congrArg (fun z : ToType ((multiplicativeSheaf.{u, v} X).obj.obj T) =>
        ((Additive.toMul z.down : (Γ(T.unop.left, ⊤))ˣ) : Γ(T.unop.left, ⊤))) hab
    have hzero : (1 : Γ(T.unop.left, ⊤)) = 0 := by
      refine one_eq_zero_of_map_eq_zero (structHom k f T.unop) hne ?_
      rw [map_sub, hval, sub_self]
    exact X.smallEtaleTopology.superset_covering bot_le
      (smallEtale_bot_mem X (isEmpty_of_one_eq_zero hzero))

/-- On sections, the inclusion `μ_n ⟶ 𝐆_m` sends the comparison to `μ_n` to the comparison
to `𝐆_m`. -/
private theorem rootsOfUnityι_app_constToRoots_app (T : X.Etaleᵒᵖ)
    (x : (Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))) |>.obj T) :
    (rootsOfUnityι.{u, v} X n).hom.app T ((constToRoots.{u, v} k f n hn hnk).app T x) =
      (constToUnits.{u, v} k f n hn hnk).app T x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (constToRoots_comp_ι.{u, v} k f n hn hnk) T) x

/-- The comparison to `μ_n` is locally injective, since the comparison to `𝐆_m` is and the
inclusion `μ_n ⟶ 𝐆_m` is injective on sections. -/
theorem constToRoots_isLocallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constToRoots.{u, v} k f n hn hnk) := by
  refine ⟨fun {T} x y hxy => ?_⟩
  refine (constToUnits_isLocallyInjective.{u, v} k f n hn hnk).equalizerSieve_mem x y ?_
  exact (rootsOfUnityι_app_constToRoots_app.{u, v} k f n hn hnk T x).symm.trans
    ((congrArg ((rootsOfUnityι.{u, v} X n).hom.app T) hxy).trans
      (rootsOfUnityι_app_constToRoots_app.{u, v} k f n hn hnk T y))

/-- A root of unity in the sections over an étale `X`-scheme is, on a covering family of the
small étale site, one of the `n` constants: the loci where it is constant form an open cover,
and an open cover is a covering family. -/
theorem exists_cover_const_of_pow_eq_one {ζ : k} (hζ : IsPrimitiveRoot ζ n) (T : X.Etale)
    (w : Γ(T.left, ⊤)) (hw : w ^ n = 1) :
    ∃ (I : Type (u + 1)) (W : I → X.Etale) (a : ∀ i, W i ⟶ T) (jj : I → ZMod n),
      Sieve.ofArrows W a ∈ X.smallEtaleTopology T ∧
        ∀ i, (a i).left.appTop.hom w =
          structHom k f (W i) ((zeta k n hn hnk (jj i) : kˣ) : k) := by
  classical
  choose V ξ hyV hξ hpull using
    fun y => exists_open_pullback_eq_const hn hζ T.left (structHom k f T) w hw y
  have hVcover : TopologicalSpace.IsOpenCover V :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hyV x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtaleScheme_openCoverData X V hVcover
  choose jj hjj using fun i : I => exists_zeta_eq k n hn hnk (hξ (r i))
  refine ⟨I, W, a, jj, hcover, fun i => ?_⟩
  rw [hjj i, ← structHom_naturality k f (a i)]
  exact hpull (r i) _ (a i).left (hmaps i)

/-- Every section of `μ_n` is locally a constant root of unity. -/
theorem constToRoots_isLocallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constToRoots.{u, v} k f n hn hnk) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : k, IsPrimitiveRoot ζ n := by
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have : NeZero (n : k) := ⟨hnk.ne_zero⟩
    exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n
  refine ⟨fun {T} s => ?_⟩
  let r := rootsOfUnitySection.{u, v} X n (op T) s
  have hwn : ((r.1 : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, r.2, Units.val_one]
  obtain ⟨I, W, a, jj, hcover, heq⟩ :=
    exists_cover_const_of_pow_eq_one.{u} k f n hn hnk hζ T _ hwn
  refine X.smallEtaleTopology.superset_covering ?_ hcover
  intro Z g hg
  obtain ⟨i, g', rfl⟩ := (Sieve.mem_ofArrows_iff W a g).mp hg
  apply (Presheaf.imageSieve (constToRoots.{u, v} k f n hn hnk) s).downward_closed
  refine ⟨ULift.up (jj i), ?_⟩
  apply rootsOfUnityι_app_injective.{u, v} n (W i)
  have hstep3 : (rootsOfUnityι.{u, v} X n).hom.app (op (W i))
        ((rootsOfUnitySheaf.{u, v} X n).obj.map (a i).op s) =
      (multiplicativeSheaf.{u, v} X).obj.map (a i).op
        ((rootsOfUnityι.{u, v} X n).hom.app (op T) s) :=
    NatTrans.naturality_apply (rootsOfUnityι.{u, v} X n).hom (a i).op s
  rw [rootsOfUnityι_app_constToRoots_app.{u, v} k f n hn hnk (op (W i)) (ULift.up (jj i)),
    hstep3, rootsOfUnityι_app_eq_ofUnit, map_ofUnit]
  change ofUnit _ = ofUnit _
  congr 1
  ext
  exact (heq i).symm

include f hn hnk in
/-- **`𝐙/n𝐙 ≅ μ_n` as sheaves of abelian groups on the small étale site.** Let `k` be an
algebraically closed field, `X` a `k`-scheme and `n ≥ 1` invertible in `k`. The constant sheaf
with value `𝐙/n𝐙` on the small étale site of `X`, at the étale coefficient universe, is
isomorphic to the sheaf `μ_n` of `n`-th roots of unity.

The isomorphism depends on the choice of isomorphism `𝐙/n𝐙 ≅ μ_n(k)` made by
`AlgebraicGeometry.zmodAddEquivRootsOfUnity`. -/
@[sga "4 XVI 3.10" "special case",
  sga "4½ Arcata 2.2.4" "special case",
  sga "4½ Arcata 3.3.5" "more general",
  sga "4½ Arcata 6.1" "special case",
  sga "5 VI 3.2" "Local freeness clause"]
def constantSheafIsoRootsOfUnitySheaf :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n))) ≅
      rootsOfUnitySheaf.{u, v} X n := by
  let J := X.smallEtaleTopology
  have hα : IsIso ((presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).map
      (constToRoots.{u, v} k f n hn hnk)) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective _).mpr
      ⟨constToRoots_isLocallyInjective.{u, v} k f n hn hnk,
        constToRoots_isLocallySurjective.{u, v} k f n hn hnk⟩
  exact @asIso _ _ _ _ ((presheafToSheaf J AddCommGrpCat.{max (u + 1) v}).map
      (constToRoots.{u, v} k f n hn hnk)) hα ≪≫
    asIso ((sheafificationAdjunction J AddCommGrpCat.{max (u + 1) v}).counit.app
      (rootsOfUnitySheaf.{u, v} X n))

include f hn hnk in
/-- **A constant sheaf whose value is cyclic of order `n` is isomorphic to `μ_n`** on the small
étale site of a scheme over an algebraically closed field in which `n` is invertible. -/
@[sga "4 XIX 3.3" "special case", sga "4½ Arcata 3.3.5" "more general"]
theorem nonempty_constantSheaf_iso_rootsOfUnitySheaf
    (E : AddCommGrpCat.{max (u + 1) v}) (hE : Nonempty (E ≃+ ZMod n)) :
    Nonempty ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E ≅
      rootsOfUnitySheaf.{u, v} X n) := by
  obtain ⟨e⟩ := hE
  exact ⟨(constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).mapIso
      (AddEquiv.toAddCommGrpIso (Y := AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))
        (e.trans (AddEquiv.ulift : ULift.{max (u + 1) v} (ZMod n) ≃+ ZMod n).symm)) ≪≫
    constantSheafIsoRootsOfUnitySheaf.{u, v} (k := k) (f := f) (n := n) (hn := hn) (hnk := hnk)⟩

end Stacks.Kummer

end
