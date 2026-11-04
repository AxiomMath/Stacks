module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.KrullDimension.Module
public import StacksFrontier.RingTheory.Length.Finiteness
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Removing maximal-ideal-power torsion

Let `(A, 𝔪)` be a Noetherian local ring and `M` a finite `A`-module. The submodule `M[𝔪^∞]` of
elements annihilated by some power of `𝔪` is Mathlib's `Ideal.primaryComponent M 𝔪`. It has
finite length; it is nonzero as soon as `M` is nonzero of depth zero; the quotient
`M' = M/M[𝔪^∞]` has positive depth; and, when the support of `M` has positive dimension, passing
to `M'` does not change that dimension.

For a complex `ω` the tautological sequence `0 → M[𝔪^∞] → M → M' → 0` gives, by the
contravariant exact sequence of `Ext(-, ω)`, the two exactness statements in degrees zero and
one that the source uses: the image of `Ext^0(M', ω)` is the kernel of restriction to
`Ext^0(M[𝔪^∞], ω)`, and the image of that restriction is the kernel of the connecting map into
`Ext^1(M', ω)`. When `ω` is a normalized dualizing complex, `Ext^0(-, ω)` on finite-length
modules is Matlis duality, and `Dualizing.NaturalMatlisExtComparison` packages such an
identification together with its naturality, so that the two exactness statements can be read
with the Matlis dual `Hom_A(M[𝔪^∞], E)` in the middle.

## Main definitions

* `Dualizing.maximalIdealPowerTorsion` — the submodule killed elementwise by powers of `𝔪`,
  i.e. `Ideal.primaryComponent M 𝔪`.
* `Dualizing.quotientMaximalIdealPowerTorsion` — the quotient by that submodule.
* `Dualizing.extComparison` — the canonical contravariant `Ext` map induced by the quotient.
* `Dualizing.extRestriction` — restriction to the torsion submodule.
* `Dualizing.extPrecomp` — contravariant `Ext` functoriality for a linear map.
* `Dualizing.torsionShortComplex` — the tautological short complex of the torsion submodule.
* `Dualizing.extBoundary` — the connecting map of that short exact sequence.
* `Dualizing.NaturalMatlisExtComparison` — a natural degree-zero `Ext`-level Matlis duality on
  finite-length modules.

## Main results

* `Dualizing.torsionShortComplex_shortExact` — the tautological sequence is short exact.
* `Dualizing.nontrivial_maximalIdealPowerTorsion` — depth zero forces nonzero `𝔪`-power
  torsion.
* `Dualizing.isFiniteLength_maximalIdealPowerTorsion` — the `𝔪`-power torsion of a finite
  module has finite length.
* `Dualizing.depth_quotientMaximalIdealPowerTorsion_pos` — the quotient has positive depth.
* `Dualizing.supportDim_quotientMaximalIdealPowerTorsion` — the quotient has the same support
  dimension.
* `Dualizing.exact_extComparison_matlisRestriction` and
  `Dualizing.exact_matlisRestriction_boundary` — the two exactness statements of the four-term
  sequence in degrees zero and one.

## Implementation notes

`Ext` is the `ℤ`-graded `Hom` of the derived category, `DerivedCategory.Ext X Y i`, since the
second argument is a complex rather than a module; neither Mathlib nor this library packages a
long exact sequence at that generality, so the two exactness statements are derived directly
from `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished` and
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`, once for the triangle itself and once
for its double rotation. The comparison maps are not arbitrary isomorphisms: they are
precomposition with the image in the derived category of the quotient map, of the inclusion, and
the connecting morphism `singleδ` respectively. The module universe is independent of the
universe of the ring, and the derived category is taken at the standard model, as the
normalization predicate `Dualizing.IsNormalizedDualizingComplex` is.

## References

* [Stacks Project, Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Lemma 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The submodule consisting of elements annihilated by some power of the maximal ideal. -/
abbrev maximalIdealPowerTorsion {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] : Submodule A M :=
  Ideal.primaryComponent M (maximalIdeal A)

/-- The quotient by the maximal-ideal-power torsion submodule. -/
abbrev quotientMaximalIdealPowerTorsion {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] :=
  M ⧸ (maximalIdealPowerTorsion M : Submodule A M)

/-! ### The tautological short exact sequence -/

/-- The tautological short complex formed by the power-torsion submodule, the original
module, and the quotient. -/
def torsionShortComplex {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] :
    ShortComplex (ModuleCat.{max v u} A) :=
  ModuleCat.shortComplexOfCompEqZero
    (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))
    (Submodule.mkQ (maximalIdealPowerTorsion (A := A) M))
    (by ext x; simp)

/-- The tautological sequence of the torsion submodule and its quotient is short exact. -/
lemma torsionShortComplex_shortExact {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] :
    (torsionShortComplex (A := A) M).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (LinearMap.exact_subtype_mkQ (maximalIdealPowerTorsion (A := A) M))
    (maximalIdealPowerTorsion (A := A) M).injective_subtype
    (Submodule.mkQ_surjective _)

/-! ### The three contravariant `Ext` maps -/

/-- The canonical map on Ext induced contravariantly by the quotient onto the module modulo its
maximal-ideal-power torsion. -/
def extComparison {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (quotientMaximalIdealPowerTorsion (A := A) M))) ω i →+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) ω i where
  toFun x :=
    (ShiftedHom.mk₀ 0 rfl
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.mkQ (maximalIdealPowerTorsion (A := A) M))))).comp x
          (add_zero i)
  map_zero' := ShiftedHom.comp_zero _ _ _
  map_add' x y := ShiftedHom.comp_add _ x y _

/-- The canonical restriction from Ext of `M` to Ext of its maximal-ideal-power torsion. -/
def extRestriction {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) ω i →+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) ω i where
  toFun x :=
    (ShiftedHom.mk₀ 0 rfl
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))))).comp x
          (add_zero i)
  map_zero' := ShiftedHom.comp_zero _ _ _
  map_add' x y := ShiftedHom.comp_add _ x y _

/-- Contravariant Ext functoriality for a linear map of modules. -/
def extPrecomp {A : Type u} [CommRing A]
    {N N' : Type (max v u)} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (f : N →ₗ[A] N')
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A N')) ω i →+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A N)) ω i where
  toFun x :=
    (ShiftedHom.mk₀ 0 rfl
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom f))).comp x (add_zero i)
  map_zero' := ShiftedHom.comp_zero _ _ _
  map_add' x y := ShiftedHom.comp_add _ x y _

/-- The canonical connecting map on Ext attached to the torsion short exact sequence. -/
def extBoundary {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) ω 0 →+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (quotientMaximalIdealPowerTorsion (A := A) M))) ω 1 where
  toFun x := ShiftedHom.comp
    (ShortComplex.ShortExact.singleδ (torsionShortComplex_shortExact M)) x (zero_add 1)
  map_zero' := ShiftedHom.comp_zero _ _ _
  map_add' x y := ShiftedHom.comp_add _ x y _

/-- A degree-zero Matlis comparison on all finite-length modules, natural in the module.
This is the Ext-level form of the natural isomorphism of [Stacks, Tag 0A7Q]. -/
structure NaturalMatlisExtComparison (A : Type u) [CommRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (E : Type (max v u)) [AddCommGroup E] [Module A E] where
  /-- For each finite-length `N`, an isomorphism `Ext⁰(N, ω) ≃+ Hom_A(N, E)`. -/
  equiv : ∀ (N : Type (max v u)) [AddCommGroup N] [Module A N],
    IsFiniteLength A N →
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A N)) ω 0 ≃+ (N →ₗ[A] E))
  /-- The isomorphisms `equiv` commute with precomposition by `A`-linear maps `N → N'`. -/
  naturality : ∀ (N N' : Type (max v u)) [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (hN : IsFiniteLength A N)
    (hN' : IsFiniteLength A N') (f : N →ₗ[A] N')
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A N')) ω 0),
    equiv N hN (extPrecomp f ω 0 x) = (equiv N' hN' x).comp f

/-! ### The module-theoretic statements -/

section Algebra

/-- The maximal-ideal-power torsion submodule is itself maximal-ideal-power torsion. -/
private lemma isIPowerTorsion_maximalIdealPowerTorsion
    {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] :
    IsIPowerTorsion A (maximalIdealPowerTorsion (A := A) M) (maximalIdeal A) := by
  intro x
  obtain ⟨n, hn⟩ :=
    (Ideal.primaryComponent_mem M (maximalIdeal A) x.1).mp x.2
  refine ⟨n + 1, n.succ_pos, fun a ha => Subtype.ext ?_⟩
  exact (Submodule.mem_torsionBySet_iff _ _).mp hn
    ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) ha⟩

/-- An `M`-regular element of `I` witnesses `1 ≤ depth_I(M)`. -/
private lemma one_le_depth_of_isSMulRegular {A : Type u} [CommRing A] (I : Ideal A)
    (X : Type (max v u)) [AddCommGroup X] [Module A X] [Module.Finite A X]
    {x : A} (hx : x ∈ I) (hreg : IsSMulRegular X x) :
    1 ≤ Module.depth A I X := by
  rw [Module.depth_eq_iSup_isWeaklyRegular_length]
  refine le_iSup₂_of_le [x] ⟨?_, ?_⟩ (by simp)
  · simpa using hx
  · exact RingTheory.Sequence.IsWeaklyRegular.cons hreg
      (RingTheory.Sequence.IsWeaklyRegular.nil ..)

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- If an associated prime contains the maximal ideal, some nonzero element is killed by it. -/
private lemma exists_ne_zero_smul_eq_zero_of_maximalIdeal_le_associatedPrimes
    (X : Type (max v u)) [AddCommGroup X] [Module A X] {q : Ideal A}
    (hq : q ∈ associatedPrimes A X) (hle : maximalIdeal A ≤ q) :
    ∃ x : X, x ≠ 0 ∧ ∀ a ∈ maximalIdeal A, a • x = 0 := by
  have hqm : q = maximalIdeal A :=
    le_antisymm (IsLocalRing.le_maximalIdeal hq.isPrime.ne_top) hle
  obtain ⟨-, x, hx⟩ := Submodule.isAssociatedPrime_iff.mp hq
  refine ⟨x, ?_, fun a ha => ?_⟩
  · intro hx0
    refine (maximalIdeal.isMaximal A).ne_top ?_
    rw [← hqm, hx, hx0]
    exact eq_top_iff.mpr fun a _ => Submodule.mem_colon_singleton.mpr (by simp)
  · have hmem : a ∈ Submodule.colon (⊥ : Submodule A X) {x} := hx ▸ hqm ▸ ha
    simpa using Submodule.mem_colon_singleton.mp hmem

/-- For a nonzero finite module of depth zero, its maximal-ideal-power torsion is nonzero. -/
lemma nontrivial_maximalIdealPowerTorsion
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (hdepth : Module.depth A (maximalIdeal A) M = 0) :
    Nontrivial (maximalIdealPowerTorsion (A := A) M) := by
  have hnoreg : ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular M x := by
    rintro ⟨x, hx, hreg⟩
    have h1 := one_le_depth_of_isSMulRegular (A := A) (maximalIdeal A) M hx hreg
    rw [hdepth] at h1
    exact absurd h1 (by simp)
  rw [Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le _ _
    (associatedPrimes.finite A M)] at hnoreg
  push Not at hnoreg
  obtain ⟨p, hp, hle⟩ := hnoreg
  obtain ⟨x, hx0, hkill⟩ :=
    exists_ne_zero_smul_eq_zero_of_maximalIdeal_le_associatedPrimes (A := A) M hp hle
  have hmem : x ∈ maximalIdealPowerTorsion (A := A) M := by
    refine (Ideal.primaryComponent_mem M (maximalIdeal A) x).mpr ⟨1, ?_⟩
    refine (Submodule.mem_torsionBySet_iff _ _).mpr ?_
    rintro ⟨a, ha⟩
    exact hkill a (by simpa using ha)
  exact nontrivial_of_ne (⟨x, hmem⟩ : maximalIdealPowerTorsion (A := A) M) 0
    fun h => hx0 (congrArg Subtype.val h)

/-- The maximal-ideal-power torsion in a finite module has finite length. -/
lemma isFiniteLength_maximalIdealPowerTorsion
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsFiniteLength A (maximalIdealPowerTorsion (A := A) M) := by
  have hmFG : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hfin : Module.Finite A (maximalIdealPowerTorsion (A := A) M) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hsupp := (isIPowerTorsion_iff_support_subset A
      (maximalIdealPowerTorsion (A := A) M) (maximalIdeal A) hmFG).mp
    (isIPowerTorsion_maximalIdealPowerTorsion (A := A) M)
  obtain ⟨n, hn⟩ := (main_theorem_00l6 (M := (maximalIdealPowerTorsion (A := A) M))
    (maximalIdeal A)).mpr hsupp
  exact Module.length_ne_top_iff.mp
    (ne_of_lt (length_lt_top_of_pow_smul_eq_bot (maximalIdeal A) hmFG n hn))

/-- Quotienting by maximal-ideal-power torsion gives a module of positive depth. -/
lemma depth_quotientMaximalIdealPowerTorsion_pos
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    0 < Module.depth A (maximalIdeal A)
      (quotientMaximalIdealPowerTorsion (A := A) M) := by
  have hmFG : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hzero := torsionBySet_quotient_primaryComponent_eq_bot
    (maximalIdeal A) hmFG M
  have hnotmem : ∀ q ∈ associatedPrimes A (quotientMaximalIdealPowerTorsion (A := A) M),
      ¬ maximalIdeal A ≤ q := by
    intro q hq hle
    obtain ⟨x, hx0, hkill⟩ :=
      exists_ne_zero_smul_eq_zero_of_maximalIdeal_le_associatedPrimes (A := A)
        (quotientMaximalIdealPowerTorsion (A := A) M) hq hle
    have hxmem : x ∈ Submodule.torsionBySet A
        (quotientMaximalIdealPowerTorsion (A := A) M) (maximalIdeal A : Set A) :=
      (Submodule.mem_torsionBySet_iff _ _).mpr fun a => hkill a a.2
    exact hx0 (by simpa [hzero] using hxmem)
  obtain ⟨x, hx, hreg⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le (maximalIdeal A)
      (quotientMaximalIdealPowerTorsion (A := A) M)
      (associatedPrimes.finite A _)).mpr hnotmem
  exact lt_of_lt_of_le zero_lt_one
    (one_le_depth_of_isSMulRegular (A := A) (maximalIdeal A) _ hx hreg)

/-- The support dimension of the maximal-ideal-power torsion is at most zero. -/
private lemma supportDim_maximalIdealPowerTorsion_le_zero
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.supportDim A (maximalIdealPowerTorsion (A := A) M) ≤ 0 := by
  have hfin : Module.Finite A (maximalIdealPowerTorsion (A := A) M) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  rcases subsingleton_or_nontrivial (maximalIdealPowerTorsion (A := A) M) with hsub | hnt
  · rw [Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  · have hsupp : Module.support A (maximalIdealPowerTorsion (A := A) M) =
        {IsLocalRing.closedPoint A} :=
      support_point.mpr (isFiniteLength_maximalIdealPowerTorsion A M)
    have : Unique
        (Module.support A (maximalIdealPowerTorsion (A := A) M)) := by
      rw [hsupp]
      exact Set.uniqueSingleton _
    rw [Module.supportDim]
    exact le_of_eq Order.krullDim_eq_zero

/-- Removing maximal-ideal-power torsion preserves the dimension of the support. -/
lemma supportDim_quotientMaximalIdealPowerTorsion
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hdim : 0 < Module.supportDim A M) :
    Module.supportDim A (quotientMaximalIdealPowerTorsion (A := A) M) =
      Module.supportDim A M := by
  have hmax := Module.supportDim_of_exact
    (LinearMap.exact_subtype_mkQ (maximalIdealPowerTorsion (A := A) M))
    (maximalIdealPowerTorsion (A := A) M).injective_subtype
    (Submodule.mkQ_surjective (maximalIdealPowerTorsion (A := A) M))
  have hlt : Module.supportDim A (maximalIdealPowerTorsion (A := A) M) <
      Module.supportDim A M :=
    lt_of_le_of_lt (supportDim_maximalIdealPowerTorsion_le_zero A M) hdim
  rcases max_choice (Module.supportDim A (maximalIdealPowerTorsion (A := A) M))
      (Module.supportDim A (quotientMaximalIdealPowerTorsion (A := A) M)) with h | h
  · exact absurd (hmax.trans h).symm (ne_of_lt hlt)
  · exact (hmax.trans h).symm

end Algebra

/-! ### The contravariant `Ext` exact sequence of the torsion sequence -/

section ExtSequence

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A composite through `F.map (a ≫ b)` vanishes as soon as `d ≫ F.map a` does. -/
private lemma comp_functor_map_comp_eq_zero {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms E] (F : D ⥤ E) {X Y Z : D} (a : X ⟶ Y) (b : Y ⟶ Z)
    {P W : E} (d : P ⟶ F.obj X) (s : F.obj Z ⟶ W)
    (h : d ≫ F.map a = 0) :
    d ≫ F.map (a ≫ b) ≫ s = 0 := by
  rw [F.map_comp, ← Category.assoc, ← Category.assoc, h, Limits.zero_comp, Limits.zero_comp]

/-- `extComparison M ω i` is precomposition with the image of the quotient map
`M → M / maximalIdealPowerTorsion M`. -/
lemma extComparison_apply (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (x : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (quotientMaximalIdealPowerTorsion (A := A) M)) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) i).obj ω) :
    extComparison (A := A) M ω i x =
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.mkQ (maximalIdealPowerTorsion (A := A) M))) ≫ x := by
  change (ShiftedHom.mk₀ 0 rfl _).comp x (add_zero i) = _
  exact ShiftedHom.mk₀_comp _ _ _ _

/-- `extRestriction M ω i` is precomposition with the image of the inclusion
`maximalIdealPowerTorsion M → M`. -/
lemma extRestriction_apply (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (x : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) i).obj ω) :
    extRestriction (A := A) M ω i x =
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))) ≫ x := by
  change (ShiftedHom.mk₀ 0 rfl _).comp x (add_zero i) = _
  exact ShiftedHom.mk₀_comp _ _ _ _

/-- `extBoundary M ω` is precomposition with the connecting morphism of the torsion short exact
sequence, followed by the identification of the shift by `1` with the shift by `0 + 1`. -/
lemma extBoundary_apply (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (x : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M)) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (0 : ℤ)).obj ω) :
    extBoundary (A := A) M ω x =
      (torsionShortComplex_shortExact (A := A) M).singleδ ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map x ≫
          (shiftFunctorAdd' (DerivedCategory (ModuleCat.{max v u} A)) 0 1 1
            (zero_add 1)).inv.app ω :=
  rfl

/-- `Hom(-, X)` applied to the torsion sequence is exact at the middle term. -/
private lemma yoneda_exact_aux (M : Type (max v u)) [AddCommGroup M] [Module A M]
    {X : DerivedCategory (ModuleCat.{max v u} A)}
    (f : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M) ⟶ X)
    (hf : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))) ≫ f = 0) :
    ∃ g, f = (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.mkQ (maximalIdealPowerTorsion (A := A) M))) ≫ g :=
  Triangle.yoneda_exact₂ _
    (torsionShortComplex_shortExact (A := A) M).singleTriangle_distinguished f hf

/-- Exactness of the contravariant `Ext` sequence at `Ext^0(M, ω)`: the image of
`Ext^0(M/M[𝔪^∞], ω)` is the kernel of restriction to `Ext^0(M[𝔪^∞], ω)`. -/
lemma exact_extComparison_extRestriction
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    Function.Exact (extComparison (A := A) M ω 0) (extRestriction (A := A) M ω 0) := by
  have h0 : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.mkQ (maximalIdealPowerTorsion (A := A) M))) = 0 :=
    comp_distTriang_mor_zero₁₂ _
      (torsionShortComplex_shortExact (A := A) M).singleTriangle_distinguished
  intro x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := yoneda_exact_aux (A := A) M x
      ((extRestriction_apply (A := A) M ω 0 x).symm.trans hx)
    exact ⟨g, (extComparison_apply.{u, v} (A := A) M ω 0 g).trans hg.symm⟩
  · rintro ⟨z, rfl⟩
    refine (extRestriction_apply (A := A) M ω 0 _).trans ?_
    rw [extComparison_apply, ← Category.assoc, h0, Limits.zero_comp]

/-- Exactness of the contravariant `Ext` sequence at `Ext^0(M[𝔪^∞], ω)`: the image of
restriction is the kernel of the connecting map into `Ext^1(M/M[𝔪^∞], ω)`. -/
lemma exact_extRestriction_extBoundary
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    Function.Exact (extRestriction (A := A) M ω 0) (extBoundary (A := A) M ω) := by
  have hδ : (torsionShortComplex_shortExact (A := A) M).singleδ ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M)))) = 0 :=
    comp_distTriang_mor_zero₃₁ _
      (torsionShortComplex_shortExact (A := A) M).singleTriangle_distinguished
  intro x
  constructor
  · intro hx
    have hx' : (torsionShortComplex_shortExact (A := A) M).singleδ ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map x = 0 := by
      rw [← cancel_mono ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{max v u} A)) 0 1 1
        (zero_add 1)).inv.app ω), Category.assoc, Limits.zero_comp]
      exact (extBoundary_apply (A := A) M ω x).symm.trans hx
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _
      (rot_of_distTriang _ (rot_of_distTriang _
        (torsionShortComplex_shortExact (A := A) M).singleTriangle_distinguished))
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map x) hx'
    obtain ⟨y, hy⟩ :=
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map_surjective
        (X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M))
        (Y := (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (0 : ℤ)).obj ω) g
    have hg' : (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map x =
        (-(shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
            (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))))) ≫
          (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map y := by
      rwa [hy]
    have key : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
        (ModuleCat.ofHom (Submodule.subtype (maximalIdealPowerTorsion (A := A) M))) ≫ (-y) = x := by
      refine (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).map_injective ?_
      rw [Functor.map_comp, Functor.map_neg, Preadditive.comp_neg, ← Preadditive.neg_comp, hg']
    exact ⟨-y, (extRestriction_apply.{u, v} (A := A) M ω 0 (-y)).trans key⟩
  · rintro ⟨y, rfl⟩
    rw [extRestriction_apply.{u, v}, extBoundary_apply]
    exact comp_functor_map_comp_eq_zero _ _ y _ _ hδ

end ExtSequence

/-! ### The two exactness statements read through a Matlis comparison -/

/-- The image of degree-zero Ext of the quotient is exactly the kernel of restriction to the
Matlis dual of the removed torsion. -/
lemma exact_extComparison_matlisRestriction
    (A : Type u) (M E : Type (max v u))
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    [AddCommGroup E] [Module A E]
    (c : NaturalMatlisExtComparison A ω E) :
    let e := c.equiv (maximalIdealPowerTorsion (A := A) M)
      (isFiniteLength_maximalIdealPowerTorsion A M)
    Function.Exact (extComparison (A := A) M ω 0)
      (e.toAddMonoidHom.comp (extRestriction M ω 0)) := by
  intro e y
  exact e.map_eq_zero_iff.trans (exact_extComparison_extRestriction (A := A) M ω y)

/-- The image of restriction to the Matlis dual is exactly the kernel of the canonical
connecting map into degree-one Ext of the quotient. -/
lemma exact_matlisRestriction_boundary
    (A : Type u) (M E : Type (max v u))
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    [AddCommGroup E] [Module A E]
    (c : NaturalMatlisExtComparison A ω E) :
    let e := c.equiv (maximalIdealPowerTorsion (A := A) M)
      (isFiniteLength_maximalIdealPowerTorsion A M)
    Function.Exact (e.toAddMonoidHom.comp (extRestriction M ω 0))
      ((extBoundary M ω).comp e.symm.toAddMonoidHom) := by
  intro e b
  refine Iff.trans (exact_extRestriction_extBoundary (A := A) M ω (e.symm b)) ?_
  exact ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [← ha]⟩⟩

end Dualizing

end
