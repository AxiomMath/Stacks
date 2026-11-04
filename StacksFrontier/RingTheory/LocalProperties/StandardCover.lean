module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

universe u

/-! ## Setup

Stacks 00EO ("Zariski-local properties of modules and algebras") packages eight
statements. They are formalised here in the canonical Mathlib form: the localised
module / ring / algebra at `f i` is the canonical `LocalizedModule (Submonoid.powers (f i)) M`
/ `Localization.Away (f i)` / `Localization.Away (algebraMap R S (f i))`, and the
induced map on a localisation of `M` is `LocalizedModule.map (Submonoid.powers (f i))`.
The hypothesis `Ideal.span (Set.range f) = ⊤` is exactly the Stacks condition
`(f₁, …, fₙ) = R`.
-/

/-- **Stacks 00EO (1).** If each canonical localisation
`LocalizedModule (powers (f i)) M` is the zero module and the `f i` generate the
unit ideal, then `M` itself is the zero module. -/
@[stacks 00EO "(1)"]
theorem Module.subsingleton_of_localizationSpan_range
    {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Subsingleton (LocalizedModule (Submonoid.powers (f i)) M)) :
    Subsingleton M :=
  subsingleton_of_forall_eq 0 fun m => Module.eq_zero_of_isLocalized_span (Set.range f) hf
    (fun r => LocalizedModule.Away r.1 M) (fun _ => LocalizedModule.mkLinearMap _ M) m
    (Set.forall_subtype_range_iff.2 fun i => @Subsingleton.elim _ (h i) _ _)

/-- **Stacks 00EO (2).** If each canonical localisation `M_{f i}` is finite over
`R_{f i}` and the `f i` generate the unit ideal, then `M` is a finite `R`-module. -/
@[stacks 00EO "(2)", sga "4½ Arcata 1.4.2" "(ii) fin type, Zariski"]
theorem Module.Finite.of_localizationSpan_range
    {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Module.Finite (Localization.Away (f i))
                            (LocalizedModule (Submonoid.powers (f i)) M)) :
    Module.Finite R M :=
  Module.Finite.of_localizationSpan (Set.range f) hf (Set.forall_subtype_range_iff.mpr h)

/-- **Stacks 00EO (4).** If `φ : M →ₗ[R] N` is bijective after canonical
localisation at each `f i` and the `f i` generate the unit ideal, then `φ` is
bijective. -/
@[stacks 00EO "(4)"]
theorem bijective_of_localized_span_range
    {R : Type*} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (φ : M →ₗ[R] N)
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (hiso : ∀ i, Function.Bijective
                  (LocalizedModule.map (Submonoid.powers (f i)) φ)) :
    Function.Bijective φ :=
  bijective_of_localized_span (Set.range f) hf φ (Set.forall_subtype_range_iff.mpr hiso)

/-- **Stacks 00EO (5).** Let `g : M'' →ₗ[R] M` and `h : M →ₗ[R] M'` be linear maps.
If `0 → M''_{f i} → M_{f i} → M'_{f i} → 0` is exact for each `i` and the `f i`
generate the unit ideal, then `0 → M'' → M → M' → 0` is exact. -/
@[stacks 00EO "(5)"]
theorem shortExact_of_localized_span_range
    {R : Type*} [CommSemiring R]
    {M'' M M' : Type*}
    [AddCommMonoid M''] [Module R M'']
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M']
    (g : M'' →ₗ[R] M) (h : M →ₗ[R] M')
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (hexact : ∀ i,
      Function.Injective (LocalizedModule.map (Submonoid.powers (f i)) g) ∧
      Function.Exact (LocalizedModule.map (Submonoid.powers (f i)) g)
        (LocalizedModule.map (Submonoid.powers (f i)) h) ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers (f i)) h)) :
    Function.Injective g ∧ Function.Exact g h ∧ Function.Surjective h :=
  ⟨injective_of_localized_span _ hf g (Set.forall_subtype_range_iff.2 fun i => (hexact i).1),
    exact_of_localized_span _ hf g h (Set.forall_subtype_range_iff.2 fun i => (hexact i).2.1),
    surjective_of_localized_span _ hf h (Set.forall_subtype_range_iff.2 fun i => (hexact i).2.2)⟩

/-- **Stacks 00EO (6).** If each canonical `R_{f i} = Localization.Away (f i)`
is Noetherian and the `f i` generate the unit ideal, then `R` is Noetherian. -/
@[stacks 00EO "(6)"]
theorem IsNoetherianRing.of_localizationSpan_range
    {R : Type*} [CommSemiring R]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, IsNoetherianRing (Localization.Away (f i))) :
    IsNoetherianRing R :=
  -- The image of an ideal `I` in each `Localization.Away (f i)` is an ideal in a Noetherian
  -- ring, hence finitely generated.
  (isNoetherianRing_iff_ideal_fg _).2 fun _ => Ideal.fg_of_localizationSpan (Set.range f) hf
    (Set.forall_subtype_range_iff.2 fun i => (isNoetherianRing_iff_ideal_fg _).1 (h i) _)

open TensorProduct in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 00EO (7).** If each canonical `S_{f i}` is a finite-type
`R_{f i}`-algebra and the `f i` generate the unit ideal, then `S` is a
finite-type `R`-algebra. -/
@[stacks 00EO "(7)"]
theorem Algebra.FiniteType.of_localizationSpan_range
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, (Localization.awayMap (algebraMap R S) (f i)).FiniteType) :
    Algebra.FiniteType R S := by
  refine Algebra.FiniteType.of_span_eq_top_source (Set.range f) hf ?_
  rintro _ ⟨i, rfl⟩
  let e := IsLocalization.Away.tensorRightEquiv S (f i) (Localization.Away (f i))
  have key : algebraMap (Localization.Away (f i)) (Localization.Away (f i) ⊗[R] S) =
      (e.symm : _ →+* _).comp (Localization.awayMap (algebraMap R S) (f i)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f i))
    ext
    simp [e, RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← RingHom.finiteType_algebraMap, key]
  exact RingHom.FiniteType.comp_surjective
    (g := (e.symm : Localization.Away (algebraMap R S (f i)) →+* Localization.Away (f i) ⊗[R] S))
    (h i) (by simpa using e.symm.surjective)

/-- **Stacks 00EO (8).** If each canonical `S_{f i}` is of finite presentation
over `R_{f i}` and the `f i` generate the unit ideal, then `S` is a finitely
presented `R`-algebra. -/
@[stacks 00EO "(8)"]
theorem Algebra.FinitePresentation.of_localizationSpan_range
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, letI : Algebra (Localization.Away (f i))
                              (Localization.Away (algebraMap R S (f i))) :=
                (IsLocalization.Away.map (Localization.Away (f i))
                  (Localization.Away (algebraMap R S (f i)))
                  (algebraMap R S) (f i)).toAlgebra
              Algebra.FinitePresentation (Localization.Away (f i))
                                         (Localization.Away (algebraMap R S (f i)))) :
    Algebra.FinitePresentation R S :=
  RingHom.finitePresentation_algebraMap.1 <| RingHom.finitePresentation_isLocal.ofLocalizationSpan
    (algebraMap R S) (Set.range f) hf (Set.forall_subtype_range_iff.2 h)

/-- **Stacks 00EO (3).** If each canonical localisation `M_{f i}` is finitely
presented over `R_{f i}` and the `f i` generate the unit ideal, then `M` is
finitely presented over `R`. -/
@[stacks 00EO "(3)", sga "4½ Arcata 1.4.2" "(ii) fin pres, Zariski"]
theorem Module.FinitePresentation.of_localizationSpan_range
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Module.FinitePresentation (Localization.Away (f i))
                                       (LocalizedModule (Submonoid.powers (f i)) M)) :
    Module.FinitePresentation R M :=
  Module.FinitePresentation.of_localizationSpan (Set.range f) hf
    (Set.forall_subtype_range_iff.mpr h)

/-!
### Stacks 00EP

Stacks 00EP — if `g₁, …, gₙ` generate the unit ideal of `S` and each `S_{gᵢ}` is of finite
type (resp. finite presentation) over `R`, then so is `S` — is Mathlib's
`Algebra.FiniteType.of_span_eq_top_target` and
`Algebra.FinitePresentation.of_span_eq_top_target`.
-/

add_to_stacks 00EP "(1)" Algebra.FiniteType.of_span_eq_top_target
add_to_sga "4 IV 8.5.5" "special case" Algebra.FiniteType.of_span_eq_top_target
add_to_stacks 00EP "(2)" Algebra.FinitePresentation.of_span_eq_top_target
add_to_sga "4 IV 8.5.5" "special case" Algebra.FinitePresentation.of_span_eq_top_target

end
