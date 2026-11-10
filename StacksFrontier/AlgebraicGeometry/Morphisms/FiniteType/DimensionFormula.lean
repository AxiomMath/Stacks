module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenResidueField
public import StacksFrontier.RingTheory.DimensionFormula
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The dimension formula for a morphism locally of finite type

Let `f : X ⟶ S` be a dominant morphism of integral schemes which is locally of finite type,
with `S` locally Noetherian, and let `x` be a point of `X`. The dimension formula compares the
dimension of the local ring `𝒪_{X,x}` with the dimension of `𝒪_{S,f x}`, correcting by the
transcendence degree of the residue field extension `κ(x)/κ(f x)` and by that of the extension
of function fields:

* `dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + trdeg_{R(S)} R(X)`, and
* equality holds when `S` is universally catenary.

This is the scheme-theoretic form of the ring-level dimension formula
`height_add_trdeg_residue_le` / `height_add_trdeg_residue_eq` (Stacks 02IJ): choosing affine
opens `x ∈ V ⊆ f ⁻¹ U` and `f x ∈ U` turns the two local dimensions into the heights of the
primes of `Γ(X, V)` and `Γ(S, U)` cut out by `x` and `f x`, the residue-field extension into
the extension of residue fields of those primes, and — because `f` is dominant, so that
`Γ(S, U) → Γ(X, V)` is injective with `Γ(S, U)` Noetherian and `Γ(X, V)` of finite type over
it — the function-field extension into the extension `Frac Γ(S, U) ⊆ Frac Γ(X, V)`.

Dropping integrality and dominance gives the *general* dimension formula, in which the
function-field term is replaced by the supremum `E` of the residue-field transcendence degrees
at the generic points of the irreducible components of `X` through `x`:

* `dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + E`.

Taking the supremum over all `x` and over all components turns this into a bound for the
dimension of `X` itself: `dim X ≤ dim S + E`, with `E` now the supremum over all generic points
of `X`.

## Main definitions

* `AlgebraicGeometry.residueFieldTranscendenceDegree` — the transcendence degree of the
  residue-field
  extension `κ(x)/κ(f x)` induced by a morphism of schemes at a point.
* `AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt` — the quantity `E` of
  Stacks 0BAE, the supremum
  of those degrees over the generic points of the irreducible components through a point.

## Main results

* `AlgebraicGeometry.localDimension_add_trdeg_le` — the dimension-formula inequality.
* `AlgebraicGeometry.localDimension_add_trdeg_eq` — its equality form over a universally
  catenary base.
* `AlgebraicGeometry.ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le` — the general
  dimension formula,
  with no integrality or dominance hypothesis.
* `AlgebraicGeometry.topologicalKrullDim_le_add_iSup_residueFieldTrdeg` — the resulting bound
  for the dimension of the source.
* `Algebra.trdeg_eq_of_ringEquiv` — transcendence degree is invariant under a pair of
  compatible ring isomorphisms of the base and of the extension field.
* `Cardinal.toENat_eq_toNat_of_lt_aleph0` — below `ℵ₀` the two roundings of a cardinal to
  `ℕ∞` agree.

## Implementation notes

Mathlib's `AlgebraicGeometry.Scheme.functionField`, the stalk at the generic point of an
integral scheme, is the field of rational functions. Dominance identifies the image of the
generic point with the generic point of the base (Stacks 0CC1), and transporting the stalk map
along that identification is `AlgebraicGeometry.dominantFunctionFieldMap`, which with the square
comparing it to the map on sections lives in
`StacksFrontier/AlgebraicGeometry/Morphisms/Dominant/FunctionFieldMap.lean`. The residue-field term
is added on the
left rather than subtracted on the right, so that the formula remains meaningful in
`WithBot ℕ∞` when a local dimension is infinite; the cardinal-valued transcendence degrees are
pushed into that type with `Cardinal.toENat`.

The general formula is reduced to the integral one along the irreducible components of `X`
through `x`. These are indexed by the minimal primes of `𝒪_{X,x}`, which is Noetherian, and the
component attached to a minimal prime `p` carries the reduced induced structure on the closure
of the point `Scheme.fromSpecStalk x p`; its local ring at `x` is `𝒪_{X,x} ⧸ p`, so that
`dim 𝒪_{X,x}` is the supremum of the `dim (𝒪_{X,x} ⧸ p)`. The component maps to the reduced
closure of its image in `S` (Stacks 0356) by a dominant morphism of integral schemes, to which
the integral dimension formula applies, and both closed immersions are surjective on stalks, so
they do not change the residue fields.

The quantity `E` is a supremum rather than a maximum: the indexing family is finite and (under
the hypotheses of the theorem) nonempty, so the two agree, but the supremum needs no such
argument to be well defined.

## References

* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 0BAG](https://stacks.math.columbia.edu/tag/0BAG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- A cardinal below `ℵ₀` has the same image in `ℕ∞` under `Cardinal.toENat` as the cast of its
`Cardinal.toNat`. -/
theorem Cardinal.toENat_eq_toNat_of_lt_aleph0 {c : Cardinal.{u}} (hc : c < Cardinal.aleph0) :
    Cardinal.toENat c = (Cardinal.toNat c : ℕ∞) := by
  have htop : Cardinal.toENat c ≠ ⊤ := fun h =>
    (not_le_of_gt hc) (Cardinal.toENat_eq_top.mp h)
  rw [← Cardinal.toNat_toENat]
  exact (ENat.natCast_toNat htop).symm

/-- Transcendence degree depends on a field extension only up to compatible ring isomorphisms
of the base field and of the extension field. -/
theorem Algebra.trdeg_eq_of_ringEquiv
    {K K' L L' : Type u} [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcompat : ∀ a, eL (algebraMap K L a) = algebraMap K' L' (eK a)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  let : Algebra K K' := eK.toRingHom.toAlgebra
  let : FaithfulSMul K K' := (faithfulSMul_iff_algebraMap_injective K K').mpr eK.injective
  let : Algebra K L' := (eL.toRingHom.comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' (by ext a; exact hcompat a)
  let : FaithfulSMul K' L' :=
    (faithfulSMul_iff_algebraMap_injective K' L').mpr (RingHom.injective (algebraMap K' L'))
  have hAlgebraic : Algebra.IsAlgebraic K K' := by
    refine ⟨fun x => ⟨Polynomial.X - Polynomial.C (eK.symm x), Polynomial.X_sub_C_ne_zero _, ?_⟩⟩
    rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    change x - eK (eK.symm x) = 0
    simp
  let := hAlgebraic
  have hIso : Algebra.trdeg K L = Algebra.trdeg K L' :=
    AlgEquiv.trdeg_eq (AlgEquiv.ofRingEquiv (f := eL) (by intro a; rfl))
  have hTower := trdeg_add_eq K K' (A := L')
  rw [trdeg_eq_zero, zero_add] at hTower
  exact hIso.trans hTower.symm

namespace AlgebraicGeometry

/-- Transcendence degree is insensitive to passing to fraction fields: for domains `A ⊆ B` with
fraction fields `K ⊆ L`, the degree of `B` over `A` equals that of `L` over `K`, since `K/A`
and `L/B` are algebraic. -/
private lemma trdeg_eq_of_fraction_fields
    {A B K L : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [FaithfulSMul A B]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra A L]
    [Algebra K L] [IsScalarTower A K L] [IsScalarTower A B L] :
    Algebra.trdeg A B = Algebra.trdeg K L := by
  let : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (IsFractionRing.injective B L)
  let : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).mpr (RingHom.injective (algebraMap K L))
  let : FaithfulSMul A L := by
    rw [faithfulSMul_iff_algebraMap_injective A L]
    intro a b hab
    apply FaithfulSMul.algebraMap_injective A B
    apply FaithfulSMul.algebraMap_injective B L
    simpa only [IsScalarTower.algebraMap_apply A B L] using hab
  have hA : Algebra.IsAlgebraic A K := by
    rw [IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := K)]
    exact ⟨fun x => ⟨Polynomial.X - Polynomial.C x, Polynomial.X_sub_C_ne_zero x, by simp⟩⟩
  have hB : Algebra.IsAlgebraic B L := by
    rw [IsFractionRing.comap_isAlgebraic_iff (A := B) (K := L) (C := L)]
    exact ⟨fun x => ⟨Polynomial.X - Polynomial.C x, Polynomial.X_sub_C_ne_zero x, by simp⟩⟩
  let := hA
  let := hB
  have h1 : Algebra.trdeg A B + Algebra.trdeg B L = Algebra.trdeg A L := trdeg_add_eq A B
  have h2 : Algebra.trdeg A K + Algebra.trdeg K L = Algebra.trdeg A L := trdeg_add_eq A K
  rw [show Algebra.trdeg B L = 0 from trdeg_eq_zero, add_zero] at h1
  rw [show Algebra.trdeg A K = 0 from trdeg_eq_zero, zero_add] at h2
  exact h1.trans h2.symm

/-- The section ring of an affine open of a universally catenary scheme is a universally
catenary ring: a finite-type algebra `C` over it gives a locally finite-type morphism
`Spec C ⟶ S` through the affine open, whose source is therefore catenary. -/
private theorem affine_sectionRing_isUniversallyCatenary
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (V : S.Opens) (hV : IsAffineOpen V) :
    IsUniversallyCatenary Γ(S, V) := by
  intro C _ _ hC
  let : Algebra.FiniteType Γ(S, V) C := hC
  let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of Γ(S, V)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) C))
  let : LocallyOfFiniteType g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.mpr hC)
  let f : Spec (CommRingCat.of C) ⟶ S := g ≫ hV.fromSpec
  let : LocallyOfFiniteType f := by
    dsimp [f, g]
    infer_instance
  exact hS (Spec (CommRingCat.of C)) f

/-- For a dominant morphism of integral schemes and affine opens `V ≤ f ⁻¹ U`, the
transcendence degree of `Γ(X, V)` over `Γ(S, U)` is that of the function field extension: the
section rings are domains with those function fields as fraction fields. -/
@[ega "IV 5.5.7" "more general"]
private theorem trdeg_appLE_eq_functionField
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X] [IsIntegral S] [IsDominant f]
    (U : S.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hinj : Function.Injective (f.appLE U V hVU).hom) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    letI := (dominantFunctionFieldMap f).toAlgebra
    Algebra.trdeg Γ(S, U) Γ(X, V) = Algebra.trdeg S.functionField X.functionField := by
  let A : Type u := Γ(S, U)
  let B : Type u := Γ(X, V)
  let K : Type u := S.functionField
  let L : Type u := X.functionField
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let : Algebra A K := (S.germToFunctionField U).hom.toAlgebra
  let : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen S U hU
  let : Algebra B L := (X.germToFunctionField V).hom.toAlgebra
  let : IsFractionRing B L := functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra K L := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra A L :=
    (RingHom.comp (dominantFunctionFieldMap f) (S.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsScalarTower A B L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    have hηS : f (genericPoint X) = genericPoint S :=
      ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
    have hηU : f (genericPoint X) ∈ U := hηS.symm ▸
      ((genericPoint_spec S).mem_open_set_iff U.2).mpr
        (by simpa using (‹Nonempty U› : Nonempty U))
    have hηV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.2).mpr
        (by simpa using (‹Nonempty V› : Nonempty V))
    have hNat := appLE_germToFunctionField_commutes f (genericPoint X) U hηU V hηV hVU
    change ((dominantFunctionFieldMap f).comp (S.germToFunctionField U).hom) a =
      ((X.germToFunctionField V).hom.comp (f.appLE U V hVU).hom) a
    exact congrArg (fun g : A →+* L => g a) hNat.symm
  exact trdeg_eq_of_fraction_fields

/-- The identification of residue fields on affine opens is compatible with the maps induced by
`f`: the residue-field map of `f` at `x` corresponds to the residue-field map of
`Γ(S, U) → Γ(X, V)` at the pair of primes cut out by `f x` and `x`. -/
theorem residueFieldMap_affine_compatible
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (x : X) (hx : x ∈ V) :
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
    let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    let hqOver : q.LiesOver p :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩;
    RingHom.comp (residueFieldEquivOfAffineOpen V hV x hx)
        (f.residueFieldMap x).hom =
      RingHom.comp (Ideal.ResidueField.map p q (f.appLE U V hVU).hom hqOver.over)
        (residueFieldEquivOfAffineOpen U hU (f x) (hVU hx)) := by
  dsimp
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : p.IsPrime := (hU.primeIdealOf ⟨f x, hVU hx⟩).2
  let : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).2
  let : Algebra Γ(S, U) (S.presheaf.stalk (f x)) :=
    (S.presheaf.germ U (f x) (hVU hx)).hom.toAlgebra
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    (X.presheaf.germ V x hx).hom.toAlgebra
  let : IsLocalization p.primeCompl (S.presheaf.stalk (f x)) :=
    hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let : IsLocalization q.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let hqOver : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let eSring : S.presheaf.stalk (f x) ≃+* Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (f x)) (Localization.AtPrime p)
  let eXring : X.presheaf.stalk x ≃+* Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x) (Localization.AtPrime q)
  let eSiso := (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (f x))
      (Localization.AtPrime p)).toCommRingCatIso
  let eXiso := (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime q)).toCommRingCatIso
  let localMap : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q (f.appLE U V hVU).hom hqOver.over
  have hStalk : RingHom.comp localMap eSring.toRingHom =
      RingHom.comp eXring.toRingHom (f.stalkMap x).hom := by
    have hCat : eSiso.hom ≫ CommRingCat.ofHom localMap =
        CommRingCat.ofHom (f.stalkMap x).hom ≫ eXiso.hom :=
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx).hom.w
    have h := congrArg CommRingCat.Hom.hom hCat
    have hES : CommRingCat.Hom.hom eSiso.hom = eSring.toRingHom := rfl
    have hEX : CommRingCat.Hom.hom eXiso.hom = eXring.toRingHom := rfl
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, hES, hEX] using h
  let : IsLocalHom eSring.toRingHom :=
    IsLocalHom.of_surjective eSring.toRingHom eSring.surjective
  let : IsLocalHom eXring.toRingHom :=
    IsLocalHom.of_surjective eXring.toRingHom eXring.surjective
  let : IsLocalHom localMap := Localization.isLocalHom_localRingHom p q
    (f.appLE U V hVU).hom hqOver.over
  have hMap : IsLocalRing.ResidueField.map (localMap.comp eSring.toRingHom) =
      IsLocalRing.ResidueField.map (eXring.toRingHom.comp (f.stalkMap x).hom) := by
    ext z
    refine Quotient.inductionOn' z fun a => ?_
    change IsLocalRing.ResidueField.map (localMap.comp eSring.toRingHom)
        (IsLocalRing.residue (S.presheaf.stalk (f x)) a) =
      IsLocalRing.ResidueField.map (eXring.toRingHom.comp (f.stalkMap x).hom)
        (IsLocalRing.residue (S.presheaf.stalk (f x)) a)
    simp only [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue (Localization.AtPrime q))
      (RingHom.congr_fun hStalk a)
  rw [IsLocalRing.ResidueField.map_comp, IsLocalRing.ResidueField.map_comp] at hMap
  change RingHom.comp (IsLocalRing.ResidueField.map eXring.toRingHom)
        (IsLocalRing.ResidueField.map (f.stalkMap x).hom) =
      RingHom.comp (IsLocalRing.ResidueField.map localMap)
        (IsLocalRing.ResidueField.map eSring.toRingHom)
  exact hMap.symm

/-- Around a point `x`, the two local dimensions plus residue and function-field transcendence
degrees of a dominant morphism of integral schemes are the heights and transcendence degrees of a
finite-type extension `A ⊆ B` of domains, with `A` Noetherian, at primes `q` over `p`; if `S`
is universally catenary, so is `A`. -/
private theorem exists_ring_model_localDimension_add_trdeg
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [IsIntegral X] [IsIntegral S] [IsDominant f] (x : X) :
    letI := (dominantFunctionFieldMap f).toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : IsDomain A)
      (_ : IsDomain B) (_ : IsNoetherianRing A) (_ : Algebra.FiniteType A B)
      (_ : Function.Injective (algebraMap A B)) (p : Ideal A) (q : Ideal B)
      (_ : p.IsPrime) (_ : q.IsPrime) (_ : q.LiesOver p),
      (Scheme.IsUniversallyCatenary S → IsUniversallyCatenary A) ∧
      letI := Ideal.ResidueField.algebraOfLiesOver p q
      ringKrullDim (X.presheaf.stalk x) +
          (Cardinal.toENat
            (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞) =
        ((q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞) :
          ℕ∞) : WithBot ℕ∞) ∧
      ringKrullDim (S.presheaf.stalk (f x)) +
          (Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) =
        ((p.height + (Cardinal.toNat (Algebra.trdeg A B) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  let : Nonempty U := ⟨⟨f x, hxU⟩⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A := Γ(S, U)
  let B := Γ(X, V)
  let p := (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra.FiniteType A B := f.finiteType_appLE hU hV hVU
  let : p.IsPrime := (hU.primeIdealOf ⟨f x, hxU⟩).2
  let : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).2
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
  have hforall : ∀ (W : X.affineOpens) (Z : S.affineOpens)
      (_ : Nonempty W.1) (_ : Nonempty Z.1) (hWZ : W.1 ≤ f ⁻¹ᵁ Z.1),
      Function.Injective (f.appLE Z.1 W.1 hWZ).hom :=
    ((tfae_isDominant_of_isIntegral f).out 1 4).mp (inferInstance : IsDominant f)
  have hinj : Function.Injective (f.appLE U V hVU).hom :=
    hforall ⟨V, hV⟩ ⟨U, hU⟩ ‹Nonempty V› ‹Nonempty U› hVU
  let := Ideal.ResidueField.algebraOfLiesOver p q
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hdimX : ringKrullDim (X.presheaf.stalk x) = q.height := by
    simpa [q] using hV.ringKrullDim_stalk_eq_height x hxV
  have hdimS : ringKrullDim (S.presheaf.stalk (f x)) = p.height := by
    simpa [p] using hU.ringKrullDim_stalk_eq_height (f x) hxU
  have hFun := trdeg_appLE_eq_functionField f U hU V hV hVU hinj
  have hRes :
      Algebra.trdeg p.ResidueField q.ResidueField =
        Algebra.trdeg (S.residueField (f x)) (X.residueField x) := by
    have hcomm := residueFieldMap_affine_compatible f U hU V hV hVU x hxV
    dsimp at hcomm
    exact (Algebra.trdeg_eq_of_ringEquiv (residueFieldEquivOfAffineOpen U hU (f x) hxU)
      (residueFieldEquivOfAffineOpen V hV x hxV) fun a => RingHom.congr_fun hcomm a).symm
  have hFunFinite : Algebra.trdeg A B < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  have hResFinite : Algebra.trdeg p.ResidueField q.ResidueField < Cardinal.aleph0 :=
    resfield_trdeg_lt_aleph0_general p q
  refine ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hinj, p, q, inferInstance, inferInstance, inferInstance,
    fun hS => affine_sectionRing_isUniversallyCatenary hS U hU, ?_, ?_⟩
  · rw [hdimX, ← hRes, Cardinal.toENat_eq_toNat_of_lt_aleph0 hResFinite]
    norm_cast
  · rw [hdimS, ← hFun, Cardinal.toENat_eq_toNat_of_lt_aleph0 hFunFinite]
    norm_cast

/-- **Stacks 02JU.** The dimension formula for a dominant locally finite-type morphism of
integral schemes over a locally Noetherian base: the dimension of the local ring at `x` plus
the transcendence degree of `κ(x)/κ(f x)` is at most the dimension of the local ring at `f x`
plus the transcendence degree of the function field extension. -/
@[stacks 02JU "dimension-formula inequality"]
theorem localDimension_add_trdeg_le {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [IsIntegral X] [IsIntegral S] [IsDominant f] (x : X) :
    letI := (dominantFunctionFieldMap f).toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toENat
          (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞) ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) := by
  obtain ⟨A, B, _, _, _, _, _, _, _, hinj, p, q, _, _, _, -, hX, hY⟩ :=
    exists_ring_model_localDimension_add_trdeg f x
  rw [hX, hY]
  exact_mod_cast height_add_trdeg_residue_le hinj p q

/-- **Stacks 02JU.** Over a universally catenary base the dimension formula is an equality. -/
@[stacks 02JU "universally catenary equality"]
theorem localDimension_add_trdeg_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [IsIntegral X] [IsIntegral S] [IsDominant f]
    (hS : Scheme.IsUniversallyCatenary S) (x : X) :
    letI := (dominantFunctionFieldMap f).toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x) +
        (Cardinal.toENat
          (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : WithBot ℕ∞) =
      ringKrullDim (S.presheaf.stalk (f x)) +
        (Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) := by
  obtain ⟨A, B, _, _, _, _, _, _, _, hinj, p, q, _, _, _, hcat, hX, hY⟩ :=
    exists_ring_model_localDimension_add_trdeg f x
  rw [hX, hY]
  exact_mod_cast height_add_trdeg_residue_eq hinj (hcat hS) p q

/-! ### The general dimension formula -/

/-- The reduced induced closed subscheme structure on the closure of a point, i.e. the
irreducible closed subscheme `closure {z} ⊆ X` with its reduced structure. -/
noncomputable def reducedPointClosure (X : Scheme.{u}) (z : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))

/-- The support of `reducedPointClosure X z` is the closure of `{z}`. -/
theorem reducedPointClosure_support (X : Scheme.{u}) (z : X) :
    ((reducedPointClosure X z).support : Set X) = closure {z} := by
  change ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).support :
    Set X) = closure {z}
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

private instance isIntegral_subscheme_reducedPointClosure (X : Scheme.{u}) (z : X) :
    IsIntegral (reducedPointClosure X z).subscheme := by
  have : IrreducibleSpace (reducedPointClosure X z).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [Scheme.IdealSheafData.range_subschemeι, reducedPointClosure_support]
      exact isIrreducible_singleton.closure)
  have : IsReduced (reducedPointClosure X z).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem mem_range_subschemeι_reducedPointClosure {X : Scheme.{u}} {z w : X}
    (hw : w ∈ closure ({z} : Set X)) : w ∈ Set.range (reducedPointClosure X z).subschemeι := by
  rwa [Scheme.IdealSheafData.range_subschemeι, reducedPointClosure_support]

/-- The generic point of the reduced closure of `z` is `z` itself. -/
private theorem subschemeι_reducedPointClosure_genericPoint (X : Scheme.{u}) (z : X) :
    (reducedPointClosure X z).subschemeι
        (genericPoint (reducedPointClosure X z).subscheme) = z := by
  have hrange : Set.range (reducedPointClosure X z).subschemeι = (closure {z} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, reducedPointClosure_support]
  have hgen := (genericPoint_spec (reducedPointClosure X z).subscheme).image
    (reducedPointClosure X z).subschemeι.continuous
  rw [show closure ((reducedPointClosure X z).subschemeι ''
      (Set.univ : Set (reducedPointClosure X z).subscheme)) = (closure {z} : Set X) by
    rw [Set.image_univ, hrange, closure_closure]] at hgen
  exact hgen.eq isGenericPoint_closure

/-- A morphism of schemes maps the reduced closure of a point into the reduced closure of its
image: by Stacks 0356 it suffices that the set-theoretic image lies in that closure. -/
@[ega "IV 13.2.4" "partial"]
private theorem exists_map_reducedPointClosure {X S : Scheme.{u}} (f : X ⟶ S) (η : X) :
    ∃ g : (reducedPointClosure X η).subscheme ⟶ (reducedPointClosure S (f η)).subscheme,
      g ≫ (reducedPointClosure S (f η)).subschemeι =
        (reducedPointClosure X η).subschemeι ≫ f := by
  apply (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    (reducedPointClosure S (f η)) ((reducedPointClosure X η).subschemeι ≫ f)).2
  rintro _ ⟨z, rfl⟩
  have hz : ((reducedPointClosure X η).subschemeι z : X) ∈ closure ({η} : Set X) := by
    rw [← reducedPointClosure_support X η, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hclosure := image_closure_subset_closure_image f.continuous
    (Set.mem_image_of_mem f hz)
  change f ((reducedPointClosure X η).subschemeι z) ∈
    ((reducedPointClosure S (f η)).support : Set S)
  rw [reducedPointClosure_support]
  simpa using hclosure

/-- The map of reduced point closures induced by a morphism is dominant: it takes the generic
point to the generic point. -/
theorem isDominant_map_reducedPointClosure {X S : Scheme.{u}} (f : X ⟶ S) (η : X)
    (g : (reducedPointClosure X η).subscheme ⟶ (reducedPointClosure S (f η)).subscheme)
    (hg : g ≫ (reducedPointClosure S (f η)).subschemeι =
      (reducedPointClosure X η).subschemeι ≫ f) : IsDominant g := by
  have hpoint : g (genericPoint (reducedPointClosure X η).subscheme) =
      genericPoint (reducedPointClosure S (f η)).subscheme := by
    apply (reducedPointClosure S (f η)).subschemeι.isEmbedding.injective
    calc
      (reducedPointClosure S (f η)).subschemeι
            (g (genericPoint (reducedPointClosure X η).subscheme)) =
          (g ≫ (reducedPointClosure S (f η)).subschemeι)
            (genericPoint (reducedPointClosure X η).subscheme) := rfl
      _ = ((reducedPointClosure X η).subschemeι ≫ f)
            (genericPoint (reducedPointClosure X η).subscheme) := by rw [hg]
      _ = f η := by
            rw [Scheme.Hom.comp_apply, subschemeι_reducedPointClosure_genericPoint]
      _ = (reducedPointClosure S (f η)).subschemeι
            (genericPoint (reducedPointClosure S (f η)).subscheme) :=
        (subschemeι_reducedPointClosure_genericPoint S (f η)).symm
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range,
    ← (genericPoint_spec (reducedPointClosure S (f η)).subscheme).def]
  refine Set.Subset.antisymm ?_ (closure_mono ?_)
  · rw [(genericPoint_spec (reducedPointClosure S (f η)).subscheme).def]
    exact Set.subset_univ _
  · rintro _ rfl
    exact ⟨genericPoint (reducedPointClosure X η).subscheme, hpoint⟩

/-- The dimension of a commutative ring is the supremum of the dimensions of the quotients by its
minimal primes, i.e. of the dimensions of its irreducible components. -/
@[ega "0 16.1.1", ega "IV 14.2.4" "special case"]
private theorem ringKrullDim_eq_iSup_minimalPrimes_quotient {R : Type*} [CommRing R] :
    ringKrullDim R =
      ⨆ p : {p : PrimeSpectrum R // p.asIdeal ∈ (⊥ : Ideal R).minimalPrimes},
        ringKrullDim (R ⧸ p.1.asIdeal) := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  refine le_antisymm (iSup_le fun q => ?_) (iSup_le fun p => ?_)
  · obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
      (R := R) (I := (⊥ : Ideal R)) (J := q.asIdeal) bot_le
    refine le_iSup_of_le (⟨⟨p, hp.1.1⟩, hp⟩ :
      {p : PrimeSpectrum R // p.asIdeal ∈ (⊥ : Ideal R).minimalPrimes}) ?_
    rw [← coheight_eq_ringKrullDim_quotient]
    exact WithBot.coe_le_coe.mpr
      (Order.coheight_anti ((PrimeSpectrum.asIdeal_le_asIdeal _ q).mpr hpq))
  · rw [← coheight_eq_ringKrullDim_quotient]
    exact le_iSup_of_le p.1 le_rfl

/-- The point of `X` cut out by a minimal prime of the local ring at `x` is the generic point of
an irreducible component of `X`. -/
theorem fromSpecStalk_mem_genericPoints_of_mem_minimalPrimes
    {X : Scheme.{u}} (x : X)
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes}) :
    X.fromSpecStalk x
      (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) ∈
        genericPoints X := by
  have hηx : X.fromSpecStalk x
      (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) ⤳ x := by
    have hmem : X.fromSpecStalk x
        (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) ∈
        Set.range (X.fromSpecStalk x) := ⟨p.1, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  have hξη : (genericPoints.ofComponent
      (⟨irreducibleComponent (X.fromSpecStalk x
          (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1))),
        irreducibleComponent_mem_irreducibleComponents _⟩ :
        irreducibleComponents X)).1 ⤳
      X.fromSpecStalk x
        (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) :=
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
  obtain ⟨q, hq⟩ : (genericPoints.ofComponent
      (⟨irreducibleComponent (X.fromSpecStalk x
          (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1))),
        irreducibleComponent_mem_irreducibleComponents _⟩ :
        irreducibleComponents X)).1 ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hξη.trans hηx
  have hspec : q ⤳ OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1) := by
    apply (X.fromSpecStalk x).isEmbedding.specializes_iff.mp
    simpa [hq] using hξη
  have hle : (OrderDual.ofDual (specOrderIsoPrimeSpectrum
      (.of (X.presheaf.stalk x)) q)).asIdeal ≤ p.1.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ p.1).2
      ((PrimeSpectrum.le_iff_specializes _ p.1).2 hspec)
  have hpmin : Minimal Ideal.IsPrime p.1.asIdeal := by
    have hp : p.1.asIdeal ∈ minimalPrimes (X.presheaf.stalk x) := p.2
    rwa [minimalPrimes_eq_minimals] at hp
  have hgen : (genericPoints.ofComponent
      (⟨irreducibleComponent (X.fromSpecStalk x
          (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1))),
        irreducibleComponent_mem_irreducibleComponents _⟩ :
        irreducibleComponents X)).1 =
      X.fromSpecStalk x
        (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) := by
    rw [← hq]
    exact congrArg (X.fromSpecStalk x) (PrimeSpectrum.ext (le_antisymm hle
      (hpmin.2 (OrderDual.ofDual (specOrderIsoPrimeSpectrum
        (.of (X.presheaf.stalk x)) q)).isPrime hle)) :
      OrderDual.ofDual (specOrderIsoPrimeSpectrum (.of (X.presheaf.stalk x)) q) = p.1)
  rw [← hgen]
  exact (genericPoints.ofComponent _).2

/-- The generic point of the irreducible component of `X` through `x` that corresponds to a
minimal prime of the local ring at `x`. -/
noncomputable def genericPointOfMinimalStalkPrime
    {X : Scheme.{u}} (x : X)
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes}) : genericPoints X :=
  ⟨X.fromSpecStalk x
      (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)),
    fromSpecStalk_mem_genericPoints_of_mem_minimalPrimes x p⟩

/-- For an integral scheme the canonical map from the spectrum of a local ring takes the generic
point to the generic point. -/
@[ega "I 7.2.8" "partial"]
theorem fromSpecStalk_genericPoint {X : Scheme.{u}} [IsIntegral X] (x : X) :
    X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) = genericPoint X := by
  have hgen := (genericPoint_spec (Spec (X.presheaf.stalk x))).image
    (X.fromSpecStalk x).continuous
  have htop : closure (Set.range (X.fromSpecStalk x)) = (Set.univ : Set X) := by
    refine Set.Subset.antisymm (Set.subset_univ _) ?_
    rw [← (genericPoint_spec X).def]
    refine closure_mono ?_
    rintro _ rfl
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes _
  rw [show closure ((X.fromSpecStalk x) '' (Set.univ : Set (Spec (X.presheaf.stalk x)))) =
      (Set.univ : Set X) by rw [Set.image_univ, htop]] at hgen
  exact hgen.eq (genericPoint_spec X)

/-- The local ring at `x` of an integral closed subscheme `I` whose generic point is the point
cut out by a minimal prime `p` of `𝒪_{X,x}` is the quotient `𝒪_{X,x} ⧸ p`. -/
private theorem ringKrullDim_stalk_subscheme_eq_ringKrullDim_quotient
    {X : Scheme.{u}} (x : X) (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (z : I.subscheme) (hz : I.subschemeι z = x)
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes})
    (hη : X.fromSpecStalk x
        (OrderDual.ofDual (primeSpectrumOrderIsoSpec (X.presheaf.stalk x) p.1)) =
      I.subschemeι (genericPoint I.subscheme)) :
    ringKrullDim (I.subscheme.presheaf.stalk z) =
      ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) := by
  set φcat := (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
    I.subschemeι.stalkMap z with hφcat
  have hsurj : Function.Surjective φcat.hom :=
    (I.subschemeι.stalkMap_surjective z).comp
      (ConcreteCategory.bijective_of_isIso
        (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom).2
  have hpoint : X.fromSpecStalk x
      ((Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z)))) =
      I.subschemeι (genericPoint I.subscheme) := by
    have hcongr : Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
        X.fromSpecStalk x = X.fromSpecStalk (I.subschemeι z) := by
      simpa [TopCat.Presheaf.stalkCongr] using
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
          (X := X) (Inseparable.of_eq hz.symm).ge)
    have hdiag : Spec.map φcat ≫ X.fromSpecStalk x =
        I.subscheme.fromSpecStalk z ≫ I.subschemeι := by
      rw [hφcat, Spec.map_comp, Category.assoc, hcongr,
        Scheme.SpecMap_stalkMap_fromSpecStalk I.subschemeι]
    rw [← Scheme.Hom.comp_apply, hdiag, Scheme.Hom.comp_apply, fromSpecStalk_genericPoint]
  have hq : (OrderDual.ofDual (specOrderIsoPrimeSpectrum
      (.of (X.presheaf.stalk x)) ((Spec.map φcat)
        (genericPoint (Spec (I.subscheme.presheaf.stalk z)))))).asIdeal =
      RingHom.ker φcat.hom := by
    rw [genericPoint_eq_bot_of_affine]
    change (PrimeSpectrum.comap φcat.hom
      (⊥ : PrimeSpectrum (I.subscheme.presheaf.stalk z))).asIdeal = _
    rw [PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot]
    rfl
  rw [← (X.fromSpecStalk x).isEmbedding.injective (hη.trans hpoint.symm)] at hq
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hq).trans
      (RingHom.quotientKerEquivOfSurjective (f := φcat.hom) hsurj))).symm

/-- The transcendence degree of the residue field extension `κ(x) / κ(f x)` induced by a morphism
of schemes at a point, as an element of `ℕ∞`. -/
noncomputable def residueFieldTranscendenceDegree {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : ℕ∞ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x))

/-- The supremum of the residue-field transcendence degrees `κ(ξ) / κ(f ξ)` over the generic
points `ξ` of the irreducible components of `X` passing through `x`. This is the quantity `E` of
Stacks 0BAE. -/
noncomputable def genericResidueFieldTranscendenceDegreeAt {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) : ℕ∞ :=
  ⨆ ξ : {ξ : genericPoints X // x ∈ closure ({(ξ.1 : X)} : Set X)},
    residueFieldTranscendenceDegree f ξ.1.1

/-- Transporting a stalk map along an equality of its base point is composition with the
comparison isomorphism of stalks. -/
theorem stalkMap_cast_target {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    {y : S} (h : f x = y) :
    h ▸ f.stalkMap x = (S.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x := by
  cases h
  simp

/-- In a commutative square whose two vertical maps are surjective on stalks, the residue-field
extension induced by the top map agrees with the one induced by the bottom map. -/
private theorem trdeg_residueField_eq_of_square
    {A X B S : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ S) (g : A ⟶ B) (f : X ⟶ S)
    [SurjectiveOnStalks i] [SurjectiveOnStalks j] (a : A) (hsq : g ≫ j = i ≫ f) :
    letI := (g.residueFieldMap a).hom.toAlgebra
    letI := (f.residueFieldMap (i a)).hom.toAlgebra
    Algebra.trdeg (B.residueField (g a)) (A.residueField a) =
      Algebra.trdeg (S.residueField (f (i a))) (X.residueField (i a)) := by
  have hp : j (g a) = f (i a) := congrArg (fun k : A ⟶ S => k a) hsq
  set eXfwd : X.residueField (i a) ≃+* A.residueField a :=
    RingEquiv.ofBijective (i.residueFieldMap a).hom (i.bijective_residueFieldMap a) with heXfwd
  set eBfwd : S.residueField (j (g a)) ≃+* B.residueField (g a) :=
    RingEquiv.ofBijective (j.residueFieldMap (g a)).hom (j.bijective_residueFieldMap (g a))
    with heBfwd
  have hring : (g.residueFieldMap a).hom.comp (j.residueFieldMap (g a)).hom =
      (i.residueFieldMap a).hom.comp
        ((f.residueFieldMap (i a)).hom.comp ((S.residueFieldCongr hp).hom).hom) := by
    have h := Scheme.Hom.residueFieldMap_congr hsq a
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at h
    have h' := congrArg CommRingCat.Hom.hom (by simpa [hp] using h :
      j.residueFieldMap (g a) ≫ g.residueFieldMap a =
        (S.residueFieldCongr hp).hom ≫ f.residueFieldMap (i a) ≫ i.residueFieldMap a)
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using h'
  let : Algebra (B.residueField (g a)) (A.residueField a) := (g.residueFieldMap a).hom.toAlgebra
  let : Algebra (S.residueField (f (i a))) (X.residueField (i a)) :=
    (f.residueFieldMap (i a)).hom.toAlgebra
  refine Algebra.trdeg_eq_of_ringEquiv
    (eBfwd.symm.trans (S.residueFieldCongr hp).commRingCatIsoToRingEquiv) eXfwd.symm fun b => ?_
  have hs : (j.residueFieldMap (g a)).hom (eBfwd.symm b) = b := eBfwd.apply_symm_apply b
  have h : (g.residueFieldMap a).hom ((j.residueFieldMap (g a)).hom (eBfwd.symm b)) =
      (i.residueFieldMap a).hom ((f.residueFieldMap (i a)).hom
        (((S.residueFieldCongr hp).hom).hom (eBfwd.symm b))) :=
    DFunLike.congr_fun hring (eBfwd.symm b)
  change eXfwd.symm ((g.residueFieldMap a).hom b) =
    (f.residueFieldMap (i a)).hom (((S.residueFieldCongr hp).hom).hom (eBfwd.symm b))
  calc eXfwd.symm ((g.residueFieldMap a).hom b)
      = eXfwd.symm ((g.residueFieldMap a).hom
          ((j.residueFieldMap (g a)).hom (eBfwd.symm b))) := by rw [hs]
    _ = eXfwd.symm ((i.residueFieldMap a).hom ((f.residueFieldMap (i a)).hom
          (((S.residueFieldCongr hp).hom).hom (eBfwd.symm b)))) := by rw [h]
    _ = (f.residueFieldMap (i a)).hom
          (((S.residueFieldCongr hp).hom).hom (eBfwd.symm b)) := eXfwd.symm_apply_apply _

/-- For a dominant morphism of integral schemes the transcendence degree of the function-field
extension is the residue-field transcendence degree at the generic point. -/
theorem toENat_trdeg_functionField_eq_residueFieldTrdeg_genericPoint
    {X S : Scheme.{u}} (g : X ⟶ S) [IsIntegral X] [IsIntegral S] [IsDominant g] :
    letI := (dominantFunctionFieldMap g).toAlgebra
    Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) =
      residueFieldTranscendenceDegree g (genericPoint X) := by
  have hgen : g (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral g).out 1 2).mp (inferInstance : IsDominant g)
  set eX : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨RingHom.injective _, X.residue_surjective (genericPoint X)⟩ with heX
  set eS : S.functionField ≃+* S.residueField (g (genericPoint X)) :=
    (RingEquiv.ofBijective (S.residue (genericPoint S)).hom
      ⟨RingHom.injective _, S.residue_surjective (genericPoint S)⟩).trans
      (S.residueFieldCongr hgen.symm).commRingCatIsoToRingEquiv with heS
  let : Algebra S.functionField X.functionField := (dominantFunctionFieldMap g).toAlgebra
  let : Algebra (S.residueField (g (genericPoint X))) (X.residueField (genericPoint X)) :=
    (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  have hcompat : ∀ a, eX (dominantFunctionFieldMap g a) =
      (g.residueFieldMap (genericPoint X)).hom (eS a) := by
    intro a
    have hcast : (dominantFunctionFieldMap g) =
        ((S.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
          g.stalkMap (genericPoint X)).hom := by
      dsimp [dominantFunctionFieldMap]
      rw [stalkMap_cast_target, CommRingCat.hom_comp]
    have hmaps :
        ((S.residue (genericPoint S) ≫ (S.residueFieldCongr hgen.symm).hom) ≫
          g.residueFieldMap (genericPoint X)) =
        ((S.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ g.stalkMap (genericPoint X)) ≫
          X.residue (genericPoint X) := by
      rw [Scheme.residue_residueFieldCongr S hgen.symm, Category.assoc,
        Scheme.residue_residueFieldMap g (genericPoint X), Category.assoc]
    have ha := congrArg (fun k => k.hom a) hmaps
    change eX ((dominantFunctionFieldMap g) a) = _
    rw [heX, hcast]
    exact ha.symm
  have htr : Algebra.trdeg S.functionField X.functionField =
      Algebra.trdeg (S.residueField (g (genericPoint X))) (X.residueField (genericPoint X)) :=
    Algebra.trdeg_eq_of_ringEquiv eS eX hcompat
  simpa [residueFieldTranscendenceDegree] using congrArg Cardinal.toENat htr

/-- The dimension formula transported across a square: for a dominant locally finite type
morphism `g : A ⟶ B` of integral schemes sitting over `f : X ⟶ S` through maps surjective on
stalks, the residue-field degrees may be computed along `f`. -/
private theorem integralSquare_localDimension_add_residueFieldTrdeg_le
    {A X B S : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ S) (g : A ⟶ B) (f : X ⟶ S)
    [IsIntegral A] [IsIntegral B] [IsDominant g] [IsLocallyNoetherian B] [LocallyOfFiniteType g]
    [SurjectiveOnStalks i] [SurjectiveOnStalks j] (a : A) (hsq : g ≫ j = i ≫ f) :
    ringKrullDim (A.presheaf.stalk a) + (residueFieldTranscendenceDegree f (i a) : WithBot ℕ∞) ≤
      ringKrullDim (B.presheaf.stalk (g a)) +
        (residueFieldTranscendenceDegree f (i (genericPoint A)) : WithBot ℕ∞) := by
  let := (dominantFunctionFieldMap g).toAlgebra
  let := (g.residueFieldMap a).hom.toAlgebra
  have h02 := localDimension_add_trdeg_le g a
  have hlocal := trdeg_residueField_eq_of_square i j g f a hsq
  have hgeneric := trdeg_residueField_eq_of_square i j g f (genericPoint A) hsq
  have hfunction := toENat_trdeg_functionField_eq_residueFieldTrdeg_genericPoint g
  unfold residueFieldTranscendenceDegree
  rw [hlocal, hfunction] at h02
  unfold residueFieldTranscendenceDegree at h02
  rwa [hgeneric] at h02

/-- The dimension formula on the irreducible component of `X` through `x` attached to a minimal
prime of `𝒪_{X,x}`. -/
theorem minimalPrime_localDimension_add_residueFieldTrdeg_le
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes}) :
    ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) +
        (residueFieldTranscendenceDegree f x : WithBot ℕ∞) ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        (genericResidueFieldTranscendenceDegreeAt f x : WithBot ℕ∞) := by
  have hηx : (genericPointOfMinimalStalkPrime x p).1 ⤳ x := by
    have hmem : (genericPointOfMinimalStalkPrime x p).1 ∈ Set.range (X.fromSpecStalk x) :=
      ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  set η : X := (genericPointOfMinimalStalkPrime x p).1
  obtain ⟨z, hzx⟩ : x ∈ Set.range (reducedPointClosure X η).subschemeι :=
    mem_range_subschemeι_reducedPointClosure (specializes_iff_mem_closure.mp hηx)
  have hdim := ringKrullDim_stalk_subscheme_eq_ringKrullDim_quotient x
    (reducedPointClosure X η) z hzx p (subschemeι_reducedPointClosure_genericPoint X η).symm
  obtain ⟨g, hg⟩ := exists_map_reducedPointClosure f η
  have : IsDominant g := isDominant_map_reducedPointClosure f η g hg
  have : LocallyOfFiniteType (g ≫ (reducedPointClosure S (f η)).subschemeι) := by
    rw [hg]
    infer_instance
  have : LocallyOfFiniteType g :=
    locallyOfFiniteType_of_comp g (reducedPointClosure S (f η)).subschemeι
  have : IsLocallyNoetherian (reducedPointClosure S (f η)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedPointClosure S (f η)).subschemeι
  have hformula := integralSquare_localDimension_add_residueFieldTrdeg_le
    (reducedPointClosure X η).subschemeι (reducedPointClosure S (f η)).subschemeι g f z hg
  rw [subschemeι_reducedPointClosure_genericPoint] at hformula
  have hjx : (reducedPointClosure S (f η)).subschemeι (g z) = f x := by
    have h := congrArg (fun k : (reducedPointClosure X η).subscheme ⟶ S => k z) hg
    simpa [Scheme.Hom.comp_apply] using h.trans (congrArg f hzx)
  have htarget : ringKrullDim ((reducedPointClosure S (f η)).subscheme.presheaf.stalk (g z)) ≤
      ringKrullDim (S.presheaf.stalk (f x)) := by
    rw [← hjx]
    exact ringKrullDim_le_of_surjective
      ((reducedPointClosure S (f η)).subschemeι.stalkMap (g z)).hom
      ((reducedPointClosure S (f η)).subschemeι.stalkMap_surjective (g z))
  have htrdeg : residueFieldTranscendenceDegree f η ≤
      genericResidueFieldTranscendenceDegreeAt f x :=
    le_iSup_of_le (⟨genericPointOfMinimalStalkPrime x p, specializes_iff_mem_closure.mp hηx⟩ :
      {ξ : genericPoints X // x ∈ closure ({(ξ.1 : X)} : Set X)}) le_rfl
  calc
    ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) +
          (residueFieldTranscendenceDegree f x : WithBot ℕ∞) =
        ringKrullDim ((reducedPointClosure X η).subscheme.presheaf.stalk z) +
          (residueFieldTranscendenceDegree f ((reducedPointClosure X η).subschemeι z) :
            WithBot ℕ∞) := by
      rw [← hdim, hzx]
    _ ≤ ringKrullDim ((reducedPointClosure S (f η)).subscheme.presheaf.stalk (g z)) +
          (residueFieldTranscendenceDegree f η : WithBot ℕ∞) := hformula
    _ ≤ ringKrullDim (S.presheaf.stalk (f x)) +
          (genericResidueFieldTranscendenceDegreeAt f x : WithBot ℕ∞) :=
      add_le_add htarget (WithBot.coe_le_coe.mpr htrdeg)

/-- For a nonempty family `d` in `ℕ∞` and `a : ℕ∞`, adding `a` on the right commutes with the
supremum in `WithBot ℕ∞`: `(⨆ i, d i) + a = ⨆ i, (d i + a)`. -/
theorem withBot_iSup_add_right {ι : Sort*} [Nonempty ι] (d : ι → ℕ∞) (a : ℕ∞) :
    (⨆ i, (d i : WithBot ℕ∞)) + (a : WithBot ℕ∞) = ⨆ i, ((d i + a : ℕ∞) : WithBot ℕ∞) := by
  calc
    (⨆ i, (d i : WithBot ℕ∞)) + (a : WithBot ℕ∞) =
        (((⨆ i, d i) + a : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_iSup (OrderTop.bddAbove _), ← WithBot.coe_add]
    _ = ((⨆ i, d i + a : ℕ∞) : WithBot ℕ∞) := by rw [ENat.iSup_add]
    _ = ⨆ i, ((d i + a : ℕ∞) : WithBot ℕ∞) := WithBot.coe_iSup (OrderTop.bddAbove _)

/-- **Stacks 0BAE.** The general dimension formula: for a morphism `f : X ⟶ S` locally of finite
type over a locally Noetherian scheme and a point `x` of `X`,
`dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) ≤ dim 𝒪_{S,f x} + E`, where `E` is the supremum of
`trdeg_{κ(f ξ)} κ(ξ)` over the generic points `ξ` of the irreducible components of `X`
containing `x`. -/
@[stacks 0BAE,
  ega "IV 13.3.4" "partial",
  ega "IV 5.5.6" "partial",
  ega "IV 5.5.7" "more general",
  ega "IV 5.5.8" "more general",
  ega "IV 5.6.5" "more general"]
theorem ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    ringKrullDim (X.presheaf.stalk x) + (residueFieldTranscendenceDegree f x : WithBot ℕ∞) ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        (genericResidueFieldTranscendenceDegreeAt f x : WithBot ℕ∞) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hM : Nonempty {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes} := by
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le
      (R := X.presheaf.stalk x) (I := (⊥ : Ideal (X.presheaf.stalk x)))
      (J := (⊤ : PrimeSpectrum (X.presheaf.stalk x)).asIdeal) bot_le
    exact ⟨⟨⟨q, hq.1.1⟩, hq⟩⟩
  have hdcast : ∀ p : {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ (⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes},
      (((ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal)).unbotD 0 : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) := by
    intro p
    have hne : ringKrullDim (X.presheaf.stalk x ⧸ p.1.asIdeal) ≠ ⊥ := by
      intro h
      have : Nontrivial (X.presheaf.stalk x ⧸ p.1.asIdeal) :=
        Ideal.Quotient.nontrivial_iff.mpr p.1.isPrime.ne_top
      exact (not_nontrivial_iff_subsingleton.mpr
        (ringKrullDim_eq_bot_iff_subsingleton.mp h)) inferInstance
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
    rw [← hn, WithBot.unbotD_coe]
  rw [ringKrullDim_eq_iSup_minimalPrimes_quotient.trans
      (iSup_congr fun p => (hdcast p).symm),
    withBot_iSup_add_right _ (residueFieldTranscendenceDegree f x)]
  refine iSup_le fun p => ?_
  rw [WithBot.coe_add, hdcast p]
  exact minimalPrime_localDimension_add_residueFieldTrdeg_le f x p

/-- **Stacks 0BAG.** The dimension of the source of a morphism locally of finite type over a
locally Noetherian scheme is at most the dimension of the target plus the supremum of the
residue-field transcendence degrees at the generic points of the irreducible components of the
source. -/
@[stacks 0BAG, ega "IV 5.6.6" "more general"]
theorem topologicalKrullDim_le_add_iSup_residueFieldTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y +
      ((⨆ ξ : genericPoints X, residueFieldTranscendenceDegree f ξ.1 : ℕ∞) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
  rcases isEmpty_or_nonempty X with _ | _
  · simp
  · have : Nonempty (genericPoints X) :=
      (dense_iff_closure_eq.mpr genericPoints.closure).nonempty.to_subtype
    refine iSup_le fun x => ?_
    calc
      ringKrullDim (X.presheaf.stalk x) ≤
          ringKrullDim (Y.presheaf.stalk (f x)) +
            (genericResidueFieldTranscendenceDegreeAt f x : WithBot ℕ∞) :=
        (le_add_of_nonneg_right (WithBot.coe_nonneg.mpr zero_le)).trans
          (ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le f x)
      _ ≤ topologicalKrullDim Y + _ := add_le_add
        (by
          rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk Y]
          exact le_iSup (fun y : Y => ringKrullDim (Y.presheaf.stalk y)) (f x))
        (WithBot.coe_le_coe.mpr (iSup_le fun ξ => le_iSup_of_le ξ.1 le_rfl))
end AlgebraicGeometry
