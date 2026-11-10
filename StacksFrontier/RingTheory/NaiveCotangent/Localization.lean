module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Localization.Algebra
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
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The naive cotangent complex and localization

For a ring map `A → B` and a presentation `α : A[x_i] → B` with kernel `I`, the naive cotangent
complex is the two term complex `NL(α) = (I/I² → Ω_{A[x_i]/A} ⊗ B)`. This file collects its
behaviour under localization, of the target and of the base, and its value on a polynomial
algebra.

## Main results

* `Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization`: for a
  localization `M⁻¹B` of `B` and presentations `α` of `B` and `β` of `M⁻¹B`, the canonical map
  `NL(α) ⊗_B M⁻¹B → NL(β)` is bijective on `H₁`.
* `Algebra.Generators.exists_cotangentComplex_comp_localizationAway_eq_prodMap`: for the
  presentation `β : P[x] → B_g`, `x ↦ 1/g`, obtained from `α` by adjoining one variable,
  `NL(β) ≅ NL(α) ⊗_B B_g ⊕ NL(B[x] → B_g)` as two term complexes, compatibly with the canonical
  maps.
* `Algebra.Generators.nonempty_cotangent_baseChange_prod_linearEquiv_of_isLocalizationAway`: for
  presentations of `S` by `n` and of `S_g` by `m` variables, with kernels `I` and `J`,
  `(I/I²)_g ⊕ S_g^{⊕m} ≅ J/J² ⊕ S_g^{⊕n}`.
* `kaehlerDifferential_subsingleton_of_isLocalization` and
  `h1Cotangent_subsingleton_of_isLocalization`: both homology modules of `NL_{S⁻¹A/A}` vanish,
  i.e. the complex is contractible.
* `naiveCotangentComplex_localization_base_homotopyEquiv`: for a localization `Aₘ` of `A` and a
  ring map `Aₘ → B`, the canonical map `NL_{B/A} → NL_{B/Aₘ}` is a homotopy equivalence.
* `natExt_cotangent_subsingleton` and `natExt_toKaehler_bijective`: for a polynomial algebra
  `B = A[x_i]` presented by its own variables, `NL_{B/A} = (0 → Ω_{B/A})`.

## References

* [StacksProject 00S7](https://stacks.math.columbia.edu/tag/00S7)
* [StacksProject 08JZ](https://stacks.math.columbia.edu/tag/08JZ)
* [StacksProject 00S6](https://stacks.math.columbia.edu/tag/00S6)
* [StacksProject 00S5](https://stacks.math.columbia.edu/tag/00S5)
* [StacksProject 00S3](https://stacks.math.columbia.edu/tag/00S3)
* [StacksProject 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [StacksProject 07BR](https://stacks.math.columbia.edu/tag/07BR)
* [StacksProject 07BS](https://stacks.math.columbia.edu/tag/07BS)
* [StacksProject 08Q1](https://stacks.math.columbia.edu/tag/08Q1)
-/

@[expose] public section

universe w u₁ u₂ u₃

/-!
## The naive cotangent complex commutes with localization

Let `A → B` be a ring map, let `M ⊆ B` be a multiplicative subset, and let `α : A[x_i] → B` and
`β : A[y_j] → M⁻¹B` be presentations with a compatible ring map `A[x_i] → A[y_j]`. The induced map
of two term complexes `NL(α) ⊗_B M⁻¹B → NL(β)` is a quasi-isomorphism. On `H₀` this is the
bijectivity of `M⁻¹B ⊗_B Ω_{B/A} → Ω_{M⁻¹B/A}`, which is
`KaehlerDifferential.isLocalizedModule_map`. On `H₁` it says that the kernel of the base changed
differential of `NL(α)` maps bijectively onto the kernel of the differential of `NL(β)`, which is
proved here.

The comparison on `H₁` is phrased as `Set.BijOn` on the two kernels, the map being the restriction
of `(Cotangent.map f).liftBaseChange T`. The presentations are arbitrary, and the conclusion does
not depend on the choice of `f`, since any two maps of extensions induce the same map on `H₁`
(`Algebra.Extension.H1Cotangent.map_eq`).
-/

section

open Algebra

/-- If `φ ∘ u = v ∘ ψ` with `ψ` bijective and `v` injective, then `φ` maps the range of `u`
bijectively onto the range of `v`. -/
private theorem bijOn_range_of_comp_eq {α β γ δ : Type*} {φ : γ → δ} {u : α → γ} {v : β → δ}
    {ψ : α → β} (h : ∀ x, φ (u x) = v (ψ x)) (hψ : Function.Bijective ψ)
    (hv : Function.Injective v) : Set.BijOn φ (Set.range u) (Set.range v) := by
  have himage : φ '' Set.range u = Set.range v := by
    rw [← Set.range_comp, Function.comp_def, funext h, ← Function.comp_def,
      hψ.surjective.range_comp]
  refine himage ▸ Set.InjOn.bijOn_image ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  rw [h, h] at hxy
  exact congrArg u (hψ.injective (hv hxy))

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] {ι κ : Type*}

/-- `H¹` of the naive cotangent complex is independent of the presentation: the comparison map
induced by any map between two presentations of the same algebra is bijective. -/
@[sga "6 0 4.4" "partial"]
private theorem bijective_h1Cotangent_map {ι' : Type*} {P : Generators R S ι}
    {P' : Generators R S ι'} (g : P.toExtension.Hom P'.toExtension) :
    Function.Bijective (Extension.H1Cotangent.map g) := by
  rw [Extension.H1Cotangent.map_eq g (Generators.defaultHom P P').toExtensionHom]
  exact (Generators.H1Cotangent.equiv P P').bijective

/-- For a localization `T = M⁻¹S` of `S` and arbitrary presentations `P` of `S` and `Q` of `T`
over `R`, the comparison map exhibits `H¹(L_Q)` as the localization of `H¹(L_P)` at `M`. -/
private theorem isLocalizedModule_h1Cotangent_map (M : Submonoid S) [IsLocalization M T]
    {P : Generators R S ι} {Q : Generators R T κ} (f : P.toExtension.Hom Q.toExtension) :
    IsLocalizedModule M (Extension.H1Cotangent.map f) := by
  set a := (Generators.defaultHom P (Generators.self R S)).toExtensionHom
  set b := (Generators.defaultHom Q (Generators.self R T)).toExtensionHom
  have key : (Extension.H1Cotangent.map b).restrictScalars S ∘ₗ Extension.H1Cotangent.map f
      = Algebra.H1Cotangent.map R R S T ∘ₗ Extension.H1Cotangent.map a :=
    LinearMap.ext fun x ↦ by
      change Extension.H1Cotangent.map b (Extension.H1Cotangent.map f x)
        = Algebra.H1Cotangent.map R R S T (Extension.H1Cotangent.map a x)
      rw [Algebra.H1Cotangent.map, ← Extension.H1Cotangent.map_comp_apply,
        ← Extension.H1Cotangent.map_comp_apply]
      exact congr($(Extension.H1Cotangent.map_eq _ _) x)
  have hcomp : IsLocalizedModule M
      ((Extension.H1Cotangent.map b).restrictScalars S ∘ₗ Extension.H1Cotangent.map f) := by
    rw [key, IsLocalizedModule.comp_iff_of_bijective_right M _ (bijective_h1Cotangent_map a)]
    infer_instance
  exact (IsLocalizedModule.comp_iff_of_bijective_left M _ (bijective_h1Cotangent_map b)).mp hcomp

omit [IsScalarTower R S T] in
/-- The comparison map of naive cotangent complexes carries the first homology into the first
homology. -/
private theorem map_liftBaseChange_comp_h1Cotangentι_baseChange {P : Extension R S}
    {Q : Extension R T} (f : P.Hom Q) :
    (Extension.Cotangent.map f).liftBaseChange T ∘ₗ P.h1Cotangentι.baseChange T
      = Q.h1Cotangentι ∘ₗ (Extension.H1Cotangent.map f).liftBaseChange T := by
  ext x
  rfl

end

/-- **The naive cotangent complex commutes with localization**, on `H₁`: let `A → B` be a ring
map, let `M ⊆ B` be a multiplicative subset with localization `M⁻¹B`, and let `α`, `β` be
presentations of `B` and of `M⁻¹B` over `A` with a compatible map `f` between them. Then the map
`M⁻¹B ⊗_B I/I² → J/J²` induced by `f` carries the kernel of the base changed differential of
`NL(α)` bijectively onto the kernel of the differential of `NL(β)`. -/
@[stacks 00S7 "The `H₁` half at the level of the complexes, where the homology is `ker (d ⊗ T)`
rather than `T ⊗ ker d`. The `H₀` half is `KaehlerDifferential.isLocalizedModule_map` and the
`H¹(L)`-level `H₁` half is `Algebra.H1Cotangent.isLocalizedModule`. See the module docstring."]
public theorem Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T] {ι κ : Type*} {P : Algebra.Generators R S ι}
    {Q : Algebra.Generators R T κ} (f : P.toExtension.Hom Q.toExtension) :
    Set.BijOn ((Algebra.Extension.Cotangent.map f).liftBaseChange T)
      (LinearMap.ker (P.toExtension.cotangentComplex.baseChange T))
      (LinearMap.ker Q.toExtension.cotangentComplex) := by
  have : Module.Flat S T := IsLocalization.flat T M
  have hex : Function.Exact (P.toExtension.h1Cotangentι.baseChange T)
      (P.toExtension.cotangentComplex.baseChange T) :=
    Module.Flat.lTensor_exact T Extension.exact_hCotangentι_cotangentComplex
  rw [hex.linearMap_ker_eq, Extension.exact_hCotangentι_cotangentComplex.linearMap_ker_eq,
    LinearMap.coe_range, LinearMap.coe_range]
  exact bijOn_range_of_comp_eq
    (fun y ↦ congr($(map_liftBaseChange_comp_h1Cotangentι_baseChange f) y))
    ((isLocalizedModule_iff_isBaseChange M T _).mp (isLocalizedModule_h1Cotangent_map M f))
    Extension.h1Cotangentι_injective

end

/-! ## Transvections of a product of modules -/

section Transvection

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The transvection `(x, y) ↦ (x + u y, y)` of `M × N` along `u : N →ₗ[A] M`, the linear
automorphism with matrix `[[1, u], [0, 1]]`. -/
@[sga "6 X 6.4" "more general"]
private def transvection (u : N →ₗ[A] M) : (M × N) ≃ₗ[A] (M × N) :=
  (LinearEquiv.prodComm A M N).trans
    (((LinearEquiv.refl A N).skewProd (LinearEquiv.refl A M) u).trans
      (LinearEquiv.prodComm A N M))

private lemma transvection_apply (u : N →ₗ[A] M) (x : M × N) :
    transvection u x = (x.1 + u x.2, x.2) := by
  simp [transvection]

private lemma transvection_symm_apply (u : N →ₗ[A] M) (x : M × N) :
    (transvection u).symm x = (x.1 - u x.2, x.2) := by
  simp [transvection, sub_eq_add_neg]

end Transvection

/-!
## The naive cotangent complex and localization away from an element

Let `A → B` be a ring map, let `g ∈ B` and let `α : P = A[x_i, i ∈ ι] → B` be a presentation with
kernel `I`. Adjoining one variable `x` and sending it to `1/g` gives a presentation
`β : P[x] → B_g` of the localization `B_g` over `A`, whose kernel `J` is generated by `I` together
with `f x - 1`, for any `f ∈ P` with `α(f) = g`. The two term naive cotangent complex of `β`
decomposes as a direct sum of complexes
```
NL(β) ≅ NL(α) ⊗_B B_g ⊕ ( B_g --g--> B_g ),
```
compatibly with the canonical maps `NL(α) ⊗_B B_g → NL(β) → NL(B[x] → B_g)` induced by
`P → P[x]` and by `P[x] → B[x]`. Degreewise this is the pair of splittings
```
J/J² = (I/I²)_g ⊕ B_g·(f x - 1),
Ω_{P[x]/A} ⊗ B_g = Ω_{P/A} ⊗ B_g ⊕ B_g·(g⁻²df + dx),
```
which are compatible with the differentials because `d(f x - 1) = x df + f dx` equals
`g·(g⁻²df + dx)` in `Ω_{P[x]/A} ⊗ B_g`. The second summand is the naive cotangent complex of
`Algebra.Generators.localizationAway T g`: it is free of rank one in each degree, on `g x - 1` and
on `dx`, and its differential is multiplication by `g`, so it is contractible.
-/

section

open TensorProduct MvPolynomial Algebra Algebra.Generators

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w}

private lemma aeval_pderiv_C_mul_X_sub_one (g : S) (v : Unit → T) :
    (aeval v) ((pderiv ()) (C g * X () - 1)) = algebraMap S T g := by
  simp only [map_sub, pderiv_C_mul, pderiv_X_self, mul_one, pderiv_one, sub_zero, algHom_C]

section LocalizationAway

variable (g : S) [IsLocalization.Away g T]

/-- The differential of the naive cotangent complex of the canonical presentation
`S[x] → S_g`, `x ↦ 1/g` sends the class of `g x - 1` to `g dx`. -/
private lemma cotangentComplex_cMulXSubOneCotangent :
    (localizationAway T g).toExtension.cotangentComplex (cMulXSubOneCotangent T g) =
      algebraMap S T g • (localizationAway T g).cotangentSpaceBasis () := by
  apply (localizationAway T g).cotangentSpaceBasis.repr.injective
  rw [cMulXSubOneCotangent, Extension.cotangentComplex_mk, map_smul, Module.Basis.repr_self]
  refine Finsupp.ext fun j ↦ ?_
  obtain ⟨⟩ := j
  rw [cotangentSpaceBasis_repr_one_tmul, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  exact aeval_pderiv_C_mul_X_sub_one g _

/-- The differential of the naive cotangent complex of the canonical presentation
`S[x] → S_g`, `x ↦ 1/g`, as a linear equivalence: both terms are free of rank one, on `g x - 1`
and on `dx`, and the differential is multiplication by the unit `g`. -/
private noncomputable def cotangentComplexEquivAway :
    (localizationAway T g).toExtension.Cotangent ≃ₗ[T]
      (localizationAway T g).toExtension.CotangentSpace :=
  (basisCotangentAway T g).equiv
    ((localizationAway T g).cotangentSpaceBasis.unitsSMul fun _ ↦
      (IsLocalization.Away.algebraMap_isUnit (S := T) g).unit) (Equiv.refl Unit)

private lemma cotangentComplexEquivAway_toLinearMap :
    (cotangentComplexEquivAway (T := T) g).toLinearMap =
      (localizationAway T g).toExtension.cotangentComplex := by
  refine (basisCotangentAway T g).ext fun i ↦ ?_
  obtain ⟨⟩ := i
  rw [LinearEquiv.coe_coe, cotangentComplexEquivAway, Module.Basis.equiv_apply,
    Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, basisCotangentAway_apply,
    cotangentComplex_cMulXSubOneCotangent]

private lemma cotangentComplexEquivAway_symm_cotangentComplex
    (b : (localizationAway T g).toExtension.Cotangent) :
    (cotangentComplexEquivAway (T := T) g).symm
      ((localizationAway T g).toExtension.cotangentComplex b) = b := by
  rw [← cotangentComplexEquivAway_toLinearMap g]
  exact (cotangentComplexEquivAway (T := T) g).symm_apply_apply b

variable (P : Generators R S ι)

private lemma relation_mem_ker :
    rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1 ∈ ((localizationAway T g).comp P).ker := by
  rw [comp_localizationAway_ker (T := T) g P (P.σ g) (by simp)]
  exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)

/-- The class of `f x - 1` in `J/J²`, for `f = P.σ g ∈ P` the chosen preimage of `g`. -/
private noncomputable def relCotangent :
    ((localizationAway T g).comp P).toExtension.Cotangent :=
  Extension.Cotangent.mk ⟨_, relation_mem_ker g P⟩

private lemma map_ofComp_relCotangent :
    Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom
        (relCotangent g P) = cMulXSubOneCotangent T g := by
  rw [relCotangent, Extension.Cotangent.map_mk]
  congr 1
  exact Subtype.ext (toAlgHom_ofComp_localizationAway P g)

/-- The splitting of `0 → Ω_{P/A} ⊗ B_g → Ω_{P[x]/A} ⊗ B_g → Ω_{B[x]/B} ⊗ B_g → 0` by `dx`,
with the summand `Ω_{P/A} ⊗ B_g` first. -/
private noncomputable def cotangentSpaceCompEquiv :
    ((localizationAway T g).comp P).toExtension.CotangentSpace ≃ₗ[T]
      T ⊗[S] P.toExtension.CotangentSpace ×
        (localizationAway T g).toExtension.CotangentSpace :=
  (CotangentSpace.compEquiv (localizationAway T g) P).trans (LinearEquiv.prodComm T _ _)

private lemma cotangentSpaceCompEquiv_symm_comp_inl :
    (cotangentSpaceCompEquiv g P).symm.toLinearMap ∘ₗ LinearMap.inl T _ _ =
      (Extension.CotangentSpace.map
        ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T := by
  rw [← CotangentSpace.compEquiv_symm_inr (localizationAway T g) P]
  ext a
  simp [cotangentSpaceCompEquiv]

private lemma snd_comp_cotangentSpaceCompEquiv :
    LinearMap.snd T _ _ ∘ₗ (cotangentSpaceCompEquiv g P).toLinearMap =
      Extension.CotangentSpace.map ((localizationAway T g).ofComp P).toExtensionHom := by
  rw [← CotangentSpace.fst_compEquiv (localizationAway T g) P]
  ext a
  simp [cotangentSpaceCompEquiv]

/-- The splitting of `(I/I²)_g → J/J² → (gx-1)/(gx-1)² → 0` by the class of `f x - 1`. -/
private noncomputable def cotangentCompEquiv :
    ((localizationAway T g).comp P).toExtension.Cotangent ≃ₗ[T]
      T ⊗[S] P.toExtension.Cotangent × (localizationAway T g).toExtension.Cotangent :=
  cotangentCompLocalizationAwayEquiv g P (map_ofComp_relCotangent g P)

private lemma cotangentCompEquiv_symm_comp_inl :
    (cotangentCompEquiv g P).symm.toLinearMap ∘ₗ LinearMap.inl T _ _ =
      (Extension.Cotangent.map
        ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T :=
  cotangentCompLocalizationAwayEquiv_symm_comp_inl g P (map_ofComp_relCotangent g P)

private lemma snd_comp_cotangentCompEquiv :
    LinearMap.snd T _ _ ∘ₗ (cotangentCompEquiv g P).toLinearMap =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom :=
  snd_comp_cotangentCompLocalizationAwayEquiv g P (map_ofComp_relCotangent g P)

/-- The splitting by `f x - 1` is a section of `J/J² → (gx-1)/(gx-1)²`. -/
private lemma map_ofComp_cotangentCompEquiv_symm_inr
    (b : (localizationAway T g).toExtension.Cotangent) :
    Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom
        ((cotangentCompEquiv g P).symm (LinearMap.inr T _ _ b)) = b := by
  rw [← DFunLike.congr_fun (snd_comp_cotangentCompEquiv g P)
    ((cotangentCompEquiv g P).symm (LinearMap.inr T _ _ b))]
  simp

/-- The off-diagonal entry of the differential of `NL(β)` read in the splittings
`J/J² = (I/I²)_g ⊕ B_g (f x - 1)` and `Ω_{P[x]/A} ⊗ B_g = Ω_{P/A} ⊗ B_g ⊕ B_g dx`: it sends
`g dx` to the `Ω_{P/A} ⊗ B_g`-component of `d(f x - 1) = x df + f dx`, that is to `g⁻¹df`. -/
private noncomputable def shearMap :
    (localizationAway T g).toExtension.CotangentSpace →ₗ[T]
      T ⊗[S] P.toExtension.CotangentSpace :=
  LinearMap.fst T _ _ ∘ₗ (cotangentSpaceCompEquiv g P).toLinearMap ∘ₗ
    ((localizationAway T g).comp P).toExtension.cotangentComplex ∘ₗ
    (cotangentCompEquiv g P).symm.toLinearMap ∘ₗ LinearMap.inr T _ _ ∘ₗ
    (cotangentComplexEquivAway g).symm.toLinearMap

private lemma shearMap_cotangentComplex (b : (localizationAway T g).toExtension.Cotangent) :
    shearMap g P ((localizationAway T g).toExtension.cotangentComplex b) =
      (cotangentSpaceCompEquiv g P
        (((localizationAway T g).comp P).toExtension.cotangentComplex
          ((cotangentCompEquiv g P).symm (LinearMap.inr T _ _ b)))).1 := by
  simp only [shearMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.fst_apply, cotangentComplexEquivAway_symm_cotangentComplex]

/-- The `Ω_{B[x]/B} ⊗ B_g`-component of the differential of `NL(β)` is the differential of
`NL(B[x] → B_g)`. -/
private lemma snd_cotangentSpaceCompEquiv_cotangentComplex
    (z : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (cotangentSpaceCompEquiv g P
        (((localizationAway T g).comp P).toExtension.cotangentComplex z)).2 =
      (localizationAway T g).toExtension.cotangentComplex
        (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom z) := by
  have h := DFunLike.congr_fun (snd_comp_cotangentSpaceCompEquiv g P)
    (((localizationAway T g).comp P).toExtension.cotangentComplex z)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.snd_apply] at h
  rw [h, Extension.CotangentSpace.map_cotangentComplex]

/-- On the summand `(I/I²)_g` of `J/J²` the differential of `NL(β)` is the differential of
`NL(α) ⊗_B B_g`. -/
private lemma cotangentSpaceCompEquiv_cotangentComplex_inl
    (a : T ⊗[S] P.toExtension.Cotangent) :
    cotangentSpaceCompEquiv g P
        (((localizationAway T g).comp P).toExtension.cotangentComplex
          ((cotangentCompEquiv g P).symm (LinearMap.inl T _ _ a))) =
      (P.toExtension.cotangentComplex.baseChange T a, 0) := by
  rw [show (cotangentCompEquiv g P).symm (LinearMap.inl T _ _ a) =
      (Extension.Cotangent.map
        ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T a from
    DFunLike.congr_fun (cotangentCompEquiv_symm_comp_inl g P) a,
    ← LinearMap.comp_apply, ← H1Cotangent.map_comp_cotangentComplex_baseChange,
    LinearMap.comp_apply, ← cotangentSpaceCompEquiv_symm_comp_inl g P]
  simp

/-- On the summand `B_g (f x - 1)` of `J/J²` the differential of `NL(β)` is
`d(f x - 1) = x df + f dx`: its `Ω_{B[x]/B} ⊗ B_g`-component is `g dx`, the differential of
`NL(B[x] → B_g)`, and its `Ω_{P/A} ⊗ B_g`-component is `shearMap` of that. -/
private lemma cotangentSpaceCompEquiv_cotangentComplex_inr
    (b : (localizationAway T g).toExtension.Cotangent) :
    cotangentSpaceCompEquiv g P
        (((localizationAway T g).comp P).toExtension.cotangentComplex
          ((cotangentCompEquiv g P).symm (LinearMap.inr T _ _ b))) =
      (shearMap g P ((localizationAway T g).toExtension.cotangentComplex b),
        (localizationAway T g).toExtension.cotangentComplex b) :=
  Prod.ext (shearMap_cotangentComplex g P b).symm
    (by rw [snd_cotangentSpaceCompEquiv_cotangentComplex,
      map_ofComp_cotangentCompEquiv_symm_inr])

/-- **The differential of `NL(β)` is triangular** in the splittings
`J/J² = (I/I²)_g ⊕ B_g (f x - 1)` and `Ω_{P[x]/A} ⊗ B_g = Ω_{P/A} ⊗ B_g ⊕ B_g dx`: its matrix
is `[[d(α) ⊗ B_g, shearMap ∘ g], [0, g]]`. -/
private lemma cotangentSpaceCompEquiv_cotangentComplex
    (z : ((localizationAway T g).comp P).toExtension.Cotangent) :
    cotangentSpaceCompEquiv g P
        (((localizationAway T g).comp P).toExtension.cotangentComplex z) =
      (P.toExtension.cotangentComplex.baseChange T (cotangentCompEquiv g P z).1 +
          shearMap g P ((localizationAway T g).toExtension.cotangentComplex
            (cotangentCompEquiv g P z).2),
        (localizationAway T g).toExtension.cotangentComplex (cotangentCompEquiv g P z).2) := by
  set a := (cotangentCompEquiv g P z).1 with ha
  set b := (cotangentCompEquiv g P z).2 with hb
  have hz : z = (cotangentCompEquiv g P).symm (LinearMap.inl T _ _ a) +
      (cotangentCompEquiv g P).symm (LinearMap.inr T _ _ b) := by
    rw [← map_add, ← (cotangentCompEquiv g P).symm_apply_apply z]
    congr 1
    simp [ha, hb]
  rw [hz, map_add, map_add, cotangentSpaceCompEquiv_cotangentComplex_inl,
    cotangentSpaceCompEquiv_cotangentComplex_inr, Prod.mk_add_mk, zero_add]

/-- The splitting of `0 → Ω_{P/A} ⊗ B_g → Ω_{P[x]/A} ⊗ B_g → Ω_{B[x]/B} ⊗ B_g → 0` by
`g⁻²df + dx`: the splitting by `dx` sheared by `shearMap`. -/
private noncomputable def cotangentSpaceCompEquivShear :
    ((localizationAway T g).comp P).toExtension.CotangentSpace ≃ₗ[T]
      T ⊗[S] P.toExtension.CotangentSpace ×
        (localizationAway T g).toExtension.CotangentSpace :=
  (cotangentSpaceCompEquiv g P).trans (transvection (-shearMap (T := T) g P))

private lemma cotangentSpaceCompEquivShear_apply
    (x : ((localizationAway T g).comp P).toExtension.CotangentSpace) :
    cotangentSpaceCompEquivShear g P x =
      transvection (-shearMap (T := T) g P) (cotangentSpaceCompEquiv g P x) := by
  rw [cotangentSpaceCompEquivShear, LinearEquiv.trans_apply]

private lemma cotangentSpaceCompEquivShear_symm_apply
    (p : T ⊗[S] P.toExtension.CotangentSpace ×
      (localizationAway T g).toExtension.CotangentSpace) :
    (cotangentSpaceCompEquivShear g P).symm p =
      (cotangentSpaceCompEquiv g P).symm ((transvection (-shearMap (T := T) g P)).symm p) := by
  rw [cotangentSpaceCompEquivShear, LinearEquiv.symm_trans_apply]

/-- The splittings by `f x - 1` and by `g⁻²df + dx` are compatible with the differentials, i.e.
they identify `NL(β)` with `NL(α) ⊗_B B_g ⊕ NL(B[x] → B_g)`. -/
private lemma cotangentSpaceCompEquivShear_comp_cotangentComplex :
    (cotangentSpaceCompEquivShear g P).toLinearMap ∘ₗ
        ((localizationAway T g).comp P).toExtension.cotangentComplex =
      (P.toExtension.cotangentComplex.baseChange T).prodMap
          (localizationAway T g).toExtension.cotangentComplex ∘ₗ
        (cotangentCompEquiv g P).toLinearMap := by
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentSpaceCompEquivShear_apply, cotangentSpaceCompEquiv_cotangentComplex,
    transvection_apply, LinearMap.neg_apply, add_neg_cancel_right, LinearMap.prodMap_apply]

private lemma cotangentSpaceCompEquivShear_symm_comp_inl :
    (cotangentSpaceCompEquivShear g P).symm.toLinearMap ∘ₗ LinearMap.inl T _ _ =
      (Extension.CotangentSpace.map
        ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T := by
  rw [← cotangentSpaceCompEquiv_symm_comp_inl g P]
  refine LinearMap.ext fun a ↦ ?_
  simp [cotangentSpaceCompEquivShear_symm_apply, transvection_symm_apply]

private lemma snd_comp_cotangentSpaceCompEquivShear :
    LinearMap.snd T _ _ ∘ₗ (cotangentSpaceCompEquivShear g P).toLinearMap =
      Extension.CotangentSpace.map ((localizationAway T g).ofComp P).toExtensionHom := by
  rw [← snd_comp_cotangentSpaceCompEquiv g P]
  refine LinearMap.ext fun z ↦ ?_
  simp [cotangentSpaceCompEquivShear_apply, transvection_apply]

end LocalizationAway

namespace Algebra.Generators

/-- **The naive cotangent complex commutes with localization at an element**: let `A → B` be a
ring map, let `α : P = A[x_i, i ∈ ι] → B` be a presentation with kernel `I`, let `g ∈ B` and let
`B_g` be a localization of `B` away from `g`. Write `β : P[x] → B_g`, `x ↦ 1/g` for the induced
presentation of `B_g` over `A`, with kernel `J`, and `B[x] → B_g` for the canonical presentation
of `B_g` over `B`. Then there are splittings
`J/J² ≅ (I/I²) ⊗_B B_g ⊕ (gx-1)/(gx-1)²` and
`Ω_{P[x]/A} ⊗ B_g ≅ (Ω_{P/A} ⊗_P B) ⊗_B B_g ⊕ Ω_{B[x]/B} ⊗ B_g`
of the two canonical exact rows which are compatible with the differentials, i.e. which
identify the two term complex `NL(β)` with the direct sum of `NL(α) ⊗_B B_g` and of the
complex `NL(B[x] → B_g) = (B_g --g--> B_g)`. -/
@[stacks 08JZ "Item (3), which contains items (1) and (2): splittings of both rows of the
source's diagram that are simultaneously compatible with the differentials. Mathlib has each
row separately, but not compatibly. See the module docstring."]
public theorem exists_cotangentComplex_comp_localizationAway_eq_prodMap
    (g : S) [IsLocalization.Away g T] (P : Generators R S ι) :
    ∃ (e : ((localizationAway T g).comp P).toExtension.Cotangent ≃ₗ[T]
        T ⊗[S] P.toExtension.Cotangent × (localizationAway T g).toExtension.Cotangent)
      (e' : ((localizationAway T g).comp P).toExtension.CotangentSpace ≃ₗ[T]
        T ⊗[S] P.toExtension.CotangentSpace ×
          (localizationAway T g).toExtension.CotangentSpace),
      e'.toLinearMap ∘ₗ ((localizationAway T g).comp P).toExtension.cotangentComplex =
          (P.toExtension.cotangentComplex.baseChange T).prodMap
            (localizationAway T g).toExtension.cotangentComplex ∘ₗ e.toLinearMap ∧
        e.symm.toLinearMap ∘ₗ LinearMap.inl T _ _ =
          (Extension.Cotangent.map
            ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T ∧
        LinearMap.snd T _ _ ∘ₗ e.toLinearMap =
          Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom ∧
        e'.symm.toLinearMap ∘ₗ LinearMap.inl T _ _ =
          (Extension.CotangentSpace.map
            ((localizationAway T g).toComp P).toExtensionHom).liftBaseChange T ∧
        LinearMap.snd T _ _ ∘ₗ e'.toLinearMap =
          Extension.CotangentSpace.map ((localizationAway T g).ofComp P).toExtensionHom :=
  ⟨cotangentCompEquiv g P, cotangentSpaceCompEquivShear g P,
    cotangentSpaceCompEquivShear_comp_cotangentComplex g P,
    cotangentCompEquiv_symm_comp_inl g P, snd_comp_cotangentCompEquiv g P,
    cotangentSpaceCompEquivShear_symm_comp_inl g P,
    snd_comp_cotangentSpaceCompEquivShear g P⟩

end Algebra.Generators

end

/-!
## Invariance of the conormal module under localization at an element

Let `R → S` be a ring map, let `g ∈ S`, let `α : R[x₁, …, xₙ] → S` be a presentation of `S` with
kernel `I` and let `β : R[y₁, …, y_m] → S_g` be a presentation of the localization `S_g` with
kernel `J`. Then there is an isomorphism of `S_g`-modules
```
(I/I²)_g ⊕ S_g^{⊕m} ≅ J/J² ⊕ S_g^{⊕n}.
```
Indeed the naive cotangent complexes of `α` and of `β` are homotopy equivalent after inverting
`g`, and Schanuel's lemma for two term complexes turns a homotopy equivalence into an isomorphism
of the degree one terms up to the degree zero terms, which here are free of ranks `n` and `m`.

Here `(I/I²)_g` is the base change `T ⊗[S] P.toExtension.Cotangent`, the free module `S_g^{⊕k}` is
`Fin k → T`, and a direct sum of two modules is their product. Homotopy equivalences of two term
complexes are recorded by the structure `TwoTermHomotopyEquiv`.
-/

section

open TensorProduct Algebra Algebra.Generators

section TwoTerm

variable {T : Type*} [CommRing T]

variable {A₁ A₀ B₁ B₀ C₁ C₀ D₁ D₀ : Type*}
  [AddCommGroup A₁] [Module T A₁] [AddCommGroup A₀] [Module T A₀]
  [AddCommGroup B₁] [Module T B₁] [AddCommGroup B₀] [Module T B₀]
  [AddCommGroup C₁] [Module T C₁] [AddCommGroup C₀] [Module T C₀]
  [AddCommGroup D₁] [Module T D₁] [AddCommGroup D₀] [Module T D₀]

/-- A homotopy equivalence between the two term complexes `dA : A₁ → A₀` and `dB : B₁ → B₀` of
`T`-modules: two chain maps `f` and `g` in opposite directions, together with homotopies `h`
and `h'` from `g ∘ f` and from `f ∘ g` to the identity. -/
private structure TwoTermHomotopyEquiv (dA : A₁ →ₗ[T] A₀) (dB : B₁ →ₗ[T] B₀) where
  /-- The chain map from `A` to `B` in degree one. -/
  f₁ : A₁ →ₗ[T] B₁
  /-- The chain map from `A` to `B` in degree zero. -/
  f₀ : A₀ →ₗ[T] B₀
  /-- The chain map from `B` to `A` in degree one. -/
  g₁ : B₁ →ₗ[T] A₁
  /-- The chain map from `B` to `A` in degree zero. -/
  g₀ : B₀ →ₗ[T] A₀
  /-- The homotopy from `g ∘ f` to the identity of `A`. -/
  h : A₀ →ₗ[T] A₁
  /-- The homotopy from `f ∘ g` to the identity of `B`. -/
  h' : B₀ →ₗ[T] B₁
  /-- `f` is a chain map. -/
  commf : ∀ x, dB (f₁ x) = f₀ (dA x)
  /-- `g` is a chain map. -/
  commg : ∀ x, dA (g₁ x) = g₀ (dB x)
  /-- `h` is a homotopy from `g ∘ f` to the identity, in degree one. -/
  sub_comp₁ : ∀ x, x - g₁ (f₁ x) = h (dA x)
  /-- `h` is a homotopy from `g ∘ f` to the identity, in degree zero. -/
  sub_comp₀ : ∀ x, x - g₀ (f₀ x) = dA (h x)
  /-- `h'` is a homotopy from `f ∘ g` to the identity, in degree one. -/
  sub_comp₁' : ∀ x, x - f₁ (g₁ x) = h' (dB x)
  /-- `h'` is a homotopy from `f ∘ g` to the identity, in degree zero. -/
  sub_comp₀' : ∀ x, x - f₀ (g₀ x) = dB (h' x)

namespace TwoTermHomotopyEquiv

variable {dA : A₁ →ₗ[T] A₀} {dB : B₁ →ₗ[T] B₀} {dC : C₁ →ₗ[T] C₀} {dD : D₁ →ₗ[T] D₀}

/-- **Homotopies compose**, in degree one: if `h` is a homotopy from `g₁ ∘ f₁` to the identity
and `k` is one from `g₁' ∘ f₁'` to the identity, then `h + g₁ ∘ k ∘ f₀` is a homotopy from
`(g₁ ∘ g₁') ∘ (f₁' ∘ f₁)` to the identity, provided `f` is a chain map. -/
private lemma homotopy_comp₁ {f₁ : A₁ →ₗ[T] B₁} {f₀ : A₀ →ₗ[T] B₀} {g₁ : B₁ →ₗ[T] A₁}
    {f₁' : B₁ →ₗ[T] C₁} {g₁' : C₁ →ₗ[T] B₁} {h : A₀ →ₗ[T] A₁} {k : B₀ →ₗ[T] B₁}
    (commf : ∀ x, dB (f₁ x) = f₀ (dA x)) (H : ∀ x, x - g₁ (f₁ x) = h (dA x))
    (K : ∀ y, y - g₁' (f₁' y) = k (dB y)) (x : A₁) :
    x - g₁ (g₁' (f₁' (f₁ x))) = h (dA x) + g₁ (k (f₀ (dA x))) := by
  have hk := congrArg g₁ (K (f₁ x))
  rw [map_sub, commf] at hk
  rw [← H x, ← hk]
  abel

/-- **Homotopies compose**, in degree zero: if `h` is a homotopy from `g₀ ∘ f₀` to the identity
and `k` is one from `g₀' ∘ f₀'` to the identity, then `h + g₁ ∘ k ∘ f₀` is a homotopy from
`(g₀ ∘ g₀') ∘ (f₀' ∘ f₀)` to the identity, provided `g` is a chain map. -/
private lemma homotopy_comp₀ {f₀ : A₀ →ₗ[T] B₀} {g₁ : B₁ →ₗ[T] A₁} {g₀ : B₀ →ₗ[T] A₀}
    {f₀' : B₀ →ₗ[T] C₀} {g₀' : C₀ →ₗ[T] B₀} {h : A₀ →ₗ[T] A₁} {k : B₀ →ₗ[T] B₁}
    (commg : ∀ y, dA (g₁ y) = g₀ (dB y)) (H : ∀ x, x - g₀ (f₀ x) = dA (h x))
    (K : ∀ y, y - g₀' (f₀' y) = dB (k y)) (x : A₀) :
    x - g₀ (g₀' (f₀' (f₀ x))) = dA (h x + g₁ (k (f₀ x))) := by
  have hk := congrArg g₀ (K (f₀ x))
  rw [map_sub, ← commg] at hk
  rw [map_add, ← H x, ← hk]
  abel

/-- The composition of two homotopy equivalences of two term complexes. -/
private def trans (E : TwoTermHomotopyEquiv dA dB) (F : TwoTermHomotopyEquiv dB dC) :
    TwoTermHomotopyEquiv dA dC where
  f₁ := F.f₁ ∘ₗ E.f₁
  f₀ := F.f₀ ∘ₗ E.f₀
  g₁ := E.g₁ ∘ₗ F.g₁
  g₀ := E.g₀ ∘ₗ F.g₀
  h := E.h + E.g₁ ∘ₗ F.h ∘ₗ E.f₀
  h' := F.h' + F.f₁ ∘ₗ E.h' ∘ₗ F.g₀
  commf x := by simp only [LinearMap.comp_apply, F.commf, E.commf]
  commg x := by simp only [LinearMap.comp_apply, E.commg, F.commg]
  sub_comp₁ x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply]
      using homotopy_comp₁ E.commf E.sub_comp₁ F.sub_comp₁ x
  sub_comp₀ x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply]
      using homotopy_comp₀ E.commg E.sub_comp₀ F.sub_comp₀ x
  sub_comp₁' x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply]
      using homotopy_comp₁ F.commg F.sub_comp₁' E.sub_comp₁' x
  sub_comp₀' x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply]
      using homotopy_comp₀ F.commf F.sub_comp₀' E.sub_comp₀' x

/-- The map `A₁ ⊕ B₀ → B₁ ⊕ A₀` given by the matrix with rows `(f₁, -h')` and `(dA, g₀)`. -/
private def prodMap (E : TwoTermHomotopyEquiv dA dB) : (A₁ × B₀) →ₗ[T] (B₁ × A₀) :=
  (E.f₁.coprod (-E.h')).prod (dA.coprod E.g₀)

/-- The map `B₁ ⊕ A₀ → A₁ ⊕ B₀` given by the matrix with rows `(g₁, h)` and `(-dB, f₀)`. -/
private def prodMapInv (E : TwoTermHomotopyEquiv dA dB) : (B₁ × A₀) →ₗ[T] (A₁ × B₀) :=
  (E.g₁.coprod E.h).prod ((-dB).coprod E.f₀)

private lemma prodMap_apply (E : TwoTermHomotopyEquiv dA dB) (x : A₁ × B₀) :
    E.prodMap x = (E.f₁ x.1 - E.h' x.2, dA x.1 + E.g₀ x.2) := by
  simp [prodMap, sub_eq_add_neg]

private lemma prodMapInv_apply (E : TwoTermHomotopyEquiv dA dB) (x : B₁ × A₀) :
    E.prodMapInv x = (E.g₁ x.1 + E.h x.2, -dB x.1 + E.f₀ x.2) := by
  simp [prodMapInv]

/-- `prodMapInv ∘ prodMap` is the transvection along `h ∘ g₀ - g₁ ∘ h'`. -/
private lemma prodMapInv_prodMap (E : TwoTermHomotopyEquiv dA dB) (x : A₁ × B₀) :
    E.prodMapInv (E.prodMap x) = transvection (E.h ∘ₗ E.g₀ - E.g₁ ∘ₗ E.h') x := by
  have h1 := E.sub_comp₁ x.1
  have h2 := E.sub_comp₀' x.2
  simp only [prodMap_apply, prodMapInv_apply, transvection_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_add, map_sub, E.commf, ← h1, ← h2, Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

/-- `prodMap ∘ prodMapInv` is the transvection along `f₁ ∘ h - h' ∘ f₀`. -/
private lemma prodMap_prodMapInv (E : TwoTermHomotopyEquiv dA dB) (x : B₁ × A₀) :
    E.prodMap (E.prodMapInv x) = transvection (E.f₁ ∘ₗ E.h - E.h' ∘ₗ E.f₀) x := by
  have h1 := E.sub_comp₁' x.1
  have h2 := E.sub_comp₀ x.2
  simp only [prodMap_apply, prodMapInv_apply, transvection_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_add, map_neg, E.commg, ← h1, ← h2, Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

private lemma bijective_prodMap (E : TwoTermHomotopyEquiv dA dB) :
    Function.Bijective E.prodMap :=
  ⟨fun x y hxy ↦ (transvection (E.h ∘ₗ E.g₀ - E.g₁ ∘ₗ E.h')).injective (by
      rw [← E.prodMapInv_prodMap, ← E.prodMapInv_prodMap, hxy]),
   fun y ↦ ⟨E.prodMapInv ((transvection (E.f₁ ∘ₗ E.h - E.h' ∘ₗ E.f₀)).symm y), by
      rw [E.prodMap_prodMapInv, LinearEquiv.apply_symm_apply]⟩⟩

/-- **Schanuel's lemma for two term complexes**: if the two term complexes `A₁ → A₀` and
`B₁ → B₀` are homotopy equivalent, then `A₁ ⊕ B₀ ≅ B₁ ⊕ A₀`. -/
private noncomputable def prodEquiv (E : TwoTermHomotopyEquiv dA dB) : (A₁ × B₀) ≃ₗ[T] (B₁ × A₀) :=
  LinearEquiv.ofBijective E.prodMap E.bijective_prodMap

/-- If a two term complex `C` is isomorphic, as a complex, to the direct sum of a two term
complex `A` and a two term complex `D` whose differential is bijective, then `A` and `C` are
homotopy equivalent: the second summand is contractible. -/
private noncomputable def ofProdOfBijective (dA : A₁ →ₗ[T] A₀) (dD : D₁ →ₗ[T] D₀)
    (dC : C₁ →ₗ[T] C₀) (e : C₁ ≃ₗ[T] A₁ × D₁) (e' : C₀ ≃ₗ[T] A₀ × D₀)
    (he : e'.toLinearMap ∘ₗ dC = dA.prodMap dD ∘ₗ e.toLinearMap)
    (hD : Function.Bijective dD) :
    TwoTermHomotopyEquiv dA dC :=
  let eD := LinearEquiv.ofBijective dD hD
  have hdC : ∀ x, e' (dC x) = (dA (e x).1, dD (e x).2) := fun x ↦ DFunLike.congr_fun he x
  have hsymm : ∀ y, eD.symm (dD y) = y := fun y ↦ eD.symm_apply_apply y
  have happly : ∀ z, dD (eD.symm z) = z := fun z ↦ eD.apply_symm_apply z
  { f₁ := e.symm.toLinearMap ∘ₗ LinearMap.inl T A₁ D₁
    f₀ := e'.symm.toLinearMap ∘ₗ LinearMap.inl T A₀ D₀
    g₁ := LinearMap.fst T A₁ D₁ ∘ₗ e.toLinearMap
    g₀ := LinearMap.fst T A₀ D₀ ∘ₗ e'.toLinearMap
    h := 0
    h' := e.symm.toLinearMap ∘ₗ LinearMap.inr T A₁ D₁ ∘ₗ eD.symm.toLinearMap ∘ₗ
      LinearMap.snd T A₀ D₀ ∘ₗ e'.toLinearMap
    commf := fun x ↦ e'.injective (by simp [hdC (e.symm (x, 0))])
    commg := fun x ↦ by simp [hdC x]
    sub_comp₁ := fun x ↦ by simp
    sub_comp₀ := fun x ↦ by simp
    sub_comp₁' := fun x ↦ by
      rw [sub_eq_iff_eq_add]
      refine e.injective ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, map_add,
        LinearEquiv.apply_symm_apply, hdC, hsymm, Prod.mk_add_mk, zero_add, add_zero]
    sub_comp₀' := fun x ↦ by
      rw [sub_eq_iff_eq_add]
      refine e'.injective ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, map_add, hdC,
        LinearEquiv.apply_symm_apply, map_zero, happly, Prod.mk_add_mk, zero_add,
        add_zero] }

end TwoTermHomotopyEquiv

end TwoTerm

section Cotangent

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {P P' : Extension R T}

/-- **A hom of extensions is unique up to homotopy**, in degree one: for homs `f : P → P'` and
`g : P' → P`, the map `Algebra.Extension.Hom.sub (.id P) (g.comp f)` on cotangent spaces is a
homotopy from `Cotangent.map g ∘ Cotangent.map f` to the identity of `P.Cotangent`. -/
private lemma sub_cotangentMap_comp (f : P.Hom P') (g : P'.Hom P) (x : P.Cotangent) :
    x - Extension.Cotangent.map g (Extension.Cotangent.map f x) =
      ((Extension.Hom.id P).sub (g.comp f)) (P.cotangentComplex x) := by
  have h1 := DFunLike.congr_fun
    (Extension.Cotangent.map_sub_map (Extension.Hom.id P) (g.comp f)) x
  simpa [Extension.Cotangent.map_comp, Extension.Cotangent.map_id] using h1

/-- **A hom of extensions is unique up to homotopy**, in degree zero: for homs `f : P → P'` and
`g : P' → P`, the map `Algebra.Extension.Hom.sub (.id P) (g.comp f)` on cotangent spaces is a
homotopy from `CotangentSpace.map g ∘ CotangentSpace.map f` to the identity of
`P.CotangentSpace`. -/
private lemma sub_cotangentSpaceMap_comp (f : P.Hom P') (g : P'.Hom P) (x : P.CotangentSpace) :
    x - Extension.CotangentSpace.map g (Extension.CotangentSpace.map f x) =
      P.cotangentComplex (((Extension.Hom.id P).sub (g.comp f)) x) := by
  have h1 := DFunLike.congr_fun
    (Extension.CotangentSpace.map_sub_map (Extension.Hom.id P) (g.comp f)) x
  simpa [Extension.CotangentSpace.map_comp, Extension.CotangentSpace.map_id] using h1

/-- Any two homs `f : P → P'` and `g : P' → P` of extensions of `T` over `R` form a homotopy
equivalence of the naive cotangent complexes. -/
private noncomputable def TwoTermHomotopyEquiv.ofExtensionHoms (f : P.Hom P') (g : P'.Hom P) :
    TwoTermHomotopyEquiv P.cotangentComplex P'.cotangentComplex where
  f₁ := Extension.Cotangent.map f
  f₀ := Extension.CotangentSpace.map f
  g₁ := Extension.Cotangent.map g
  g₀ := Extension.CotangentSpace.map g
  h := (Extension.Hom.id P).sub (g.comp f)
  h' := (Extension.Hom.id P').sub (f.comp g)
  commf x := (Extension.CotangentSpace.map_cotangentComplex _ x).symm
  commg x := (Extension.CotangentSpace.map_cotangentComplex _ x).symm
  sub_comp₁ := sub_cotangentMap_comp f g
  sub_comp₀ := sub_cotangentSpaceMap_comp f g
  sub_comp₁' := sub_cotangentMap_comp g f
  sub_comp₀' := sub_cotangentSpaceMap_comp g f

/-- Two presentations of the same algebra have homotopy equivalent naive cotangent complexes. -/
private noncomputable def homotopyEquivOfGenerators {ι ι' : Type*} (W : Generators R T ι)
    (Q : Generators R T ι') :
    TwoTermHomotopyEquiv W.toExtension.cotangentComplex Q.toExtension.cotangentComplex :=
  .ofExtensionHoms (defaultHom W Q).toExtensionHom (defaultHom Q W).toExtensionHom

end Cotangent

namespace Algebra.Generators

variable {R : Type*} {S : Type*} {T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- **The conormal module up to free summands, after localizing at an element**: let `R → S` be
a ring map, let `g ∈ S` and let `S_g` be a localization of `S` away from `g`. Let
`α : R[x₁, …, xₙ] → S` be a presentation of `S` over `R` with kernel `I` and let
`β : R[y₁, …, y_m] → S_g` be a presentation of `S_g` over `R` with kernel `J`. Then there is an
isomorphism of `S_g`-modules `(I/I²)_g ⊕ S_g^{⊕m} ≅ J/J² ⊕ S_g^{⊕n}`. -/
@[stacks 00S6 "The isomorphism is non-canonical: `Nonempty` of a linear equivalence is the whole
statement. See the module docstring."]
public theorem nonempty_cotangent_baseChange_prod_linearEquiv_of_isLocalizationAway
    (g : S) [IsLocalization.Away g T] {n m : ℕ}
    (P : Generators R S (Fin n)) (Q : Generators R T (Fin m)) :
    Nonempty (((T ⊗[S] P.toExtension.Cotangent) × (Fin m → T)) ≃ₗ[T]
      (Q.toExtension.Cotangent × (Fin n → T))) := by
  obtain ⟨e, e', hd, -, -, -, -⟩ :=
    Algebra.Generators.exists_cotangentComplex_comp_localizationAway_eq_prodMap (T := T) g P
  have E : TwoTermHomotopyEquiv (P.toExtension.cotangentComplex.baseChange T)
      Q.toExtension.cotangentComplex :=
    (TwoTermHomotopyEquiv.ofProdOfBijective _ _ _ e e' hd
      (cotangentComplexEquivAway_toLinearMap (T := T) g ▸
        (cotangentComplexEquivAway (T := T) g).bijective)).trans
      (homotopyEquivOfGenerators _ Q)
  exact ⟨((LinearEquiv.refl T _).prodCongr Q.cotangentSpaceBasis.equivFun.symm).trans
    (E.prodEquiv.trans ((LinearEquiv.refl T _).prodCongr
      (P.cotangentSpaceBasis.baseChange T).equivFun))⟩

end Algebra.Generators

end

/-!
## The naive cotangent complex of a localization is contractible

Let `A` be a commutative ring and `S ⊆ A` a multiplicative subset. Both homology modules
`H₀(NL_{S⁻¹A/A}) = Ω_{S⁻¹A/A}` and `H₁(NL_{S⁻¹A/A})` vanish, so the two term complex
`NL_{S⁻¹A/A}` is contractible. The localization is an arbitrary `A`-algebra `B` with
`IsLocalization S B`.
-/

section

variable (A : Type*) [CommRing A] (S : Submonoid A)
         (B : Type*) [CommRing B] [Algebra A B]

/-- `H₀(NL_{S⁻¹A/A}) = Ω_{S⁻¹A/A} = 0`: the module of Kähler differentials of a
localization `S⁻¹A` over `A` vanishes. -/
@[stacks 07BR]
theorem kaehlerDifferential_subsingleton_of_isLocalization
    [IsLocalization S B] :
    Subsingleton (Ω[B⁄A]) := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  exact Algebra.FormallyEtale.subsingleton_kaehlerDifferential

/-- `H₁(NL_{S⁻¹A/A}) = 0`: the first naive cotangent homology of a localization `S⁻¹A`
over `A` vanishes. -/
@[stacks 07BR]
theorem h1Cotangent_subsingleton_of_isLocalization
    [IsLocalization S B] :
    Subsingleton (Algebra.H1Cotangent A B) := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

end

/-!
## The naive cotangent complex and localization of the base ring

Let `M ⊆ A` be a multiplicative subset, let `Aₘ` be a localization of `A` at `M` and let `Aₘ → B`
be a ring map. Then the canonical map `NL_{B/A} → NL_{B/Aₘ}` is a homotopy equivalence of two term
complexes of `B`-modules. The complexes are those of the canonical presentations
`P = (Algebra.Generators.self A B).toExtension` and
`Q = (Algebra.Generators.self Aₘ B).toExtension`, and the canonical map has components
`Algebra.Extension.Cotangent.map h` and `Algebra.Extension.CotangentSpace.map h`, for `h : P.Hom Q`
the morphism of extensions induced by the tower `A → Aₘ → B`. Both components are bijective, so
the homotopy inverse is their inverse and the homotopies are zero.
-/

section

open Algebra

/-- A chain map `(φ₁, φ₀)` of two-term complexes of `B`-modules whose two components
are both bijective is a chain homotopy equivalence: its homotopy inverse is the
componentwise inverse and the contracting homotopies can be taken to be `0`. -/
theorem twoTerm_homotopyEquiv_of_bijective
    {B : Type*} [CommRing B]
    {C V C' V' : Type*}
    [AddCommGroup C] [Module B C] [AddCommGroup V] [Module B V]
    [AddCommGroup C'] [Module B C'] [AddCommGroup V'] [Module B V']
    (dP : C →ₗ[B] V) (dQ : C' →ₗ[B] V')
    (φ₁ : C →ₗ[B] C') (φ₀ : V →ₗ[B] V')
    (hchain : dQ ∘ₗ φ₁ = φ₀ ∘ₗ dP)
    (hφ₁ : Function.Bijective φ₁) (hφ₀ : Function.Bijective φ₀) :
    ∃ (ψ₁ : C' →ₗ[B] C) (ψ₀ : V' →ₗ[B] V) (s : V →ₗ[B] C) (t : V' →ₗ[B] C'),
      dQ ∘ₗ φ₁ = φ₀ ∘ₗ dP ∧
      dP ∘ₗ ψ₁ = ψ₀ ∘ₗ dQ ∧
      ψ₁ ∘ₗ φ₁ - LinearMap.id = s ∘ₗ dP ∧
      ψ₀ ∘ₗ φ₀ - LinearMap.id = dP ∘ₗ s ∧
      φ₁ ∘ₗ ψ₁ - LinearMap.id = t ∘ₗ dQ ∧
      φ₀ ∘ₗ ψ₀ - LinearMap.id = dQ ∘ₗ t := by
  let e₁ : C ≃ₗ[B] C' := LinearEquiv.ofBijective φ₁ hφ₁
  let e₀ : V ≃ₗ[B] V' := LinearEquiv.ofBijective φ₀ hφ₀
  refine ⟨(e₁.symm : C' →ₗ[B] C), (e₀.symm : V' →ₗ[B] V), 0, 0, hchain, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.eq_symm_apply]
    simpa [e₁, e₀] using (LinearMap.congr_fun hchain (e₁.symm x)).symm
  · simpa [sub_eq_zero] using LinearMap.ext e₁.symm_apply_apply
  · simpa [sub_eq_zero] using LinearMap.ext e₀.symm_apply_apply
  · simpa [sub_eq_zero] using LinearMap.ext e₁.apply_symm_apply
  · simpa [sub_eq_zero] using LinearMap.ext e₀.apply_symm_apply

section Localization


variable (A Aₘ B : Type*) [CommRing A] [CommRing Aₘ] [CommRing B]
  [Algebra A Aₘ] [Algebra A B] [Algebra Aₘ B]

/-- The canonical map `A[X_b] → Aₘ[X_b]` of presentation rings fixes each generator. -/
theorem defaultHom_self_toAlgHom_X (b : B) :
    ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toAlgHom (MvPolynomial.X b) =
      MvPolynomial.X b := by
  rw [Generators.Hom.toAlgHom_X, Generators.defaultHom_val]
  simp

/-- The canonical map `A[X_b] → Aₘ[X_b]` of presentation rings is
`MvPolynomial.map (algebraMap A Aₘ)`. -/
theorem defaultHom_self_toAlgHom_eq_map :
    (((Generators.self A B).defaultHom (Generators.self Aₘ B)).toAlgHom :
      MvPolynomial B A →+* MvPolynomial B Aₘ) = MvPolynomial.map (algebraMap A Aₘ) :=
  MvPolynomial.ringHom_ext (fun _ => by simp) fun _ => by simp

variable [IsScalarTower A Aₘ B] (M : Submonoid A) [IsLocalization M Aₘ]

include M in
-- needed: `IsLocalization.map_unique`/`ker_map` are applied to the `Generators.Ring`-to-
-- `MvPolynomial` identification, which only holds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `Aₘ[X_b] → B` is the extension of the kernel of `A[X_b] → B` along the
localization map `A[X_b] → Aₘ[X_b]`. -/
theorem ker_self_eq_map_defaultHom :
    (Generators.self Aₘ B).toExtension.ker =
      Ideal.map (((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom.toAlgHom :
        (Generators.self A B).toExtension.Ring →+* (Generators.self Aₘ B).toExtension.Ring)
        (Generators.self A B).toExtension.ker := by
  set h := ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
  let _ : Algebra (MvPolynomial B A) (MvPolynomial B Aₘ) := MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := B) M Aₘ
  set MC := Submonoid.map (MvPolynomial.C : A →+* MvPolynomial B A) M
  set g := algebraMap (Generators.self A B).toExtension.Ring B
  have hTunit : Submonoid.map g MC ≤ IsUnit.submonoid B := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    change IsUnit (g (MvPolynomial.C m))
    have e : g (MvPolynomial.C m) = algebraMap A B m :=
      (IsScalarTower.algebraMap_apply A (Generators.self A B).toExtension.Ring B m).symm
    rw [e, IsScalarTower.algebraMap_apply A Aₘ B]
    exact (IsLocalization.map_units Aₘ ⟨m, hm⟩).map (algebraMap Aₘ B)
  have := IsLocalization.of_le_isUnit hTunit
  have halg : (h.toAlgHom : (Generators.self A B).toExtension.Ring →+*
      (Generators.self Aₘ B).toExtension.Ring) =
        algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) :=
    defaultHom_self_toAlgHom_eq_map A Aₘ B
  have hcomp (x : MvPolynomial B A) :
      algebraMap (Generators.self Aₘ B).toExtension.Ring B
        (algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) x) = g x := by
    rw [← halg]
    exact h.algebraMap_toRingHom x
  rw [halg]
  convert IsLocalization.ker_map (S := MvPolynomial B Aₘ) (M := MC) B g rfl using 2 <;>
    first | rfl | (symm; apply IsLocalization.map_unique; exact hcomp)

-- needed: the `rw`s below match the ideal-squared membership only once the
-- `Generators.Ring`-to-`MvPolynomial` algebra maps unfold at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- If `h z` lies in `I_Q²` for the canonical map `h : A[X_b] → Aₘ[X_b]`, then `C m * z`
lies in `I_P²` for some `m ∈ M`. -/
theorem exists_C_mul_mem_ker_sq_of_map_mem (z : MvPolynomial B A)
    (hz : ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom.toAlgHom z ∈
      (Generators.self Aₘ B).toExtension.ker ^ 2) :
    ∃ m ∈ M, MvPolynomial.C m * z ∈ (Generators.self A B).toExtension.ker ^ 2 := by
  let _ : Algebra (MvPolynomial B A) (MvPolynomial B Aₘ) := MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := B) M Aₘ
  set MC := Submonoid.map (MvPolynomial.C : A →+* MvPolynomial B A) M
  have halg : (((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom.toAlgHom :
      (Generators.self A B).toExtension.Ring →+* (Generators.self Aₘ B).toExtension.Ring) =
        algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) :=
    defaultHom_self_toAlgHom_eq_map A Aₘ B
  replace hz : algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) z ∈
      Ideal.map (algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ))
        ((Generators.self A B).toExtension.ker ^ 2) := by
    rwa [Ideal.map_pow, ← halg, ← ker_self_eq_map_defaultHom A Aₘ B M]
  rw [IsLocalization.mem_map_algebraMap_iff MC (MvPolynomial B Aₘ)] at hz
  obtain ⟨⟨a, s⟩, hw⟩ := hz
  have hr : algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) ((s : MvPolynomial B A) * z) =
      algebraMap (MvPolynomial B A) (MvPolynomial B Aₘ) (a : MvPolynomial B A) := by
    rwa [map_mul, mul_comm]
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := MC) hr
  obtain ⟨m, hm, hmC⟩ := MC.mul_mem c.property s.property
  refine ⟨m, hm, ?_⟩
  rw [hmC, mul_assoc, hc]
  exact Ideal.mul_mem_left _ _ a.property

private theorem smul_cotangent_mk {R : Type*} [CommRing R] [Algebra A R] [Algebra R B]
    [IsScalarTower A R B] (m : A) (p : (Generators.self R B).toExtension.ker) :
    m • Extension.Cotangent.mk p =
      Extension.Cotangent.mk (algebraMap A (Generators.self R B).toExtension.Ring m • p) := by
  rw [map_smul, algebraMap_smul]

-- needed: the closing `simp` sees the cotangent class only after the
-- `Generators.Ring`-to-`MvPolynomial` identification unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- Every element of `I_Q/I_Q²` is, after scaling by some `m ∈ M`, in the image of the
cotangent map `I_P/I_P² → I_Q/I_Q²`. -/
theorem cotangent_map_surj (y : (Generators.self Aₘ B).toExtension.Cotangent) :
    ∃ x : (Generators.self A B).toExtension.Cotangent × M, x.2 • y =
      (Extension.Cotangent.map
        ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom) x.1 := by
  set h := ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
  let _ : Algebra (MvPolynomial B A) (MvPolynomial B Aₘ) := MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := B) M Aₘ
  obtain ⟨q₀, rfl⟩ := Extension.Cotangent.mk_surjective y
  obtain ⟨⟨q', _, m, hm, rfl⟩, hq⟩ :=
    IsLocalization.surj (S := MvPolynomial B Aₘ)
      (Submonoid.map (MvPolynomial.C : A →+* MvPolynomial B A) M) q₀.1
  have heq : algebraMap A (Generators.self Aₘ B).toExtension.Ring m • q₀.1 = h.toAlgHom q' := by
    have e := RingHom.congr_fun (defaultHom_self_toAlgHom_eq_map A Aₘ B) q'
    refine Eq.trans ?_ e.symm
    simp only [MvPolynomial.algebraMap_def, MvPolynomial.map_C] at hq
    rw [Algebra.smul_def, mul_comm]
    exact hq
  have hmem : q' ∈ (Generators.self A B).toExtension.ker := by
    change algebraMap (Generators.self A B).toExtension.Ring B q' = 0
    have e : algebraMap (Generators.self Aₘ B).toExtension.Ring B (h.toAlgHom q') =
        algebraMap (Generators.self A B).toExtension.Ring B q' := by simp
    rw [← e, ← heq, Algebra.smul_def, map_mul,
      show algebraMap (Generators.self Aₘ B).toExtension.Ring B q₀.1 = 0 from q₀.property,
      mul_zero]
  refine ⟨⟨Extension.Cotangent.mk ⟨q', hmem⟩, ⟨m, hm⟩⟩, ?_⟩
  rw [Extension.Cotangent.map_mk, Submonoid.mk_smul, smul_cotangent_mk]
  exact congr_arg _ (Subtype.ext heq)

/-- The cotangent map `I_P/I_P² → I_Q/I_Q²` is injective up to scaling by an element
of `M`. -/
theorem cotangent_map_exists_of_eq {x₁ x₂ : (Generators.self A B).toExtension.Cotangent}
    (hx : Extension.Cotangent.map
        ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom x₁ =
      Extension.Cotangent.map
        ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom x₂) :
    ∃ c : M, c • x₁ = c • x₂ := by
  set h := ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
  obtain ⟨p₁, rfl⟩ := Extension.Cotangent.mk_surjective x₁
  obtain ⟨p₂, rfl⟩ := Extension.Cotangent.mk_surjective x₂
  rw [Extension.Cotangent.map_mk, Extension.Cotangent.map_mk, ← sub_eq_zero, ← map_sub,
    Extension.Cotangent.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, hmem⟩ := exists_C_mul_mem_ker_sq_of_map_mem A Aₘ B M
    (show MvPolynomial B A from p₁.1 - p₂.1)
    (by rwa [map_sub])
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [Submonoid.mk_smul, Submonoid.mk_smul, smul_cotangent_mk, smul_cotangent_mk, ← sub_eq_zero,
    ← map_sub, Extension.Cotangent.mk_eq_zero_iff]
  convert hmem using 1
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, smul_eq_mul, ← mul_sub]
  rfl

end Localization

/-- The degree-`0` component `φ₀ = CotangentSpace.map h` of the canonical chain map
`NL_{B/A} → NL_{B/Aₘ}` is bijective. -/
theorem cotangentSpace_map_bijective (A Aₘ B : Type*) [CommRing A] [CommRing Aₘ] [CommRing B]
    [Algebra A Aₘ] [Algebra A B] [Algebra Aₘ B] [IsScalarTower A Aₘ B] :
    Function.Bijective
      (Algebra.Extension.CotangentSpace.map
        (((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom)) := by
  set h : ((Generators.self A B).toExtension).Hom ((Generators.self Aₘ B).toExtension) :=
    ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
  have hφ₀eq : (Algebra.Extension.CotangentSpace.map h) = (((Generators.self A
      B).cotangentSpaceBasis.equiv
      (Generators.self Aₘ B).cotangentSpaceBasis (Equiv.refl B)) : _ →ₗ[B] _) := by
    refine (Generators.self A B).cotangentSpaceBasis.ext fun i => ?_
    have hval : h.toAlgHom (MvPolynomial.X i) = MvPolynomial.X i :=
      defaultHom_self_toAlgHom_X A Aₘ B i
    have hφ₀ : Extension.CotangentSpace.map h ((Generators.self A B).cotangentSpaceBasis i) =
        (Generators.self Aₘ B).cotangentSpaceBasis i := by
      rw [Generators.cotangentSpaceBasis_apply, Generators.cotangentSpaceBasis_apply]
      erw [Algebra.Extension.CotangentSpace.map_tmul]
      rw [map_one, hval]
      rfl
    simp [hφ₀, Module.Basis.equiv_apply]
  rw [hφ₀eq]
  exact (((Generators.self A B).cotangentSpaceBasis.equiv
    (Generators.self Aₘ B).cotangentSpaceBasis (Equiv.refl B))).bijective

/-- If a linear map `f : N →ₗ[A] N'` exhibits
`N'` as a localization of `N` at `M`, and `N` is *already* `M`-local (i.e. the
identity on `N` is itself a localization-at-`M` map), then `f` is bijective: the
localization comparison map of an already-local module is an isomorphism. -/
@[ega "0 6.3.1" "more general"]
theorem bij_of_isLocalizedModule_of_local
    {A : Type*} [CommRing A] (M : Submonoid A)
    {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : N →ₗ[A] N') [IsLocalizedModule M f]
    [IsLocalizedModule M (LinearMap.id : N →ₗ[A] N)] :
    Function.Bijective f := by
  have hef : ⇑f = ⇑(IsLocalizedModule.linearEquiv M (LinearMap.id : N →ₗ[A] N) f) := by
    ext x
    simpa using (IsLocalizedModule.linearEquiv_apply M (LinearMap.id : N →ₗ[A] N) f x).symm
  exact hef ▸ (IsLocalizedModule.linearEquiv M (LinearMap.id : N →ₗ[A] N) f).bijective

/-- The degree-1 cotangent map `φ₁ = Cotangent.map h`, viewed as an `A`-linear map,
exhibits `Q.Cotangent = I_Q/I_Q²` as the localization of `P.Cotangent = I_P/I_P²`
at `M`. -/
theorem cotangent_map_isLocalizedModule
    (A : Type*) (Aₘ : Type*) (B : Type*)
    [CommRing A] [CommRing Aₘ] [CommRing B]
    [Algebra A Aₘ] [Algebra A B] [Algebra Aₘ B]
    [IsScalarTower A Aₘ B]
    (M : Submonoid A) [IsLocalization M Aₘ] :
    IsLocalizedModule M
      (LinearMap.restrictScalars A <| Extension.Cotangent.map
        ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom) :=
  ⟨fun x => by
    have key : algebraMap A (Module.End A (Generators.self Aₘ B).toExtension.Cotangent) x =
        Module.toModuleEnd A _ (algebraMap A B x) := by
      ext n
      exact (IsScalarTower.algebraMap_smul B (x : A) n).symm
    rw [key, IsScalarTower.algebraMap_apply A Aₘ B]
    exact ((IsLocalization.map_units Aₘ x).map (algebraMap Aₘ B)).map _,
    cotangent_map_surj A Aₘ B M, cotangent_map_exists_of_eq A Aₘ B M⟩

/-- The degree-`1` component `φ₁ = Cotangent.map h` of the canonical chain map
`NL_{B/A} → NL_{B/Aₘ}` is bijective. -/
theorem cotangent_map_bijective
    (A : Type*) (Aₘ : Type*) (B : Type*)
    [CommRing A] [CommRing Aₘ] [CommRing B]
    [Algebra A Aₘ] [Algebra A B] [Algebra Aₘ B]
    [IsScalarTower A Aₘ B]
    (M : Submonoid A) [IsLocalization M Aₘ] :
    Function.Bijective
      (Algebra.Extension.Cotangent.map
        (((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom)) := by
  set P := (Generators.self A B).toExtension
  set Q := (Generators.self Aₘ B).toExtension
  set h : P.Hom Q := ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
  set φ₁A : P.Cotangent →ₗ[A] Q.Cotangent := (Algebra.Extension.Cotangent.map h).restrictScalars A
  have : IsLocalizedModule M (LinearMap.id : P.Cotangent →ₗ[A] P.Cotangent) :=
    isLocalizedModule_id M P.Cotangent Aₘ
  have : IsLocalizedModule M φ₁A := cotangent_map_isLocalizedModule A Aₘ B M
  exact bij_of_isLocalizedModule_of_local M φ₁A

/-- With `Aₘ` a localization of `A` at the multiplicative subset `M` and a ring map `Aₘ → B`, the
canonical chain map `φ = (φ₁, φ₀) : NL_{B/A} → NL_{B/Aₘ}`, given by
`Algebra.Extension.Cotangent.map h` and `Algebra.Extension.CotangentSpace.map h` for the morphism
of extensions `h` induced by the tower `A → Aₘ → B`, is a homotopy equivalence of the two term
naive cotangent complexes of `B`-modules. -/
@[stacks 07BS]
theorem naiveCotangentComplex_localization_base_homotopyEquiv
    (A : Type*) (Aₘ : Type*) (B : Type*)
    [CommRing A] [CommRing Aₘ] [CommRing B]
    [Algebra A Aₘ] [Algebra A B] [Algebra Aₘ B]
    [IsScalarTower A Aₘ B]
    (M : Submonoid A) [IsLocalization M Aₘ] :
    let P := (Generators.self A B).toExtension
    let Q := (Generators.self Aₘ B).toExtension
    let h : P.Hom Q :=
      ((Generators.self A B).defaultHom (Generators.self Aₘ B)).toExtensionHom
    let φ₁ := Algebra.Extension.Cotangent.map h
    let φ₀ := Algebra.Extension.CotangentSpace.map h
    ∃ (ψ₁ : Q.Cotangent →ₗ[B] P.Cotangent)
      (ψ₀ : Q.CotangentSpace →ₗ[B] P.CotangentSpace)
      (s : P.CotangentSpace →ₗ[B] P.Cotangent)
      (t : Q.CotangentSpace →ₗ[B] Q.Cotangent),
      Q.cotangentComplex ∘ₗ φ₁ = φ₀ ∘ₗ P.cotangentComplex ∧
      P.cotangentComplex ∘ₗ ψ₁ = ψ₀ ∘ₗ Q.cotangentComplex ∧
      ψ₁ ∘ₗ φ₁ - LinearMap.id = s ∘ₗ P.cotangentComplex ∧
      ψ₀ ∘ₗ φ₀ - LinearMap.id = P.cotangentComplex ∘ₗ s ∧
      φ₁ ∘ₗ ψ₁ - LinearMap.id = t ∘ₗ Q.cotangentComplex ∧
      φ₀ ∘ₗ ψ₀ - LinearMap.id = Q.cotangentComplex ∘ₗ t := by
  intro P Q h φ₁ φ₀
  exact twoTerm_homotopyEquiv_of_bijective P.cotangentComplex Q.cotangentComplex φ₁ φ₀
    (Algebra.Extension.CotangentSpace.map_comp_cotangentComplex h).symm
    (cotangent_map_bijective A Aₘ B M) (cotangentSpace_map_bijective A Aₘ B)

end

/-!
## The naive cotangent complex of a polynomial algebra

Let `A` be a commutative ring and `ι` an arbitrary index type. The polynomial algebra
`B = MvPolynomial ι A` has the presentation `natGen A ι` by its own variables, with no relations.
For it the naive cotangent complex `NL_{B/A}` is `(0 → Ω_{B/A})`: the degree one term vanishes, the
differential is zero, and the augmentation `P.toKaehler` to `Ω[B⁄A]` is bijective.
-/

/-- The natural (zero-relations) presentation of the polynomial algebra
`MvPolynomial ι A` by its own variables: the variable-value map is
`MvPolynomial.X` and the presentation map is the identity. -/
noncomputable def natGen (A : Type*) [CommRing A] (ι : Type*) :
    Algebra.Generators A (MvPolynomial ι A) ι :=
  { val := MvPolynomial.X
    σ' := id
    aeval_val_σ' := by intro s; simp }

/-- The `Algebra.Extension` associated to the natural presentation `natGen A ι`. -/
noncomputable def natExt (A : Type*) [CommRing A] (ι : Type*) :
    Algebra.Extension A (MvPolynomial ι A) :=
  (natGen A ι).toExtension

-- needed: `natExt_ker_eq_bot` must identify `(natGen A ι).toExtension.Ring` with
-- `MvPolynomial ι A`, which is only a def-eq through the anonymous-constructor `natGen`.
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the natural presentation is `⊥` (no relations). -/
private theorem natExt_ker_eq_bot (A : Type*) [CommRing A] (ι : Type*) :
    (natExt A ι).ker = ⊥ := by
  rw [Algebra.Extension.ker, ← RingHom.injective_iff_ker_eq_bot]
  intro x y hxy
  simp only [natExt, natGen, RingHom.algebraMap_toAlgebra, MvPolynomial.aeval_X_left] at hxy
  exact hxy

/-- The degree one module of `NL_{B/A}` vanishes for the presentation `natExt A ι` of
`B = MvPolynomial ι A`. -/
@[stacks 08Q1 "Ingredient only, and only for the variables presentation B = MvPolynomial ι A: \
the degree-1 term vanishes. The homotopy equivalence NL_{B/A} ≃ (0 → Ω_{B/A}) is not stated."]
theorem natExt_cotangent_subsingleton (A : Type*) [CommRing A] (ι : Type*) :
    Subsingleton ((natExt A ι).Cotangent) := by
  change Subsingleton (natExt A ι).ker.Cotangent
  rw [natExt_ker_eq_bot]
  have : Subsingleton ↥(⊥ : Ideal (MvPolynomial ι A)) := by infer_instance
  exact Function.Surjective.subsingleton (Ideal.toCotangent_surjective ⊥)

/-- The differential of `NL_{B/A}` is the zero map for the presentation `natExt A ι`. -/
theorem natExt_cotangentComplex_eq_zero (A : Type*) [CommRing A] (ι : Type*) :
    (natExt A ι).cotangentComplex = 0 := by
  have := natExt_cotangent_subsingleton A ι
  exact Subsingleton.elim _ _

/-- The augmentation `P.toKaehler` is a `B`-linear isomorphism of `P.CotangentSpace` onto
`Ω[B⁄A]` for the presentation `P = natExt A ι`. -/
@[stacks 08Q1 "Ingredient only, and only for the variables presentation B = MvPolynomial ι A: \
the degree-0 term is Ω via the augmentation. The homotopy equivalence NL_{B/A} ≃ (0 → Ω_{B/A}) \
is not stated."]
theorem natExt_toKaehler_bijective (A : Type*) [CommRing A] (ι : Type*) :
    Function.Bijective (natExt A ι).toKaehler := by
  refine ⟨?_, Algebra.Extension.toKaehler_surjective⟩
  have hexact := Algebra.Extension.exact_cotangentComplex_toKaehler (P := natExt A ι)
  intro x y hxy
  have hsub : x - y = 0 := by
    have h := (hexact (x - y)).mp (by rw [map_sub, hxy, sub_self])
    obtain ⟨c, hc⟩ := h
    rw [natExt_cotangentComplex_eq_zero] at hc
    simpa using hc.symm
  exact sub_eq_zero.mp hsub
