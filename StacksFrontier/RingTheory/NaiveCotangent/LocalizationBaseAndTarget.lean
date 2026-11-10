module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.Localization

/-!
# Simultaneous localization of the base and the target of the naive cotangent complex

Let `R → A` be a ring map, let `𝔭` be a prime of `A` and let `𝔮 = 𝔭 ∩ R` be the prime of `R`
it contracts to. The canonical map of two-term complexes of `A_𝔭`-modules

`NL_{A/R} ⊗_A A_𝔭 ⟶ NL_{A_𝔭 / R_𝔮}`

is a quasi-isomorphism. More generally, `A_𝔭` may be any localization of `A` at a
multiplicative subset `M ⊆ A` and `R_𝔮` any localization of `R` at a multiplicative subset
`N ⊆ R`, the only compatibility being the scalar tower `R → R_𝔮 → A_𝔭`, that is, the elements of
`N` become invertible in `A_𝔭`.

## Main definitions

* `NaiveCotangent.nlExtensionBaseChange`: the base change `NL(α) ⊗_S T` of the naive cotangent
  complex of an extension `α : P → S` along a ring map `S → T`, as a
  `NaiveCotangent.TwoTerm T`. Its differential is `Algebra.Extension.cotangentComplex` base
  changed to `T`, so its degree-`1` homology is `ker (d ⊗ T)` and not `T ⊗ ker d`.
* `NaiveCotangent.nlExtensionBaseChangeMap`: the chain map `NL(α) ⊗_S T ⟶ NL(β)` induced by a
  morphism of extensions `α → β` covering the square `R → R'`, `S → T`.
* `NaiveCotangent.nlExtensionOverMap`: the chain map `NL(α) ⟶ NL(β)` induced by a morphism of
  extensions of one and the same algebra `T` over two different bases `R → R'`.

## Main results

* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization`:
  the canonical map `NL_{A/R} ⊗_A A_𝔭 ⟶ NL_{A_𝔭/R_𝔮}` is a quasi-isomorphism, for a
  localization of the target at `M ⊆ A` and of the base at `N ⊆ R`.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_atPrime`: the same statement for a prime
  `𝔭` of `A` and the prime `𝔮` of `R` it contracts to.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization`: localizing the target
  alone, `NL_{S/R} ⊗_S T ⟶ NL_{T/R}` is a quasi-isomorphism.
* `NaiveCotangent.isQuasiIso_nlExtensionOverMap_of_isLocalization`: localizing the base alone,
  `NL_{T/R} ⟶ NL_{T/R'}` is bijective in both degrees.
* `NaiveCotangent.homotopic_nlExtensionBaseChangeMap`: any two morphisms of extensions induce
  homotopic comparison maps, so the induced maps on `H₁` and `H₀` do not depend on the choice.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7), the naive cotangent
  complex and localization of the target.
* [Stacks Project, Tag 07BS](https://stacks.math.columbia.edu/tag/07BS), the naive cotangent
  complex and localization of the base.
-/

@[expose] public section

namespace NaiveCotangent

open Algebra TensorProduct

/-!
## Bijectivity criteria for the homology of a chain map of two-term complexes
-/

section Criteria

variable {S : Type*} [CommRing S] {A B : TwoTerm S}

/-- The underlying element of `f.onH₁ x` is `f.f₁` of the underlying element of `x`. -/
theorem onH₁_apply_coe (f : ChainMap A B) (x : H₁ A) :
    ((f.onH₁ x : H₁ B) : B.X₁) = f.f₁ (x : A.X₁) := rfl

/-- `f.onH₀` on the class of `x` is the class of `f.f₀ x`. -/
theorem onH₀_mk (f : ChainMap A B) (x : A.X₀) :
    f.onH₀ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.f₀ x) := rfl

/-- `B.d (f.f₁ x) = f.f₀ (A.d x)`: the commutation relation of a chain map, read on elements. -/
theorem chainMap_comm_apply (f : ChainMap A B) (x : A.X₁) :
    B.d (f.f₁ x) = f.f₀ (A.d x) :=
  congrArg (fun m => m x) f.comm

/-- **`H₁` from a bijection between the kernels.**  A chain map whose degree-`1` component
carries the kernel of the source differential bijectively onto the kernel of the target
differential is bijective on `H₁ = ker d`. -/
theorem bijective_onH₁_of_bijOn (f : ChainMap A B)
    (h : Set.BijOn f.f₁ (LinearMap.ker A.d) (LinearMap.ker B.d)) :
    Function.Bijective f.onH₁ := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hx : (x : A.X₁) ∈ LinearMap.ker A.d := x.2
    have hy : (y : A.X₁) ∈ LinearMap.ker A.d := y.2
    have : f.f₁ (x : A.X₁) = f.f₁ (y : A.X₁) := by
      simpa only [onH₁_apply_coe] using congrArg Subtype.val hxy
    exact Subtype.ext (h.injOn hx hy this)
  · obtain ⟨x, hx, hfx⟩ := h.surjOn (show (y : B.X₁) ∈ LinearMap.ker B.d from y.2)
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa only [onH₁_apply_coe] using hfx)⟩

/-- **`H₀` from a bijection between two presentations of the cokernels.**  Suppose the cokernels
of the two differentials are presented by linear maps `πA` and `πB` out of the degree-`0` terms,
with `πA` surjective and the kernel of each equal to the range of the corresponding
differential, and suppose a bijective `φ` makes the square with `f.f₀` commute.  Then `f` is
bijective on `H₀ = coker d`. -/
theorem bijective_onH₀_of_surjective_square (W₁ W₂ : Type*)
    [AddCommGroup W₁] [Module S W₁] [AddCommGroup W₂] [Module S W₂]
    (f : ChainMap A B) (πA : A.X₀ →ₗ[S] W₁) (πB : B.X₀ →ₗ[S] W₂) (φ : W₁ →ₗ[S] W₂)
    (hπA : Function.Surjective πA)
    (hkerA : LinearMap.ker πA = LinearMap.range A.d)
    (hkerB : LinearMap.ker πB = LinearMap.range B.d)
    (hsq : πB ∘ₗ f.f₀ = φ ∘ₗ πA) (hφ : Function.Bijective φ) :
    Function.Bijective f.onH₀ := by
  have hsq' : ∀ x : A.X₀, πB (f.f₀ x) = φ (πA x) := fun x => congrArg (fun m => m x) hsq
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [onH₀_mk, onH₀_mk, Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    have hmem : f.f₀ (x - y) ∈ LinearMap.ker πB := by
      rw [hkerB, map_sub]
      exact hxy
    rw [LinearMap.mem_ker, hsq'] at hmem
    have hz : πA (x - y) = 0 := hφ.injective (by simpa using hmem)
    have hx : x - y ∈ LinearMap.ker πA := by simpa only [LinearMap.mem_ker] using hz
    rwa [hkerA] at hx
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw⟩ := hφ.surjective (πB y)
    obtain ⟨x, hx⟩ := hπA w
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [onH₀_mk, Submodule.Quotient.eq]
    have hmem : f.f₀ x - y ∈ LinearMap.ker πB := by
      rw [LinearMap.mem_ker, map_sub, hsq', hx, hw, sub_self]
    rwa [hkerB] at hmem

/-- **A degreewise bijective chain map is a quasi-isomorphism.** -/
theorem isQuasiIso_of_bijective (f : ChainMap A B)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Bijective f.f₀) :
    IsQuasiIso f := by
  refine ⟨bijective_onH₁_of_bijOn f ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
    rw [chainMap_comm_apply, hx, map_zero]
  · intro x _ y _ hxy
    exact h₁.injective hxy
  · intro y hy
    obtain ⟨x, rfl⟩ := h₁.surjective y
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hy
    rw [chainMap_comm_apply] at hy
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact h₀.injective (by rw [hy, map_zero])
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [onH₀_mk, onH₀_mk, Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    obtain ⟨z, hz⟩ := hxy
    obtain ⟨w, rfl⟩ := h₁.surjective z
    refine ⟨w, h₀.injective ?_⟩
    rw [← chainMap_comm_apply, hz, map_sub]
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, rfl⟩ := h₀.surjective y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- A composite of quasi-isomorphisms of two-term complexes is a quasi-isomorphism. -/
theorem IsQuasiIso.comp {C : TwoTerm S} {g : ChainMap B C} {f : ChainMap A B}
    (hg : IsQuasiIso g) (hf : IsQuasiIso f) : IsQuasiIso (g.comp f) := by
  refine ⟨?_, ?_⟩
  · rw [show (g.comp f).onH₁ = g.onH₁ ∘ₗ f.onH₁ from ChainMap.onH₁_comp g f]
    exact hg.1.comp hf.1
  · rw [show (g.comp f).onH₀ = g.onH₀ ∘ₗ f.onH₀ from ChainMap.onH₀_comp g f]
    exact hg.2.comp hf.2

end Criteria

/-!
## The comparison maps, over the raw linear data

Identities between linear maps built from `Algebra.Extension.cotangentComplex`,
`Algebra.Extension.Cotangent.map` and their base changes.
-/

section Raw

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' T] [Algebra R T]
  [IsScalarTower R R' T] [IsScalarTower R S T]
  {P : Extension R S} {Q : Extension R' T}

omit [IsScalarTower R S T] in
/-- The base changed functorial maps commute with the differentials. -/
theorem cotangentComplex_comp_liftBaseChange_cotangentMap (h : P.Hom Q) :
    Q.cotangentComplex ∘ₗ (Extension.Cotangent.map h).liftBaseChange T =
      (Extension.CotangentSpace.map h).liftBaseChange T ∘ₗ P.cotangentComplex.baseChange T := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.baseChange_tmul, map_smul]
  exact congrArg (fun y => t • y) (Extension.CotangentSpace.map_cotangentComplex h x).symm

/-- The degree-`1` half of the homotopy between the comparison maps of two morphisms of
extensions: the base change of `Algebra.Extension.Hom.sub`. -/
theorem sub_liftBaseChange_cotangentMap (h h' : P.Hom Q) :
    (Extension.Cotangent.map h).liftBaseChange T -
        (Extension.Cotangent.map h').liftBaseChange T =
      (h.sub h').liftBaseChange T ∘ₗ P.cotangentComplex.baseChange T := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  have hx := congrArg (fun m => m x) (Extension.Cotangent.map_sub_map h h')
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at hx
  simp only [LinearMap.sub_apply, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.baseChange_tmul, ← smul_sub, hx]

/-- The degree-`0` half of the homotopy between the comparison maps of two morphisms of
extensions. -/
theorem sub_liftBaseChange_cotangentSpaceMap (h h' : P.Hom Q) :
    (Extension.CotangentSpace.map h).liftBaseChange T -
        (Extension.CotangentSpace.map h').liftBaseChange T =
      Q.cotangentComplex ∘ₗ (h.sub h').liftBaseChange T := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  have hx := congrArg (fun m => m x) (Extension.CotangentSpace.map_sub_map h h')
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars] at hx
  simp only [LinearMap.sub_apply, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
    Function.comp_apply, ← smul_sub, hx, map_smul]

end Raw

section RawOver

variable {R R' T : Type*} [CommRing R] [CommRing R'] [CommRing T] [Algebra R T] [Algebra R R']
  [Algebra R' T] [IsScalarTower R R' T] {P : Extension R T} {Q : Extension R' T}

/-- The functorial maps of a morphism of extensions of one and the same algebra commute with the
differentials. -/
theorem cotangentComplex_comp_cotangentMap (h : P.Hom Q) :
    Q.cotangentComplex ∘ₗ Extension.Cotangent.map h =
      Extension.CotangentSpace.map h ∘ₗ P.cotangentComplex :=
  LinearMap.ext fun y => (Extension.CotangentSpace.map_cotangentComplex h y).symm

end RawOver

/-!
## The base changed naive cotangent complex and the comparison maps
-/

section Maps

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]

/-- The base change `NL(α) ⊗_S T` along `S → T` of the naive cotangent complex of an extension
`α : P → S` of `S` over `R`: the two-term complex of `T`-modules
`T ⊗_S I/I² ⟶ T ⊗_S (Ω[P⁄R] ⊗_P S)` whose differential is `Algebra.Extension.cotangentComplex`
base changed along `S → T`. -/
noncomputable def nlExtensionBaseChange (P : Extension R S) (T : Type*) [CommRing T] [Algebra S T] :
    TwoTerm T where
  X₁ := T ⊗[S] P.Cotangent
  X₀ := T ⊗[S] P.CotangentSpace
  d := P.cotangentComplex.baseChange T

variable {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' T] [Algebra R T]
  [IsScalarTower R R' T] [IsScalarTower R S T]

/-- The chain map `NL(α) ⊗_S T ⟶ NL(β)` induced by a morphism of extensions `h : α → β`, where
`α` is an extension of `S` over `R` and `β` one of `T` over `R'`: in each degree it is the
`T`-linear extension of the functorial map `Algebra.Extension.Cotangent.map h`, respectively
`Algebra.Extension.CotangentSpace.map h`. -/
noncomputable def nlExtensionBaseChangeMap {P : Extension R S} {Q : Extension R' T} (h : P.Hom Q) :
    ChainMap (nlExtensionBaseChange P T) (nlOfExtension Q) where
  f₁ := (Extension.Cotangent.map h).liftBaseChange T
  f₀ := (Extension.CotangentSpace.map h).liftBaseChange T
  comm := cotangentComplex_comp_liftBaseChange_cotangentMap h

/-- **Homotopy uniqueness of the base changed comparison.**  Any two morphisms of extensions
`α → β` induce homotopic chain maps `NL(α) ⊗_S T ⟶ NL(β)`; the homotopy is the `T`-linear
extension of `Algebra.Extension.Hom.sub`. -/
theorem homotopic_nlExtensionBaseChangeMap {P : Extension R S} {Q : Extension R' T}
    (h h' : P.Hom Q) :
    Homotopic (nlExtensionBaseChangeMap (T := T) h) (nlExtensionBaseChangeMap (T := T) h') :=
  ⟨(h.sub h').liftBaseChange T, sub_liftBaseChange_cotangentMap h h',
    sub_liftBaseChange_cotangentSpaceMap h h'⟩

/-- Being a quasi-isomorphism does not depend on the morphism of extensions chosen: homotopic
chain maps induce the same maps on `H₁` and on `H₀`. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_congr {P : Extension R S} {Q : Extension R' T}
    (h h' : P.Hom Q) (hq : IsQuasiIso (nlExtensionBaseChangeMap (T := T) h')) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := T) h) := by
  refine ⟨?_, ?_⟩
  · rw [ChainMap.onH₁_eq_of_homotopic (homotopic_nlExtensionBaseChangeMap (T := T) h h')]
    exact hq.1
  · rw [ChainMap.onH₀_eq_of_homotopic (homotopic_nlExtensionBaseChangeMap (T := T) h h')]
    exact hq.2

end Maps

section OverMaps

variable {R R' T : Type*} [CommRing R] [CommRing R'] [CommRing T] [Algebra R T] [Algebra R R']
  [Algebra R' T] [IsScalarTower R R' T]

/-- The chain map `NL(α) ⟶ NL(β)` induced by a morphism of extensions `h : α → β` of one and
the same algebra `T`, over two bases `R → R'`.  Both complexes are complexes of `T`-modules, so
neither a restriction of scalars nor a base change is needed. -/
noncomputable def nlExtensionOverMap {P : Extension R T} {Q : Extension R' T} (h : P.Hom Q) :
    ChainMap (nlOfExtension P) (nlOfExtension Q) where
  f₁ := Extension.Cotangent.map h
  f₀ := Extension.CotangentSpace.map h
  comm := cotangentComplex_comp_cotangentMap h

end OverMaps

/-!
## Localizing the target
-/

section Target

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

omit [Algebra R T] [IsScalarTower R S T] in
/-- The base change to `T` of the augmentation to the module of differentials presents the
cokernel of the base changed differential: its kernel is the range of
`Algebra.Extension.cotangentComplex` base changed to `T`. -/
theorem ker_baseChange_toKaehler (P : Extension R S) :
    LinearMap.ker (P.toKaehler.baseChange T) =
      LinearMap.range (P.cotangentComplex.baseChange T) := by
  have hexA : Function.Exact (LinearMap.lTensor T P.cotangentComplex)
      (LinearMap.lTensor T P.toKaehler) :=
    lTensor_exact T P.exact_cotangentComplex_toKaehler P.toKaehler_surjective
  have hlt : ∀ z, (P.toKaehler.baseChange T) z = LinearMap.lTensor T P.toKaehler z :=
    fun z => congrArg (fun m => m z) (LinearMap.baseChange_eq_lTensor (A := T) (f := P.toKaehler))
  have hltd : ∀ z, (P.cotangentComplex.baseChange T) z =
      LinearMap.lTensor T P.cotangentComplex z :=
    fun z => congrArg (fun m => m z)
      (LinearMap.baseChange_eq_lTensor (A := T) (f := P.cotangentComplex))
  refine SetLike.ext fun z => ?_
  rw [LinearMap.mem_ker, hlt z, hexA z]
  simp only [Set.mem_range, LinearMap.mem_range]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (hltd w).trans hw⟩, fun ⟨w, hw⟩ => ⟨w, (hltd w).symm.trans hw⟩⟩

omit [Algebra R T] [IsScalarTower R S T] in
/-- The base change to `T` of the augmentation to the module of differentials is surjective. -/
theorem surjective_baseChange_toKaehler (P : Extension R S) :
    Function.Surjective (P.toKaehler.baseChange T) := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective T P.toKaehler_surjective y
  exact ⟨z, (congrArg (fun m => m z)
    (LinearMap.baseChange_eq_lTensor (A := T) (f := P.toKaehler))).trans hz⟩

/-- The comparison `T ⊗_S Ω[S⁄R] → Ω[T⁄R]` is bijective when `T` is a localization of `S`. -/
theorem bijective_mapBaseChange_of_isLocalization (M : Submonoid S) [IsLocalization M T] :
    Function.Bijective (KaehlerDifferential.mapBaseChange R S T) := by
  have hbc : IsBaseChange T (KaehlerDifferential.map R R S T) :=
    (isLocalizedModule_iff_isBaseChange M T _).mp
      (KaehlerDifferential.isLocalizedModule_map R S T M)
  have hmb : KaehlerDifferential.mapBaseChange R S T = hbc.equiv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun t ω => ?_
    rw [KaehlerDifferential.mapBaseChange_tmul]
    exact (hbc.equiv_tmul t ω).symm
  rw [hmb]
  exact hbc.equiv.bijective

/-- The augmentation `Ω[E.Ring⁄R] ⊗_{E.Ring} T ⟶ Ω[T⁄R]` of an extension `E` of `T` over `R`,
evaluated on `1 ⊗ dp`. -/
theorem toKaehler_one_tmul_D {R₀ T₀ : Type*} [CommRing R₀] [CommRing T₀] [Algebra R₀ T₀]
    (E : Extension R₀ T₀) (p : E.Ring) :
    E.toKaehler ((1 : T₀) ⊗ₜ[E.Ring] KaehlerDifferential.D R₀ E.Ring p) =
      KaehlerDifferential.D R₀ T₀ (algebraMap E.Ring T₀ p) := by
  change KaehlerDifferential.mapBaseChange R₀ E.Ring T₀
    ((1 : T₀) ⊗ₜ[E.Ring] KaehlerDifferential.D R₀ E.Ring p) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

/-- The degree-`0` comparison square for the canonical presentations: the augmentation to the
module of differentials turns `Algebra.Extension.CotangentSpace.map` into
`KaehlerDifferential.map`, as `S`-linear maps out of `Ω[R[S]⁄R] ⊗_{R[S]} S`. -/
theorem toKaehler_comp_cotangentSpaceMap_self
    (h : (Generators.self R S).toExtension.Hom (Generators.self R T).toExtension) :
    (Generators.self R T).toExtension.toKaehler.restrictScalars S ∘ₗ
        Extension.CotangentSpace.map h =
      KaehlerDifferential.map R R S T ∘ₗ (Generators.self R S).toExtension.toKaehler := by
  refine (Generators.self R S).cotangentSpaceBasis.ext fun i => ?_
  have hring : algebraMap (Generators.self R T).toExtension.Ring T (h.toAlgHom
      (MvPolynomial.X i)) =
      algebraMap S T (algebraMap (Generators.self R S).toExtension.Ring S (MvPolynomial.X i)) :=
    h.algebraMap_toRingHom (MvPolynomial.X i)
  have hXi : algebraMap (Generators.self R S).Ring S (MvPolynomial.X i) = i := by
    rw [Algebra.Generators.algebraMap_apply]
    simp
  have hbasis : (Generators.self R S).cotangentSpaceBasis i =
      (1 : S) ⊗ₜ[(Generators.self R S).toExtension.Ring]
        KaehlerDifferential.D R (Generators.self R S).toExtension.Ring (MvPolynomial.X i) :=
    (Generators.self R S).cotangentSpaceBasis_apply i
  have e1 : Extension.CotangentSpace.map h ((Generators.self R S).cotangentSpaceBasis i) =
      algebraMap S T (1 : S) ⊗ₜ[(Generators.self R T).toExtension.Ring]
        KaehlerDifferential.D R (Generators.self R T).toExtension.Ring
          (h.toAlgHom (MvPolynomial.X i)) :=
    (congrArg (fun z => Extension.CotangentSpace.map h z) hbasis).trans
      (Extension.CotangentSpace.map_tmul h (1 : S) (MvPolynomial.X i))
  have e2 : (Generators.self R T).toExtension.toKaehler
        (algebraMap S T (1 : S) ⊗ₜ[(Generators.self R T).toExtension.Ring]
          KaehlerDifferential.D R (Generators.self R T).toExtension.Ring
            (h.toAlgHom (MvPolynomial.X i))) =
      KaehlerDifferential.D R T
        (algebraMap (Generators.self R T).toExtension.Ring T
          (h.toAlgHom (MvPolynomial.X i))) := by
    rw [map_one]
    exact toKaehler_one_tmul_D _ _
  have hLHS : (Generators.self R T).toExtension.toKaehler
        (Extension.CotangentSpace.map h ((Generators.self R S).cotangentSpaceBasis i)) =
      KaehlerDifferential.D R T (algebraMap S T i) :=
    ((congrArg (fun z => (Generators.self R T).toExtension.toKaehler z) e1).trans e2).trans
      (congrArg (KaehlerDifferential.D R T)
        (hring.trans (congrArg (algebraMap S T) hXi)))
  have hRHS : KaehlerDifferential.map R R S T
        ((Generators.self R S).toExtension.toKaehler
          ((Generators.self R S).cotangentSpaceBasis i)) =
      KaehlerDifferential.D R T (algebraMap S T i) := by
    rw [Generators.toKaehler_cotangentSpaceBasis, KaehlerDifferential.map_D]
    rfl
  exact hLHS.trans hRHS.symm

/-- `NaiveCotangent.toKaehler_comp_cotangentSpaceMap_self`, read on elements. -/
theorem toKaehler_cotangentSpaceMap_self
    (h : (Generators.self R S).toExtension.Hom (Generators.self R T).toExtension)
    (x : (Generators.self R S).toExtension.CotangentSpace) :
    (Generators.self R T).toExtension.toKaehler (Extension.CotangentSpace.map h x) =
      KaehlerDifferential.map R R S T ((Generators.self R S).toExtension.toKaehler x) :=
  congrArg (fun m => m x) (toKaehler_comp_cotangentSpaceMap_self h)

/-- The degree-`0` comparison square for the canonical presentations, as an identity of linear
maps out of `T ⊗_S (Ω[R[S]⁄R] ⊗_{R[S]} S)`. -/
theorem toKaehler_comp_liftBaseChange_cotangentSpaceMap
    (h : (Generators.self R S).toExtension.Hom (Generators.self R T).toExtension) :
    (Generators.self R T).toExtension.toKaehler ∘ₗ
        (Extension.CotangentSpace.map h).liftBaseChange T =
      KaehlerDifferential.mapBaseChange R S T ∘ₗ
        (Generators.self R S).toExtension.toKaehler.baseChange T := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul, map_smul]
  exact congrArg (fun y => t • y) (toKaehler_cotangentSpaceMap_self h x)

/-- **Localizing the target**: for a localization `T = M⁻¹S` of `S` at a multiplicative subset
`M ⊆ S`, the canonical map of two-term complexes `NL_{S/R} ⊗_S T ⟶ NL_{T/R}` is a
quasi-isomorphism. -/
@[stacks 00S7 "the whole lemma at the level of the complexes: the canonical map
`NL_{S/R} ⊗_S T ⟶ NL_{T/R}` is a quasi-isomorphism. The `H₁` half alone is
`Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization`."]
theorem isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization (M : Submonoid S) [IsLocalization M T]
    (h : (Generators.self R S).toExtension.Hom (Generators.self R T).toExtension) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := T) h) :=
  ⟨bijective_onH₁_of_bijOn _
      (Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization M h),
    bijective_onH₀_of_surjective_square (T ⊗[S] Ω[S⁄R]) Ω[T⁄R] (nlExtensionBaseChangeMap (T := T) h)
      ((Generators.self R S).toExtension.toKaehler.baseChange T)
      (Generators.self R T).toExtension.toKaehler
      (KaehlerDifferential.mapBaseChange R S T)
      (surjective_baseChange_toKaehler _)
      (ker_baseChange_toKaehler _)
      (LinearMap.exact_iff.mp
        (Generators.self R T).toExtension.exact_cotangentComplex_toKaehler)
      (toKaehler_comp_liftBaseChange_cotangentSpaceMap h)
      (bijective_mapBaseChange_of_isLocalization M)⟩

end Target

/-!
## Localizing the base
-/

section Base

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] [Algebra R R']
  {T : Type*} [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]

/-- **Localizing the base**: for a localization `R' = N⁻¹R` of `R` at a multiplicative subset
`N ⊆ R` and a ring map `R' → T`, the canonical map of two-term complexes `NL_{T/R} ⟶ NL_{T/R'}`
is bijective in both degrees, hence a quasi-isomorphism. -/
@[stacks 07BS "the canonical map `NL_{T/R} ⟶ NL_{T/R'}` is bijective in both degrees, hence a
quasi-isomorphism; the homotopy equivalence itself is
`naiveCotangentComplex_localization_base_homotopyEquiv`."]
theorem isQuasiIso_nlExtensionOverMap_of_isLocalization (N : Submonoid R) [IsLocalization N R'] :
    IsQuasiIso (nlExtensionOverMap
      ((Generators.self R T).defaultHom (Generators.self R' T)).toExtensionHom) :=
  isQuasiIso_of_bijective _ (cotangent_map_bijective R R' T N)
    (cotangentSpace_map_bijective R R' T)

end Base

/-!
## Localizing the base and the target at once
-/

section BaseAndTarget

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {A' : Type u} [CommRing A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
  {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra R' A'] [IsScalarTower R R' A']

omit [IsScalarTower R A A'] in
/-- Compatibility of the degree-`1` comparison with the factorization through `NL_{A'/R}`. -/
theorem cotangentMap_comp_liftBaseChange_cotangentMap
    (h₁ : (Generators.self R A).toExtension.Hom (Generators.self R A').toExtension)
    (h₂ : (Generators.self R A').toExtension.Hom (Generators.self R' A').toExtension) :
    Extension.Cotangent.map h₂ ∘ₗ (Extension.Cotangent.map h₁).liftBaseChange A' =
      (Extension.Cotangent.map (h₂.comp h₁)).liftBaseChange A' := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  have hc := congrArg (fun m => m x) (Extension.Cotangent.map_comp _ h₁ h₂)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
    map_smul, hc]

omit [IsScalarTower R A A'] in
/-- Compatibility of the degree-`0` comparison with the factorization through `NL_{A'/R}`. -/
theorem cotangentSpaceMap_comp_liftBaseChange_cotangentSpaceMap
    (h₁ : (Generators.self R A).toExtension.Hom (Generators.self R A').toExtension)
    (h₂ : (Generators.self R A').toExtension.Hom (Generators.self R' A').toExtension) :
    Extension.CotangentSpace.map h₂ ∘ₗ
        (Extension.CotangentSpace.map h₁).liftBaseChange A' =
      (Extension.CotangentSpace.map (h₂.comp h₁)).liftBaseChange A' := by
  refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
  have hc := congrArg (fun m => m x) (Extension.CotangentSpace.map_comp h₁ h₂)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
    map_smul, hc]

omit [IsScalarTower R A A'] in
/-- The canonical factorization of the comparison through `NL_{A'/R}`: the chain map induced by
the composite of two morphisms of extensions is the composite of the two chain maps they
induce. -/
theorem nlExtensionBaseChangeMap_comp_eq
    (h₁ : (Generators.self R A).toExtension.Hom (Generators.self R A').toExtension)
    (h₂ : (Generators.self R A').toExtension.Hom (Generators.self R' A').toExtension) :
    (nlExtensionOverMap h₂).comp (nlExtensionBaseChangeMap (T := A') h₁) =
      nlExtensionBaseChangeMap (T := A') (h₂.comp h₁) :=
  ChainMap.ext (cotangentMap_comp_liftBaseChange_cotangentMap h₁ h₂)
    (cotangentSpaceMap_comp_liftBaseChange_cotangentSpaceMap h₁ h₂)

/-- **The naive cotangent complex and simultaneous localization of base and target.**  Let
`R → A` be a ring map, let `A'` be a localization of `A` at a multiplicative subset `M ⊆ A`, let
`R'` be a localization of `R` at a multiplicative subset `N ⊆ R`, and suppose `A'` is an
`R'`-algebra compatibly with `R → R' → A'` and `R → A → A'`.  Then the canonical map of two-term
complexes of `A'`-modules

`NL_{A/R} ⊗_A A' ⟶ NL_{A'/R'}`

is a quasi-isomorphism, for every morphism of extensions `h` inducing it. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization
    (M : Submonoid A) [IsLocalization M A'] (N : Submonoid R) [IsLocalization N R']
    (h : (Generators.self R A).toExtension.Hom (Generators.self R' A').toExtension) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := A') h) := by
  refine isQuasiIso_nlExtensionBaseChangeMap_congr h
    (((Generators.self R A').defaultHom (Generators.self R' A')).toExtensionHom.comp
      ((Generators.self R A).defaultHom (Generators.self R A')).toExtensionHom) ?_
  rw [← nlExtensionBaseChangeMap_comp_eq]
  exact (isQuasiIso_nlExtensionOverMap_of_isLocalization N).comp
    (isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization M _)

/-- **Localization at a prime.** Let `R → A` be a ring map, let `𝔭` be a prime of `A` and let
`𝔮 = 𝔭 ∩ R` be the prime of `R` below it. Let `A'` be the localization of `A` at `𝔭` and `R'` the
localization of `R` at `𝔮`. Then the canonical map of two-term complexes of `A_𝔭`-modules

`NL_{A/R} ⊗_A A_𝔭 ⟶ NL_{A_𝔭 / R_𝔮}`

is a quasi-isomorphism. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_atPrime (𝔭 : Ideal A) [𝔭.IsPrime]
    [IsLocalization.AtPrime A' 𝔭]
    [IsLocalization.AtPrime R' (𝔭.comap (algebraMap R A))]
    (h : (Generators.self R A).toExtension.Hom (Generators.self R' A').toExtension) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := A') h) :=
  isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization 𝔭.primeCompl
    (𝔭.comap (algebraMap R A)).primeCompl h

end BaseAndTarget

end NaiveCotangent

end
