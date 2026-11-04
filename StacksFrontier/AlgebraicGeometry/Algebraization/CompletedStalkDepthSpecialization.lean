module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksCore.Algebra.Module.LocalizedModule.LocalizationLocalization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecializationModule
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesLocallyFreeOutside

/-!
# Depth plus dimension of a completed stalk along a specialization

Let `X` be a locally Noetherian scheme, let `ℐ` be a quasi-coherent sheaf of ideals, let `(ℱ_n)`
be a coherent `ℐ`-adic system and let `y ⤳ y'` be a specialization of points of `X`, coming from
a prime `q` of `𝒪_{X,y'}` containing the stalk `ℐ_{y'}`. Write `𝒪_{X,x}^∧` for the `ℐ`-adic
completion of the local ring and `ℱ_x^∧` for the completed stalk. The second display of
[Stacks, Tag 0EHW] at the two points reads, for a prime `𝔭` of `𝒪_{X,y}^∧` with contraction `𝔭'`
along the specialization map `𝒪_{X,y'}^∧ → 𝒪_{X,y}^∧`,

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + 1 = depth((ℱ_{y'}^∧)_{𝔭'}) + dim(𝒪_{X,y'}^∧/𝔭')`,

the extra `1` being `dim(𝒪_{X,y'}/q)`, assumed to be one — the specialization is *immediate*.
This is the final step of the proof of [Stacks, Tag 0EJA].

## Main results

* `Stacks.Algebraization.completedStalkDepth_add_ringKrullDim_succ_eq_of_specializes` — the
  display above.
* `Stacks.Algebraization.exists_ringEquiv_completedLocalRing_of_specializes` — `𝒪_{X,y}^∧` is the
  `ℐ`-adic completion of `(𝒪_{X,y'}^∧)_𝔮` **compatibly with the specialization map of completed
  local rings**, where `𝔮` is the prime of `𝒪_{X,y'}^∧` above `q`.

## Main definitions

* `Stacks.Algebraization.completedStalkLocalization`,
  `Stacks.Algebraization.completedStalkLocalizationIdeal` and
  `Stacks.Algebraization.completedStalkLocalizedModule` — the localization `C = (𝒪_{X,y'}^∧)_𝔮`,
  its adic ideal `ℐC` and the localization `(ℱ_{y'}^∧)_𝔮`, the three objects the completion is
  taken of.

## Proof outline

The second display of [Stacks, Tag 0EHW] is available, as
`Module.depth_add_ringKrullDim_quotient_adicCompletion_of_isUniversallyCatenary`, for a Noetherian
local ring which is universally catenary and whose local rings have Cohen--Macaulay formal fibres
-- the two things the source derives from its dualizing complex, and all its proof uses. It is
applied to `C = (𝒪_{X,y'}^∧)_𝔮`, which is Noetherian local and inherits both properties from
`𝒪_{X,y'}^∧`, universal catenarity by `Ring.IsUniversallyCatenary.localization`
([Stacks, Tag 00NJ]) and the formal fibres by
`Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_localizationAtPrime`. It gives

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) = depth(((ℱ_{y'}^∧)_𝔮)_{𝔭 ∩ C}) + dim(C/𝔭 ∩ C)`

once the two sides are transported along the identification of `𝒪_{X,y}^∧` with the `ℐ`-adic
completion of `C` and of `ℱ_y^∧` with the `ℐ`-adic completion of `(ℱ_{y'}^∧)_𝔮`. Localizing
`ℱ_{y'}^∧` at `𝔮` and then at `𝔭 ∩ C` is localizing at `𝔭'`, so the first term on the right is
`depth((ℱ_{y'}^∧)_{𝔭'})`; and `dim(C/𝔭 ∩ C) + dim(𝒪_{X,y'}^∧/𝔮) = dim(𝒪_{X,y'}^∧/𝔭')` because
`𝒪_{X,y'}^∧` is universally catenary ([Stacks, Tag 0A80]), with
`dim(𝒪_{X,y'}^∧/𝔮) = dim(𝒪_{X,y'}/q) = 1`.

## Implementation notes

The two identifications are supplied by
`Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_of_specializes` and
`Stacks.Algebraization.nonempty_linearEquiv_completedStalk_of_specializes`, both as isomorphisms
of `𝒪_{X,y'}`-algebras resp. `𝒪_{X,y'}`-modules. What the statement about primes of
`𝒪_{X,y}^∧` and `𝒪_{X,y'}^∧` needs is more: the ring isomorphism must intertwine the
specialization map `𝒪_{X,y'}^∧ → 𝒪_{X,y}^∧` with `𝒪_{X,y'}^∧ → C → C^∧`, and the module
isomorphism must be semilinear over it. Both upgrades are automatic and are carried out here:

* over `𝒪_{X,y'}^∧`, because `C^∧` is `ℐ_{y'}`-adically Hausdorff and two ring maps out of
  `𝒪_{X,y'}^∧` into it agree as soon as they agree on `𝒪_{X,y'}`
  (`Stacks.Algebraization.ringHom_eq_of_comp_algebraMap_eq`);
* over `𝒪_{X,y}`, because `𝒪_{X,y}` is a localization of `𝒪_{X,y'}` whose denominators act
  invertibly on `C` (`Stacks.Algebraization.semilinear_of_localization`), and then over
  `𝒪_{X,y}^∧` by the same Hausdorff argument, now on the module
  (`Stacks.Algebraization.semilinear_of_adicCompletion`).

The adic ideal of `C` is spelled as the extension of `ℐ𝒪_{X,y'}^∧` along `𝒪_{X,y'}^∧ → C`, while
`Stacks.Algebraization.nonempty_linearEquiv_completedStalk_of_specializes` spells it as the
extension of `ℐ_{y'}` along the composite `𝒪_{X,y'} → C`. The two `𝒪_{X,y'}`-algebra structures
on `C` available in the library are not definitionally equal, so the two ideals are equal but not
syntactically so; `Stacks.Algebraization.adicCompletionCongr` and
`Stacks.Algebraization.adicCompletionModuleCongr` transport the completions between them.

Transporting depth at a prime along the isomorphisms is
`Stacks.Algebraization.depth_localizedModule_eq_of_semilinearEquiv`: viewed over the smaller
ring, the localization of the target at the image prime satisfies the universal property of the
localization of the source, and the resulting linear isomorphism is semilinear over the induced
isomorphism of the two local rings.

## References

* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), the second display.
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE), finiteness of the
  completed stalk.
* [Stacks Project, Tag 00NJ](https://stacks.math.columbia.edu/tag/00NJ), universal catenarity
  under localization.
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY), the formal fibres.
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
* [Stacks Project, Tag 02C7](https://stacks.math.columbia.edu/tag/02C7), iterated localization.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Shrinking the multiplicative set of a localized module -/

/-- **A localization at `T` is a localization at a smaller `S`** when every element of `T`
divides into `S`: the extra denominators are already invertible. This is the module analogue of
`IsLocalization.isLocalization_of_is_exists_mul_mem`, read in the opposite direction. -/
private theorem isLocalizedModule_of_exists_mul_mem {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (S T : Submonoid R) (hST : S ≤ T) (hdiv : ∀ x : T, ∃ m : R, m * (x : R) ∈ S)
    (f : M →ₗ[R] N) [IsLocalizedModule T f] : IsLocalizedModule S f where
  map_units x := IsLocalizedModule.map_units f ⟨(x : R), hST x.2⟩
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj T f y
    obtain ⟨m, hm⟩ := hdiv t
    refine ⟨⟨m • x, ⟨m * (t : R), hm⟩⟩, ?_⟩
    rw [Submonoid.smul_def] at e
    rw [Submonoid.smul_def, mul_smul, map_smul, e]
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) e
    obtain ⟨m, hm⟩ := hdiv c
    refine ⟨⟨m * (c : R), hm⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def] at hc
    rw [Submonoid.smul_def, Submonoid.smul_def, mul_smul, mul_smul, hc]

/-! ### Semilinearity of a semilinear map on localizations -/

/-- **A semilinear additive map between modules over localizations is semilinear over any ring map
compatible with the base**, provided the denominators act invertibly on the target. Both sides
have the same product with the image of a denominator. -/
private theorem smul_of_semilinear_localization
    {A D : Type*} [CommRing A] [CommRing D] (e : A →+* D) (S : Submonoid A)
    {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra D A₂]
    [IsLocalization S A₁] (ε : A₁ →+* A₂)
    (hε : ∀ a : A, ε (algebraMap A A₁ a) = algebraMap D A₂ (e a))
    (hunit : ∀ s : S, IsUnit (algebraMap D A₂ (e (s : A))))
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module A W₁] [Module A₁ W₁] [IsScalarTower A A₁ W₁]
    [AddCommGroup W₂] [Module D W₂] [Module A₂ W₂] [IsScalarTower D A₂ W₂]
    (Φ : W₁ →+ W₂) (hΦ : ∀ (a : A) (w : W₁), Φ (a • w) = e a • Φ w)
    (x : A₁) (z : W₁) : Φ (x • z) = ε x • Φ z := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  refine ((hunit s).smul_left_cancel (α := A₂)).1 ?_
  have hmul : algebraMap A A₁ (s : A) * IsLocalization.mk' A₁ a s = algebraMap A A₁ a :=
    IsLocalization.mk'_spec' A₁ a s
  calc algebraMap D A₂ (e (s : A)) • Φ (IsLocalization.mk' A₁ a s • z)
      = e (s : A) • Φ (IsLocalization.mk' A₁ a s • z) := by rw [algebraMap_smul]
    _ = Φ ((s : A) • (IsLocalization.mk' A₁ a s • z)) := (hΦ _ _).symm
    _ = Φ ((algebraMap A A₁ (s : A) * IsLocalization.mk' A₁ a s) • z) := by
        rw [mul_smul, algebraMap_smul]
    _ = Φ (a • z) := by rw [hmul, algebraMap_smul]
    _ = e a • Φ z := hΦ a z
    _ = algebraMap D A₂ (e a) • Φ z := by rw [algebraMap_smul]
    _ = (ε (algebraMap A A₁ (s : A)) * ε (IsLocalization.mk' A₁ a s)) • Φ z := by
        rw [← map_mul, hmul, hε]
    _ = algebraMap D A₂ (e (s : A)) • ε (IsLocalization.mk' A₁ a s) • Φ z := by
        rw [mul_smul, hε]

/-- **Depth is invariant under a semilinear isomorphism of localized modules.** Let `e : A ≃+* D`
carry the multiplicative set `S` onto `T`, let `A₁`, `A₂` be the localizations at `S` and `T`
which are local rings, and let `Φ : W₁ ≃+ W₂` be `e`-semilinear. If `ε : A₁ ≃+* A₂` extends `e`,
then `Φ` is `ε`-semilinear by `Stacks.Algebraization.smul_of_semilinear_localization`, so the
depths over the maximal ideals agree. -/
private theorem depth_eq_of_semilinearEquiv_localization
    {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)
    (S : Submonoid A) (T : Submonoid D) (hST : S.map (e : A →* D) = T)
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra D A₂]
    [IsLocalization S A₁] [IsLocalization T A₂] [IsLocalRing A₁] [IsLocalRing A₂]
    {W₁ W₂ : Type u} [AddCommGroup W₁] [Module A W₁] [Module A₁ W₁] [IsScalarTower A A₁ W₁]
    [AddCommGroup W₂] [Module D W₂] [Module A₂ W₂] [IsScalarTower D A₂ W₂]
    (ε : A₁ ≃+* A₂) (hε : ∀ a : A, ε (algebraMap A A₁ a) = algebraMap D A₂ (e a))
    (Φ : W₁ ≃+ W₂) (hΦ : ∀ (a : A) (w : W₁), Φ (a • w) = e a • Φ w) :
    Module.depth A₁ (maximalIdeal A₁) W₁ = Module.depth A₂ (maximalIdeal A₂) W₂ := by
  have hsemi := smul_of_semilinear_localization (e : A →+* D) S (ε : A₁ →+* A₂) hε
    (fun s => IsLocalization.map_units A₂
      ⟨e (s : A), show e (s : A) ∈ T from hST ▸ ⟨(s : A), s.2, rfl⟩⟩)
    Φ.toAddMonoidHom hΦ
  rw [Module.depth_eq_of_semilinearEquiv ε (maximalIdeal A₁) Φ hsemi]
  congr 1
  exact IsLocalRing.map_ringEquiv_maximalIdeal ε

/-! ### Depth at corresponding primes -/

/-- **Depth at corresponding primes is an invariant of a semilinear isomorphism.** Let
`e : A ≃+* D` be an isomorphism of rings and let `φ : M ≃+ N` be an `e`-semilinear isomorphism
from an `A`-module to a `D`-module. If `𝔭` and `𝔓` are primes with `e(𝔭) = 𝔓`, then the depth of
`M_𝔭` over `A_𝔭` is the depth of `N_𝔓` over `D_𝔓`.

The localized modules are matched by the universal property of a localized module: viewed over
`A` through `e`, the module `N_𝔓` is a localization of `M` at the complement of `𝔭`. The
resulting `A`-linear isomorphism is semilinear over the induced isomorphism `A_𝔭 ≃+* D_𝔓` by
`Stacks.Algebraization.depth_eq_of_semilinearEquiv_localization`. -/
private theorem depth_localizedModule_eq_of_semilinearEquiv
    {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)
    {M : Type u} [AddCommGroup M] [Module A M]
    {N : Type u} [AddCommGroup N] [Module D N]
    (φ : M ≃+ N) (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m)
    (p : Ideal A) [p.IsPrime] (P : Ideal D) [P.IsPrime]
    (hP : p.primeCompl.map (e : A →* D) = P.primeCompl) :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl N) := by
  have hmem : ∀ s : p.primeCompl, e (s : A) ∈ P.primeCompl := fun s =>
    hP ▸ ⟨(s : A), s.2, rfl⟩
  have hsurj : ∀ t : P.primeCompl, ∃ s : A, s ∈ p.primeCompl ∧ e s = (t : D) := fun t => by
    have ht : (t : D) ∈ Submonoid.map (e : A →* D) p.primeCompl := by
      rw [hP]
      exact t.2
    exact ht
  let : Algebra A D := (e : A →+* D).toAlgebra
  let : Module A N := Module.compHom N (e : A →+* D)
  let : Module A (LocalizedModule P.primeCompl N) :=
    Module.compHom (LocalizedModule P.primeCompl N) (e : A →+* D)
  let φ' : M ≃ₗ[A] N := { __ := φ, map_smul' := hφ }
  let mkA : N →ₗ[A] LocalizedModule P.primeCompl N :=
    { toFun := fun n => LocalizedModule.mk n 1
      map_add' := fun x y => (LocalizedModule.mkLinearMap P.primeCompl N).map_add x y
      map_smul' := fun a n => (LocalizedModule.mkLinearMap P.primeCompl N).map_smul (e a) n }
  let g : M →ₗ[A] LocalizedModule P.primeCompl N := mkA ∘ₗ (φ' : M →ₗ[A] N)
  have hgval : ∀ m : M, g m = LocalizedModule.mk (φ m) 1 := fun _ => rfl
  have hg : IsLocalizedModule p.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {m₁ m₂} hm => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hu := IsLocalizedModule.map_units
        (LocalizedModule.mkLinearMap P.primeCompl N) ⟨e (s : A), hmem s⟩
      rw [Module.End.isUnit_iff] at hu
      exact hu
    · obtain ⟨⟨n, t⟩, ht⟩ := IsLocalizedModule.surj P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N) y
      obtain ⟨s, hs, hst⟩ := hsurj t
      refine ⟨⟨φ.symm n, ⟨s, hs⟩⟩, ?_⟩
      have hy : e s • y = LocalizedModule.mk n 1 := by
        rw [hst]
        exact ht
      rw [hgval, φ.apply_symm_apply]
      exact hy
    · have h1 : LocalizedModule.mk (φ m₁) (1 : P.primeCompl) = LocalizedModule.mk (φ m₂) 1 := hm
      obtain ⟨t, hts⟩ := IsLocalizedModule.exists_of_eq
        (S := P.primeCompl) (f := LocalizedModule.mkLinearMap P.primeCompl N) h1
      obtain ⟨s, hs, hst⟩ := hsurj t
      have h3 : s • m₁ = s • m₂ := φ.injective (by
        rw [hφ, hφ, hst]
        exact hts)
      exact ⟨⟨s, hs⟩, h3⟩
  let Φ₀ : LocalizedModule p.primeCompl M ≃ₗ[A] LocalizedModule P.primeCompl N :=
    IsLocalizedModule.iso p.primeCompl g
  let ε : Localization.AtPrime p ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime P) e hP
  have hε : ∀ a : A, ε (algebraMap A (Localization.AtPrime p) a) =
      algebraMap D (Localization.AtPrime P) (e a) := fun a =>
    IsLocalization.ringEquivOfRingEquiv_eq _ a
  have hΦ : ∀ (a : A) (w : LocalizedModule p.primeCompl M),
      Φ₀.toAddEquiv (a • w) = e a • Φ₀.toAddEquiv w := fun a w => Φ₀.map_smul a w
  exact depth_eq_of_semilinearEquiv_localization e p.primeCompl P.primeCompl hP ε hε
    Φ₀.toAddEquiv hΦ




/-- A prime of the localization `B_𝔮` contracts to a prime contained in `𝔮`. -/
private theorem comap_le_of_isPrime_atPrime {B : Type*} [CommRing B] (𝔮 : Ideal B) [𝔮.IsPrime]
    (P : Ideal (Localization.AtPrime 𝔮)) [P.IsPrime] :
    P.comap (algebraMap B (Localization.AtPrime 𝔮)) ≤ 𝔮 :=
  (Ideal.comap_mono (IsLocalRing.le_maximalIdeal ‹P.IsPrime›.ne_top)).trans_eq
    Localization.AtPrime.under_maximalIdeal

/-- **Depth at a prime of a localization, read on the base.** Let `𝔮` be a prime of `B`, let `M`
be a `B`-module and let `𝔓` be a prime of `B_𝔮` lying over the prime `𝔭 = 𝔓 ∩ B`. Then the depth
of `(M_𝔮)_𝔓` over `(B_𝔮)_𝔓` is the depth of `M_𝔭` over `B_𝔭`.

Localizing at `𝔮` and then at `𝔓` is localizing at `𝔭`: the extra denominators introduced at the
first step are already invertible after the second, which is
`Stacks.Algebraization.isLocalizedModule_of_exists_mul_mem` for the module and
`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization` for the ring. -/
private theorem depth_localizedModule_localization_atPrime
    {B : Type u} [CommRing B] (𝔮 : Ideal B) [𝔮.IsPrime]
    (M : Type u) [AddCommGroup M] [Module B M]
    (P : Ideal (Localization.AtPrime 𝔮)) [P.IsPrime] :
    Module.depth
          (Localization.AtPrime (P.comap (algebraMap B (Localization.AtPrime 𝔮))))
          (maximalIdeal (Localization.AtPrime
            (P.comap (algebraMap B (Localization.AtPrime 𝔮)))))
          (LocalizedModule
            (P.comap (algebraMap B (Localization.AtPrime 𝔮))).primeCompl M) =
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl (LocalizedModule 𝔮.primeCompl M)) := by
  set C := Localization.AtPrime 𝔮 with hC
  set p : Ideal B := P.comap (algebraMap B C)
  have _ : p.IsPrime := Ideal.IsPrime.comap _
  have hple : p ≤ 𝔮 := comap_le_of_isPrime_atPrime 𝔮 P
  have hcompl : 𝔮.primeCompl ≤ p.primeCompl := fun x hx hmem => hx (hple hmem)
  have hsup : p.primeCompl ⊔ 𝔮.primeCompl = p.primeCompl := sup_eq_left.mpr hcompl
  -- the multiplicative sets of the two localizations of the module
  have hST : Algebra.algebraMapSubmonoid C p.primeCompl ≤ P.primeCompl := by
    rintro _ ⟨b, hb, rfl⟩
    exact hb
  have hdiv : ∀ x : P.primeCompl, ∃ m : C, m * (x : C) ∈
      Algebra.algebraMapSubmonoid C p.primeCompl := by
    intro x
    obtain ⟨b, u, hbu⟩ := IsLocalization.exists_mk'_eq 𝔮.primeCompl (x : C)
    refine ⟨algebraMap B C (u : B), ?_⟩
    have hmul : algebraMap B C (u : B) * (x : C) = algebraMap B C b := by
      rw [← hbu]
      exact IsLocalization.mk'_spec' C b u
    rw [hmul]
    refine ⟨b, ?_, rfl⟩
    intro hbp
    refine (x.2 : (x : C) ∉ P) ?_
    have hbP : algebraMap B C b ∈ P := hbp
    exact (‹P.IsPrime›.mem_or_mem (hmul ▸ hbP)).resolve_left fun h => hcompl u.2 h
  have _ : IsLocalizedModule (Algebra.algebraMapSubmonoid C p.primeCompl)
      (LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule 𝔮.primeCompl M)) :=
    isLocalizedModule_of_exists_mul_mem _ P.primeCompl hST hdiv _
  have _ : IsLocalizedModule p.primeCompl
      ((LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule 𝔮.primeCompl M)).restrictScalars
        B) :=
    IsLocalizedModule.restrictScalars p.primeCompl _
  have hdouble : IsLocalizedModule p.primeCompl
      (LocalizedModule.doubleMkLinearMap p.primeCompl 𝔮.primeCompl M) := by
    have h : IsLocalizedModule (p.primeCompl ⊔ 𝔮.primeCompl)
        (LocalizedModule.doubleMkLinearMap p.primeCompl 𝔮.primeCompl M) := inferInstance
    rwa [hsup] at h
  let Ψ : LocalizedModule p.primeCompl (LocalizedModule 𝔮.primeCompl M) ≃ₗ[B]
      LocalizedModule P.primeCompl (LocalizedModule 𝔮.primeCompl M) :=
    IsLocalizedModule.linearEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (LocalizedModule 𝔮.primeCompl M))
      ((LocalizedModule.mkLinearMap P.primeCompl
        (LocalizedModule 𝔮.primeCompl M)).restrictScalars B)
  let Φ : LocalizedModule p.primeCompl M ≃ₗ[B]
      LocalizedModule P.primeCompl (LocalizedModule 𝔮.primeCompl M) :=
    (IsLocalizedModule.iso p.primeCompl
      (LocalizedModule.doubleMkLinearMap p.primeCompl 𝔮.primeCompl M)).trans Ψ
  let εalg : Localization.AtPrime p ≃ₐ[B] Localization.AtPrime P :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (Localization.AtPrime P)
  have hε : ∀ b : B, εalg.toRingEquiv (algebraMap B (Localization.AtPrime p) b) =
      algebraMap B (Localization.AtPrime P) ((RingEquiv.refl B) b) := fun b => εalg.commutes b
  exact depth_eq_of_semilinearEquiv_localization (RingEquiv.refl B) p.primeCompl p.primeCompl
    (Submonoid.map_id _) εalg.toRingEquiv hε Φ.toAddEquiv (fun b w => Φ.map_smul b w)


/-! ### The dimension of a quotient splits along a bigger prime -/


/-- **In a Noetherian universally catenary local ring the dimension of `A/𝔭` splits along a
prime `𝔮 ⊇ 𝔭`** as the dimension of `A_𝔮/𝔭A_𝔮` plus the dimension of `A/𝔮`.

The ring `A/𝔭` is a Noetherian universally catenary local domain, so heights in it are additive
along `𝔮/𝔭 ≤ 𝔪`; the two summands are the dimension of the localization of `A/𝔭` at `𝔮/𝔭`, which
is `A_𝔮/𝔭A_𝔮`, and the dimension of `(A/𝔭)/(𝔮/𝔭) = A/𝔮`. -/
private theorem ringKrullDim_quotient_localization_add
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcat : Ring.IsUniversallyCatenary A) (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) +
      ringKrullDim (A ⧸ q) = ringKrullDim (A ⧸ p) := by
  classical
  rw [Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p q hpq]
  let Bq := A ⧸ p
  let qbar : Ideal Bq := q.map (Ideal.Quotient.mk p)
  have hqbarPrime : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have _ : qbar.IsPrime := hqbarPrime
  have _ : Nontrivial Bq := Ideal.Quotient.nontrivial_iff.mpr ‹p.IsPrime›.ne_top
  have _ : IsLocalRing Bq :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hqbarMax : qbar ≤ maximalIdeal Bq := IsLocalRing.le_maximalIdeal hqbarPrime.ne_top
  have hcatB : Ring.IsUniversallyCatenary Bq :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hcat
  have hsum := catenary_height_add (universallyCatenaryOfRingUniversallyCatenary' hcatB) qbar
    (maximalIdeal Bq) hqbarMax
  have _ : Nontrivial (Bq ⧸ qbar) := Ideal.Quotient.nontrivial_iff.mpr hqbarPrime.ne_top
  have _ : IsLocalRing (Bq ⧸ qbar) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk qbar) Ideal.Quotient.mk_surjective
  have hdimtop : ((Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal Bq)).height : WithBot ℕ∞) =
      ringKrullDim (A ⧸ q) := by
    calc ((Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal Bq)).height : WithBot ℕ∞) =
        ringKrullDim (Bq ⧸ qbar) := by
          rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Bq ⧸ qbar),
            IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk qbar)
              Ideal.Quotient.mk_surjective]
      _ = ringKrullDim (A ⧸ q) :=
          ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)
  calc (qbar.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q)
      = ((qbar.height + (Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal Bq)).height :
          ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add, hdimtop]
    _ = ((maximalIdeal Bq).height : WithBot ℕ∞) := congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞))
        hsum.symm
    _ = ringKrullDim (A ⧸ p) := IsLocalRing.maximalIdeal_height_eq_ringKrullDim


/-! ### Primes along a ring isomorphism -/

/-- A ring isomorphism carries the complement of a prime onto the complement of a prime lying
under it. -/
private theorem primeCompl_map_ringEquiv {A D : Type*} [CommRing A] [CommRing D]
    (e : A ≃+* D) {p : Ideal A} [p.IsPrime] {P : Ideal D} [P.IsPrime]
    (hP : P.comap (e : A →+* D) = p) :
    p.primeCompl.map (e : A →* D) = P.primeCompl := by
  ext x
  simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, rfl⟩ hmem
    rw [← hP] at ha
    exact ha hmem
  · intro hx
    refine ⟨e.symm x, fun hmem => hx ?_, e.apply_symm_apply x⟩
    rw [← hP, Ideal.mem_comap] at hmem
    simpa using hmem

/-! ### Depth at equal primes -/

/-- The depth of a localized module at a prime depends on the prime only through its value: the
primality instance is a proposition. -/
private theorem depth_localizedModule_congr {B : Type u} [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] {p p' : Ideal B} [p.IsPrime] [p'.IsPrime]
    (hpp : p = p') :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl M) := by
  subst hpp
  rfl

/-! ### The algebraic form of the second display along a localization -/

/-- **The second display of [Stacks, Tag 0EHW] across the completion of a localization.**

Let `B` be a Noetherian local ring which is universally catenary and whose local rings have
Cohen--Macaulay formal fibres, let `𝔮` be a prime with
`dim(B/𝔮) = 1`, let `M` be a finite `B`-module, and write `C = B_𝔮` and `N = M_𝔮`. Let `K ⊆ 𝔪_C`
be an ideal, let `σ : B → A` be a ring map and let `e : A ≃+* C^∧` be an isomorphism onto the
`K`-adic completion of `C` with `e ∘ σ` the structure map `B → C → C^∧`, and let `φ` identify an
`A`-module `Mfs` with the `K`-adic completion of `N`, semilinearly over `e`. Then for every prime
`𝔭` of `A`, writing `𝔭₀ = σ⁻¹(𝔭)`,

`depth(Mfs_𝔭) + dim(A/𝔭) + 1 = depth(M_{𝔭₀}) + dim(B/𝔭₀)`.

The second display of [Stacks, Tag 0EHW] for the ring `C`, which inherits both hypotheses
from `B`, gives `depth(Mfs_𝔭) + dim(A/𝔭) = depth(N_{𝔭 ∩ C}) + dim(C/(𝔭 ∩ C))` after transporting
both sides along `e` and `φ`. The depth term is `depth(M_{𝔭₀})` because localizing `M` at `𝔮` and
then at `𝔭 ∩ C` is localizing at `𝔭₀`, and `dim(C/(𝔭 ∩ C)) + 1 = dim(B/𝔭₀)` because `B` is
universally catenary and `dim(B/𝔮) = 1`. -/
private theorem depth_add_ringKrullDim_succ_eq_of_adicCompletion_localization
    {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (hcat : Ring.IsUniversallyCatenary B)
    (hCM : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u} B)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hdim𝔮 : ringKrullDim (B ⧸ 𝔮) = 1)
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    {A : Type u} [CommRing A] (σ : B →+* A)
    {Mfs : Type u} [AddCommGroup Mfs] [Module A Mfs]
    {K : Ideal (Localization.AtPrime 𝔮)}
    (hKmax : K ≤ maximalIdeal (Localization.AtPrime 𝔮))
    (e : A ≃+* AdicCompletion K (Localization.AtPrime 𝔮))
    (he : ∀ b : B, e (σ b) =
      algebraMap (Localization.AtPrime 𝔮) (AdicCompletion K (Localization.AtPrime 𝔮))
        (algebraMap B (Localization.AtPrime 𝔮) b))
    (φ : Mfs ≃+ AdicCompletion K (LocalizedModule 𝔮.primeCompl M))
    (hφ : ∀ (a : A) (m : Mfs), φ (a • m) = e a • φ m)
    (p : Ideal A) [p.IsPrime] :
    (Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl Mfs) : WithBot ℕ∞) + ringKrullDim (A ⧸ p) + 1 =
      (Module.depth (Localization.AtPrime (p.comap σ))
          (maximalIdeal (Localization.AtPrime (p.comap σ)))
          (LocalizedModule (p.comap σ).primeCompl M) : WithBot ℕ∞) +
        ringKrullDim (B ⧸ p.comap σ) := by
  classical
  -- both hypotheses pass to the localization `C = B_𝔮`
  have hcatC : Ring.IsUniversallyCatenary (Localization.AtPrime 𝔮) :=
    Ring.IsUniversallyCatenary.localization 𝔮.primeCompl (Localization.AtPrime 𝔮) hcat
  have hCMC : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
      (Localization.AtPrime 𝔮) :=
    Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_localizationAtPrime hCM 𝔮
  have hesurj : Function.Surjective
      (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮)) := e.surjective
  have hker : RingHom.ker (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 e.injective
  set P := p.map (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮)) with hPdef
  set P₀ := P.comap (algebraMap (Localization.AtPrime 𝔮)
    (AdicCompletion K (Localization.AtPrime 𝔮))) with hP₀def
  have _ : P.IsPrime := Ideal.map_isPrime_of_surjective
    (f := (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮))) hesurj
    (le_of_eq_of_le hker bot_le)
  have hPprime : P₀.IsPrime := Ideal.IsPrime.comap _
  have _ : P.LiesOver P₀ := ⟨rfl⟩
  have _ : (p.comap σ).IsPrime := Ideal.IsPrime.comap _
  -- the contraction of `𝔭` along `e` is `𝔭`
  have hcomapP' : P.comap (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮)) = p := by
    have h0 : Ideal.comap (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮))
        (⊥ : Ideal (AdicCompletion K (Localization.AtPrime 𝔮))) = ⊥ := hker
    rw [hPdef, Ideal.comap_map_of_surjective _ hesurj, h0, sup_bot_eq]
  -- the contraction of `𝔭 ∩ C` to `B` is `𝔭₀`
  have hcomp : (algebraMap (Localization.AtPrime 𝔮)
        (AdicCompletion K (Localization.AtPrime 𝔮))).comp
      (algebraMap B (Localization.AtPrime 𝔮)) =
      (e : A →+* AdicCompletion K (Localization.AtPrime 𝔮)).comp σ :=
    RingHom.ext fun b => (he b).symm
  have hPcomap : P₀.comap (algebraMap B (Localization.AtPrime 𝔮)) = p.comap σ := by
    rw [hP₀def, Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hcomapP']
  -- the second display for `C`
  have hmain := Module.depth_add_ringKrullDim_quotient_adicCompletion_of_isUniversallyCatenary
    (Localization.AtPrime 𝔮) hcatC hCMC K hKmax (LocalizedModule 𝔮.primeCompl M) P₀ P
  -- the depth at `𝔭` and the dimension of `A/𝔭`, read on the completion
  have ha := depth_localizedModule_eq_of_semilinearEquiv e φ hφ p P
    (primeCompl_map_ringEquiv e hcomapP')
  have hb : ringKrullDim (A ⧸ p) =
      ringKrullDim (AdicCompletion K (Localization.AtPrime 𝔮) ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p _ e rfl)
  -- the depth at `𝔭 ∩ C` is the depth at `𝔭₀`
  have hc := depth_localizedModule_localization_atPrime 𝔮 M P₀
  have hcc := depth_localizedModule_congr M hPcomap
  -- the dimension of `C/(𝔭 ∩ C)` plus one is the dimension of `B/𝔭₀`
  have hple : p.comap σ ≤ 𝔮 := hPcomap ▸ comap_le_of_isPrime_atPrime 𝔮 P₀
  have hPeq : P₀ = (p.comap σ).map (algebraMap B (Localization.AtPrime 𝔮)) := by
    rw [← hPcomap]
    exact (IsLocalization.map_under 𝔮.primeCompl (Localization.AtPrime 𝔮) _).symm
  have hd := ringKrullDim_quotient_localization_add hcat (p.comap σ) 𝔮 hple
  rw [← hPeq, hdim𝔮] at hd
  rw [ha, hb, hmain, ← hc, hcc, ← hd, add_assoc]



/-! ### Rigidity of a map out of an adic completion -/

/-- **Two ring maps out of an adic completion that agree on the base agree**, provided the target
has no nonzero element divisible by every power of the ideal. Every element of `R^∧` is congruent
to an element of `R` modulo `IⁿR^∧`, so the two images differ by an element of `Iⁿ` in the target
for every `n`. -/
private theorem ringHom_eq_of_comp_algebraMap_eq {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I.FG) {T : Type u} [CommRing T] (ρ : R →+* T)
    (hsep : ∀ t : T, (∀ n : ℕ, t ∈ (I ^ n).map ρ) → t = 0)
    (τ₁ τ₂ : AdicCompletion I R →+* T)
    (hτ₁ : τ₁.comp (algebraMap R (AdicCompletion I R)) = ρ)
    (hτ₂ : τ₂.comp (algebraMap R (AdicCompletion I R)) = ρ) :
    τ₁ = τ₂ := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  obtain ⟨a, ha⟩ := AdicCompletion.exists_sub_mem_map_pow I hI n x
  have key : ∀ τ : AdicCompletion I R →+* T,
      τ.comp (algebraMap R (AdicCompletion I R)) = ρ → τ x - ρ a ∈ (I ^ n).map ρ := by
    intro τ hτ
    have h1 : τ (x - algebraMap R (AdicCompletion I R) a) ∈
        ((I ^ n).map (algebraMap R (AdicCompletion I R))).map τ := Ideal.mem_map_of_mem τ ha
    rw [Ideal.map_map, hτ, map_sub] at h1
    have h2 : τ (algebraMap R (AdicCompletion I R) a) = ρ a := by
      rw [← RingHom.comp_apply, hτ]
    rwa [h2] at h1
  rw [← sub_sub_sub_cancel_right (τ₁ x) (τ₂ x) (ρ a)]
  exact Ideal.sub_mem _ (key τ₁ hτ₁) (key τ₂ hτ₂)

/-! ### Transport of an adic completion along an equality of ideals -/

/-- The adic completions of a ring along two equal ideals are isomorphic. -/
private def adicCompletionCongr {C : Type u} [CommRing C] {K₁ K₂ : Ideal C} (hK : K₁ = K₂) :
    AdicCompletion K₁ C ≃+* AdicCompletion K₂ C := by
  subst hK; exact RingEquiv.refl _

/-- The adic completions of a module along two equal ideals are isomorphic. -/
private def adicCompletionModuleCongr {C : Type u} [CommRing C] {K₁ K₂ : Ideal C} (hK : K₁ = K₂)
    (N : Type u) [AddCommGroup N] [Module C N] :
    AdicCompletion K₁ N ≃+ AdicCompletion K₂ N := by
  subst hK; exact AddEquiv.refl _

/-- The isomorphism of `Stacks.Algebraization.adicCompletionModuleCongr` is linear. -/
private theorem adicCompletionModuleCongr_smul {C : Type u} [CommRing C] {K₁ K₂ : Ideal C}
    (hK : K₁ = K₂) (N : Type u) [AddCommGroup N] [Module C N] (c : C)
    (x : AdicCompletion K₁ N) :
    adicCompletionModuleCongr hK N (c • x) = c • adicCompletionModuleCongr hK N x := by
  subst hK
  rfl

/-- The isomorphism of `Stacks.Algebraization.adicCompletionCongr` is compatible with the
structure maps. -/
private theorem adicCompletionCongr_algebraMap {C : Type u} [CommRing C] {K₁ K₂ : Ideal C}
    (hK : K₁ = K₂) (x : C) :
    adicCompletionCongr hK (algebraMap C (AdicCompletion K₁ C) x) =
      algebraMap C (AdicCompletion K₂ C) x := by
  subst hK
  rfl


/-! ### Semilinearity from linearity -/

/-- Acting by an element of `I • A` on a module over `A` lands in `I • M`. -/
private theorem smul_mem_smul_top {R : Type*} [CommRing R] (I : Ideal R)
    {A : Type*} [CommRing A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    [Module A M] [IsScalarTower R A M] {x : A} (hx : x ∈ I • (⊤ : Submodule R A)) (m : M) :
    x • m ∈ I • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hx (fun c hc a _ => ?_) (fun u v hu hv => ?_)
  · rw [smul_assoc]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  · rw [add_smul]
    exact Submodule.add_mem _ hu hv

/-- An `f`-semilinear additive map carries `I • M₁` into `(I·C) • M₂`. -/
private theorem smul_top_of_semilinear {S C : Type*} [CommRing S] [CommRing C] (f : S →+* C)
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module C M₂]
    (ψ : M₁ →+ M₂) (hψ : ∀ (t : S) (x : M₁), ψ (t • x) = f t • ψ x) (I : Ideal S)
    {x : M₁} (hx : x ∈ I • (⊤ : Submodule S M₁)) :
    ψ x ∈ (I.map f) • (⊤ : Submodule C M₂) := by
  refine Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => ?_)
  · rw [hψ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem f hc) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hu hv

/-- **An `R`-linear map is automatically semilinear over a localization of `R`**, provided the
denominators act invertibly on the target: both sides have the same product with the image of a
denominator. -/
private theorem semilinear_of_localization {R : Type u} [CommRing R] (T : Submonoid R)
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalization T S]
    {C : Type u} [CommRing C] [Algebra R C] (f : S →+* C)
    (hf : ∀ r : R, f (algebraMap R S r) = algebraMap R C r)
    {M₁ : Type u} [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
    {M₂ : Type u} [AddCommGroup M₂] [Module R M₂] [Module C M₂] [IsScalarTower R C M₂]
    (ψ : M₁ →ₗ[R] M₂) (t : S) (x : M₁) : ψ (t • x) = f t • ψ x := by
  refine smul_of_semilinear_localization (RingHom.id R) T f hf (fun s => ?_) ψ.toAddMonoidHom
    ψ.map_smul t x
  rw [RingHom.id_apply, ← hf]
  exact (IsLocalization.map_units S s).map f

/-- **A semilinear isomorphism onto an adic completion is semilinear for the completed
scalars.** Every element of `S^∧` is congruent to one of `S` modulo `Isⁿ`, the two sides of the
semilinearity identity agree there, and they differ by an element of `Kⁿ·M₂` for every `n`, so
they agree by Hausdorffness of `M₂`. -/
private theorem semilinear_of_adicCompletion
    {S : Type u} [CommRing S] (Is : Ideal S) (hIs : Is.FG)
    {C : Type u} [CommRing C] {K : Ideal C} (f : S →+* C) (hK : Is.map f = K)
    {M₁ : Type u} [AddCommGroup M₁] [Module S M₁]
      [Module (AdicCompletion Is S) M₁] [IsScalarTower S (AdicCompletion Is S) M₁]
    {M₂ : Type u} [AddCommGroup M₂] [Module C M₂] [IsHausdorff K M₂]
      [Module (AdicCompletion K C) M₂] [IsScalarTower C (AdicCompletion K C) M₂]
    (φ : M₁ ≃+ M₂) (hφ : ∀ (t : S) (x : M₁), φ (t • x) = f t • φ x)
    (e : AdicCompletion Is S ≃+* AdicCompletion K C)
    (he : ∀ t : S, e (algebraMap S (AdicCompletion Is S) t) =
      algebraMap C (AdicCompletion K C) (f t))
    (a : AdicCompletion Is S) (m : M₁) :
    φ (a • m) = e a • φ m := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus ‹IsHausdorff K M₂› _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero]
  obtain ⟨t, ht⟩ := AdicCompletion.exists_sub_mem_map_pow Is hIs n a
  have hmem : a - algebraMap S (AdicCompletion Is S) t ∈
      (Is ^ n) • (⊤ : Submodule S (AdicCompletion Is S)) := by
    rw [Ideal.smul_top_eq_map]
    exact ht
  have hesemi : ∀ (u : S) (x : AdicCompletion Is S),
      e.toAddMonoidHom (u • x) = f u • e.toAddMonoidHom x := by
    intro u x
    have h1 : (u : S) • x = algebraMap S (AdicCompletion Is S) u * x := (Algebra.smul_def _ _)
    have h2 : f u • e x = algebraMap C (AdicCompletion K C) (f u) * e x := Algebra.smul_def _ _
    show e (u • x) = f u • e x
    rw [h1, h2, map_mul, he]
  have h1 : φ.toAddMonoidHom ((a - algebraMap S (AdicCompletion Is S) t) • m) ∈
      ((Is ^ n).map f) • (⊤ : Submodule C M₂) :=
    smul_top_of_semilinear f φ.toAddMonoidHom hφ (Is ^ n)
      (smul_mem_smul_top (Is ^ n) hmem m)
  have h2 : e.toAddMonoidHom (a - algebraMap S (AdicCompletion Is S) t) ∈
      ((Is ^ n).map f) • (⊤ : Submodule C (AdicCompletion K C)) :=
    smul_top_of_semilinear f e.toAddMonoidHom hesemi (Is ^ n) hmem
  have h3 : e (a - algebraMap S (AdicCompletion Is S) t) • φ m ∈
      ((Is ^ n).map f) • (⊤ : Submodule C M₂) :=
    smul_mem_smul_top ((Is ^ n).map f) h2 (φ m)
  have halgt : (algebraMap S (AdicCompletion Is S) t) • m = t • m := algebraMap_smul _ t m
  have halgf : algebraMap C (AdicCompletion K C) (f t) • φ m = f t • φ m :=
    algebraMap_smul _ (f t) (φ m)
  have key : φ (a • m) - e a • φ m =
      φ ((a - algebraMap S (AdicCompletion Is S) t) • m) -
        e (a - algebraMap S (AdicCompletion Is S) t) • φ m := by
    have hA : (a - algebraMap S (AdicCompletion Is S) t) • m = a • m - t • m := by
      rw [sub_smul, halgt]
    have hB : e (a - algebraMap S (AdicCompletion Is S) t) • φ m =
        e a • φ m - f t • φ m := by
      rw [map_sub, sub_smul, he, halgf]
    rw [hA, hB, map_sub, hφ]
    abel
  have hKn : (Is ^ n).map f = K ^ n := by rw [Ideal.map_pow, hK]
  rw [key, ← hKn]
  exact Submodule.sub_mem _ h1 h3

/-! ### The localized completed stalk -/

variable {X : Scheme.{u}}

/-- The localization `(𝒪_{X,y'}^∧)_𝔮` of the completed local ring at the prime `𝔮` of
`Stacks.Algebraization.completedStalkPrime` attached to a prime `q ⊇ ℐ_{y'}` of
`𝒪_{X,y'}`. -/
public abbrev completedStalkLocalization (J : X.IdealSheafData) (y' : X)
    (q : PrimeSpectrum (X.presheaf.stalk y'))
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal) :=
  Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal

/-- The adic ideal `ℐ(𝒪_{X,y'}^∧)_𝔮` of that localization, the extension of
`ℐ𝒪_{X,y'}^∧`. -/
public abbrev completedStalkLocalizationIdeal (J : X.IdealSheafData) (y' : X)
    (q : PrimeSpectrum (X.presheaf.stalk y'))
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal) :
    Ideal (completedStalkLocalization J y' q hq) :=
  (completedLocalIdeal J y').map
    (algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq))

/-- The localization `(ℱ_{y'}^∧)_𝔮` of the completed stalk at that prime, a finite module over
`Stacks.Algebraization.completedStalkLocalization`. -/
public abbrev completedStalkLocalizedModule (J : X.IdealSheafData)
    (G : Stacks.Coherent.CoherentAdicSystems J) (y' : X)
    (q : PrimeSpectrum (X.presheaf.stalk y'))
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal) :=
  LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl (completedStalk J G y')

/-! ### The reduction of Tag 0EJA to the base change of the completed stalk -/

/-- **[Stacks, Tag 0EHW] along an immediate specialization, granted the two base changes.**

The final step of [Stacks, Tag 0EJA], given an isomorphism `e` identifying `𝒪_{X,y}^∧` with the
`ℐ`-adic completion of `(𝒪_{X,y'}^∧)_𝔮` compatibly with the specialization map (`he`), and an
additive isomorphism `φ` from `ℱ_y^∧` onto the `ℐ`-adic completion of `(ℱ_{y'}^∧)_𝔮`, semilinear
over `e` (`hφ`).

The ring `(𝒪_{X,y'}^∧)_𝔮` is universally catenary with Cohen--Macaulay formal fibres because
`𝒪_{X,y'}^∧` is, so the second display of [Stacks, Tag 0EHW] applies to it; the depth at
`𝔭 ∩ (𝒪_{X,y'}^∧)_𝔮` is the depth at `𝔭 ∩ 𝒪_{X,y'}^∧`, and `dim(𝒪_{X,y'}^∧/𝔭 ∩ 𝒪_{X,y'}^∧)`
splits along `𝔮`, where `dim(𝒪_{X,y'}^∧/𝔮) = dim(𝒪_{X,y'}/q) = 1`. -/
private theorem completedStalkDepth_add_ringKrullDim_succ_eq_of_specializes_aux
    [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (G : Stacks.Coherent.CoherentAdicSystems J) {y y' : X} (h : y ⤳ y')
    (q : PrimeSpectrum (X.presheaf.stalk y'))
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal)
    (hJmax : IdealSheafData.stalk J y' ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y'))
    (hcat : Ring.IsUniversallyCatenary (completedLocalRing J y'))
    (hCM : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
      (completedLocalRing J y'))
    (hone : ringKrullDim (X.presheaf.stalk y' ⧸ q.asIdeal) = 1)
    (p : PrimeSpectrum (completedLocalRing J y))
    (e : completedLocalRing J y ≃+*
      AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
        (completedStalkLocalization J y' q hq))
    (he : ∀ b : completedLocalRing J y',
      e (completedLocalRingSpecializes J h b) =
        algebraMap (completedStalkLocalization J y' q hq)
          (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
            (completedStalkLocalization J y' q hq))
          (algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq) b))
    (φ : completedStalk J G y ≃+
      AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
        (completedStalkLocalizedModule J G y' q hq))
    (hφ : ∀ (a : completedLocalRing J y) (m : completedStalk J G y),
      φ (a • m) = e a • φ m) :
    (completedStalkDepth J G y p : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing J y ⧸ p.asIdeal) + 1 =
      (completedStalkDepth J G y'
          (PrimeSpectrum.comap (completedLocalRingSpecializes J h) p) : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing J y' ⧸
          (PrimeSpectrum.comap (completedLocalRingSpecializes J h) p).asIdeal) := by
  have _ : IsNoetherianRing (completedLocalRing J y') :=
    AdicCompletion.isNoetherianRing (IdealSheafData.stalk J y')
  have _ : IsLocalRing (completedLocalRing J y') :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal
      (IdealSheafData.stalk J y') hJmax
  have _ : Module.Finite (completedLocalRing J y') (completedStalk J G y') :=
    finite_completedStalk J G y'
  have hdim : ringKrullDim (completedLocalRing J y' ⧸
      (completedStalkPrime J y' q hq).asIdeal) = 1 := by
    rw [ringKrullDim_quotient_completedStalkPrime, hone]
  have hKmax : completedStalkLocalizationIdeal J y' q hq ≤
      maximalIdeal (completedStalkLocalization J y' q hq) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal
      (I := (completedStalkPrime J y' q hq).asIdeal)]
    exact Ideal.map_mono (completedLocalIdeal_le_completedStalkPrime J y' q hq)
  exact depth_add_ringKrullDim_succ_eq_of_adicCompletion_localization hcat hCM
    (completedStalkPrime J y' q hq).asIdeal hdim (completedStalk J G y')
    (completedLocalRingSpecializes J h) hKmax e he φ hφ p.asIdeal




/-! ### The completed local ring at a generalization, over the completed local ring -/

/-- The specialization map of completed local rings, evaluated on the image of a stalk element. -/
private theorem completedLocalRingSpecializes_algebraMap (J : X.IdealSheafData) {y y' : X}
    (h : y ⤳ y') (r : X.presheaf.stalk y') :
    completedLocalRingSpecializes J h
        (algebraMap (X.presheaf.stalk y') (completedLocalRing J y') r) =
      algebraMap (X.presheaf.stalk y) (completedLocalRing J y)
        ((X.presheaf.stalkSpecializes h).hom r) :=
  DFunLike.congr_fun (completedLocalRingSpecializes_comp_algebraMap J h) r

/-- **`𝒪_{X,y}^∧` is the `ℐ`-adic completion of `(𝒪_{X,y'}^∧)_𝔮`, compatibly with the
specialization map of completed local rings.**

`Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_of_specializes` identifies
`𝒪_{X,y}^∧` with that completion as an algebra over the *uncompleted* local ring `𝒪_{X,y'}`; what
a statement about the primes of the two rings needs is the compatibility over `𝒪_{X,y'}^∧`, which
is the ring the localization is formed from. The upgrade is automatic: the target is
`ℐ_{y'}`-adically Hausdorff, so two ring maps out of `𝒪_{X,y'}^∧` into it agree as soon as they
agree on `𝒪_{X,y'}` (`Stacks.Algebraization.ringHom_eq_of_comp_algebraMap_eq`), and the
isomorphism composed with the specialization map agrees there with the structure map. -/
public theorem exists_ringEquiv_completedLocalRing_of_specializes [IsLocallyNoetherian X]
    (J : X.IdealSheafData) {y y' : X} (h : y ⤳ y')
    (q : PrimeSpectrum (X.presheaf.stalk y')) (hqy : X.fromSpecStalk y' q = y)
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal) :
    ∃ e : completedLocalRing J y ≃+*
        AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
          (completedStalkLocalization J y' q hq),
      ∀ b : completedLocalRing J y',
        e (completedLocalRingSpecializes J h b) =
          algebraMap (completedStalkLocalization J y' q hq)
            (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
              (completedStalkLocalization J y' q hq))
            (algebraMap (completedLocalRing J y')
              (completedStalkLocalization J y' q hq) b) := by
  have hfg : (IdealSheafData.stalk J y').FG := Ideal.fg_of_isNoetherianRing _
  let : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let : Algebra (X.presheaf.stalk y') (completedStalkLocalization J y' q hq) :=
    ((algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq)).comp
      (algebraMap (X.presheaf.stalk y') (completedLocalRing J y'))).toAlgebra
  obtain ⟨e₀⟩ := nonempty_algEquiv_completedLocalRing_of_specializes J h hfg q hqy hq
    (completedStalkLocalization J y' q hq)
  have hKeq : (IdealSheafData.stalk J y').map
      (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq)) =
      completedStalkLocalizationIdeal J y' q hq := by
    rw [show completedStalkLocalizationIdeal J y' q hq =
        ((IdealSheafData.stalk J y').map
            (algebraMap (X.presheaf.stalk y') (completedLocalRing J y'))).map
          (algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq)) from rfl,
      Ideal.map_map]
    rfl
  refine ⟨e₀.toRingEquiv.trans (adicCompletionCongr hKeq), fun b => ?_⟩
  -- the structure map `𝒪_{X,y'} ⟶ ((𝒪_{X,y'}^∧)_𝔮)^∧` the two maps are compared through
  set ρ : (X.presheaf.stalk y') →+*
      AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
        (completedStalkLocalization J y' q hq) :=
    (algebraMap (completedStalkLocalization J y' q hq)
        (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
          (completedStalkLocalization J y' q hq))).comp
      ((algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq)).comp
        (algebraMap (X.presheaf.stalk y') (completedLocalRing J y'))) with hρ
  have hmapn : ∀ n : ℕ, ((IdealSheafData.stalk J y') ^ n).map ρ =
      ((completedStalkLocalizationIdeal J y' q hq) ^ n).map
        (algebraMap (completedStalkLocalization J y' q hq)
          (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
            (completedStalkLocalization J y' q hq))) := by
    intro n
    rw [Ideal.map_pow, Ideal.map_pow, hρ,
      show completedStalkLocalizationIdeal J y' q hq =
        ((IdealSheafData.stalk J y').map
            (algebraMap (X.presheaf.stalk y') (completedLocalRing J y'))).map
          (algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq)) from rfl,
      Ideal.map_map, Ideal.map_map]
  have hcomplete : IsHausdorff (completedStalkLocalizationIdeal J y' q hq)
      (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
        (completedStalkLocalization J y' q hq)) :=
    (AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing _)).toIsHausdorff
  have hsep : ∀ t : AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
      (completedStalkLocalization J y' q hq),
      (∀ n : ℕ, t ∈ ((IdealSheafData.stalk J y') ^ n).map ρ) → t = 0 := by
    intro t ht
    refine hcomplete.haus t fun n => ?_
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have hn := ht n
    rwa [hmapn n] at hn
  have key := ringHom_eq_of_comp_algebraMap_eq (IdealSheafData.stalk J y') hfg ρ hsep
    ((adicCompletionCongr hKeq).toRingHom.comp
      (e₀.toRingEquiv.toRingHom.comp (completedLocalRingSpecializes J h)))
    ((algebraMap (completedStalkLocalization J y' q hq)
        (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
          (completedStalkLocalization J y' q hq))).comp
      (algebraMap (completedLocalRing J y') (completedStalkLocalization J y' q hq)))
    (RingHom.ext fun r => ?_) (RingHom.comp_assoc _ _ _)
  · exact DFunLike.congr_fun key b
  · -- the isomorphism composed with the specialization map, on `𝒪_{X,y'}`
    have h1 : completedLocalRingSpecializes J h
          (algebraMap (X.presheaf.stalk y') (completedLocalRing J y') r) =
        algebraMap (X.presheaf.stalk y') (completedLocalRing J y) r := by
      exact completedLocalRingSpecializes_algebraMap J h r
    have h2 : e₀.toRingEquiv (algebraMap (X.presheaf.stalk y') (completedLocalRing J y) r) =
        algebraMap (X.presheaf.stalk y')
          (AdicCompletion ((IdealSheafData.stalk J y').map
            (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq)))
            (completedStalkLocalization J y' q hq)) r := e₀.commutes r
    have h3 : algebraMap (X.presheaf.stalk y')
          (AdicCompletion ((IdealSheafData.stalk J y').map
            (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq)))
            (completedStalkLocalization J y' q hq)) r =
        algebraMap (completedStalkLocalization J y' q hq) _
          (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq) r) := rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, h3,
      adicCompletionCongr_algebraMap]
    rfl




/-! ### Tag 0EHW along a specialization -/

/-- **[Stacks, Tag 0EHW] along a specialization of points**, the final step in the proof of
[Stacks, Tag 0EJA].

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals, `(ℱ_n)` a coherent
`ℐ`-adic system and `y ⤳ y'` a specialization of points of `X` coming from a prime `q` of
`𝒪_{X,y'}` which contains `ℐ_{y'}` and satisfies `dim(𝒪_{X,y'}/q) = 1`. Assume `ℐ_{y'}` lies in
the maximal ideal and that `𝒪_{X,y'}^∧` is universally catenary with Cohen--Macaulay formal
fibres -- the two consequences of a dualizing complex that the source's proof of
[Stacks, Tag 0EHW] uses, and which a dualizing complex on `𝒪_{X,y'}` supplies through
[Stacks, Tag 0BFR]. Then for every prime `𝔭` of
`𝒪_{X,y}^∧`, with `𝔭'` its contraction along the specialization map `𝒪_{X,y'}^∧ → 𝒪_{X,y}^∧`,

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + 1 = depth((ℱ_{y'}^∧)_{𝔭'}) + dim(𝒪_{X,y'}^∧/𝔭')`.

Write `𝔮` for the prime of `𝒪_{X,y'}^∧` above `q` and `C = (𝒪_{X,y'}^∧)_𝔮`. The ring `𝒪_{X,y}^∧`
is the `ℐ`-adic completion of `C` compatibly with the specialization map
(`Stacks.Algebraization.exists_ringEquiv_completedLocalRing_of_specializes`) and `ℱ_y^∧` is the
`ℐ`-adic completion of `(ℱ_{y'}^∧)_𝔮`
(`Stacks.Algebraization.nonempty_linearEquiv_completedStalk_of_specializes`); the latter is only
`𝒪_{X,y'}`-linear, and it is upgraded to semilinearity over the former by
`Stacks.Algebraization.semilinear_of_localization` and
`Stacks.Algebraization.semilinear_of_adicCompletion`. The second display of [Stacks, Tag 0EHW]
for `C`, which inherits both hypotheses from `𝒪_{X,y'}^∧`, then gives the identity after the
depth at `𝔭 ∩ C` is identified with the depth at `𝔭'` and `dim(C/𝔭 ∩ C) + 1` with
`dim(𝒪_{X,y'}^∧/𝔭')`, the latter because `𝒪_{X,y'}^∧` is universally catenary and
`dim(𝒪_{X,y'}^∧/𝔮) = dim(𝒪_{X,y'}/q) = 1`. -/
@[stacks 0EHW "second display, along a specialization of points"]
public theorem completedStalkDepth_add_ringKrullDim_succ_eq_of_specializes
    [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (G : Stacks.Coherent.CoherentAdicSystems J) {y y' : X} (h : y ⤳ y')
    (q : PrimeSpectrum (X.presheaf.stalk y')) (hqy : X.fromSpecStalk y' q = y)
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal)
    (hJmax : IdealSheafData.stalk J y' ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y'))
    (hcat : Ring.IsUniversallyCatenary (completedLocalRing J y'))
    (hCM : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
      (completedLocalRing J y'))
    (hone : ringKrullDim (X.presheaf.stalk y' ⧸ q.asIdeal) = 1)
    (p : PrimeSpectrum (completedLocalRing J y)) :
    (completedStalkDepth J G y p : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing J y ⧸ p.asIdeal) + 1 =
      (completedStalkDepth J G y'
          (PrimeSpectrum.comap (completedLocalRingSpecializes J h) p) : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing J y' ⧸
          (PrimeSpectrum.comap (completedLocalRingSpecializes J h) p).asIdeal) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_completedLocalRing_of_specializes J h q hqy hq
  let : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let : Module (X.presheaf.stalk y') (formalStalk G y) :=
    Module.compHom _ (X.presheaf.stalkSpecializes h).hom
  have : IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y) (formalStalk G y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ψ⟩ := nonempty_linearEquiv_completedStalk_of_specializes J G h q hqy hq
  have : IsLocalization q.asIdeal.primeCompl (X.presheaf.stalk y) :=
    Chow.isLocalization_stalk_of_specializes h q hqy
  -- the denominators of `𝒪_{X,y}` become invertible in `C = (𝒪_{X,y'}^∧)_𝔮`
  have hunits : ∀ s : q.asIdeal.primeCompl,
      IsUnit (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq)
        (s : X.presheaf.stalk y')) := by
    intro s
    have hs : algebraMap (X.presheaf.stalk y') (completedLocalRing J y') (s : _) ∈
        (completedStalkPrime J y' q hq).asIdeal.primeCompl := by
      intro hmem
      have h1 : (s : X.presheaf.stalk y') ∈
          (completedStalkPrime J y' q hq).asIdeal.comap
            (algebraMap (X.presheaf.stalk y') (completedLocalRing J y')) := hmem
      rw [comap_completedStalkPrime J y' q hq] at h1
      exact (s.2 : (s : X.presheaf.stalk y') ∉ q.asIdeal) h1
    have hu := IsLocalization.map_units (M := (completedStalkPrime J y' q hq).asIdeal.primeCompl)
      (completedStalkLocalization J y' q hq) ⟨_, hs⟩
    rwa [← IsScalarTower.algebraMap_apply (X.presheaf.stalk y') (completedLocalRing J y')
      (completedStalkLocalization J y' q hq) (s : _)] at hu
  -- the induced map `𝒪_{X,y} ⟶ C`
  set f : (X.presheaf.stalk y) →+* completedStalkLocalization J y' q hq :=
    IsLocalization.lift (M := q.asIdeal.primeCompl) hunits with hfdef
  have hf : ∀ r : X.presheaf.stalk y',
      f (algebraMap (X.presheaf.stalk y') (X.presheaf.stalk y) r) =
        algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq) r := fun r =>
    IsLocalization.lift_eq hunits r
  -- the two spellings of the adic ideal of `C`
  have hKRB : (IdealSheafData.stalk J y').map
      (algebraMap (X.presheaf.stalk y') (completedStalkLocalization J y' q hq)) =
      completedStalkLocalizationIdeal J y' q hq := by
    rw [completedStalkLocalizationIdeal, completedLocalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq (X.presheaf.stalk y') (completedLocalRing J y')
        (completedStalkLocalization J y' q hq)]
  -- the module isomorphism, in the spelling the reduction wants
  set φ : completedStalk J G y ≃+
      AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
        (completedStalkLocalizedModule J G y' q hq) :=
    ψ.toAddEquiv.trans (adicCompletionModuleCongr hKRB
      (completedStalkLocalizedModule J G y' q hq)) with hφdef
  have hφS : ∀ (t : X.presheaf.stalk y) (x : completedStalk J G y),
      φ (t • x) = f t • φ x := by
    intro t x
    have hψ := semilinear_of_localization q.asIdeal.primeCompl f hf ψ.toLinearMap t x
    rw [hφdef]
    show adicCompletionModuleCongr hKRB _ (ψ (t • x)) =
      f t • adicCompletionModuleCongr hKRB _ (ψ x)
    rw [show ψ (t • x) = f t • ψ x from hψ, adicCompletionModuleCongr_smul]
  -- the ring isomorphism is compatible with `𝒪_{X,y} ⟶ C` as well
  have heS : ∀ t : X.presheaf.stalk y,
      e (algebraMap (X.presheaf.stalk y) (completedLocalRing J y) t) =
        algebraMap (completedStalkLocalization J y' q hq) _ (f t) := by
    have hext : ((e : completedLocalRing J y →+* _).comp
          (algebraMap (X.presheaf.stalk y) (completedLocalRing J y))) =
        (algebraMap (completedStalkLocalization J y' q hq)
          (AdicCompletion (completedStalkLocalizationIdeal J y' q hq)
            (completedStalkLocalization J y' q hq))).comp f := by
      refine IsLocalization.ringHom_ext q.asIdeal.primeCompl ?_
      refine RingHom.ext fun r => ?_
      have hbase : algebraMap (X.presheaf.stalk y) (completedLocalRing J y)
            (algebraMap (X.presheaf.stalk y') (X.presheaf.stalk y) r) =
          completedLocalRingSpecializes J h
            (algebraMap (X.presheaf.stalk y') (completedLocalRing J y') r) := by
        exact completedLocalRingSpecializes_algebraMap J h r
      simp only [RingHom.comp_apply, RingHom.coe_coe, hbase, he, hf]
      rw [← IsScalarTower.algebraMap_apply (X.presheaf.stalk y') (completedLocalRing J y')
        (completedStalkLocalization J y' q hq) r]
    intro t
    exact DFunLike.congr_fun hext t
  -- the adic ideal of `𝒪_{X,y}` extends to that of `C`
  have hKf : (IdealSheafData.stalk J y).map f = completedStalkLocalizationIdeal J y' q hq := by
    rw [← hKRB, Chow.idealStalk_eq_map_stalkSpecializes J h, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => hf r
  have hφ : ∀ (a : completedLocalRing J y) (m : completedStalk J G y),
      φ (a • m) = e a • φ m := fun a m =>
    semilinear_of_adicCompletion (IdealSheafData.stalk J y) (Ideal.fg_of_isNoetherianRing _) f
      hKf φ hφS e heS a m
  exact completedStalkDepth_add_ringKrullDim_succ_eq_of_specializes_aux J G h q hq hJmax hcat
    hCM hone p e he φ hφ

end Stacks.Algebraization

end
