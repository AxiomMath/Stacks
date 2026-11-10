module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StalkIsoSpreadout
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SectionsUniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FreeStalk
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricallyIrreducibleFibres
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap

/-!
# Universal injectivity of the free map of the Raynaud–Gruson induction

The induction step of [Stacks, Tag 0815] chooses, on an affine chart, a map
`α : 𝒪_X^{⊕ r} ⟶ ℱ` from a finite free module which is an isomorphism on an open `W ⊆ X`
surjecting onto the base. This file proves that the map of global sections of such an `α` is
**universally injective** over the ring of the base.

That is the conjunction of two tags of the source. [Stacks, Tag 05IA] says that flatness of `ℱ`
over the base at the generic point of a fibre makes the localization of `α` at the corresponding
prime of the base universally injective — and `α` *is* an isomorphism near those generic points,
because `W` surjects onto the base, so `ℱ` is finite free and hence flat there.
[Stacks, Tag 05CL] assembles those local statements into one global one.

## Main results

* `AlgebraicGeometry.universallyInjective_schemeApp_of_isIso_on_open`: the map of global sections
  of `α` is universally injective over `Γ(S, ⊤)`.

## Implementation notes

The form of [Stacks, Tag 05IA] used here is
`Module.universallyInjective_localizedMap_of_flat_localizedModule`, which is indexed by a prime
`q` of the chart ring and asks for flatness at `q`. The induction supplies flatness only at the
generic points of the fibres, so it is applied at `q = 𝔯·Γ(X, ⊤)`, the generic point of the fibre
over `𝔯`; `AlgebraicGeometry.universallyInjective_localizedMap_atPrime_of_flat_generic` is that
reading, with the prime of the base named separately so that the identification
`(𝔯·Γ(X, ⊤)) ∩ Γ(S, ⊤) = 𝔯` can be substituted.

The assembly of [Stacks, Tag 05CL] runs over the primes of the *chart* rather than of the base:
`Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤)` need not be surjective, and at a prime of the base outside its
image the fibre is the zero ring, which is never geometrically integral, so Stacks 05IA has no
input there. `AlgebraicGeometry.universallyInjective_of_forall_primeUnder_localized` therefore
asks for the local statement only at the primes `q ∩ Γ(S, ⊤)`, which are exactly the primes that
are hit, and checks injectivity after tensoring at the maximal ideals of the chart ring.

The geometric integrality that [Stacks, Tag 05IA] needs is the instance
`GeometricallyIntegral (Spec.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)))`;
`AlgebraicGeometry.geometricallyIntegral_specMap_appTop` produces it from
`GeometricallyIntegral f`, the two morphisms being identified by
`AlgebraicGeometry.Scheme.isoSpec`.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
* [Stacks Project, Tag 05CM](https://stacks.math.columbia.edu/tag/05CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AssociatedPointsMono
open Stacks.AlgebraicGeometry.AssociatedPointPrime

universe u

namespace AlgebraicGeometry

/-! ### Universal injectivity of the free map over the base: Stacks 05IA and 05CL -/

/-- An element of a localized module vanishes exactly when its numerator is annihilated by some
element of the localizing submonoid. -/
private theorem localizedModule_mk_eq_zero_iff' {R A : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] {T : Submonoid R} (a : A) (s : T) :
    LocalizedModule.mk a s = 0 ↔ ∃ t : T, (t : R) • a = 0 := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
  simp

/-- **Stacks 05IA, the implication (1) implies (3), at a prime of the base.** Let `R → S` be flat
and of finite presentation with geometrically integral fibres, let `r` be a prime of `R` and let
`p` be a prime of `S` lying over it. If `a : Sⁿ → N` becomes injective over the residue field of
the generic point `rS` of the fibre over `r`, and `N_p` is flat over `R`, then `a` localized at
`r` is universally injective as a map of `R`-modules.

This is the library's `Module.universallyInjective_localizedMap_of_flat_localizedModule`, with the
prime of `R` named separately from the prime of `S` above it, so that the application below may
take for `p` the generic point `rS` itself — which is where the flattening induction has
arranged flatness. -/
private theorem universallyInjective_localizedMap_atPrime_of_flat_generic
    {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime] (p : Ideal S) [p.IsPrime] (hpr : p.under R = r)
    {n : ℕ} (a : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Injective (a.rTensor (Ideal.map (algebraMap R S) r).ResidueField))
    (hflat : Module.Flat R (LocalizedModule p.primeCompl N))
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective (((LocalizedModule.map r.primeCompl
      (a.restrictScalars R)).restrictScalars R).rTensor Q) := by
  subst hpr
  exact Module.universallyInjective_localizedMap_of_flat_localizedModule R S p N n a halpha
    hflat Q

/-- The ideal `q ∩ R` extended to `S` and contracted back is `q ∩ R`, as `q` lies over it. -/
private theorem comap_map_under_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    ((q.under R).map (algebraMap R S)).comap (algebraMap R S) = q.under R := by
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  exact ⟨q, inferInstance, rfl⟩

/-- **Stacks 05IA at the prime of `R` below a prime of `S`.** For `q` a prime of `S` and
`r = q ∩ R`, the generic point `rS` of the fibre over `r` is a prime of `S` lying over `r` —
`q` itself witnesses that `r` is in the image of `Spec S` — so flatness of `N` at `rS` and
bijectivity of `a` over `κ(rS)` make `a` localized at `r` universally injective over `R`. -/
private theorem universallyInjective_localizedMap_under_of_flat_generic
    {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    (q : Ideal S) [q.IsPrime] {n : ℕ} (a : (Fin n → S) →ₗ[S] N)
    (hbij : ∀ hp : ((q.under R).map (algebraMap R S)).IsPrime,
      Function.Bijective
        (a.rTensor (@Ideal.ResidueField S _ ((q.under R).map (algebraMap R S)) hp)))
    (hflat : ∀ hp : ((q.under R).map (algebraMap R S)).IsPrime,
      Module.Flat R
        (LocalizedModule
          (@Ideal.primeCompl S _ ((q.under R).map (algebraMap R S)) hp) N)) :
    ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective (((LocalizedModule.map (q.under R).primeCompl
        (a.restrictScalars R)).restrictScalars R).rTensor Q) := by
  intro Q _ _
  have hp : ((q.under R).map (algebraMap R S)).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
  exact universallyInjective_localizedMap_atPrime_of_flat_generic (q.under R) _
    (comap_map_under_eq q) a
    (hbij hp).1 (hflat hp) Q

/-- **The local half of Stacks 05CL.** If the localization of `f` at a prime `p` of `R` is
universally injective as a map of `R`-modules, then `f ⊗ id_Q` is injective after localizing at
`p`, for every `R`-module `Q`. Stated separately so that the reduction to local injectivity can
be run over a different ring. -/
private theorem injective_localizedModuleMap_rTensor_of_universallyInjective_localized
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : Ideal R) [p.IsPrime]
    (h : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective (((LocalizedModule.map p.primeCompl f).restrictScalars R).rTensor Q))
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective (LocalizedModule.map p.primeCompl (f.rTensor Q)) := by
  let gM := TensorProduct.AlgebraTensorModule.rTensor R Q
    (LocalizedModule.mkLinearMap p.primeCompl M)
  let gN := TensorProduct.AlgebraTensorModule.rTensor R Q
    (LocalizedModule.mkLinearMap p.primeCompl N)
  have : IsLocalizedModule p.primeCompl gM :=
    IsLocalizedModule.rTensor R p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M)
  have : IsLocalizedModule p.primeCompl gN :=
    IsLocalizedModule.rTensor R p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl N)
  let b := TensorProduct.AlgebraTensorModule.rTensor R Q f
  let b' := TensorProduct.AlgebraTensorModule.rTensor R Q
    ((LocalizedModule.map p.primeCompl f).restrictScalars R)
  have hb' : Function.Injective b' := by
    convert h Q using 1
    rfl
  have hnat : b' ∘ₗ gM = gN ∘ₗ b := by
    dsimp [b', b, gM, gN]
    rw [← TensorProduct.AlgebraTensorModule.rTensor_comp,
      ← TensorProduct.AlgebraTensorModule.rTensor_comp]
    congr 1
    apply LinearMap.ext
    intro x
    exact LocalizedModule.map_mk p.primeCompl f x 1
  have heq : IsLocalizedModule.map p.primeCompl gM gN b = b' := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl gM gN
    rw [IsLocalizedModule.map_comp, hnat]
  have himap : Function.Injective (IsLocalizedModule.map p.primeCompl gM gN b) := by
    rw [heq]
    exact hb'
  have hcanon : Function.Injective (LocalizedModule.map p.primeCompl b) :=
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective gM gN).mp himap
  convert hcanon using 1
  rfl

/-- Localizing `S` at a prime `q` is coarser than localizing the base ring `R` at `q ∩ R`:
an `S`-linear map that is injective after localizing `R` at `q ∩ R` is injective after
localizing `S` at `q`. Indeed an element killed by some `v ∉ q ∩ R` is killed by
`algebraMap R S v ∉ q`. -/
private theorem injective_localizedModuleMap_of_injective_under
    {R S A B : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
    [AddCommGroup B] [Module R B] [Module S B] [IsScalarTower R S B]
    (b : A →ₗ[S] B) (q : Ideal S) [q.IsPrime]
    (h : Function.Injective
      (LocalizedModule.map (q.under R).primeCompl (b.restrictScalars R))) :
    Function.Injective (LocalizedModule.map q.primeCompl b) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using LocalizedModule.induction_on with
  | _ a s =>
    rw [LocalizedModule.map_mk] at hx
    obtain ⟨t, ht⟩ := (localizedModule_mk_eq_zero_iff' (b a) s).mp hx
    have hba : b ((t : S) • a) = 0 := by rwa [map_smul]
    have hzero : LocalizedModule.map (q.under R).primeCompl (b.restrictScalars R)
        (LocalizedModule.mk ((t : S) • a) 1) = 0 := by
      rw [LocalizedModule.map_mk]
      simp [hba]
    obtain ⟨v, hv⟩ := (localizedModule_mk_eq_zero_iff' ((t : S) • a)
      (1 : (q.under R).primeCompl)).mp (injective_iff_map_eq_zero _ |>.mp h _ hzero)
    refine (localizedModule_mk_eq_zero_iff' a s).mpr ⟨⟨algebraMap R S (v : R) * (t : S),
      mul_mem (fun hmem => v.2 (Ideal.mem_comap.mpr hmem)) t.2⟩, ?_⟩
    calc (algebraMap R S (v : R) * (t : S)) • a
        = algebraMap R S (v : R) • ((t : S) • a) := mul_smul _ _ _
      _ = (v : R) • ((t : S) • a) := algebraMap_smul S _ _
      _ = 0 := hv

/-- **Stacks 05CL over the base ring of a chart.** Let `R → S` be a ring map and let
`f : M → N` be a map of `S`-modules. If for every prime `q` of `S` the map `f` localized at the
prime `q ∩ R` is universally injective over `R`, then `f` is universally injective as a map of
`R`-modules.

The hypothesis is restricted to the primes of `R` in the image of `Spec S → Spec R`, which are
the only ones at which it can be had when that map is not surjective. The reduction to local
injectivity is run over `S` instead of over `R`: the map `f ⊗ id_Q` is again `S`-linear, so
injectivity may be checked at the maximal ideals of `S`, and each of those lies over a prime of
`R` covered by the hypothesis. -/
private theorem universallyInjective_of_forall_primeUnder_localized
    {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[S] N)
    (h : ∀ (q : Ideal S) [q.IsPrime],
      ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective (((LocalizedModule.map (q.under R).primeCompl
          (f.restrictScalars R)).restrictScalars R).rTensor Q)) :
    _root_.UniversallyInjective (f.restrictScalars R) := by
  intro Q _ _
  have key : Function.Injective (TensorProduct.AlgebraTensorModule.rTensor R Q f) := by
    apply injective_of_localized_maximal
    intro J hJ
    have : J.IsPrime := hJ.isPrime
    exact injective_localizedModuleMap_of_injective_under
      (TensorProduct.AlgebraTensorModule.rTensor R Q f) J
      (injective_localizedModuleMap_rTensor_of_universallyInjective_localized
        (f.restrictScalars R) (J.under R) (h J) Q)
  exact key

/-- **Stacks 05IA at every prime of the base hit by `Spec S`, assembled by Stacks 05CL.** Let
`R → S` be flat and of finite presentation with geometrically integral fibres and let `N` be a
finite `S`-module. If `a : Sⁿ → N` becomes an isomorphism over the residue field of the generic
point of every fibre, and `N` is `R`-flat at those generic points, then `a` is universally
injective as a map of `R`-modules. -/
private theorem universallyInjective_freeMap_of_flat_genericPoints
    {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    {n : ℕ} (a : (Fin n → S) →ₗ[S] N)
    (hbij : ∀ (q : Ideal S) [q.IsPrime]
      (hp : ((q.under R).map (algebraMap R S)).IsPrime),
      Function.Bijective
        (a.rTensor (@Ideal.ResidueField S _ ((q.under R).map (algebraMap R S)) hp)))
    (hflat : ∀ (q : Ideal S) [q.IsPrime]
      (hp : ((q.under R).map (algebraMap R S)).IsPrime),
      Module.Flat R (LocalizedModule
        (@Ideal.primeCompl S _ ((q.under R).map (algebraMap R S)) hp) N)) :
    _root_.UniversallyInjective (a.restrictScalars R) :=
  universallyInjective_of_forall_primeUnder_localized a fun q _ =>
    universallyInjective_localizedMap_under_of_flat_generic q a (hbij q) (hflat q)

/-! ### The global chart of an affine morphism -/

/-- **The global chart of an affine morphism of affine schemes with geometrically integral fibres
has geometrically integral fibres.** The morphism of spectra attached to the map of global
sections is isomorphic to `f` itself, through `AlgebraicGeometry.Scheme.isoSpec`. -/
private theorem geometricallyIntegral_specMap_appTop
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [GeometricallyIntegral f] :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let fSpec : Spec (.of Γ(X, ⊤)) ⟶ Spec (.of Γ(S, ⊤)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))
  let eSpec : Arrow.mk f ≅ Arrow.mk fSpec :=
    Arrow.isoMk X.isoSpec S.isoSpec (Scheme.isoSpec_hom_naturality f)
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := (@GeometricallyIntegral : MorphismProperty Scheme.{u})) eSpec).mp inferInstance

private lemma appLE_top_top' {X S : Scheme.{u}} (f : X ⟶ S)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) : f.appLE ⊤ ⊤ hUV = f.appTop :=
  Stacks.AffineAlgebraEquivalence.appLE_top_top f hUV

/-- `AlgebraicGeometry.geometricallyIntegral_specMap_appTop`, with the map of global sections
read as `Scheme.Hom.appLE`, which is the spelling the chart hypotheses below use. -/
private theorem geometricallyIntegral_specMap_appLE
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [GeometricallyIntegral f]
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) := by
  rw [appLE_top_top' f hUV]
  exact geometricallyIntegral_specMap_appTop f



/-- Specialization of the points of an affine open at two nested primes of its sections. -/
private theorem specializes_fromSpec_of_le {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : PrimeSpectrum Γ(X, U)} (h : y ≤ z) :
    hU.fromSpec y ⤳ hU.fromSpec z :=
  ((PrimeSpectrum.le_iff_specializes y z).mp h).map hU.fromSpec.continuous

/-- The prime of the point of an affine open attached to a prime of its sections. -/
private theorem primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec y, hy⟩ = y :=
  IsAffineOpen.primeIdealOf_fromSpec hU y hy

/-- **The generic point of a fibre is in every open which surjects onto the base.**  If the
prime `y` of the global chart of `X` is contained in every prime over the same prime of the
base, then the point of `X` at `y` lies in every open surjecting onto `S`. -/
private theorem fromSpec_mem_of_surjective_on_base
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens))
    (W : X.Opens) (hW : Function.Surjective (W.ι ≫ f).base)
    (y : PrimeSpectrum Γ(X, ⊤))
    (hy : ∀ z : PrimeSpectrum Γ(X, ⊤),
      z.comap (f.appLE ⊤ ⊤ hUV).hom = y.comap (f.appLE ⊤ ⊤ hUV).hom → y ≤ z) :
    (isAffineOpen_top X).fromSpec y ∈ W := by
  obtain ⟨w, hw⟩ := hW ((isAffineOpen_top S).fromSpec (y.comap (f.appLE ⊤ ⊤ hUV).hom))
  have hw' : f (W.ι w) = (isAffineOpen_top S).fromSpec
      (y.comap (f.appLE ⊤ ⊤ hUV).hom) := by
    simpa only [Scheme.Hom.comp_apply] using hw
  have hmem : (W.ι w) ∈ (⊤ : X.Opens) := trivial
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top S) ⊤
    (isAffineOpen_top X) hUV hmem
  have hbase : (isAffineOpen_top S).primeIdealOf ⟨f (W.ι w), hUV hmem⟩ =
      y.comap (f.appLE ⊤ ⊤ hUV).hom := by
    rw [hw']
    exact primeIdealOf_fromSpec (isAffineOpen_top S) _ _
  have hle := hy ((isAffineOpen_top X).primeIdealOf ⟨W.ι w, hmem⟩) (hcomap.trans hbase)
  refine (specializes_fromSpec_of_le (isAffineOpen_top X) hle).mem_open W.isOpen ?_
  rw [IsAffineOpen.fromSpec_primeIdealOf]
  exact w.2


/-- **Flatness of the localized sections at a point, from flatness over the base there.**  The
stalk is the localization of the sections over an affine open at the prime of the point, so
flatness of the module over the base at `z` is flatness of that localization over `Γ(S, V)`. -/
theorem flat_localizedModule_sections_of_isFlatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) {z : X} (hz : z ∈ U)
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F z) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Module.Flat Γ(S, V)
      (LocalizedModule (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl Γ(F, U)) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let p := (hU.primeIdealOf ⟨z, hz⟩).asIdeal
  let : Module Γ(X, U) (F.presheaf.stalk z) := sectionsStalkModule F hz
  let sF : Module Γ(S, V) (F.presheaf.stalk z) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) (F.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hloc : IsLocalizedModule p.primeCompl (germₗ F hz) := isLocalizedModule_germₗ F hU hz
  have hstalk : @Module.Flat Γ(S, V) (F.presheaf.stalk z) _ _ sF := by
    rw [isFlatOverAt_iff_flat_sectionsStalk f F hV z (hUV hz)] at hF
    rwa [show sF = _ from sectionsStalkModule_compHom_eq f F hUV hz]
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso p.primeCompl (germₗ F hz)).restrictScalars Γ(S, V))


/-- Pulling back along an isomorphism of schemes reflects isomorphisms of modules. -/
private theorem isIso_of_isIso_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y) {M N : Y.Modules}
    (β : M ⟶ N) (h : IsIso ((Scheme.Modules.pullback e.hom).map β)) : IsIso β := by
  have h2 : IsIso ((Scheme.Modules.pullback e.inv).map
      ((Scheme.Modules.pullback e.hom).map β)) :=
    have := h
    Functor.map_isIso _ _
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp e.inv e.hom ≪≫
    Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y) β).mp h2



/-- An isomorphism of pullbacks of quasi-coherent modules on an affine scheme is one for the
associated sheaves of the maps of global sections. -/
private theorem isIso_pullback_map_tilde_of_isIso {A : CommRingCat.{u}} {Z : Scheme.{u}}
    (h : Z ⟶ Spec A) {G' F' : (Spec A).Modules} [G'.IsQuasicoherent] [F'.IsQuasicoherent]
    (β : G' ⟶ F') (hβ : IsIso ((Scheme.Modules.pullback h).map β)) :
    IsIso ((Scheme.Modules.pullback h).map
      ((moduleSpecΓFunctor ⋙ tilde.functor A).map β)) := by
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app G') :=
    (inferInstance : IsIso G'.fromTildeΓ)
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app F') :=
    (inferInstance : IsIso F'.fromTildeΓ)
  have h1 : IsIso ((Scheme.Modules.pullback h).map
      (Scheme.Modules.fromTildeΓNatTrans.app G')) := Functor.map_isIso _ _
  have h2 : IsIso ((Scheme.Modules.pullback h).map
      (Scheme.Modules.fromTildeΓNatTrans.app F')) := Functor.map_isIso _ _
  have key : (Scheme.Modules.pullback h).map
        ((moduleSpecΓFunctor ⋙ tilde.functor A).map β) ≫
      (Scheme.Modules.pullback h).map (Scheme.Modules.fromTildeΓNatTrans.app F') =
      (Scheme.Modules.pullback h).map (Scheme.Modules.fromTildeΓNatTrans.app G') ≫
        (Scheme.Modules.pullback h).map β := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      Scheme.Modules.fromTildeΓNatTrans.naturality β]
    rfl
  have h3 : IsIso ((Scheme.Modules.pullback h).map
        ((moduleSpecΓFunctor ⋙ tilde.functor A).map β) ≫
      (Scheme.Modules.pullback h).map (Scheme.Modules.fromTildeΓNatTrans.app F')) := by
    rw [key]
    have := hβ
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pullback h).map (Scheme.Modules.fromTildeΓNatTrans.app F'))


/-- Right tensoring with a module takes an isomorphism of modules to a bijection. -/
private theorem bijective_rTensor_of_iso {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Bijective (LinearMap.rTensor Q e.hom.hom) :=
  (LinearEquiv.rTensor Q e.toLinearEquiv).bijective

/-- The converse of `affineTildePullback_map_isIso`: if the pullback along `Spec K ⟶ Spec R` of
the associated sheaf of a map of modules is an isomorphism, the map becomes bijective after
tensoring with `K`. -/
private theorem bijective_rTensor_of_isIso_pullback_tilde
    (R K : Type u) [CommRing R] [CommRing K] (f : R →+* K)
    (M N : ModuleCat.{u} R) (g : M ⟶ N)
    (hg : IsIso ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).map
      ((tilde.functor (CommRingCat.of R)).map g))) :
    letI : Algebra R K := f.toAlgebra
    Function.Bijective (LinearMap.rTensor K g.hom) := by
  let : Algebra R K := f.toAlgebra
  have h1 : IsIso ((tilde.functor (.of K)).map
      ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)) :=
    (NatIso.isIso_map_iff
      (AlgebraicGeometry.pullbackTildeIso (.of R) (.of K)
        (CommRingCat.ofHom f)) g).mp hg
  have h2 : IsIso ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g) := by
    have h3 : IsIso ((tilde.functor (.of K) ⋙ moduleSpecΓFunctor).map
        ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)) :=
      have := h1
      Functor.map_isIso moduleSpecΓFunctor _
    exact (NatIso.isIso_map_iff (tilde.toTildeΓNatIso (R := .of K))
      ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)).mpr h3
  rw [ConcreteCategory.isIso_iff_bijective] at h2
  change Function.Bijective (LinearMap.baseChange K g.hom) at h2
  rw [LinearMap.baseChange_eq_lTensor] at h2
  exact (LinearMap.lTensor_bij_iff_rTensor_bij K g.hom).1 h2


/-- Bijectivity over the residue field at a prime of an affine scheme, from an isomorphism of
the pullback to that residue field. -/
private theorem bijective_rTensor_residueField_of_isIso_pullback
    (B : CommRingCat.{u}) {G' F' : (Spec B).Modules}
    [G'.IsQuasicoherent] [F'.IsQuasicoherent] (β : G' ⟶ F')
    (p : Ideal B) [hp : p.IsPrime]
    (hβ : IsIso ((Scheme.Modules.pullback
      ((Spec B).fromSpecResidueField ⟨p, hp⟩)).map β)) :
    Function.Bijective (LinearMap.rTensor p.ResidueField (moduleSpecΓFunctor.map β).hom) := by
  set x : (Spec B : Scheme.{u}) := ⟨p, hp⟩
  have hβx : IsIso ((Scheme.Modules.pullback ((Spec B).fromSpecResidueField x)).map β) := hβ
  have h3 : IsIso ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B p.ResidueField)))).map β) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField] at hβx
    have hβ' := (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp
      (Spec.map (Scheme.Spec.residueFieldIso B x).inv)
      (Spec.map (CommRingCat.ofHom (algebraMap B p.ResidueField)))) β).mpr hβx
    exact isIso_of_isIso_pullback_iso
      (asIso (Spec.map (Scheme.Spec.residueFieldIso B x).inv)) _ hβ'
  have h4 : IsIso ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B p.ResidueField)))).map
      ((moduleSpecΓFunctor ⋙ tilde.functor B).map β)) :=
    isIso_pullback_map_tilde_of_isIso _ β h3
  have hm : @Algebra.toModule B p.ResidueField _ _
        (algebraMap B p.ResidueField).toAlgebra =
      (inferInstance : Module B p.ResidueField) :=
    Module.ext' _ _ fun b x => (Algebra.smul_def b x).symm
  have h5 := bijective_rTensor_of_isIso_pullback_tilde B p.ResidueField
    (algebraMap B p.ResidueField) _ _ (moduleSpecΓFunctor.map β) h4
  rwa [hm] at h5


/-- **Bijectivity over the residue field at a prime, from an isomorphism over an open.**  If
`α` becomes an isomorphism after pullback along the inclusion of an open `W` of `X`, and the
point of `X` attached to a prime `p` of the sections over an affine open `U` lies in `W`, then
the map of sections of `α` over `U` becomes bijective after tensoring with the residue field
of `p`. -/
private theorem bijective_rTensor_residueField_of_isIso_on_open
    {X : Scheme.{u}} {G F : X.Modules} [G.IsQuasicoherent] [F.IsQuasicoherent]
    (α : G ⟶ F) {U : X.Opens} (hU : IsAffineOpen U)
    (W : X.Opens) (hαW : IsIso ((Scheme.Modules.pullback W.ι).map α))
    (p : Ideal Γ(X, U)) [hp : p.IsPrime] (hpW : hU.fromSpec ⟨p, hp⟩ ∈ W) :
    Function.Bijective (LinearMap.rTensor p.ResidueField (schemeAppLinearMap α U)) := by
  set x : (Spec Γ(X, U) : Scheme.{u}) := ⟨p, hp⟩ with hxdef
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hk : IsIso ((Scheme.Modules.pullback
      ((Spec Γ(X, U)).fromSpecResidueField x ≫ hU.fromSpec)).map α) := by
    refine isIso_pullback_map_of_range_le α W hαW _ ?_
    rintro _ ⟨y, rfl⟩
    change hU.fromSpec (((Spec Γ(X, U)).fromSpecResidueField x) y) ∈ W
    rw [Scheme.fromSpecResidueField_apply]
    exact hpW
  have h2 : IsIso ((Scheme.Modules.pullback
      ((Spec Γ(X, U)).fromSpecResidueField x)).map
      ((Scheme.Modules.pullback hU.fromSpec).map α)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp
      ((Spec Γ(X, U)).fromSpecResidueField x) hU.fromSpec) α).mpr hk
  have h5 := bijective_rTensor_residueField_of_isIso_pullback Γ(X, U)
    ((Scheme.Modules.pullback hU.fromSpec).map α) p h2
  have hrw : ModuleCat.ofHom (schemeAppLinearMap α U) =
      (pullbackFromSpecSectionsIso G U hU).inv ≫
        moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α) ≫
        (pullbackFromSpecSectionsIso F U hU).hom := by
    rw [pullbackFromSpecSectionsIso_naturality α U hU, Iso.inv_hom_id_assoc]
  have hcomp : (schemeAppLinearMap α U) =
      ((pullbackFromSpecSectionsIso F U hU).hom.hom.comp
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α)).hom).comp
        (pullbackFromSpecSectionsIso G U hU).inv.hom := by
    have h := congrArg ModuleCat.Hom.hom hrw
    simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_assoc] using h
  rw [hcomp, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
  simp only [LinearMap.coe_comp]
  refine Function.Bijective.comp (Function.Bijective.comp ?_ h5) ?_
  · exact bijective_rTensor_of_iso (pullbackFromSpecSectionsIso F U hU) _
  · exact bijective_rTensor_of_iso (pullbackFromSpecSectionsIso G U hU).symm _


/-- The sections over an affine open of a finite coproduct of copies of the structure sheaf
are the finite free module of that rank over the sections of the structure sheaf. -/
private noncomputable def freeSectionsIso {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (r : ℕ) :
    ModuleCat.of Γ(X, U)
        Γ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules), U) ≅
      ModuleCat.of Γ(X, U) (Fin r → Γ(X, U)) := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let P := Scheme.Modules.pullback hU.fromSpec
  let eu : P.obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso hU.fromSpec
  let ef : P.obj (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) ≅
      ∐ fun _ : Fin r => SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf :=
    PreservesCoproduct.iso P _ ≪≫ Sigma.mapIso fun _ => eu
  exact (pullbackFromSpecSectionsIso _ U hU).symm ≪≫
    moduleSpecΓFunctor.mapIso (ef ≪≫ freeTildeIso Γ(X, U) r) ≪≫
    (tilde.toTildeΓNatIso.app (ModuleCat.of Γ(X, U) (Fin r → Γ(X, U)))).symm


/-- A module which a map from a finite free module turns into an isomorphism on an open is
flat over the base on that open: its stalk there is isomorphic to the free stalk of the
coproduct, hence free, and a free stalk is flat over a flat base. -/
private theorem isFlatOverAt_pullback_of_isIso_freeMap
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] {F : X.Modules} {r : ℕ}
    (α : (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ F)
    (W : X.Opens) (hαW : IsIso ((Scheme.Modules.pullback W.ι).map α)) (w : W.toScheme) :
    AlgebraicGeometry.IsFlatOverAt (W.ι ≫ f).toLRSHom.toShHom
      ((Scheme.Modules.pullback W.ι).obj F) w := by
  have hiso : IsIso ((Scheme.Modules.pullback W.ι).map α) := hαW
  have hG : Module.Free (W.toScheme.presheaf.stalk w)
      (((Scheme.Modules.pullback W.ι).obj
        (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules)).presheaf.stalk w) :=
    Stacks.StalkFreeBridge.free_stalk_pullback W.ι
      (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) w
      (Stacks.StalkFreeBridge.free_stalk_coproductUnit r (W.ι w))
  exact isFlatOverAt_of_free_stalk (W.ι ≫ f) ((Scheme.Modules.pullback W.ι).obj F) w
    (Module.Free.of_equiv
      (schemeStalkLinearEquiv (@asIso _ _ _ _ ((Scheme.Modules.pullback W.ι).map α) hiso) w))

/-- A module isomorphic to a finite free module on an open is flat over a flat base at every
point of that open. -/
private theorem isFlatOverAt_of_isIso_freeMap_on_open
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] {F : X.Modules} {r : ℕ}
    (α : (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ F)
    (W : X.Opens) (hαW : IsIso ((Scheme.Modules.pullback W.ι).map α))
    (z : X) (hz : z ∈ W) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F z :=
  (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt W.ι f F ⟨z, hz⟩
      ((Flat.iff_flat_stalkMap W.ι).mp inferInstance ⟨z, hz⟩)).mpr
    (isFlatOverAt_pullback_of_isIso_freeMap f α W hαW ⟨z, hz⟩)

/-- A finite coproduct of copies of the structure sheaf is of finite type. -/
instance isFiniteType_coproductUnit {X : Scheme.{u}} (r : ℕ) :
    (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.StalkFreeBridge.coproductUnitIsoFree (X := X) r).symm

/-- A finite coproduct of copies of the structure sheaf is quasi-coherent. -/
instance isQuasicoherent_coproductUnit {X : Scheme.{u}} (r : ℕ) :
    (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := by
  let e : (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) : X.Modules) :=
    Sigma.whiskerEquiv (f := fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf)
      (g := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit X.ringCatSheaf)
      Equiv.ulift.symm fun _ ↦ Iso.refl _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm inferInstance

/-- **Universal injectivity of the sections of a generically invertible free map.**  Let
`f : X ⟶ S` be a flat morphism, locally of finite presentation, of affine schemes with
geometrically integral fibres, let `F` be a quasi-coherent module of finite type on `X`, and let
`α : 𝒪_X^r ⟶ F` be a morphism which is an isomorphism over an open `W` surjecting onto `S`.
Then the map of global sections of `α` is universally injective over `Γ(S, ⊤)`.

This is the conjunction of Stacks 05IA — flatness of `F` at the generic point of every fibre
makes the localization of `α` universally injective there — and Stacks 05CL, which assembles
those local statements. -/
theorem universallyInjective_schemeApp_of_isIso_on_open
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    {F : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    {r : ℕ} (α : (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ F)
    (W : X.Opens) (hWsurj : Function.Surjective (W.ι ≫ f).base)
    (hαW : IsIso ((Scheme.Modules.pullback W.ι).map α))
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
    letI : Module Γ(S, ⊤)
        Γ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
      Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
    letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤)
        Γ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    _root_.UniversallyInjective ((schemeAppLinearMap α ⊤).restrictScalars Γ(S, ⊤)) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
  let : Module Γ(S, ⊤)
      Γ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
    Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
  let : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤)
      Γ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfp : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    f.finitePresentation_appLE (isAffineOpen_top S) (isAffineOpen_top X) hUV
  have hflatalg : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    f.flat_appLE (isAffineOpen_top S) (isAffineOpen_top X) hUV
  have hfin : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
    finite_sections_of_isAffineOpen F ⊤ (isAffineOpen_top X)
  set e := freeSectionsIso (X := X) ⊤ (isAffineOpen_top X) r
  set a : (Fin r → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
    (schemeAppLinearMap α ⊤).comp e.inv.hom with ha
  have hmem : ∀ (q : Ideal Γ(X, ⊤)) [q.IsPrime]
      (hp : ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))).IsPrime),
      (isAffineOpen_top X).fromSpec
        ⟨(q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤)), hp⟩ ∈ W := by
    intro q hq hp
    refine fromSpec_mem_of_surjective_on_base f hUV W hWsurj _ fun z hz => ?_
    have h1 : z.asIdeal.comap (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = q.under Γ(S, ⊤) :=
      (congrArg PrimeSpectrum.asIdeal hz).trans (comap_map_under_eq q)
    refine (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp ?_
    rw [Ideal.map_le_iff_le_comap, h1]
  have hbij : ∀ (q : Ideal Γ(X, ⊤)) [q.IsPrime]
      (hp : ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))).IsPrime),
      Function.Bijective (a.rTensor (@Ideal.ResidueField Γ(X, ⊤) _
        ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))) hp)) := by
    intro q hq hp
    have hb := bijective_rTensor_residueField_of_isIso_on_open α (isAffineOpen_top X) W hαW
      ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))) (hmem q hp)
    rw [ha, LinearMap.rTensor_comp]
    simp only [LinearMap.coe_comp]
    exact hb.comp (bijective_rTensor_of_iso e.symm _)
  have hflat : ∀ (q : Ideal Γ(X, ⊤)) [q.IsPrime]
      (hp : ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))).IsPrime),
      Module.Flat Γ(S, ⊤) (LocalizedModule (@Ideal.primeCompl Γ(X, ⊤) _
        ((q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤))) hp) Γ(F, ⊤)) := by
    intro q hq hp
    have hkey := flat_localizedModule_sections_of_isFlatOverAt f F (isAffineOpen_top S)
      (isAffineOpen_top X) hUV (Set.mem_univ _ : _ ∈ (⊤ : X.Opens))
      (isFlatOverAt_of_isIso_freeMap_on_open f α W hαW _ (hmem q hp))
    rwa [show (isAffineOpen_top X).primeIdealOf
        ⟨(isAffineOpen_top X).fromSpec
          ⟨(q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤)), hp⟩, Set.mem_univ _⟩ =
        ⟨(q.under Γ(S, ⊤)).map (algebraMap Γ(S, ⊤) Γ(X, ⊤)), hp⟩ from
      primeIdealOf_fromSpec (isAffineOpen_top X) _ _] at hkey
  have : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) :=
    geometricallyIntegral_specMap_appLE f hUV
  exact universallyInjective_of_linearEquiv
    ((e.toLinearEquiv.symm).restrictScalars Γ(S, ⊤))
    (LinearEquiv.refl Γ(S, ⊤) Γ(F, ⊤)) (fun _ => rfl)
    (universallyInjective_freeMap_of_flat_genericPoints a hbij hflat)
end AlgebraicGeometry

end
