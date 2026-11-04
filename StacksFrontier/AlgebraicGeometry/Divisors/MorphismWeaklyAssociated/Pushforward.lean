module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Functoriality

/-!
# Associated and weakly associated points of a direct image

Let `f : X ⟶ S` be a morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module. This
file compares the associated and the weakly associated points of the direct image `f_* F` with
those of `F`.

For an affine morphism the weakly associated points of `f_* F` are always *contained* in the
image of the weakly associated points of `F`: the comparison is affine-local, where it is the
statement that a weakly associated prime of a module over a ring extension contracts to a
weakly associated prime of the base.

Two cases give an equality. If the source is locally Noetherian then associated and weakly
associated points agree on both sides, and the image of `Ass(F)` is exactly `Ass(f_* F)`; the
nontrivial inclusion comes from the affine-local comparison of associated points with
associated primes of the modules of sections. If instead `f` is finite then no Noetherian
hypothesis is needed, because over a finite ring extension the weakly associated primes of the
base are precisely the contractions of the weakly associated primes upstairs.

## Main results

* `AlgebraicGeometry.weaklyAssociatedPoints_pushforward_subset_image`: for an affine morphism,
  `WeakAss(f_* F) ⊆ f(WeakAss(F))`.
* `AlgebraicGeometry.image_associatedPoints_eq_associatedPoints_pushforward`: for an affine
  morphism with locally Noetherian source, `f(Ass(F)) = Ass(f_* F)`.
* `AlgebraicGeometry.associatedPoints_pushforward_eq_weaklyAssociatedPoints_pushforward`: under
  the same hypotheses, `Ass(f_* F) = WeakAss(f_* F)`.
* `AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isAffineHom`: under the same
  hypotheses, `WeakAss(f_* F) = f(WeakAss(F))`.
* `AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isFinite`: for a finite
  morphism, `WeakAss(f_* F) = f(WeakAss(F))`, with no Noetherian hypothesis.

## Implementation notes

The direct image is Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward`, and the image on
points is the set-theoretic image of the underlying continuous map of the scheme morphism. The
affine-local comparisons are taken on a preimage `f ⁻¹ᵁ U` of an affine open `U` of `S`, which
is affine because `f` is affine; the algebra structure of `Γ(X, f ⁻¹ᵁ U)` over `Γ(S, U)` is the
one induced by `f.app U`.

## References

* [Stacks Project, Tag 05EX](https://stacks.math.columbia.edu/tag/05EX)
* [Stacks Project, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)
* [Stacks Project, Tag 05EZ](https://stacks.math.columbia.edu/tag/05EZ)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Contracting a prime of the sections over `f ⁻¹ᵁ U` along `f.app U` gives the prime of the
image point. -/
private theorem comap_app_primeIdealOf
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] {U : S.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ f ⁻¹ᵁ U) :
    Ideal.comap (f.app U).hom ((hU.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal =
      (hU.primeIdealOf ⟨f x, hx⟩).asIdeal := by
  have hc := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U hU _ (hU.preimage f) le_rfl hx)
  change Ideal.comap _ _ = _ at hc
  simpa only [Scheme.Hom.app_eq_appLE] using hc

/-- A weakly associated prime of the sections of `F` over the preimage of an affine open `U`
which contracts to the prime of `s ∈ U` exhibits `s` as the image of a weakly associated point
of `F`. -/
private theorem mem_image_weaklyAssociatedPoints_of_comap_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent]
    {U : S.Opens} (hU : IsAffineOpen U) {s : S} (hsU : s ∈ U) {q : Ideal Γ(X, f ⁻¹ᵁ U)}
    (hq : IsWeaklyAssociatedPrime Γ(X, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U) q)
    (hqs : Ideal.comap (f.app U).hom q = (hU.primeIdealOf ⟨s, hsU⟩).asIdeal) :
    s ∈ f '' Stacks.Divisors.weaklyAssociatedPoints F := by
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let q' : Spec Γ(X, f ⁻¹ᵁ U) := ⟨q, hq.isPrime⟩
  let x : X := hV.fromSpec q'
  have hxV : x ∈ f ⁻¹ᵁ U := by
    have hx : hV.fromSpec q' ∈ Set.range hV.fromSpec := Set.mem_range_self q'
    rwa [hV.range_fromSpec] at hx
  have hqx : hV.primeIdealOf ⟨x, hxV⟩ = q' :=
    hV.fromSpec.isOpenEmbedding.injective (by rw [hV.fromSpec_primeIdealOf])
  refine ⟨x, ?_, ?_⟩
  · rwa [Stacks.Divisors.mem_weaklyAssociatedPoints_iff,
      ← isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F _ hV x hxV, hqx]
  · have hc := comap_app_primeIdealOf f hU hxV
    rw [hqx] at hc
    have he : hU.primeIdealOf ⟨f x, hxV⟩ = hU.primeIdealOf ⟨s, hsU⟩ :=
      PrimeSpectrum.ext (hc.symm.trans hqs)
    exact congrArg Subtype.val
      ((CategoryTheory.ConcreteCategory.bijective_of_isIso hU.isoSpec.hom.base).injective he)

/-- **Stacks Project, Tag 05EX.** Every weakly associated point of the pushforward along an
affine morphism is the image of a weakly associated point of the original module. -/
@[stacks 05EX]
theorem weaklyAssociatedPoints_pushforward_subset_image
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Divisors.weaklyAssociatedPoints ((Scheme.Modules.pushforward f).obj F) ⊆
      f '' Stacks.Divisors.weaklyAssociatedPoints F := by
  intro s hs
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  let V : X.Opens := f ⁻¹ᵁ U
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    pushforward_isQuasicoherent f F
  let : Algebra Γ(S, U) Γ(X, V) := (f.app U).hom.toAlgebra
  let : Module Γ(X, V) Γ((Scheme.Modules.pushforward f).obj F, U) := by
    show Module Γ(X, V) Γ(F, V)
    infer_instance
  let : IsScalarTower Γ(S, U) Γ(X, V)
      Γ((Scheme.Modules.pushforward f).obj F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [Stacks.Divisors.mem_weaklyAssociatedPoints_iff,
    ← isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      ((Scheme.Modules.pushforward f).obj F) U hU s hsU] at hs
  obtain ⟨q, hq, hqs⟩ := weakAss_subset_image_comap
    (algebraMap Γ(S, U) Γ(X, V)) hs
  exact mem_image_weaklyAssociatedPoints_of_comap_eq f F hU hsU hq hqs

/-- Along an affine morphism with locally Noetherian source, the image of an associated point
of `F` is an associated point of the pushforward. -/
private theorem image_associatedPoints_subset_associatedPoints_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    f '' Stacks.Divisors.associatedPoints F ⊆
      Stacks.Divisors.associatedPoints ((Scheme.Modules.pushforward f).obj F) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  have hxV : x ∈ V := by simpa [V] using hyU
  let A := Γ(S, U)
  let B := Γ(X, V)
  let N := Γ(F, V)
  let φ : A →+* B := (f.app U).hom
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra A B := φ.toAlgebra
  let : Module A N := by
    show Module A Γ((Scheme.Modules.pushforward f).obj F, U)
    infer_instance
  have hq := (isAssociatedPrime_sections_of_isAssociatedPoint_of_fg
    F V hV hxV (Ideal.FG.of_isNoetherianRing _))
      (by rwa [Stacks.Divisors.mem_associatedPoints_iff] at hx)
  let q : PrimeSpectrum B := hV.primeIdealOf ⟨x, hxV⟩
  have hq' : IsAssociatedPrimeStacks B N q.asIdeal := by
    simpa [B, N, q] using hq
  let p : PrimeSpectrum A := hU.primeIdealOf ⟨f x, hyU⟩
  have hmap' : p.asIdeal = Ideal.comap φ q.asIdeal := (comap_app_primeIdealOf f hU hxV).symm
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    pushforward_isQuasicoherent f F
  have hp : IsAssociatedPrimeStacks A
      Γ((Scheme.Modules.pushforward f).obj F, U) p.asIdeal := by
    obtain ⟨-, m, hm⟩ := hq'
    refine ⟨p.isPrime, m, ?_⟩
    show (⊥ : Submodule A N).colon (Submodule.span A {m}) = p.asIdeal
    rw [hmap']
    ext a
    rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_comap,
      ← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    rfl
  exact isAssociatedPoint_of_isAssociatedPrime_sections
    ((Scheme.Modules.pushforward f).obj F) U hU hyU hp

/-- **Stacks Project, Tag 05EY.** The associated points of a quasi-coherent pushforward along
an affine morphism are the images of the associated points on the locally Noetherian
source. -/
@[stacks 05EY "associated points"]
theorem image_associatedPoints_eq_associatedPoints_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    f '' Stacks.Divisors.associatedPoints F =
      Stacks.Divisors.associatedPoints ((Scheme.Modules.pushforward f).obj F) :=
  (image_associatedPoints_subset_associatedPoints_pushforward f F).antisymm fun _ hy ↦ by
    simpa only [← associatedPoints_eq_weaklyAssociatedPoints X F] using
      weaklyAssociatedPoints_pushforward_subset_image f F
        (associatedPoints_subset_weaklyAssociatedPoints _ hy)

/-- **Stacks Project, Tag 05EY.** The associated and weakly associated points of the pushforward
along an affine morphism agree when the source is locally Noetherian. -/
@[stacks 05EY "associated and weakly associated points of the pushforward"]
theorem associatedPoints_pushforward_eq_weaklyAssociatedPoints_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Divisors.associatedPoints ((Scheme.Modules.pushforward f).obj F) =
      Stacks.Divisors.weaklyAssociatedPoints ((Scheme.Modules.pushforward f).obj F) := by
  refine Set.Subset.antisymm
    (associatedPoints_subset_weaklyAssociatedPoints _) ?_
  rw [← image_associatedPoints_eq_associatedPoints_pushforward f F,
    associatedPoints_eq_weaklyAssociatedPoints X F]
  exact weaklyAssociatedPoints_pushforward_subset_image f F

/-- **Stacks Project, Tag 05EY.** The weakly associated points of a quasi-coherent pushforward
along an affine morphism are the images of the weakly associated points on the locally
Noetherian source. -/
@[stacks 05EY "weakly associated points"]
theorem weaklyAssociatedPoints_pushforward_eq_image_of_isAffineHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Divisors.weaklyAssociatedPoints ((Scheme.Modules.pushforward f).obj F) =
      f '' Stacks.Divisors.weaklyAssociatedPoints F := by
  rw [← associatedPoints_pushforward_eq_weaklyAssociatedPoints_pushforward f F,
    ← image_associatedPoints_eq_associatedPoints_pushforward f F,
    associatedPoints_eq_weaklyAssociatedPoints X F]

/-- **Stacks Project, Tag 05EZ.** For a finite morphism, the weakly associated points of the
pushforward of a quasi-coherent module are the images of its weakly associated points. -/
@[stacks 05EZ]
theorem weaklyAssociatedPoints_pushforward_eq_image_of_isFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] :
    Stacks.Divisors.weaklyAssociatedPoints ((Scheme.Modules.pushforward f).obj F) =
      f '' Stacks.Divisors.weaklyAssociatedPoints F := by
  ext s
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let : Algebra Γ(S, U) Γ(X, V) := (f.app U).hom.toAlgebra
  let : Module Γ(X, V) Γ((Scheme.Modules.pushforward f).obj F, U) := by
    show Module Γ(X, V) Γ(F, V)
    infer_instance
  let : IsScalarTower Γ(S, U) Γ(X, V)
      Γ((Scheme.Modules.pushforward f).obj F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hfin : Module.Finite Γ(S, U) Γ(X, V) := f.finite_app U hU
  rw [Stacks.Divisors.mem_weaklyAssociatedPoints_iff,
    ← isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      ((Scheme.Modules.pushforward f).obj F) U hU s hsU,
    mem_weakAss_iff_exists_comap_of_finite
      (M := Γ((Scheme.Modules.pushforward f).obj F, U)) hfin]
  refine ⟨fun ⟨q, hq, hqs⟩ ↦ mem_image_weaklyAssociatedPoints_of_comap_eq f F hU hsU hq hqs, ?_⟩
  rintro ⟨x, hx, rfl⟩
  have hxV : x ∈ V := hsU
  refine ⟨(hV.primeIdealOf ⟨x, hxV⟩).asIdeal,
    (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F V hV x hxV).2 hx, ?_⟩
  simpa only [RingHom.algebraMap_toAlgebra] using comap_app_primeIdealOf f hU hxV

end AlgebraicGeometry
