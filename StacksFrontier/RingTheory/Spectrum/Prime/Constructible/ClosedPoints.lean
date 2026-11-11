module

public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Chevalley
public import StacksFrontier.Topology.Jacobson.ConstructibleClosedPoints
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Constructible sets and closed points of spectra over a Noetherian Jacobson ring (Stacks 00GE)

Let `R → S` be a ring map of finite type with `R` Jacobson, and write `f : Y = Spec S → X = Spec R`
and `X₀`, `Y₀` for the closed points. Then `f` sends `Y₀` into `X₀`
(`PrimeSpectrum.mapsTo_comap_closedPoints`) and, for constructible `E ⊆ Y`, the closed points of
`X` in `f(E)` are the images of the closed points of `E`
(`PrimeSpectrum.restrictToClosedPoints_comap_image`). When `R` is moreover Noetherian, Chevalley's
theorem makes `f(E)` constructible, and these facts assemble into the commutative square of
Stacks 00GE between the constructible sets of `Y`, `Y₀`, `X` and `X₀`
(`PrimeSpectrum.exists_commSq_constructible_restrictToClosedPoints`), whose horizontal arrows are
the bijections of Stacks 005Y.
-/

@[expose] public section

namespace PrimeSpectrum

open Topology

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a finite-type ring map `φ : R → S` out of a Jacobson ring, the induced map
`Spec S → Spec R` sends closed points to closed points: the residue field `S/𝔪` of a maximal
ideal is a field of finite type over `R`, hence finite over `R` by the Jacobson property, so the
kernel `φ⁻¹(𝔪)` of `R → S/𝔪` is maximal. -/
theorem mapsTo_comap_closedPoints [IsJacobsonRing R] {φ : R →+* S} (hφ : φ.FiniteType) :
    Set.MapsTo (comap φ) (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := by
  intro y hy
  rw [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal] at hy ⊢
  let : Field (S ⧸ y.asIdeal) := @Ideal.Quotient.field _ _ y.asIdeal hy
  have hψ : ((Ideal.Quotient.mk y.asIdeal).comp φ).FiniteType :=
    hφ.comp_surjective Ideal.Quotient.mk_surjective
  have hint := (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hψ).to_isIntegral
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint ⊥
  rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hmax
  rw [comap_asIdeal]
  exact hmax

/-- For a finite-type ring map `φ : R → S` out of a Jacobson ring and a constructible
`E ⊆ Spec S`, the closed points of `Spec R` lying in the image of `E` are exactly the images of
the closed points of `E`: in the notation of Stacks 00GE, `f(E)₀ = f(E₀)` as subsets of the
space `X₀` of closed points.

A closed point `x = f(y)` with `y ∈ E` has a locally closed fibre `f⁻¹(x)`; inside it `E`
contains a locally closed neighbourhood of `y`, which contains a closed point of the Jacobson
space `Spec S`. -/
theorem restrictToClosedPoints_comap_image [IsJacobsonRing R] {φ : R →+* S}
    (hφ : φ.FiniteType) {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    JacobsonSpace.restrictToClosedPoints (comap φ '' E) =
      (mapsTo_comap_closedPoints hφ).restrict (comap φ) _ _ ''
        JacobsonSpace.restrictToClosedPoints E := by
  have : IsJacobsonRing S := hφ.isJacobsonRing
  ext ⟨x, hx⟩
  simp only [JacobsonSpace.restrictToClosedPoints, Set.mem_preimage]
  constructor
  · rintro ⟨y, hyE, rfl⟩
    have hfib : IsLocallyClosed (comap φ ⁻¹' {comap φ y}) :=
      ((mem_closedPoints_iff.mp hx).preimage (continuous_comap φ)).isLocallyClosed
    obtain ⟨W, hWlc, hyW, hWfib, hW⟩ :=
      hE.exists_isLocallyClosed_subset_or_subset_compl _ hfib y
        (Set.mem_preimage.2 (Set.mem_singleton _))
    have hWE : W ⊆ E := hW.resolve_right fun h => h hyW hyE
    obtain ⟨z, hzW, hz⟩ := nonempty_inter_closedPoints ⟨y, hyW⟩ hWlc
    exact ⟨⟨z, hz⟩, hWE hzW, Subtype.ext (hWfib hzW)⟩
  · rintro ⟨⟨y, hy⟩, hyE, hxy⟩
    exact ⟨y, hyE, congrArg Subtype.val hxy⟩

/-- **Stacks 00GE.** Let `R` be a Noetherian Jacobson ring and `φ : R → S` a ring map of
finite type, with `f : Y = Spec S → X = Spec R`, and write `X₀`, `Y₀` for the spaces of closed
points. There is a commutative square
```
Constr(Y)  --E ↦ E₀-->  Constr(Y₀)
   |                       |
 f(·)                    f(·)
   v                       v
Constr(X)  --E ↦ E₀-->  Constr(X₀)
```
whose horizontal arrows are the bijections `E ↦ E ∩ X₀` of Stacks 005Y
(`JacobsonSpace.restrictToClosedPoints_bijective`) and whose vertical arrows take images under
`f` and under its restriction `Y₀ → X₀` (`mapsTo_comap_closedPoints`). Here `S` is Jacobson as
a finite-type algebra over a Jacobson ring, so 005Y applies to both `X` and `Y`.

The statement records the full content of the lemma: each of the four arrows is pinned down by
its action on underlying sets (so both vertical arrows are well defined, i.e. land in
constructible sets), both horizontal arrows are bijective, and `right ∘ top = bot ∘ left`, which
on underlying sets is `f(E)₀ = f(E₀)`.

The left arrow is well defined by Chevalley's theorem
(`isConstructible_comap_image_of_finiteType`, via Stacks 00FP and 00FE); commutativity is
`restrictToClosedPoints_comap_image` (part (1) of Stacks 00GD); the right arrow is then well
defined because every constructible subset of `Y₀` is some `E₀`, whose image `f(E₀) = f(E)₀` is
constructible. -/
@[stacks 00GE "the full square: both vertical arrows well defined, horizontal arrows the \
  bijections of 005Y, and f(E)₀ = f(E₀)"]
theorem exists_commSq_constructible_restrictToClosedPoints [IsNoetherianRing R]
    [IsJacobsonRing R] (φ : R →+* S) (hφ : φ.FiniteType) :
    ∃ (left : {E : Set (PrimeSpectrum S) // IsConstructible E} →
          {E : Set (PrimeSpectrum R) // IsConstructible E})
      (right : {F : Set (closedPoints (PrimeSpectrum S)) // IsConstructible F} →
          {F : Set (closedPoints (PrimeSpectrum R)) // IsConstructible F})
      (top : {E : Set (PrimeSpectrum S) // IsConstructible E} →
          {F : Set (closedPoints (PrimeSpectrum S)) // IsConstructible F})
      (bot : {E : Set (PrimeSpectrum R) // IsConstructible E} →
          {F : Set (closedPoints (PrimeSpectrum R)) // IsConstructible F}),
      (∀ E, (left E).1 = comap φ '' E.1) ∧
      (∀ F, (right F).1 = (mapsTo_comap_closedPoints hφ).restrict (comap φ) _ _ '' F.1) ∧
      (∀ E, (top E).1 = JacobsonSpace.restrictToClosedPoints E.1) ∧
      (∀ E, (bot E).1 = JacobsonSpace.restrictToClosedPoints E.1) ∧
      Function.Bijective top ∧ Function.Bijective bot ∧
      right ∘ top = bot ∘ left := by
  have : IsJacobsonRing S := hφ.isJacobsonRing
  have hleft (E : Set (PrimeSpectrum S)) (hE : IsConstructible E) :
      IsConstructible (comap φ '' E) :=
    isConstructible_comap_image_of_finiteType φ hφ hE
  have hright (F : Set (closedPoints (PrimeSpectrum S))) (hF : IsConstructible F) :
      IsConstructible ((mapsTo_comap_closedPoints hφ).restrict (comap φ) _ _ '' F) := by
    obtain ⟨⟨E, hE⟩, hEF⟩ :=
      (JacobsonSpace.restrictToClosedPoints_bijective (X := PrimeSpectrum S)).2 ⟨F, hF⟩
    have hEF' : JacobsonSpace.restrictToClosedPoints E = F := congrArg Subtype.val hEF
    rw [← hEF', ← restrictToClosedPoints_comap_image hφ hE]
    exact JacobsonSpace.isConstructible_restrictToClosedPoints (hleft E hE)
  refine ⟨fun E => ⟨comap φ '' E.1, hleft E.1 E.2⟩, fun F => ⟨_, hright F.1 F.2⟩,
    fun E => ⟨JacobsonSpace.restrictToClosedPoints E.1,
      JacobsonSpace.isConstructible_restrictToClosedPoints E.2⟩,
    fun E => ⟨JacobsonSpace.restrictToClosedPoints E.1,
      JacobsonSpace.isConstructible_restrictToClosedPoints E.2⟩,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    JacobsonSpace.restrictToClosedPoints_bijective,
    JacobsonSpace.restrictToClosedPoints_bijective, ?_⟩
  funext E
  exact Subtype.ext (restrictToClosedPoints_comap_image hφ E.2).symm

end PrimeSpectrum
