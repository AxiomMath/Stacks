module

public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible

/-!
# Generic freeness in the good half of the generic-fibre dichotomy

`StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced` and
`StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible` leave Stacks 05FT standing on
exactly two statements, the *good halves* of the affine cases of Stacks 0578 and Stacks 055A at
the generic point: over a Noetherian domain `D` with a finite type algebra `T`, a geometrically
reduced — respectively geometrically irreducible — generic fibre forces a nonempty basic open of
`Spec D` inside the corresponding fibre locus.

**This file adds generic freeness to the data those two statements may be proved from.** The good
half for a property `P` need only be proved for algebras `T` which are *free* as `D`-modules: the
general case follows, by replacing `D` with a localization `D_g` on which the base change becomes
free (Stacks 051Z, `Module.Free.exists_ne_zero_of_isReduced`) and descending the resulting basic
open along `Spec D_g → Spec D`.

**The argument.** Generic freeness gives a nonzero `g : D` with `D_g ⊗[D] T` free over `D_g`. A
field `K` over `D` with `ker (D → K) = (0)` kills nothing in `D`, so `g` is invertible in `K` and
`K` is a field over `D_g` with `ker (D_g → K) = (0)`; the fibres of `D_g ⊗[D] T` are those of `T`
by `Algebra.fibreTensorEquiv`, so a geometrically good generic fibre of `T` is a geometrically
good generic fibre of `D_g ⊗[D] T`. The free case then yields a nonzero `h : D_g` with `D(h)`
inside the fibre locus over `D_g`. Writing `h = a / gⁿ`, the basic open `D(a ⬝ g) ⊆ Spec D` works:
a prime `p` avoiding `g` is avoided by no field `K` over `D` with `ker (D → K) = p`, so such a `K`
is again a field over `D_g`, its kernel there is a prime avoiding `h` because `h` maps to a
nonzero multiple of the image of `a`, and the fibre of `T` at `K` is the fibre of `D_g ⊗[D] T` at
`K`.

Localizations are the only base changes along which a fibre locus descends this way. The
contraction `Spec D_g → Spec D` is injective with image `D(g)`, and — what the argument actually
uses — *every* field over `D` at a prime of `D(g)` is a field over `D_g`, by
`IsLocalization.Away.lift`. For a general `D`-algebra `E` only the failure of a fibre property
descends, which is `Algebra.not_mem_fibreLocus_comap`, and that is why the bad halves in
`StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut` can use an arbitrary auxiliary algebra
while this file cannot.

## Main results

* `Algebra.mem_fibreLocus_bot_baseChange_of_away`: a good generic fibre stays good after
  localizing the base away from a nonzero element.
* `Algebra.exists_basicOpen_subset_fibreLocus_of_away`: **the descent step.** A nonempty basic
  open of `Spec D_g` inside the fibre locus of `D_g ⊗[D] T` produces a nonempty basic open of
  `Spec D` inside the fibre locus of `T`.
* `Algebra.exists_basicOpen_subset_fibreLocus_of_free`: **the reduction.** The good half of the
  generic-fibre dichotomy for a property `P` follows from the good half for algebras that are
  free modules over the base.
* `Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_free` and
  `Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_free`: that reduction at
  reducedness and at irreducibility of the spectrum, the two properties Stacks 05FT needs.
* `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves`: constructibility of
  the geometrically integral fibre locus over a Noetherian ring, granted the affine cases of
  Stacks 0578 and Stacks 055A at the generic point *for free algebras only*.

## Implementation notes

The hypothesis `[Module.Free D T]` is on `T` as a `D`-module, not on a base change of `T`, and is
used only through the free case supplied by generic freeness; the conclusion carries no freeness.
`Module.Free.exists_ne_zero_of_isReduced` produces freeness of `Localization.Away g ⊗[D] T` over
`Localization.Away g`, which is the shape the reduction consumes, so the auxiliary algebra is a
`Localization.Away` and not — as in
`Algebra.exists_subalgebra_finiteType_free` — a subalgebra of a field.

The two descent lemmas take the localization as an abstract `[IsLocalization.Away g E]` rather
than as `Localization.Away g`, so that a caller holding some other model of the localization need
not transport along an isomorphism. `[IsDomain E]` is a hypothesis rather than a consequence
because the statements mention the generic point `(0)` of `Spec E`, which needs the instance to
typecheck.

**What this does and does not advance.** By
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` and
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible` the
*unrestricted* good halves are equivalent to the constructibility statements they are invoked to
prove. The reduction here shows the free-restricted good halves imply the unrestricted ones, so
they too are equivalent to that conclusion: this file does not shrink the logical gap left by
Stacks 05FT, and no hypothesis of the eight dévissage theorems that assume constructibility of
the geometrically integral fibre locus is discharged by it. What it does is enlarge the data a
proof of either half may use, by exactly the freeness that the classical proofs of Stacks 0578
and Stacks 055A reduce to first.

Nothing here carries a Stacks attribute. The statements proved are a reduction between two forms
of one half of Stacks 0578 and Stacks 055A, and Stacks 05FT conditional on the restricted forms.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)
-/

@[expose] public section

open PrimeSpectrum Topology

open scoped TensorProduct

universe u

namespace Algebra

variable {P : ∀ (R : Type u) [CommRing R], Prop}

/-- A ring-isomorphism-invariant property of `T ⊗[D] F` is one of `(E ⊗[D] T) ⊗[E] F`. -/
private theorem prop_baseChange_iff
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (D T E F : Type u) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E]
    [CommRing F] [Algebra D F] [Algebra E F] [IsScalarTower D E F] :
    P (T ⊗[D] F) ↔ P ((E ⊗[D] T) ⊗[E] F) :=
  hP _ _ ((fibreTensorEquiv D T E F).trans (Algebra.TensorProduct.comm E F (E ⊗[D] T)).toRingEquiv)

section Localization

variable {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T]
  {g : D} (E : Type u) [CommRing E] [IsDomain E] [Algebra D E] [IsLocalization.Away g E]

/-- **A good generic fibre survives a localization of the base.** Let `D` be a domain, `T` a
`D`-algebra and `E` a localization of `D` away from a nonzero `g`. If the generic fibre of `T` has
an isomorphism-invariant property `P`, so does the generic fibre of the base change `E ⊗[D] T`.

A field `F` over `E` with `ker (E → F) = (0)` is a field over `D` with `ker (D → F) = (0)`,
because `D → E` is injective, and its fibre `F ⊗[E] (E ⊗[D] T)` is the fibre `T ⊗[D] F` by
`Algebra.fibreTensorEquiv`. -/
theorem mem_fibreLocus_bot_baseChange_of_away (hg0 : g ≠ 0)
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) ∈ fibreLocus E (E ⊗[D] T) P := by
  have hinj : Function.Injective (algebraMap D E) :=
    IsLocalization.injective E (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  intro F _ _ hker
  let : Algebra D F := ((algebraMap E F).comp (algebraMap D E)).toAlgebra
  have : IsScalarTower D E F := IsScalarTower.of_algebraMap_eq' rfl
  have hkerD :
      RingHom.ker (algebraMap D F) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D).asIdeal := by
    change RingHom.ker ((algebraMap E F).comp (algebraMap D E)) = ⊥
    rw [← RingHom.comap_ker, hker, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  exact (prop_baseChange_iff hP D T E F).mp (hgen F hkerD)

/-- **Descent of a basic open in a fibre locus along a localization.** Let `D` be a domain, `T` a
`D`-algebra and `E` a localization of `D` away from a nonzero `g`. A nonzero `h : E` whose basic
open lies in the fibre locus of `E ⊗[D] T` produces a nonzero `f : D` whose basic open lies in
the fibre locus of `T`.

Write `h` as `a / gⁿ`, so that `h ⬝ gⁿ = a` in `E`, and take `f = a ⬝ g`; it is nonzero because
`E` is a domain in which `g` is invertible and `h ≠ 0`. Let `p` be a prime of `D` avoiding `a ⬝ g`
and let `K` be a field over `D` with `ker (D → K) = p`. Then `g ∉ p` makes `g` invertible in `K`,
so `K` is a field over `E` by `IsLocalization.Away.lift`; its kernel `q` there is a prime avoiding
`h`, since `h` maps to a nonzero multiple of the image of `a`, which is nonzero because `a ∉ p`.
So `q` lies in the fibre locus of `E ⊗[D] T`, and the fibre of `E ⊗[D] T` at `K` is the fibre
`T ⊗[D] K` by `Algebra.fibreTensorEquiv`. -/
theorem exists_basicOpen_subset_fibreLocus_of_away (hg0 : g ≠ 0)
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    {h : E} (hh0 : h ≠ 0)
    (hsub : (basicOpen h : Set (PrimeSpectrum E)) ⊆ fibreLocus E (E ⊗[D] T) P) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆ fibreLocus D T P := by
  have hpow := powers_le_nonZeroDivisors_of_noZeroDivisors hg0 (M₀ := D)
  have hinj : Function.Injective (algebraMap D E) := IsLocalization.injective E hpow
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) h
  have hspec : h * algebraMap D E (m : D) = algebraMap D E a := by
    rw [← hm]; exact IsLocalization.mk'_spec E a m
  have hmD : (m : D) ≠ 0 := by
    obtain ⟨n, hn⟩ := m.2
    rw [← hn]
    exact pow_ne_zero n hg0
  have hm0 : algebraMap D E (m : D) ≠ 0 := fun h0 => hmD (hinj (by simpa using h0))
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hspec
    exact hh0 ((mul_eq_zero.mp hspec).resolve_right hm0)
  refine ⟨a * g, mul_ne_zero ha0 hg0, fun p hp => ?_⟩
  rw [SetLike.mem_coe, mem_basicOpen] at hp
  have hap : a ∉ p.asIdeal := fun hx => hp (p.asIdeal.mul_mem_right g hx)
  have hgp : g ∉ p.asIdeal := fun hx => hp (p.asIdeal.mul_mem_left a hx)
  intro K _ _ hkerK
  have hker : ∀ x : D, algebraMap D K x = 0 → x ∈ p.asIdeal := fun x hx => by
    rw [← hkerK]; exact RingHom.mem_ker.mpr hx
  have hunit : IsUnit (algebraMap D K g) :=
    isUnit_iff_ne_zero.mpr fun h0 => hgp (hker g h0)
  let : Algebra E K := (IsLocalization.Away.lift g hunit).toAlgebra
  have : IsScalarTower D E K := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have hhq : h ∉ RingHom.ker (algebraMap E K) := by
    intro hmem
    refine hap (hker a ?_)
    have := congrArg (algebraMap E K) hspec
    rw [map_mul, RingHom.mem_ker.mp hmem, zero_mul,
      ← IsScalarTower.algebraMap_apply] at this
    exact this.symm
  have hq := hsub (a := (⟨RingHom.ker (algebraMap E K), RingHom.ker_isPrime _⟩ :
    PrimeSpectrum E)) (by rw [SetLike.mem_coe, mem_basicOpen]; exact hhq)
  exact (prop_baseChange_iff hP D T E K).mpr (hq K rfl)

end Localization

section Free

/-- **The good half of the generic-fibre dichotomy may assume the algebra free.** Let `P` be a
property of rings invariant under ring isomorphism. If, over every Noetherian domain, a finite
type algebra which is *free as a module over the base* and whose generic fibre has `P` admits a
nonempty basic open of the base inside its fibre locus, then the same holds with the freeness
hypothesis dropped.

Generic freeness (Stacks 051Z) gives a nonzero `g` with `D_g ⊗[D] T` free over `D_g`; the generic
fibre stays good by `Algebra.mem_fibreLocus_bot_baseChange_of_away`, the free case applies over
`D_g`, and `Algebra.exists_basicOpen_subset_fibreLocus_of_away` brings the resulting basic open
back down to `Spec D`. -/
theorem exists_basicOpen_subset_fibreLocus_of_free
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (hfree : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆ fibreLocus D T P)
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆ fibreLocus D T P := by
  obtain ⟨g, hg0, hgfree⟩ := Module.Free.exists_ne_zero_of_isReduced D T
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  have : Module.Free (Localization.Away g) (Localization.Away g ⊗[D] T) := hgfree
  obtain ⟨h, hh0, hhsub⟩ := hfree (Localization.Away g) (Localization.Away g ⊗[D] T)
    (mem_fibreLocus_bot_baseChange_of_away _ hg0 hP hgen)
  exact exists_basicOpen_subset_fibreLocus_of_away _ hg0 hP hh0 hhsub

/-- **The affine case of Stacks 0578 at the generic point may assume the algebra free.** The good
half of the generic-fibre dichotomy for geometric reducedness follows from its restriction to
finite type algebras that are free modules over the base.

This is `Algebra.exists_basicOpen_subset_fibreLocus_of_free` at `P = IsReduced`. -/
theorem exists_basicOpen_subset_geometricallyReducedFibreLocus_of_free
    (hfree : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyReducedFibreLocus D T)
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  simp only [geometricallyReducedFibreLocus_eq_fibreLocus] at hfree hgen ⊢
  exact exists_basicOpen_subset_fibreLocus_of_free (fun _ _ _ _ e => isReduced_congr e) hfree D T
    hgen

/-- **The affine case of Stacks 055A at the generic point may assume the algebra free.** The good
half of the generic-fibre dichotomy for geometric irreducibility follows from its restriction to
finite type algebras that are free modules over the base.

This is `Algebra.exists_basicOpen_subset_fibreLocus_of_free` at irreducibility of the
spectrum. -/
theorem exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_free
    (hfree : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIrreducibleFibreLocus D T := by
  simp only [geometricallyIrreducibleFibreLocus_eq_fibreLocus] at hfree hgen ⊢
  exact exists_basicOpen_subset_fibreLocus_of_free
    (fun _ _ _ _ e => irreducibleSpace_primeSpectrum_congr e) hfree D T hgen

/-- **Constructibility of the geometrically integral fibre locus from the free cases of the two
good halves.** Over a Noetherian ring `A` the geometrically integral fibre locus of a finite type
algebra `C` is constructible, granted the affine cases of Stacks 0578 and Stacks 055A at the
generic point *for algebras that are free modules over the base*.

The two hypotheses are extended to all finite type algebras by
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_free` and
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_free`, then turned into
constructibility of the two halves by
`Algebra.isConstructible_geometricallyReducedFibreLocus_of_goodGeneric` and
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_goodGeneric`, and intersected by
`Algebra.isConstructible_geometricallyIntegralFibreLocus`, the locus of Stacks 05FT being the
intersection of the other two by Stacks 05DY.

This is the hypothesis-free form of the constructibility statement that the dévissage theorems of
Stacks 05I4 assume, reduced to the two free cases and to nothing else. -/
theorem isConstructible_geometricallyIntegralFibreLocus_of_free_halves
    (hred : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyReducedFibreLocus D T)
    (hirr : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  isConstructible_geometricallyIntegralFibreLocus A C
    (isConstructible_geometricallyIrreducibleFibreLocus_of_goodGeneric
      (fun D T _ _ _ _ _ _ =>
        exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_free hirr D T) A C)
    (isConstructible_geometricallyReducedFibreLocus_of_goodGeneric
      (fun D T _ _ _ _ _ _ =>
        exists_basicOpen_subset_geometricallyReducedFibreLocus_of_free hred D T) A C)

end Free

end Algebra

end
