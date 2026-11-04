module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Locality

@[expose] public section

/-!
# Relative pseudo-coherence over a Noetherian base

Let `A` be a finite-type algebra over a Noetherian commutative ring `R`. Relative
pseudo-coherence from a fixed degree is characterized by bounded-above cohomology together with
finiteness of cohomology from that degree onward. Relative pseudo-coherence is characterized by
bounded-above finite cohomology in every degree, and an `A`-module is relatively pseudo-coherent
exactly when it is finite.

## Main results

* `PseudoCoherence.relativePseudoCoherent_iff_boundedAbove_finite_homology` (Stacks 067F): the
  three characterizations of relative pseudo-coherence over a Noetherian base.

## Implementation notes

The proof works with one polynomial presentation at a time, reducing to Stacks 066E over the
polynomial algebra, which is Noetherian when the base is; Stacks 065H makes the answer
independent of the presentation. Complexes are represented by objects of the derived category,
and membership in the bounded-above derived category is expressed by eventual vanishing of
homology objects.

## References

* [The Stacks Project, Lemma 15.82.15 (067F)](https://stacks.math.columbia.edu/tag/067F)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

private lemma pseudoCoherentFrom_of_iso
    {S : Type*} [Ring S] {X Y : DerivedCategory (ModuleCat.{u} S)} {m : ℤ}
    (e : X ≅ Y) (hX : IsPseudoCoherentFrom X m) : IsPseudoCoherentFrom Y m := by
  obtain ⟨E, hE, α, hα, hαm⟩ := hX
  refine ⟨E, hE, α ≫ e.hom, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have := hα i hi
    exact IsIso.comp_isIso
  · rw [Functor.map_comp]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) m).map e.hom) :=
      IsIso.epi_of_iso _
    exact epi_comp _ _

private lemma pseudoCoherent_iff_of_iso
    {S : Type*} [Ring S] {X Y : DerivedCategory (ModuleCat.{u} S)}
    (e : X ≅ Y) : IsPseudoCoherent X ↔ IsPseudoCoherent Y := by
  constructor
  · rintro ⟨E, hE, ⟨e'⟩⟩
    exact ⟨E, hE, ⟨e' ≪≫ e⟩⟩
  · rintro ⟨E, hE, ⟨e'⟩⟩
    exact ⟨E, hE, ⟨e' ≪≫ e.symm⟩⟩

/-- Restriction of scalars along a ring hom `S →+* T` is finite over `S` iff it is finite over `T`,
provided `T` is finite over `S`. -/
private lemma finite_restrict_iff_of_finite
    {S T N : Type*} [CommRing S] [CommRing T] [AddCommGroup N]
    (f : S →+* T) (hf : f.Finite) [Module T N] :
    @Module.Finite S N _ _ (Module.compHom N f) ↔ Module.Finite T N := by
  let : Algebra S T := f.toAlgebra
  let : Module S N := Module.compHom N f
  have : IsScalarTower S T N := ⟨fun s t n ↦ by
    change (f s * t) • n = f s • t • n
    exact mul_smul _ _ _⟩
  have : Module.Finite S T := hf
  exact ⟨fun _ ↦ Module.Finite.of_restrictScalars_finite S T N, fun _ ↦ Module.Finite.trans T N⟩

private lemma isZero_restrictScalars_iff
    {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (N : ModuleCat T) :
    IsZero ((ModuleCat.restrictScalars f).obj N) ↔ IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

private lemma relativePseudoCoherentFrom_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔ IsPseudoCoherentFrom K m := by
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  let P := MvPolynomial (Fin n) R
  let : Algebra P A := α.toRingHom.toAlgebra
  let F := ModuleCat.restrictScalars.{u} α.toRingHom
  let KR := F.mapDerivedCategory.obj K
  let eH (i : ℤ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{u} P) i).obj KR ≅
        F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    (_root_.StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app K
  have hfin (i : ℤ) :
      Module.Finite P ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} P) i).obj KR) ↔
      Module.Finite A ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} A) i).obj K) := by
    let : Module P ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
      Module.compHom _ α.toRingHom
    exact (Module.Finite.equiv_iff (eH i).toLinearEquiv).trans
      (finite_restrict_iff_of_finite (N := (DerivedCategory.homologyFunctor
        (ModuleCat.{u} A) i).obj K) α.toRingHom (RingHom.Finite.of_surjective _ hα))
  have hzero (i : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P) i).obj KR) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
    rw [(eH i).isZero_iff, isZero_restrictScalars_iff]
  have hrelKR : IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsPseudoCoherentFrom KR m :=
    ⟨fun h ↦ h n α hα, fun h ↦
      (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} K m).1.mp ⟨n, α, hα, h⟩⟩
  have hn := (pseudoCoherent_iff_boundedAbove_finite_homology KR m
    (F.obj ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} A) 0).obj K))).1
  have hc :
      ((∃ b : ℤ, ∀ i : ℤ, b < i →
          IsZero ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} P) i).obj KR)) ∧
        ∀ i : ℤ, m ≤ i → Module.Finite P ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} P) i).obj KR)) ↔
      ((∃ b : ℤ, ∀ i : ℤ, b < i →
          IsZero ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} A) i).obj K)) ∧
        ∀ i : ℤ, m ≤ i → Module.Finite A ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} A) i).obj K)) :=
    and_congr (exists_congr fun _ ↦ forall₂_congr fun i _ ↦ hzero i)
      (forall₂_congr fun i _ ↦ hfin i)
  have := Algebra.FiniteType.isNoetherianRing R A
  exact hrelKR.trans (hn.trans (hc.trans (pseudoCoherent_iff_boundedAbove_finite_homology K m
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj K)).1.symm))

/-- **Stacks 067F.** For a finite-type algebra over a Noetherian ring, relative
pseudo-coherence from degree `m` means bounded-above finite homology in degrees at least `m`;
relative pseudo-coherence means bounded-above finite homology in every degree; and relative
pseudo-coherence of a module is equivalent to its finiteness. -/
@[stacks 067F]
public theorem relativePseudoCoherent_iff_boundedAbove_finite_homology
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (M : Type u) [AddCommGroup M] [Module A M] :
    (IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} A) i).obj K)) ∧
      ∀ i : ℤ, m ≤ i →
        Module.Finite A ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} A) i).obj K)) ∧
    (IsRelativelyPseudoCoherent (R := R) K ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} A) i).obj K)) ∧
      ∀ i : ℤ,
        Module.Finite A ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} A) i).obj K)) ∧
    (IsModuleRelativelyPseudoCoherent (R := R) (A := A) M ↔
      Module.Finite A M) := by
  have := Algebra.FiniteType.isNoetherianRing R A
  have hall (L : DerivedCategory (ModuleCat.{u} A)) :
      IsRelativelyPseudoCoherent (R := R) L ↔ IsPseudoCoherent L := by
    rw [IsRelativelyPseudoCoherent, pseudoCoherent_iff_all L]
    exact forall_congr' fun n ↦ relativePseudoCoherentFrom_iff L n
  rw [relativePseudoCoherentFrom_iff K m, hall K,
    show IsModuleRelativelyPseudoCoherent (R := R) (A := A) M ↔
      IsModulePseudoCoherent (R := A) M from
      hall ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))]
  exact pseudoCoherent_iff_boundedAbove_finite_homology K m M

end PseudoCoherence
