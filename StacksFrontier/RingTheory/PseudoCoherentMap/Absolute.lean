module

public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs

@[expose] public section

/-!
# Relative pseudo-coherence over a pseudo-coherent ring map

Over a pseudo-coherent ring map `R → A`, the relative notions of Stacks 065I collapse onto the
absolute ones of Stacks 064Q: an object of `D(A)` is `m`-pseudo-coherent relative to `R` exactly
when it is `m`-pseudo-coherent, and relatively pseudo-coherent exactly when pseudo-coherent.

## Main results

* `PseudoCoherence.relativelyPseudoCoherent_iff_pseudoCoherent` (Stacks 0DHQ).

## Implementation notes

The two assertions the source separates by “respectively” are packaged as a conjunction. The
finite-type instance that the relative notions require is extracted from the pseudo-coherent
ring map hypothesis.

Taking `R → A → A` in Stacks 067D reduces the claim to the case `R = A`, where the empty
polynomial presentation `A[∅] ≅ A` is available: restriction of scalars along it changes nothing,
so Stacks 064Z and the presentation-independence of Stacks 065H identify relative
pseudo-coherence over `A` with pseudo-coherence over `A`.

## References

* [The Stacks Project, Lemma 15.83.11 (0DHQ)](https://stacks.math.columbia.edu/tag/0DHQ)
-/

open CategoryTheory
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

private lemma isPseudoCoherentFrom_iff_of_iso
    {S : Type u} [Ring S] {K L : DerivedCategory (ModuleCat.{u} S)} (e : K ≅ L) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔ IsPseudoCoherentFrom L m :=
  ⟨fun h ↦ h.ofIso e, fun h ↦ h.ofIso e.symm⟩

private lemma isPseudoCoherent_iff_of_iso
    {S : Type u} [Ring S] {K L : DerivedCategory (ModuleCat.{u} S)} (e : K ≅ L) :
    IsPseudoCoherent K ↔ IsPseudoCoherent L :=
  ⟨fun h ↦ h.ofIso e, fun h ↦ h.ofIso e.symm⟩

private lemma isModulePseudoCoherent_of_finite_free
    {S : Type u} [Ring S] (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Free S M] : IsModulePseudoCoherent (R := S) M := by
  let E := (HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of S M)
  refine ⟨E, ⟨⟨0, inferInstance⟩, ?_⟩, ⟨Iso.refl _⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    change Module.Finite S M ∧ Module.Free S M
    exact ⟨inferInstance, inferInstance⟩
  · have : Subsingleton (E.X i) := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of S M) i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton S _⟩

private lemma isModulePseudoCoherent_restrictScalars_ringEquiv
    {S : Type u} {T : Type u} [Ring S] [Ring T] (e : S ≃+* T) :
    IsModulePseudoCoherent (R := S)
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) := by
  let e' : S ≃ₗ[S] (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) :=
    { e.toAddEquiv with map_smul' := fun r s ↦ e.map_mul r s }
  have := Module.Finite.equiv e'
  have := Module.Free.of_equiv e'
  exact isModulePseudoCoherent_of_finite_free _

/-- Over `A` itself the empty polynomial presentation is available, so relative
`m`-pseudo-coherence over `A` is `m`-pseudo-coherence. -/
private lemma selfRelativePseudoCoherentFrom_iff
    {A : Type u} [CommRing A] (L : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := A) (DerivedCategory.Q.obj L) m ↔
      IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m := by
  let e : MvPolynomial (Fin 0) A ≃ₐ[A] A := MvPolynomial.isEmptyAlgEquiv A (Fin 0)
  let f : MvPolynomial (Fin 0) A →ₐ[A] A := e.toAlgHom
  let F := ModuleCat.restrictScalars.{u} f.toRingHom
  have hModule : IsModulePseudoCoherent (R := MvPolynomial (Fin 0) A)
      ((ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of A A)) :=
    isModulePseudoCoherent_restrictScalars_ringEquiv e.toRingEquiv
  have hRestriction :=
    (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars.{u, u, u}
      f.toRingHom hModule L m).1
  have hPresentation :
      IsPseudoCoherentFrom (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) m ↔
        IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m :=
    (isPseudoCoherentFrom_iff_of_iso (F.mapDerivedCategoryFactors.app L) m).trans
      hRestriction.symm
  exact ⟨fun h ↦ hPresentation.mp (h 0 f e.surjective), fun h ↦
    (isPseudoCoherentFrom_polynomialPresentation_independent
      (DerivedCategory.Q.obj L) m).1.mp ⟨0, f, e.surjective, hPresentation.mpr h⟩⟩

/-- Over `A` itself relative pseudo-coherence is pseudo-coherence. -/
private lemma selfRelativePseudoCoherent_iff
    {A : Type u} [CommRing A] (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsRelativelyPseudoCoherent (R := A) (DerivedCategory.Q.obj L) ↔
      IsPseudoCoherent (DerivedCategory.Q.obj L) := by
  rw [IsRelativelyPseudoCoherent, pseudoCoherent_iff_all (DerivedCategory.Q.obj L)]
  exact forall_congr' fun m ↦ selfRelativePseudoCoherentFrom_iff L m

/-- Relative `m`-pseudo-coherence over `R` is invariant under isomorphism in `D(A)`. -/
public lemma isRelativelyPseudoCoherentFrom_iff_of_iso
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsRelativelyPseudoCoherentFrom (R := R) L m :=
  forall_congr' fun _ ↦ forall_congr' fun f ↦ imp_congr_right fun _ ↦
    isPseudoCoherentFrom_iff_of_iso
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.mapIso e) m

private lemma isRelativelyPseudoCoherent_iff_of_iso
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L) :
    IsRelativelyPseudoCoherent (R := R) K ↔ IsRelativelyPseudoCoherent (R := R) L :=
  forall_congr' fun m ↦ isRelativelyPseudoCoherentFrom_iff_of_iso e m

/-- **Stacks 0DHQ.** Let `R → A` be a pseudo-coherent ring map. An object of `D(A)` is
`m`-pseudo-coherent relative to `R` exactly when it is `m`-pseudo-coherent, and it is
pseudo-coherent relative to `R` exactly when it is pseudo-coherent. -/
@[stacks 0DHQ]
public theorem relativelyPseudoCoherent_iff_pseudoCoherent
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hRA : Algebra.PseudoCoherent R A)
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    (IsRelativelyPseudoCoherentFrom (R := R) K m ↔ IsPseudoCoherentFrom K m) ∧
    (IsRelativelyPseudoCoherent (R := R) K ↔ IsPseudoCoherent K) := by
  let L := (DerivedCategory.Q (C := ModuleCat.{u} A)).objPreimage K
  let e := (DerivedCategory.Q (C := ModuleCat.{u} A)).objObjPreimageIso K
  have hcomp := relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := A)
    (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hRA)
    (DerivedCategory.Q.obj L) m
  exact ⟨(isRelativelyPseudoCoherentFrom_iff_of_iso e m).symm.trans
      (hcomp.1.symm.trans
        ((selfRelativePseudoCoherentFrom_iff L m).trans (isPseudoCoherentFrom_iff_of_iso e m))),
    (isRelativelyPseudoCoherent_iff_of_iso e).symm.trans
      (hcomp.2.symm.trans
        ((selfRelativePseudoCoherent_iff L).trans (isPseudoCoherent_iff_of_iso e)))⟩

end PseudoCoherence
