module

public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.Eta.Perfect.SectionsBasisPresentation
public import StacksFrontier.Homology.Perfect.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A bounded finite free model of a perfect object over a local ring

Let `A` be a local ring.  A perfect object of `D(A)` is by definition represented by a bounded
complex of finite projective `A`-modules; over a local ring a finite projective module is free,
and chosen bases turn such a complex into a `BoundedComplex A`, the matrix-level datum the
determinantal-ideal calculus of More on Algebra, Section 15.98 is written for.  This file
records that passage, and the consequence that a *complex* of `A`-modules with perfect class in
`D(A)` receives a quasi-isomorphism from the cochain complex of a `BoundedComplex A`.

The second statement is where K-projectivity enters: a bounded complex of finite free modules is
K-projective (`Stacks.Eta.DeterminantalIdeal.isKProjective_toCochainComplex`), so every morphism
out of it in `D(A)` — in particular the comparison isomorphism with the given complex — is the
image of an actual morphism of complexes ([Stacks, Tag 064B], in the form
`CochainComplex.IsKProjective.Q_map_surjective`).  Such a lift is a quasi-isomorphism precisely
because its image in `D(A)` is invertible.

## Main results

* `StacksDraft.Perfect.exists_boundedComplex_iso_of_isPerfect`: over a local ring a perfect
  object of the derived category is represented by the cochain complex of a `BoundedComplex`.
* `StacksDraft.Perfect.exists_quasiIso_of_iso_Q`: a derived isomorphism out of the cochain
  complex of a `BoundedComplex` is realized by a quasi-isomorphism of complexes.
* `StacksDraft.Perfect.exists_boundedComplex_quasiIso_of_isPerfect`: if the class of a complex
  `K` of `A`-modules is perfect, there are a `BoundedComplex A` and a *quasi-isomorphism* from
  its cochain complex to `K`.

## References

* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 064B](https://stacks.math.columbia.edu/tag/064B)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace StacksDraft.Perfect

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **A perfect object of `D(A)` over a local ring is represented by a bounded complex of finite
free modules, in chosen bases.**  Perfectness gives a bounded complex of finite projective
modules; over a local ring a finite projective module is free
(`Module.free_of_flat_of_isLocalRing`), and only finitely many terms are nonzero, so
`Stacks.Eta.BasisPresentation.exists_of_free` presents the complex as the cochain complex of a
`BoundedComplex A`. -/
theorem exists_boundedComplex_iso_of_isPerfect (M : DerivedCategory (ModuleCat.{u} A))
    (hM : IsPerfect M) :
    ∃ C : BoundedComplex A, Nonempty (DerivedCategory.Q.obj C.toCochainComplex ≅ M) := by
  obtain ⟨P, lo, hi, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hM
  have hfree : ∀ i : ℤ, Module.Free A (P.X i) := by
    intro i
    have := hfin i
    have := hproj i
    exact Module.free_of_flat_of_isLocalRing
  have hvanish : ∀ i : ℤ, (i < lo ∨ hi < i) → Subsingleton (P.X i) := by
    rintro i (h | h)
    · exact ModuleCat.isZero_iff_subsingleton.mp ((CochainComplex.isStrictlyGE_iff P lo).mp hGE i h)
    · exact ModuleCat.isZero_iff_subsingleton.mp ((CochainComplex.isStrictlyLE_iff P hi).mp hLE i h)
  have hzero : {i : ℤ | ¬ Subsingleton (P.X i)}.Finite := by
    refine (Set.finite_Icc lo hi).subset fun i hi' => ?_
    by_contra hc
    exact hi' (hvanish i (by simp only [Set.mem_Icc, not_and_or, not_le] at hc; omega))
  obtain ⟨Pres⟩ := Stacks.Eta.BasisPresentation.exists_of_free hfree hfin hzero
  exact ⟨Pres.toBoundedComplex, ⟨(DerivedCategory.Q.mapIso Pres.iso).symm ≪≫ e.symm⟩⟩

/-- **A derived isomorphism out of a bounded complex of finite free modules is realized by a
quasi-isomorphism of complexes.**  The cochain complex of a `BoundedComplex` is K-projective
(`Stacks.Eta.DeterminantalIdeal.isKProjective_toCochainComplex`), so every morphism out of it in
`D(A)` is the image of a morphism of complexes ([Stacks, Tag 064B], in the form
`CochainComplex.IsKProjective.Q_map_surjective`); a lift of an isomorphism is a quasi-isomorphism
because its image in `D(A)` is invertible.  No hypothesis on `A` is used. -/
@[sga "6 I 2.2" "a), b), special case"]
theorem exists_quasiIso_of_iso_Q {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (C : BoundedComplex A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj C.toCochainComplex ≅ DerivedCategory.Q.obj K) :
    ∃ ψ : C.toCochainComplex ⟶ K, QuasiIso ψ := by
  have := Stacks.Eta.DeterminantalIdeal.isKProjective_toCochainComplex C
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.Q_map_surjective C.toCochainComplex K e.hom
  exact ⟨ψ, (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ).mp (by rw [hψ]; infer_instance)⟩

/-- **A quasi-isomorphism from a bounded finite free model.**  Let `A` be a local ring and let
`K` be a cochain complex of `A`-modules whose class in `D(A)` is perfect.  Then there are a
bounded complex `C` of finite free `A`-modules in chosen bases and a quasi-isomorphism
`C ⟶ K`.

`StacksDraft.Perfect.exists_boundedComplex_iso_of_isPerfect` gives `C` with an isomorphism
`Q(C) ≅ Q(K)` in `D(A)`; `C` is K-projective, so that isomorphism is the image of a morphism of
complexes `ψ : C ⟶ K` by [Stacks, Tag 064B], and `ψ` is a quasi-isomorphism because `Q(ψ)` is
invertible. -/
@[sga "6 I 2.2" "a)"]
theorem exists_boundedComplex_quasiIso_of_isPerfect (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsPerfect (DerivedCategory.Q.obj K)) :
    ∃ (C : BoundedComplex A) (ψ : C.toCochainComplex ⟶ K), QuasiIso ψ := by
  obtain ⟨C, ⟨e⟩⟩ := exists_boundedComplex_iso_of_isPerfect (DerivedCategory.Q.obj K) hK
  exact ⟨C, exists_quasiIso_of_iso_Q C K e⟩

end StacksDraft.Perfect

end
