module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteFlatDeRhamTrace
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteProjectionToProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover

/-!
# Pullback to a smooth projective variety from projective space is injective on de Rham cohomology

In the proof of axiom (A6) for de Rham cohomology (Stacks, Proposition 0FWD, the paragraph
"Proof of Axiom (A6) for `X` irreducible") the source takes, for `k` algebraically closed of
characteristic zero and `X` an irreducible smooth projective scheme of dimension `d` over `k`, a
finite syntomic morphism `f : X ⟶ 𝐏^d_k`, and observes that the trace map of de Rham complexes
gives `Θ : H^n_{dR}(X/k) ⟶ H^n_{dR}(𝐏^d_k/k)` with `Θ ∘ f^*` multiplication by a positive
integer. This file combines the two ingredients: the existence of `f`
(`Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace_of_relativeDimension`) and the
trace map of a finite syntomic morphism whose direct image of the structure sheaf is finite
locally free of constant positive rank (`Stacks.WeilDeRham.exists_deRhamCohomologyTrace`,
`Stacks.WeilDeRham.injective_deRhamCohomologyPullback_of_charZero`).

The bridge is that `f_*𝒪_X` is finite locally free of constant positive rank. A finite flat
morphism to a locally Noetherian scheme is finite locally free (Stacks, Tag 02KB); its degree is
locally constant (Stacks, Tag 04MH), hence constant on the irreducible scheme `𝐏^d_k`; and it is
positive because `f` is surjective: over an open on which `f_*𝒪_X` is free of rank zero the
direct image is zero, whereas its sections are those of `𝒪_X` over a nonempty open.

## Main results

* `Stacks.WeilDeRham.exists_isFiniteLocallyFreeOfRank_of_preconnectedSpace`: a finite locally free
  morphism to a nonempty connected scheme has a constant degree.
* `Stacks.WeilDeRham.pos_of_isFiniteLocallyFreeOfRank_of_surjective`: a surjective finite locally
  free morphism from a nonempty scheme has positive degree.
* `Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace_deRhamCohomologyTrace`: the
  statement used in the proof of (A6): `f`, a positive integer `e`, maps `Θ_n` with
  `Θ_n ∘ f^* = e`, and injectivity of `f^*` in every degree.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.WeilDeRham

/-! ### The degree of a finite locally free morphism -/

section Degree

/-- **A finite locally free morphism to a nonempty connected scheme has constant degree.** The
target decomposes into open and closed pieces by the degree (Stacks, Tag 04MH); on a connected
space the piece containing one point is everything, and the degree is local on the target. -/
theorem exists_isFiniteLocallyFreeOfRank_of_preconnectedSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [PreconnectedSpace S] [Nonempty S] :
    ∃ r : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r := by
  obtain ⟨U, hU, hr⟩ := Stacks.Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank f
  obtain ⟨s⟩ := ‹Nonempty S›
  let r := hU.index s
  have htop : U r = ⊤ :=
    TopologicalSpace.Opens.ext (by simpa using (hU.isClopen r).eq_univ ⟨s, hU.mem_index s⟩)
  have := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_isZariskiLocalAtTarget.{u} r
  exact ⟨r, (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r) (fun _ : Unit => U r)
    (by simp [htop]) (f := f)).2 fun _ => hr r⟩

/-- The free sheaf of modules of rank zero on a scheme is a zero object: a morphism out of it is
a family of sections indexed by the empty type. -/
theorem isZero_free_fin_zero (S : Scheme.{u}) :
    IsZero (_root_.SheafOfModules.free.{u} (R := S.ringCatSheaf) (ULift.{u, 0} (Fin 0))) :=
  IsInitial.isZero (IsInitial.ofUniqueHom (fun M => M.freeHomEquiv.symm isEmptyElim)
    fun M _ => M.freeHomEquiv.injective (funext fun i => isEmptyElim i))

/-- **A surjective finite locally free morphism from a nonempty scheme has positive degree.** If
the degree were zero, `f_*𝒪_X` would vanish on an open `U` containing the image of a point of
`X`, so the ring `Γ(f⁻¹U, 𝒪_X)` of sections of `f_*𝒪_X` over `U` would be zero although
`f⁻¹U` is nonempty. -/
theorem pos_of_isFiniteLocallyFreeOfRank_of_surjective {X S : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [Nonempty X] {r : ℕ} (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r) :
    0 < r := by
  refine Nat.pos_of_ne_zero ?_
  rintro rfl
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, ⟨ε⟩⟩ :=
    ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_pointwise f 0).mp h).2 (f.base x)
  have hZ : IsZero (Stacks.Morphisms.pushforwardStructureSheaf (f ∣_ U)) :=
    (isZero_free_fin_zero U.toScheme).of_iso
      ((Stacks.Morphisms.pushforwardStructureSheafRestrictIso f U).symm ≪≫ ε)
  have h2 := Functor.map_isZero
    (_root_.SheafOfModules.evaluation (R := U.toScheme.ringCatSheaf) (Opposite.op ⊤)) hZ
  rw [ModuleCat.isZero_iff_subsingleton] at h2
  have : Nonempty ((f ∣_ U) ⁻¹ᵁ (⊤ : U.toScheme.Opens)) := ⟨⟨⟨x, hU⟩, trivial⟩⟩
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ ⊤))
  exact hab (@Subsingleton.elim _ h2 a b)

/-- **A finite flat surjection from a nonempty scheme onto a connected locally Noetherian scheme
is finite locally free of constant positive degree.** -/
theorem exists_pos_isFiniteLocallyFreeOfRank_of_isFinite_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian S] [PreconnectedSpace S]
    [Nonempty X] : ∃ r : ℕ, 0 < r ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r := by
  have : Stacks.Morphisms.IsFiniteLocallyFree f :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian f).2
      ⟨‹_›, ‹_›⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty S := ⟨f.base x⟩
  obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_of_preconnectedSpace f
  exact ⟨r, pos_of_isFiniteLocallyFreeOfRank_of_surjective f hr, hr⟩

end Degree

/-! ### The statement used in the proof of axiom (A6) -/

section Projection

variable {k : Type u} [Field k]

/-- **The finite syntomic projection to projective space and its de Rham trace** (Stacks,
Proposition 0FWD, proof of axiom (A6) for `X` irreducible). Let `k` be an algebraically closed
field of characteristic zero and `X` an irreducible scheme, smooth and projective over `k`, of
relative dimension `d`. Then there is a finite, surjective, syntomic morphism
`f : X ⟶ 𝐏^d_k = Proj k[T₀, …, T_d]` over `k` and a positive integer `e` such that `f` is finite
locally free of degree `e` and, in every degree `n`, there is a map
`Θ_n : H^n_{dR}(X/k) ⟶ H^n_{dR}(𝐏^d_k/k)` with `Θ_n(f^* x) = e • x` for all `x`, and the pullback
`f^* : H^n_{dR}(𝐏^d_k/k) ⟶ H^n_{dR}(X/k)` is injective. -/
theorem exists_isFinite_syntomic_toProjectiveSpace_deRhamCohomologyTrace [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IrreducibleSpace X] (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hproj : IsProjective sX) (d : ℕ) (hd : RelativeDimension sX d) :
    ∃ (f : X ⟶ AlgebraicGeometry.Proj (polyGrading k d)) (hf : f ≫ projToSpecCoeff k d = sX),
      IsFinite f ∧ Surjective f ∧ Syntomic f ∧
      ∃ e : ℕ, 0 < e ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank f e ∧ ∀ n : ℤ,
        (∃ Θ : Scheme.Hom.deRhamCohomology sX n ⟶
            Scheme.Hom.deRhamCohomology (projToSpecCoeff k d) n,
          ∀ x : Scheme.Hom.deRhamCohomology (projToSpecCoeff k d) n,
            Θ.hom ((Scheme.Hom.deRhamCohomologyPullback f (projToSpecCoeff k d) sX (𝟙 _)
              (hf.trans (Category.comp_id sX).symm) n).hom x) = e • x) ∧
        Function.Injective (Scheme.Hom.deRhamCohomologyPullback f (projToSpecCoeff k d) sX
          (𝟙 _) (hf.trans (Category.comp_id sX).symm) n).hom := by
  obtain ⟨f, hf, hfin, hsurj, hflat, hsyn, -⟩ :=
    exists_isFinite_syntomic_toProjectiveSpace_of_relativeDimension sX hproj d hd
  have : SmoothOfRelativeDimension d (projToSpecCoeff k d) :=
    smoothOfRelativeDimension_projToSpecCoeff k d
  have : Smooth (projToSpecCoeff k d) := SmoothOfRelativeDimension.smooth d _
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading k d)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff k d)
  obtain ⟨e, he, hrank⟩ := exists_pos_isFiniteLocallyFreeOfRank_of_isFinite_flat f
  have hf' := hf.trans (Category.comp_id sX).symm
  exact ⟨f, hf, hfin, hsurj, hsyn, e, he, hrank, fun n =>
    ⟨exists_deRhamCohomologyTrace f (projToSpecCoeff k d) hsyn e sX hf' n,
    injective_deRhamCohomologyPullback_of_charZero f hsyn e (projToSpecCoeff k d) sX hf' he n⟩⟩

end Projection

end Stacks.WeilDeRham

end
