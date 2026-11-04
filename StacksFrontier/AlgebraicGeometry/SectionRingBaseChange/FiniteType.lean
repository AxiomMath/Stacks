module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FiniteType
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Generation

/-!
# The truncated section ring of an ample invertible module over a Noetherian ring

Let `R` be a Noetherian ring, `f : Y ⟶ Spec R` proper and `ℳ` an ample invertible `𝒪_Y`-module.
For every positive cut `e`, the graded ring

`R ⊕ ⨁_{d ≥ e} Γ(Y, ℳ^{⊗ d})`

of sections of the tail truncation of `f_*(⨁_{n ∈ ℤ} ℳ^{⊗ n})` is a finitely generated
`R`-algebra.  This is the finite generation of the source's algebra
`B = R'_0 ⊕ ⨁_{d ≥ max(d_0, d'_0)} (A'_0)_d` in step (a) of the proof of [Stacks, Tag 0D4F], and
it is proved as the source proves the finite generation of the section ring in
[Stacks, Tag 0B5T] (1): each `Γ(Y, ℳ^{⊗ d})` is a finite `R`-module ([Stacks, Tag 02O5]), and
above a bound every section of `ℳ^{⊗ d}` is a combination of products of sections of `ℳ^{⊗ n}`
and `ℳ^{⊗ (d - n)}`, by Serre vanishing for the kernel of a presentation of `ℳ^{⊗ n}`
(`Stacks.AlgebraicGeometry.SectionRingBaseChange.exists_forall_eq_sum_mul`).

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.finiteType_tailAlgebra_strHom`.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.SectionAlgebra

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y M]

include f in
/-- **Every homogeneous piece of the truncated section ring is a finite module** over the
functions on the base: in degree zero it is the base itself, in the band it vanishes, and in the
tail it is `Γ(Y, ℳ^{⊗ d})`, finite by [Stacks, Tag 02O5]. -/
theorem moduleFinite_tailAlgebra_sectionPieces (e : ℕ) (he : 0 < e) (d : ℕ) :
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((tailAlgebra f M e he).sectionPieces ⊤ d) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases h0 : d = 0
  · subst h0
    obtain ⟨-, hsurj⟩ := bijective_smul_one_tail _ e he _ _ (⊤ : (Spec (CommRingCat.of R)).Opens)
    exact Module.Finite.of_surjective
      (LinearMap.toSpanSingleton Γ(Spec (CommRingCat.of R), ⊤) _
        ((tailAlgebra f M e he).one ⊤)) hsurj
  · by_cases hd : e ≤ d
    · have hcoh : ((Scheme.Modules.pushforward f).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece (d : ℤ))).IsCoherent := by
        have := isInvertibleModule_laurentPowers_piece M (d : ℤ)
        have := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y
          ((Stacks.RelativeAmple.laurentPowers M).piece (d : ℤ))
        exact AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _
      obtain ⟨hqc, hft⟩ :=
        Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
          ((Scheme.Modules.pushforward f).obj
            ((Stacks.RelativeAmple.laurentPowers M).piece (d : ℤ)))
      have := hqc
      have := hft
      have := AlgebraicGeometry.moduleFinite_sections_on_affine
        ((Scheme.Modules.pushforward f).obj ((Stacks.RelativeAmple.laurentPowers M).piece (d : ℤ)))
        ⊤ (isAffineOpen_top _)
      let ℓ := Scheme.Modules.sectionsLinearMap (X := Spec (CommRingCat.of R))
        (M := (Scheme.Modules.pushforward f).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece (d : ℤ)))
        (N := tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          f (Stacks.RelativeAmple.laurentPowers M)) e (d : ℤ))
        (eqToHom (tailPiece_eq_piece
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
            f (Stacks.RelativeAmple.laurentPowers M)) e he
          (show (e : ℤ) ≤ (d : ℤ) by omega)).symm) ⊤
      exact Module.Finite.of_surjective ℓ (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece
        (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          f (Stacks.RelativeAmple.laurentPowers M)) e he
            (show (e : ℤ) ≤ (d : ℤ) by omega)).symm) (op ⊤)).2
    · have : Subsingleton ((tailAlgebra f M e he).sectionPieces ⊤ d) :=
        subsingleton_of_forall_eq 0 fun z => eq_zero_of_tailPiece _ e
          (show (d : ℤ) ≠ 0 by omega) (show ¬ (e : ℤ) ≤ (d : ℤ) by omega) _ z
      exact Module.Finite.of_finite

include f in
/-- **The truncated section ring of an ample invertible module on a scheme proper over a
Noetherian ring is a finitely generated algebra.** -/
theorem finiteType_tailAlgebra_strHom (hM : Stacks.Ample.IsAmple Y M) (e : ℕ) (he : 0 < e) :
    ((tailAlgebra f M e he).strHom ⊤).FiniteType := by
  classical
  obtain ⟨n, I, _, s, N, hen, hgen⟩ := exists_forall_eq_sum_mul f M hM e
  set D := n + max e N with hD
  -- Finitely many generators of each piece of degree below `D`.
  have hfin := moduleFinite_tailAlgebra_sectionPieces f M e he
  choose r g hg using fun d : Fin D => Module.Finite.exists_fin (R := Γ(Spec (CommRingCat.of R), ⊤))
    (M := (tailAlgebra f M e he).sectionPieces ⊤ d)
  let x : (Σ d : Fin D, Fin (r d)) → (tailAlgebra f M e he).sectionRing ⊤ := fun p =>
    DirectSum.of ((tailAlgebra f M e he).sectionPieces ⊤) p.1 (g p.1 p.2)
  let S := Algebra.adjoin ↥((tailAlgebra f M e he).grading ⊤ 0) (Set.range x)
  have m0 : ∀ c : Γ(Spec (CommRingCat.of R), ⊤), (tailAlgebra f M e he).strHom ⊤ c ∈ S := fun c =>
    S.algebraMap_mem ⟨(tailAlgebra f M e he).strHom ⊤ c, (tailAlgebra f M e he).strHom_mem ⊤ c⟩
  have m1 : ∀ d : Fin D, ∀ y : (tailAlgebra f M e he).sectionPieces ⊤ d,
      DirectSum.of ((tailAlgebra f M e he).sectionPieces ⊤) d y ∈ S := by
    intro d y
    have hy : y ∈ Submodule.span Γ(Spec (CommRingCat.of R), ⊤) (Set.range (g d)) :=
      hg d ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Algebra.subset_adjoin ⟨⟨d, i⟩, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add z z' _ _ hz hz' => rw [map_add]; exact S.add_mem hz hz'
    | smul c z _ hz =>
      rw [← (tailAlgebra f M e he).strHom_mul_of ⊤ c z]
      exact S.mul_mem (m0 c) hz
  have key : ∀ d (y : (tailAlgebra f M e he).sectionPieces ⊤ d),
      DirectSum.of ((tailAlgebra f M e he).sectionPieces ⊤) d y ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y
      by_cases hd : d < D
      · exact m1 ⟨d, hd⟩ y
      · obtain ⟨k, rfl⟩ : ∃ k, d = n + k := ⟨d - n, by omega⟩
        have hk : max e N ≤ k := by omega
        obtain ⟨b, hb⟩ := exists_tailIncl_eq _ e he _ _ ⊤ (n + k) (by omega) y
        rw [← hb]
        obtain ⟨a, ha⟩ := hgen k (le_trans (le_max_right _ _) hk) b
        rw [ha]
        erw [map_sum]
        refine Subalgebra.sum_mem _ fun i _ => ?_
        have hmul := tailIncl_mul
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
            f (Stacks.RelativeAmple.laurentPowers M)) e he
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.isCommutative_pushforwardGradedAlgebra
            _ _ (Stacks.RelativeAmple.isCommutative_laurentPowers M))
          (Stacks.RelativeAmple.isQuasicoherent_pushforward_laurentPowers f M) ⊤ n k hen (by omega)
          ((s i).val (op ⊤)) (a i)
        refine (congrArg (· ∈ S) hmul).mp (S.mul_mem ?_ ?_)
        · exact ih n (by omega) _
        · exact ih k (by omega) _
  exact SheafGradedAlgebra.finiteType_strHom_of_adjoin_eq_top (tailAlgebra f M e he) ⊤
    (bijective_smul_one_tail _ e he _ _ ⊤) x
    (eq_top_iff.mpr fun z _ => DirectSum.induction_on z S.zero_mem key fun _ _ => S.add_mem)

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
