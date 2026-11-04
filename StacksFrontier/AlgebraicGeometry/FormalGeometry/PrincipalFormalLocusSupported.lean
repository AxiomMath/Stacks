module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAlgebraizationII
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocus

/-!
# The comparison map for a module supported on the formal locus

Let `I, 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a coherent
module on `U` all of whose associated points lie in `V(I)`. Then the support of `F` lies in
`U ∩ V(I)`, so some power `Iⁿ 𝒪_U` kills `F` (Stacks 01Y9), and the comparison map

`colim_V Γ(V, F) ⟶ lim Γ(U, F / Iᵐ F)`

of Stacks 0EG2 is an isomorphism. This is the sentence "the lemma holds trivially for any
coherent `𝒪_U`-module supported on `V(f) ∩ U`" of the first proof of Stacks 0H49, for an
arbitrary ideal in place of `(f)`.

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_associatedPoints_le` — the comparison map is an
  isomorphism for a coherent module whose associated points all lie in `V(I)`.

## Implementation notes

Injectivity is `Stacks.Algebraization.mono_comparisonMap`. For surjectivity a formal section is
realized on `U` itself: once `Iᴺ F = 0` the projections `F ⟶ F / Iᵐ F` are isomorphisms for all
`m ≥ N` (`Stacks.Algebraization.isIso_cokernel_π_of_idealPowerMultiple_eq_bot`), so the
component of the formal section at `N` lifts uniquely to a section of `F` on `U`, and that
section reduces to every other component, below `N` along the transition maps and above `N`
because the transition maps there are bijective on sections.

## References

* [Stacks Project, Tag 0H49](https://stacks.math.columbia.edu/tag/0H49)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-- **The comparison map of a module supported on the formal locus is an isomorphism.** For a
coherent module `F` on `U = Spec(A) ∖ V(𝔞)` over a Noetherian ring whose associated points all
lie in `V(I)`, the comparison map `colim_V Γ(V, F) ⟶ lim Γ(U, F / Iⁿ F)` of Stacks 0EG2 is an
isomorphism. -/
theorem isIso_comparisonMap_of_associatedPoints_le [IsNoetherianRing A]
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hAss : ∀ x ∈ Stacks.Divisors.associatedPoints F, I ≤ x.1.asIdeal) :
    IsIso (comparisonMap A I a F) := by
  set J := idealSheafNearVanishing A I a with hJ
  have hqf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := hqf.1
  have : F.IsFiniteType := hqf.2
  have hsupp : SheafOfModules.supp F ⊆ (J.support : Set (complementZeroLocus A a : Scheme)) := by
    rw [supp_eq_closure_associatedPoints]
    exact closure_minimal (fun x hx => mem_support_baseIdealSheaf I _ (hAss x hx))
      J.support.isClosed
  obtain ⟨N, hN⟩ := (AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset F J).2 hsupp
  have hiso : ∀ m, N ≤ m → IsIso (adicProj J F (op m)) := fun m hm =>
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot J m F (idealPowerMultiple_eq_bot_of_le hN hm)
  have hbij : ∀ m, N ≤ m → Function.Bijective
      (ConcreteCategory.hom ((adicProj J F (op m)).app ⊤)) := fun m hm => by
    have := hiso m hm
    exact ConcreteCategory.bijective_of_isIso ((adicProj J F (op m)).app ⊤)
  have hres : ∀ n : ℕᵒᵖ, resNearVanishing A I a F (FormalSectionsII.topNearVanishing A I
      a) n = 𝟙 _ :=
    fun n => (congrArg ((quotientSystemNearVanishing A I a F).obj n).presheaf.map
      (Subsingleton.elim _ _)).trans (((quotientSystemNearVanishing A I a F).obj
          n).presheaf.map_id _)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (mono_comparisonMap A I a F), ?_⟩
  rw [surjective_comparisonMap_iff]
  intro s
  obtain ⟨t, ht⟩ := (hbij N le_rfl).2 (ConcreteCategory.hom (limit.π (formalSections A I a F) (op
      N)) s)
  let T := FormalSectionsII.topNearVanishing A I a
  let t' : ToType ((sectionsNearVanishing A I a F).obj T) := t
  refine ⟨T, t', Concrete.limit_ext _ _ _ fun n => ?_⟩
  have hR : ∀ z, ConcreteCategory.hom (resNearVanishing A I a F T n) z = z := fun z =>
    (ConcreteCategory.congr_hom (hres n) z).trans rfl
  have hinv : ∀ y, ConcreteCategory.hom (inv (resNearVanishing A I a F T n)) y = y := fun y =>
    (hR _).symm.trans (by rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]; rfl)
  have hc : ConcreteCategory.hom (limit.π (formalSections A I a F) n)
      (ConcreteCategory.hom (comparisonAt A I a F T) t') =
      ConcreteCategory.hom (inv (resNearVanishing A I a F T n))
        (ConcreteCategory.hom (projNearVanishing A I a F T n) t') := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, comparisonAt_π]
  rw [hc, hinv]
  show ConcreteCategory.hom ((adicProj J F n).app ⊤) t = _
  rcases le_total n.unop N with hn | hn
  · have h : op N ⟶ n := (homOfLE hn).op
    rw [← adicProj_comp_map J F h, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ht,
      ← limit.w (formalSections A I a F) h, ConcreteCategory.comp_apply]
    rfl
  · have h : n ⟶ op N := (homOfLE hn).op
    obtain ⟨t', ht'⟩ := (hbij n.unop hn).2 (ConcreteCategory.hom (limit.π (formalSections A I a F)
        n) s)
    have hcomp : ∀ y : Γ(F, ⊤), ConcreteCategory.hom ((adicProj J F (op N)).app ⊤) y =
        ConcreteCategory.hom ((formalSections A I a F).map h)
          (ConcreteCategory.hom ((adicProj J F n).app ⊤) y) := fun y =>
      (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤)
        (adicProj_comp_map J F h)) y).symm
    have htt' : t = t' := by
      refine (hbij N le_rfl).1 ?_
      rw [hcomp t', ht', ht]
      exact (ConcreteCategory.congr_hom (limit.w (formalSections A I a F) h) s).symm
    rw [htt']
    exact ht'

end Stacks.Algebraization

end
