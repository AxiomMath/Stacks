module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType

/-!
# Relative completions are topologically of finite type

Being topologically of finite type is a property of the second map in a composition: a dense
polynomial presentation over a ring `A` is in particular a dense polynomial presentation over
any ring receiving a map from `A`.  The relative completion of `A'` over `A` receives `A'` with
dense image, because the completion carries the inverse-limit topology of the discrete quotients
and a point of it is matched by a single element of `A'` in any finite set of them.  Combined,
these show that the canonical map from `A` to the completion of `A'` over `A` is topologically
of finite type whenever `A →+* A'` is étale.

## Main results

* `TopologicalRing.isTopologicallyOfFiniteType_of_comp`: if a composite `ρ ∘ ψ` is topologically
  of finite type, then so is `ρ`.
* `TopologicalRing.isTopologicallyOfFiniteType_canonicalMap_of_etale`: the canonical map to the
  completion of `A'` over `A` is topologically of finite type when `A →+* A'` is étale.

## References

* [Stacks Project, Tag 0ANS](https://stacks.math.columbia.edu/tag/0ANS)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
-/

@[expose] public section

namespace TopologicalRing

universe u

section Comp

/-- Being topologically of finite type only depends on the second map of a composition: a
polynomial algebra over `A` with dense image in `C` can be replaced by a polynomial algebra
over `B` in the same number of variables, by evaluating the variables at the same points. -/
public theorem isTopologicallyOfFiniteType_of_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [TopologicalSpace C]
    (ψ : A →+* B) (ρ : B →+* C)
    (h : TopologicalRing.IsTopologicallyOfFiniteType (ρ.comp ψ)) :
    TopologicalRing.IsTopologicallyOfFiniteType ρ := by
  obtain ⟨n, F, hFC, hFdense⟩ := h
  refine ⟨n, MvPolynomial.eval₂Hom ρ (fun i ↦ F (MvPolynomial.X i)), ?_, ?_⟩
  · exact RingHom.ext (MvPolynomial.eval₂Hom_C ρ (fun i ↦ F (MvPolynomial.X i)))
  · have hFG : F = (MvPolynomial.eval₂Hom ρ (fun i ↦ F (MvPolynomial.X i))).comp
        (MvPolynomial.map ψ) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · rw [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
        exact DFunLike.congr_fun hFC a
      · rw [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
    refine Dense.mono ?_ hFdense
    rintro _ ⟨p, rfl⟩
    exact ⟨MvPolynomial.map ψ p, (DFunLike.congr_fun hFG p).symm⟩

end Comp

namespace CompletionOver

section Lift

variable {A A' : Type u} [CommRing A] [TopologicalSpace A] [CommRing A']

/-- A point of the relative completion agrees with the class of a single element of `A'` in any
prescribed finite set of the defining quotients. -/
private theorem exists_approximation (g : A →+* A')
    (x : TopologicalRing.CompletionOver g)
    (s : Finset (TopologicalRing.WeakIdealOfDefinitionIndex A)) :
    ∃ a : A', ∀ K ∈ s,
      Ideal.Quotient.mk (TopologicalRing.extendedIdeal g K) a = x.1 K := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨J, _⟩
  · exact ⟨0, by simp⟩
  · obtain ⟨L, -, hLs⟩ := exists_weakIdeal_le_finset J s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.1 L)
    refine ⟨a, fun K hK ↦ ?_⟩
    calc Ideal.Quotient.mk (TopologicalRing.extendedIdeal g K) a
        = TopologicalRing.transitionMap g (hLs K hK)
            (Ideal.Quotient.mk (TopologicalRing.extendedIdeal g L) a) :=
          (Ideal.Quotient.factor_mk (Ideal.map_mono (hLs K hK)) a).symm
      _ = x.1 K := by
        rw [ha]
        exact x.2 L K (hLs K hK)

/-- The map `ofTarget g` has dense image: the relative completion carries the inverse-limit
topology, so a point is approximated by any element of `A'` matching it in finitely many of
the defining quotients. -/
@[ega "0 7.2.1" "Density clause"]
private theorem denseRange_ofTarget_discreteQuotients (g : A →+* A') :
    DenseRange (ofTarget g) := by
  let _ (J : TopologicalRing.WeakIdealOfDefinitionIndex A) :
      TopologicalSpace (A' ⧸ TopologicalRing.extendedIdeal g J) := ⊥
  refine fun x ↦ mem_closure_iff.mpr fun U hU hxU ↦ ?_
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hxV : x.1 ∈ V := by simpa [← hVU] using hxU
  obtain ⟨s, W, hW, hsub⟩ := isOpen_pi_iff.mp hV x.1 hxV
  obtain ⟨a, ha⟩ := exists_approximation g x s
  refine ⟨ofTarget g a, ?_, ⟨a, rfl⟩⟩
  rw [← hVU]
  refine hsub fun K hK ↦ ?_
  change Ideal.Quotient.mk (extendedIdeal g K) a ∈ W K
  rw [ha K hK]
  exact (hW K hK).2

end Lift

end CompletionOver

section Etale

/-- For an étale ring map `g : A →+* A'`, the canonical map from `A` to the completion of `A'`
over `A` is topologically of finite type: an étale map is of finite type, so `A'` is a quotient
of a polynomial algebra over `A` in finitely many variables, and `A'` is dense in the relative
completion. -/
public theorem isTopologicallyOfFiniteType_canonicalMap_of_etale
    {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing A'] (g : A →+* A') (hg : g.Etale) :
    TopologicalRing.IsTopologicallyOfFiniteType
      (TopologicalRing.CompletionOver.canonicalMap g) := by
  obtain ⟨-, -, hfp⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp hg
  let _ : Algebra A A' := g.toAlgebra
  have hft : Algebra.FiniteType A A' := RingHom.FiniteType.of_finitePresentation hfp
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  have hsC (a : A) : s (MvPolynomial.C a) = g a := s.commutes a
  refine ⟨n, (CompletionOver.ofTarget g).comp s.toRingHom, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    change CompletionOver.ofTarget g (s (MvPolynomial.C a)) = _
    rw [hsC a]
    exact DFunLike.congr_fun (CompletionOver.ofTarget_comp g) a
  · refine Dense.mono ?_ (CompletionOver.denseRange_ofTarget_discreteQuotients g)
    rintro _ ⟨a, rfl⟩
    obtain ⟨p, rfl⟩ := hs a
    exact ⟨p, rfl⟩

end Etale

end TopologicalRing

end
