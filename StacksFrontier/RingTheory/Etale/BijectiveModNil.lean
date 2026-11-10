module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.TranslatedSmoothModel

/-!
# Lifting along a nil ideal, and étale maps which are bijective modulo a nil ideal

Mathlib's lifting properties of formally smooth and formally unramified algebras are stated for a
*nilpotent* ideal. For an algebra of finite presentation (respectively of finite type) they hold
along an arbitrary *nil* ideal, that is an ideal contained in the nilradical: only finitely many
elements of the ideal are involved in a given lifting problem, and the ideal they generate is
finitely generated and nil, hence nilpotent. The lifting statement is
`Algebra.FormallySmooth.exists_lift_of_le_nilradical`; this file adds the uniqueness statement.

As a consequence an étale algebra `E → F` whose reduction modulo a nil ideal `I` of `E` is
bijective is itself bijective: the reduction gives an `E`-algebra map `F → E ⧸ I`, which lifts to
a retraction `F → E` of the structure map, and the composite `F → E → F` is an `E`-algebra
endomorphism of `F` agreeing with the identity modulo the nil ideal `I F`, hence equal to it.

## Main results

* `Algebra.FormallyUnramified.ext_of_le_nilradical`: uniqueness of lifts along a nil ideal, for a
  formally unramified algebra of finite type.
* `Algebra.Etale.bijective_algebraMap_of_bijective_quotientMap`: an étale algebra whose
  reduction modulo a nil ideal of the base is bijective is bijective.
-/

@[expose] public section

open Function

universe u v w

namespace Ideal

variable {C : Type w} [CommRing C]

/-- A finitely generated ideal contained in the nilradical is nilpotent. -/
theorem FG.isNilpotent_of_le_nilradical {I : Ideal C} (hfg : I.FG) (hI : I ≤ nilradical C) :
    IsNilpotent I :=
  hfg.isNilpotent_iff_le_nilradical.mpr hI

/-- The ideal spanned by finitely many elements of a nil ideal is nilpotent. -/
theorem isNilpotent_span_of_subset_of_le_nilradical {I : Ideal C} (hI : I ≤ nilradical C)
    {s : Set C} (hs : s.Finite) (hsI : s ⊆ I) : IsNilpotent (Ideal.span s) :=
  FG.isNilpotent_of_le_nilradical ⟨hs.toFinset, by simp⟩
    ((Ideal.span_le.mpr hsI).trans hI)

end Ideal

namespace Algebra

variable {E : Type u} {F : Type v} [CommRing E] [CommRing F] [Algebra E F]
variable {C : Type w} [CommRing C] [Algebra E C]

/-- **Uniqueness of lifts along a nil ideal.** Two maps out of a formally unramified algebra of
finite type which agree modulo an ideal contained in the nilradical are equal. -/
theorem FormallyUnramified.ext_of_le_nilradical [FormallyUnramified E F] [FiniteType E F]
    (I : Ideal C) (hI : I ≤ nilradical C) {g₁ g₂ : F →ₐ[E] C}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ := by
  classical
  obtain ⟨s, hs⟩ := FiniteType.out (R := E) (A := F)
  let I₀ : Ideal C := Ideal.span ((fun x => g₁ x - g₂ x) '' (s : Set F))
  have hI₀ : IsNilpotent I₀ := by
    refine Ideal.isNilpotent_span_of_subset_of_le_nilradical hI (s.finite_toSet.image _) ?_
    rintro _ ⟨x, -, rfl⟩
    exact Ideal.Quotient.eq.mp (H x)
  refine FormallyUnramified.ext I₀ hI₀ (g₁ := g₁) (g₂ := g₂) fun x => ?_
  have key : (Ideal.Quotient.mkₐ E I₀).comp g₁ = (Ideal.Quotient.mkₐ E I₀).comp g₂ := by
    refine AlgHom.ext_of_adjoin_eq_top hs fun y hy => ?_
    simp only [AlgHom.coe_comp, comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨y, hy, rfl⟩)
  simpa using congrArg (fun q => q x) key

/-- The image of a nil ideal under a ring homomorphism generates a nil ideal. -/
theorem map_le_nilradical_of_le_nilradical {I : Ideal E} (hI : I ≤ nilradical E) :
    I.map (algebraMap E F) ≤ nilradical F := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact mem_nilradical.mpr ((mem_nilradical.mp (hI hx)).map (algebraMap E F))

/-- **An étale algebra which is bijective modulo a nil ideal of the base is bijective.** If
`E → F` is étale, `I` is an ideal of `E` contained in the nilradical and the induced map
`E ⧸ I → F ⧸ I F` is bijective, then `E → F` is bijective. -/
theorem Etale.bijective_algebraMap_of_bijective_quotientMap [Etale E F] (I : Ideal E)
    (hI : I ≤ nilradical E)
    (h : Bijective (Ideal.quotientMap (I.map (algebraMap E F)) (algebraMap E F)
      Ideal.le_comap_map)) :
    Bijective (algebraMap E F) := by
  classical
  set J : Ideal F := I.map (algebraMap E F)
  let e : (E ⧸ I) ≃+* (F ⧸ J) := RingEquiv.ofBijective _ h
  have he : ∀ a : E, e (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap E F a) :=
    fun a => rfl
  -- the reduction `F → E ⧸ I`, an `E`-algebra map
  let g : F →ₐ[E] E ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk J)
      commutes' := fun a => by
        change e.symm (Ideal.Quotient.mk J (algebraMap E F a)) = _
        rw [← he, RingEquiv.symm_apply_apply]
        rfl }
  obtain ⟨r, hr⟩ := FormallySmooth.exists_lift_of_le_nilradical I hI g
  have hr' : ∀ y : F, Ideal.Quotient.mk I (r y) = e.symm (Ideal.Quotient.mk J y) := fun y =>
    congrArg (fun q => q y) hr
  have hinj : Injective (algebraMap E F) := by
    intro a b hab
    have := congrArg r hab
    rwa [r.commutes, r.commutes] at this
  have hφ : (Algebra.ofId E F).comp r = AlgHom.id E F := by
    refine FormallyUnramified.ext_of_le_nilradical J (map_le_nilradical_of_le_nilradical hI)
      fun x => ?_
    change Ideal.Quotient.mk J (algebraMap E F (r x)) = Ideal.Quotient.mk J x
    rw [← he, hr', RingEquiv.apply_symm_apply]
  exact ⟨hinj, fun y => ⟨r y, congrArg (fun q => q y) hφ⟩⟩

end Algebra

end
