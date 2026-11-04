module

public import Mathlib.NumberTheory.Real.Irrational
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RationalGaloisQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RationalGaloisQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Radicial
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The Galois quotient of the spectrum of `ℚ̄` is not radicial over `Spec ℚ`

The fppf sheaf quotient `Spec ℚ̄ / Gal(ℚ̄/ℚ)` of
`AlgebraicGeometry.RationalGaloisQuotient.galoisQuotient` is an algebraic space over `Spec ℚ`,
and its structure morphism to `Spec ℚ` is universally injective
(`AlgebraicGeometry.RationalGaloisQuotient.universallyInjective_galoisQuotientToBase`) but not
radicial. So for morphisms of algebraic spaces, unlike for morphisms of schemes, universal
injectivity is strictly weaker than radicialness: this is **Stacks 0483**.

## Main results

* `AlgebraicGeometry.RationalGaloisQuotient.not_isRadicial_galoisQuotientToBase`: the
  structure morphism of the quotient is not radicial, the second half of **Stacks 0483**.
* `AlgebraicGeometry.RationalGaloisQuotient.universallyInjective_and_not_isRadicial`: the two
  halves of **Stacks 0483** together, over a big fppf site containing the two spectra.
* `AlgebraicGeometry.RationalGaloisQuotient.exists_universallyInjective_not_isRadicial`:
  **Stacks 0483** with no site assumed, which is the non-equivalence the example asserts:
  a universally injective morphism of algebraic spaces which is not radicial exists.

## Implementation notes

Failure of radicialness is stated at the quotient *as an algebraic space*, the radicial
condition of Tag 0481 taking the algebraicity of the source and of the target as explicit
arguments. The radicial condition is refuted at the field `ℚ` itself, tested on the terminal
object of the site and the identity point of the base, for which the fibre is the quotient:
`ℚ` is perfect, so a purely inseparable extension of `ℚ` is `ℚ`, and the reduction of that
fibre is neither pointless — the projection of `Spec ℚ̄` provides a point, and the inclusion of
the reduction is surjective on points — nor the spectrum of a copy of `ℚ`, because a field
algebraic over `ℚ` carrying a point of the quotient is a copy of `ℚ̄` or of the real algebraic
numbers, and neither of those is `ℚ`, both containing a square root of two.

## References

* [Stacks Project, Tag 0481](https://stacks.math.columbia.edu/tag/0481)
* [Stacks Project, Tag 0483](https://stacks.math.columbia.edu/tag/0483)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace RationalGaloisQuotient

variable (B : BigFppfSite.{0}) (hS : B.Contains base) (hU : B.Contains cover.left)

/-! ### Failure of radicialness

The radicial condition of Tag 0481 asks the reduction of the fibre over a field-valued point
to be either pointless or the spectrum of a purely inseparable extension of that field. Over
`ℚ`, which is perfect, the second alternative means the spectrum of a copy of `ℚ`; the three
lemmas of this block rule a copy of `ℚ` out, by exhibiting a square root of two in each of
the two fields that a field-valued point of the quotient can have. -/

/-- No rational number squares to two. -/
private theorem rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro hq
  have h2 : (q : ℝ) ^ 2 = 2 := by exact_mod_cast congrArg (fun r : ℚ ↦ (r : ℝ)) hq
  refine irrational_sqrt_two ⟨|q|, ?_⟩
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, h2]

/-- Transport surjectivity of the structure map of a `ℚ`-algebra along an isomorphism. -/
private theorem surjective_algebraMap_of_algEquiv {L M : Type} [Field L] [Field M]
    [Algebra ℚ L] [Algebra ℚ M] (ε : L ≃ₐ[ℚ] M)
    (h : Function.Surjective (algebraMap ℚ L)) :
    Function.Surjective (algebraMap ℚ M) := by
  intro y
  obtain ⟨q, hq⟩ := h (ε.symm y)
  exact ⟨q, by rw [← ε.commutes q, hq, ε.apply_symm_apply]⟩

/-- `ℚ̄` is not a copy of `ℚ`: being algebraically closed it contains a square root of
two, and no rational number squares to two. -/
private theorem not_surjective_algebraMap_algebraicClosure :
    ¬ Function.Surjective (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  intro hs
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  obtain ⟨q, rfl⟩ := hs z
  refine rat_sq_ne_two q ?_
  have h : algebraMap ℚ (AlgebraicClosure ℚ) (q ^ 2) =
      algebraMap ℚ (AlgebraicClosure ℚ) 2 := by
    rw [map_pow, hz]
    simp
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective h

/-- The square root of two is algebraic over `ℚ`, being a root of the monic polynomial
`X ^ 2 - 2`. -/
private theorem isAlgebraic_rat_sqrt_two : IsAlgebraic ℚ (Real.sqrt 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2,
    (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)).ne_zero, ?_⟩
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [h]

/-- The field of real algebraic numbers is not a copy of `ℚ`: it contains the square root of
two, which is a real number algebraic over `ℚ`. -/
private theorem not_surjective_algebraMap_realAlgebraic :
    ¬ Function.Surjective (algebraMap ℚ (algebraicClosure ℚ ℝ)) := by
  intro hs
  obtain ⟨q, hq⟩ := hs ⟨Real.sqrt 2, mem_algebraicClosure_iff.mpr isAlgebraic_rat_sqrt_two⟩
  refine irrational_sqrt_two ⟨q, ?_⟩
  exact congrArg (fun x : algebraicClosure ℚ ℝ ↦ (x : ℝ)) hq

attribute [local instance] Space.pointTopology

/-- The reduced closed subspace of an algebraic space on *all* of its points has a point as
soon as the space has one: the point set of the subspace is the whole of the point set of the
space by Tag 03IQ, so the inclusion is surjective on points. -/
private theorem not_isEmpty_points_reducedClosedSubspace
    {P : (BigFppfOver B base hS)ᵒᵖ ⥤ Type 0} (hP : IsAlgebraicSpace B base hS P)
    (x : Space.points B base hS P) :
    ¬ IsEmpty (Space.points B base hS
      (Space.reducedClosedSubspace B base hS P hP Set.univ isClosed_univ).toFunctor) := by
  intro hempty
  have hr :=
    Space.range_pointsMap_ι_reducedClosedSubspace B base hS P hP Set.univ isClosed_univ
  obtain ⟨z, -⟩ := hr.symm.subset (Set.mem_univ x)
  exact hempty.false z

/-- A subfunctor of `P` isomorphic to the presheaf represented by an object `U` has a section
over `U`, namely the one corresponding to the identity of `U`; pushing it into `P` and along a
morphism `P ⟶ X` gives a section of `X` over `U`. -/
private theorem nonempty_obj_of_subfunctor_iso_yoneda
    {P X : (BigFppfOver B base hS)ᵒᵖ ⥤ Type 0} {Z : Subfunctor P}
    {U : BigFppfOver B base hS} (e : Z.toFunctor ≅ yoneda.obj U) (α : P ⟶ X) :
    Nonempty (X.obj (Opposite.op U)) :=
  ⟨α.app _ (Z.ι.app _ (e.inv.app (Opposite.op U) (𝟙 U)))⟩

section NotRadicial

variable [HasSheafify (BigFppfOver.topology B base hS) (Type 0)]

/-- The canonical `ℚ̄`-valued point of the Galois quotient: the image of the identity of
`Spec ℚ̄` under the projection onto the quotient. -/
private noncomputable def coverFieldPoint :
    Space.FieldValuedPoint B base hS (galoisQuotient B hS hU) where
  carrier := AlgebraicClosure ℚ
  contained := hU
  toBase := cover.hom
  value := (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B base hS)
      (Over.post B.inclusion)
      (Space.actionRelation (Space.underlyingOver B hS (siteCover B hS hU)) galoisGroup
        (galoisAction B hS hU))).app (Opposite.op (siteCover B hS hU))
    (𝟙 (Space.underlyingOver B hS (siteCover B hS hU)))

/-- **Stacks 0483.** The structure morphism of the Galois quotient of `Spec ℚ̄` to `Spec ℚ` is
*not* radicial.

Radicialness is tested at the field `ℚ` itself, on the terminal object of the site with the
identity point of the base, so that the fibre is the quotient itself. Its reduction is not
pointless, because the `ℚ̄`-valued point coming from the projection of `Spec ℚ̄` survives to
the reduction; and it is not the spectrum of a purely inseparable extension `L` of `ℚ`
either: `ℚ` is perfect, so the structure map `ℚ → L` is surjective, while a field algebraic
over `ℚ` carrying a point of the quotient is a copy of `ℚ̄` or of the real algebraic numbers
by `AlgebraicGeometry.RationalGaloisQuotient.fieldPoint_algEquiv_algebraicClosure_or_real`,
and the structure map of `ℚ` into either of those is not surjective, both fields containing
a square root of two. -/
@[stacks 0483 "not radicial"]
theorem not_isRadicial_galoisQuotientToBase :
    ¬ Space.IsRadicial B base hS (isAlgebraicSpace_galoisQuotient B hS hU)
      (isAlgebraicSpace_yoneda B base hS (Over.mk (𝟙 (B.obj hS))))
      (galoisQuotientToBase B hS hU) := by
  intro h
  obtain hempty | ⟨L, hLfield, hLalg, hLins, U, _, eU, e, _, _⟩ :=
    h ℚ (Over.mk (𝟙 (B.obj hS))) (Iso.refl _) (𝟙 _)
  · refine not_isEmpty_points_reducedClosedSubspace B hS _ ?_ hempty
    exact Space.pointsMap B base hS (galoisQuotient B hS hU)
      (inv (pullback.snd (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hS)))))
        (galoisQuotientToBase B hS hU)))
      (Quot.mk _ (coverFieldPoint B hS hU))
  · let : Field L := hLfield
    let : Algebra ℚ L := hLalg
    have : IsPurelyInseparable ℚ L := hLins
    have : Algebra.IsAlgebraic ℚ L := IsPurelyInseparable.isAlgebraic ℚ L
    have hsurj : Function.Surjective (algebraMap ℚ L) :=
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable ℚ L
    have hsize : ((BigFppfOver.toScheme B base hS).obj U).size < B.cutoff := U.left.property
    have hK : B.Contains (Spec (.of L)) := by rwa [Scheme.size_congr eU] at hsize
    have eW : (Over.mk (ObjectProperty.homMk (eU.inv ≫ B.inclusion.map U.hom) :
        B.obj hK ⟶ B.obj hS) : BigFppfOver B base hS) ≅ U :=
      Over.isoMk (ObjectProperty.isoMk _ eU.symm) (by rfl)
    obtain ⟨sU⟩ := nonempty_obj_of_subfunctor_iso_yoneda B hS e
      (pullback.snd (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hS)))))
        (galoisQuotientToBase B hS hU))
    rcases fieldPoint_algEquiv_algebraicClosure_or_real B hS hU L hK
      (eU.inv ≫ B.inclusion.map U.hom) ((galoisQuotient B hS hU).map eW.hom.op sU) with
      ⟨⟨ε⟩⟩ | ⟨⟨ε⟩⟩
    · exact not_surjective_algebraMap_algebraicClosure
        (surjective_algebraMap_of_algEquiv ε hsurj)
    · exact not_surjective_algebraMap_realAlgebraic
        (surjective_algebraMap_of_algEquiv ε hsurj)

/-- **Stacks 0483.** The structure morphism of the Galois quotient of `Spec ℚ̄` to `Spec ℚ` is
universally injective but is not radicial: for algebraic spaces, unlike for schemes,
universal injectivity is strictly weaker than radicialness.

This is the conjunction over a fixed big fppf site containing the two spectra;
`AlgebraicGeometry.RationalGaloisQuotient.exists_universallyInjective_not_isRadicial`
exhibits such a site and so asserts the non-equivalence outright. -/
@[stacks 0483 "the two halves together, over a big fppf site containing the two spectra"]
theorem universallyInjective_and_not_isRadicial :
    Space.UniversallyInjective B base hS (galoisQuotientToBase B hS hU) ∧
      ¬ Space.IsRadicial B base hS (isAlgebraicSpace_galoisQuotient B hS hU)
        (isAlgebraicSpace_yoneda B base hS (Over.mk (𝟙 (B.obj hS))))
        (galoisQuotientToBase B hS hU) :=
  ⟨universallyInjective_galoisQuotientToBase B hS hU,
    not_isRadicial_galoisQuotientToBase B hS hU⟩

end NotRadicial

/-- **Stacks 0483.** Universal injectivity is not equivalent to radicialness for morphisms of
algebraic spaces: there are a big fppf site over `Spec ℚ`, an algebraic space over `Spec ℚ` in
it, and a structure morphism of that space to `Spec ℚ` which is universally injective and is
not radicial.

Nothing is assumed: the site is the one
`AlgebraicGeometry.BigFppfSite.exists_containing` supplies for the two schemes `Spec ℚ` and
`Spec ℚ̄`, and the space is the Galois quotient of `Spec ℚ̄`, so this is
`AlgebraicGeometry.RationalGaloisQuotient.universallyInjective_and_not_isRadicial` with its
site hypotheses discharged. -/
@[stacks 0483]
theorem exists_universallyInjective_not_isRadicial :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains base)
      (X : (BigFppfOver B base hS)ᵒᵖ ⥤ Type 0) (hX : IsAlgebraicSpace B base hS X)
      (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))),
      Space.UniversallyInjective B base hS f ∧
        ¬ Space.IsRadicial B base hS hX
          (isAlgebraicSpace_yoneda B base hS (Over.mk (𝟙 (B.obj hS)))) f := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({base, cover.left} : Set Scheme.{0})
  have hS : B.Contains base := hB _ (by simp)
  have hU : B.Contains cover.left := hB _ (by simp)
  exact ⟨B, hS, galoisQuotient B hS hU, isAlgebraicSpace_galoisQuotient B hS hU,
    galoisQuotientToBase B hS hU, universallyInjective_and_not_isRadicial B hS hU⟩

end RationalGaloisQuotient

end AlgebraicGeometry

end
