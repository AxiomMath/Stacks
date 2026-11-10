module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective

/-!
# Blowing up a centre pulled back from the base

Let `X` be a scheme and let `I`, `J` be quasi-coherent ideal sheaves on `X`. Blowing `X` up in
`I` and then blowing the result up in the inverse image of `J` is the same as blowing `X` up in
the single centre `I · J`, canonically over `X`; and the support of `I · J` is
`Supp I ∪ b(Supp(J·𝒪_{Bl_I(X)}))`.

The point of this module is that these two statements are **unconditional**. The general
`AlgebraicGeometry.nonempty_blowUpCompositionIso` and
`AlgebraicGeometry.supportSet_mul_eq_union_image` ([Stacks, Tag 080B]) need a factorisation
`J·𝒪_{Bl_I(X)} = E ^ d · Z'` of the second centre off the exceptional divisor, which for a
general second centre `Z'` is Stacks Lemma 31.32.5 and is not available here. For a second
centre pulled back from the base the factorisation is trivial, with `d = 0` and `Z'` the inverse
image itself, so both statements apply with nothing carried.

Together they are exactly the two hypotheses `e` and `hK` of [Stacks, Tag 080I]
(`Stacks.StrictTransform.strictTransformSheaf_comp_blowUp` and
`Stacks.StrictTransform.strictTransform_comp_blowUp`). So for a two-step blowup whose second
centre comes from the base, the iterated strict transform is identified with the strict
transform in `I · J` unconditionally.

## Main results

The support of the composite centre -- the hypothesis `hK` of [Stacks, Tag 080I] -- is the
pre-existing `AlgebraicGeometry.supportSet_mul_eq_union_image_comap`
(`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/StrictTransformFlatnessTransport.lean:139`),
whose statement is identical; this module supplies that lemma's hypotheses unconditionally for a
second centre pulled back from the base.
* `AlgebraicGeometry.nonempty_blowUpCompositionIso_comap`: the composite of the two blowups is
  the blowup in `I · J` over `X`, the hypothesis `e` of [Stacks, Tag 080I].
* `AlgebraicGeometry.isAdmissibleBlowup_blowUpToBase_mul`: the product of two centres which are
  `U`-admissible is again `U`-admissible, so the composite is a `U`-admissible blowup.

## Implementation notes

The support statement needs that the blowup morphism hits every point outside its centre,
`AlgebraicGeometry.exists_blowUpToBase_eq_of_notMem_support` ([Stacks, Tag 02OS] part (1)):
a point of `Supp J` away from `Supp I` is the image of a point of the blowup, which then lies in
the inverse image of `Supp J`.

Nothing here is registered under [Stacks, Tag 080Y]. The first paragraph of Remark 38.30.1
reduces the blowup problem to a *finite chain* of admissible blowups, and for a chain whose
steps have arbitrary centres that reduction rests on [Stacks, Tag 080L],
`Stacks.Blowup.IsAdmissibleBlowup.comp`. That composition theorem is now unconditional — its
second-centre factorisation is `Stacks.Blowup.exists_factorization_blowUp` — but the chain
reduction itself is not carried out here. What is proved here is the base-centre case of that
chain, which is a special case and so is not the paragraph.

## References

* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A centre pulled back from the base factors off the exceptional divisor trivially: its
inverse image on the blowup is the zeroth power of the exceptional ideal times itself. This is
the hypothesis `hcomap` of the two clauses of [Stacks, Tag 080B], at `d = 0`. -/
public theorem comap_eq_exceptionalIdeal_pow_zero_mul (I J : X.IdealSheafData) :
    J.comap (blowUpToBase I) = exceptionalIdeal I ^ 0 * J.comap (blowUpToBase I) := by
  rw [pow_zero, one_mul]

/-- The support of `J` is contained in `Supp I` together with the image of the support of the
inverse image of `J`: a point of `Supp J` outside `Supp I` is the image of a point of the
blowup ([Stacks, Tag 02OS] part (1)), and that point lies over `Supp J`, hence in the support of
the inverse image. -/
public theorem supportSet_subset_union_image_comap (I J : X.IdealSheafData) :
    J.supportSet ⊆
      I.supportSet ∪ (blowUpToBase I).base '' (J.comap (blowUpToBase I)).supportSet := by
  intro x hx
  by_cases hxI : x ∈ I.supportSet
  · exact Set.mem_union_left _ hxI
  · obtain ⟨y, hy⟩ := exists_blowUpToBase_eq_of_notMem_support I hxI
    refine Set.mem_union_right _ ⟨y, ?_, hy⟩
    change y ∈ ((J.comap (blowUpToBase I)).support : Set (blowUp I))
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    change (blowUpToBase I).base y ∈ (J.support : Set X)
    rw [hy]
    exact hx

/-- **The composite of two blowups is the blowup in the product centre, unconditionally**, when
the second centre is pulled back from the base. Blowing `X` up in `I` and then in the inverse
image of `J` gives the blowup of `X` in `I · J`, canonically over `X`.

This is the clause of [Stacks, Tag 080B] identifying the composite morphism, with its
factorisation hypothesis discharged by
`AlgebraicGeometry.comap_eq_exceptionalIdeal_pow_zero_mul`, and it is the hypothesis `e` of
[Stacks, Tag 080I] for a second centre pulled back from the base. -/
public theorem nonempty_blowUpCompositionIso_comap (I J : X.IdealSheafData) :
    Nonempty (Over.mk (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I) ≅
      Over.mk (blowUpToBase (I * J))) :=
  nonempty_blowUpCompositionIso I (J.comap (blowUpToBase I)) 0 J
    (comap_eq_exceptionalIdeal_pow_zero_mul I J)

/-- **The product of two `U`-admissible centres is `U`-admissible.** If `I` and `J` cut out
finitely presented closed subschemes supported away from `U`, so does `I · J`, so the blowup of
`X` in `I · J` — which by `AlgebraicGeometry.nonempty_blowUpCompositionIso_comap` is the two-step
blowup in `I` and then in the inverse image of `J` — is a `U`-admissible blowup.

Finite presentation of the product centre is `AlgebraicGeometry.finitePresentation_mul_subschemeι`
([Stacks, Tag 080B]); the support of a product is the union of the supports. -/
public theorem isAdmissibleBlowup_blowUpToBase_mul (U : X.Opens) (I J : X.IdealSheafData)
    (hI : FinitePresentation I.subschemeι) (hJ : FinitePresentation J.subschemeι)
    (hIU : Disjoint (U : Set X) (I.support : Set X))
    (hJU : Disjoint (U : Set X) (J.support : Set X)) :
    Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase (I * J)) := by
  have hJfg : ∀ V : X.affineOpens, (J.ideal V).FG := by
    rw [finitePresentation_iff_fg_ker, Scheme.IdealSheafData.ker_subschemeι] at hJ
    exact hJ
  have hfp : FinitePresentation (I * J).subschemeι := finitePresentation_mul_subschemeι I J hI hJfg
  have hdisj : Disjoint (U : Set X) (((I * J).support : Set X)) := by
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    exact Set.disjoint_union_right.mpr ⟨hIU, hJU⟩
  exact (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨I * J, hfp, hdisj, Iso.refl _, Category.id_comp _⟩

end AlgebraicGeometry

end
