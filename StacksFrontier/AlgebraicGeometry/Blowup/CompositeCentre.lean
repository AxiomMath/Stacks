module

public import StacksFrontier.AlgebraicGeometry.Blowup.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic

/-!
# Blowing up a composite centre

Let `X` be a scheme, let `I` be a quasi-coherent ideal sheaf on `X` with blowup
`b : X' = Bl_I(X) ⟶ X` and exceptional ideal `E = I·𝒪_{X'}`, and let `Z'` be a quasi-coherent
ideal sheaf on `X'`. Suppose a quasi-coherent ideal sheaf `J` on `X` factors the second centre
off the exceptional divisor, in the sense that
`b⁻¹J·𝒪_{X'} = E ^ d · Z'` for some `d`.

Then the two-step blowup `Bl_{Z'}(X') ⟶ X' ⟶ X` is the blowup of `X` in the single centre
`I · J`, canonically over `X`, and the centre `I · J` is of finite presentation with support
`Supp I ∪ b(Supp Z')` as soon as `I` is of finite presentation and `J` is of finite type.

Both conclusions are stated at the shape in which [Stacks, Tag 080I] consumes them, as its
hypotheses `hK` and `e`.

## Main results

* `AlgebraicGeometry.finitePresentation_mul_subschemeι`: the product of a finitely presented
  centre with a centre of finite type is a finitely presented centre.
* `AlgebraicGeometry.supportSet_mul_eq_union_image_comap`: the support of `I · J` is the support
  of `I` together with the image of the support of `b⁻¹J·𝒪_{X'}`, for every `J`.
* `AlgebraicGeometry.supportSet_mul_eq_union_image`: the support of `I · J` is
  `Supp I ∪ b(Supp Z')`.
* `AlgebraicGeometry.nonempty_blowUpCompositionIso`: the two-step blowup is the blowup in
  `I · J`, as a scheme over `X`.
The statements of the tag itself, which quantify over the centre `Y` instead of taking the
factorization as an argument, are in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentreExistence.lean`; they cannot live here,
because `StacksFrontier/AlgebraicGeometry/Blowup/CentreInsidePower.lean` imports this file and the
second centre is built above it.

## Implementation notes

The isomorphism is obtained from [Stacks, Tag 080A]
(`AlgebraicGeometry.blowUpMulIso`), which identifies the blowup in `I · J` with the blowup of
`X` in `I` followed by the blowup in `b⁻¹J·𝒪_{X'}`. The hypothesis rewrites that second centre
as `E ^ d · Z'`, and the power of the exceptional ideal is removed by a second application of
tag 080A together with [Stacks, Tag 0807]: `E ^ d` is an effective Cartier divisor, so blowing
`X'` up in it is an isomorphism, and [Stacks, Tag 0805] transports the centre `Z'` across that
isomorphism.

Finite presentation of the product centre is [Stacks, Tag 01TV] on both sides: it says that a
closed immersion is of finite presentation exactly when its ideal is of finite type, and the
ideal of `I · J` over an affine open is the product of the two ideals there.

The support identity needs no hypothesis bounding `Supp J`: the Stacks proof bounds it by
`Z ∪ b(Z')` using the choice of `𝒥` made there, but the inclusion is already forced by the
factorization `b⁻¹J·𝒪_{X'} = E ^ d · Z'`, since `Supp E` lies over `Supp I` and the blowup is
surjective off its centre ([Stacks, Tag 02OS]).

**The factorization `hcomap` is discharged.** `Stacks.Blowup.exists_secondCentre`, in
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreExistence.lean`, produces from a finite-type
centre `Z'` on the blowup a `d > 0` and a finite-type `J ≤ I ^ d` on `X` with
`b⁻¹J·𝒪_{X'} = E ^ d · Z'`. It is Stacks Lemma 31.32.5, [Stacks, Tag 0803], applied to the Rees
algebra `⨁ Iⁿ`.

Tag 0803 is formalized for a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, as
`Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_presentation_supp`;
`Stacks.Blowup.reesSheafGradedAlgebra` puts the Rees algebra on that substrate, and two of the
tag's inputs are discharged there for a centre of finite type —
`Stacks.Blowup.isFiniteType_reesSheafGradedAlgebra_piece` and
`Stacks.Blowup.quasiCompact_relativeProj_reesSheafGradedAlgebra_toBase`. Its hypothesis `hZ`,
the relative case of [Stacks, Tag 0801], is
`Stacks.AlgebraicGeometry.RelativeProjTwists.vanishingIdealPresentation`. The submodule
`ℱ ⊆ (⨁ Iⁿ)_d` that the tag produces is named as a centre on `X` by
`Stacks.Blowup.reesCentre`, with `Stacks.Blowup.reesCentre_le_pow` and
`Stacks.Blowup.isFiniteType_reesCentre`, and the presentation `Z' = Proj(𝒜/ℱ𝒜)` is read at the
degree-one charts `D₊(a)`, `a ∈ I(U)`, through
`Stacks.Blowup.reesProjBlowUpIso`, which identifies the relative `Proj` of the Rees algebra
with `blowUp I` compatibly with those charts and not merely over the base.

With that, the clauses of the tag are stated with the centre quantified over, in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentreExistence.lean`. They are not stated here
because the chain of imports that builds the second centre passes through
`StacksFrontier/AlgebraicGeometry/Blowup/CentreInsidePower.lean`, which imports this file. The
statements below, which take the factorization as an argument, are the engine those are proved
from, and they are the shape [Stacks, Tag 080I] consumes.

**Reading the conclusion of Tag 0803 as the factorization is no longer a gap.** That conclusion
is a finite-type submodule `ℱ ⊆ 𝒜_d`, read as an ideal sheaf `J` on `X` by
`AlgebraicGeometry.idealSheafDataOfHom`, and that constructor now has its `comap` lemma:
`AlgebraicGeometry.comap_idealSheafDataOfHom_eq_idealSheafDataOfHom_pullback`, and on a pair of
affine charts `AlgebraicGeometry.ideal_comap_idealSheafDataOfHom`, in
`StacksFrontier/AlgebraicGeometry/Properties/ExtendFiniteType/IdealSheafOfHomComap.lean`. The
chart-level factorization of `StacksFrontier/RingTheory/Blowup/IdealFactorization.lean` is
globalized in `StacksFrontier/AlgebraicGeometry/Blowup/CentreNormalizeChart.lean`:
`Stacks.BlowUpChartCover.comap_idealSheafDataOfHom_eq_exceptionalIdeal_pow_mul_iff` reduces
`hcomap`, for a centre presented as the image of a quasi-coherent module, to the chartwise
statement that `Z'` is generated by the fractions `φ(x)/aᵈ`, and
`Stacks.BlowUpChartCover.existsUnique_comap_eq_exceptionalIdeal_pow_mul` says that the second
factor of such a factorization is unique, so a `Z'` produced by any other construction is the
one obtained by dividing by `E ^ d`.

The converse direction, which produces `Z'` from a centre `J ≤ I ^ d` and needs none of that, is
`StacksFrontier/AlgebraicGeometry/Blowup/CentreInsidePower.lean`.

## References

* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B), in whose proof the
  composite centre `I · J` is produced.
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The product of a finitely presented centre with a centre of finite type is again a finitely
presented centre: by [Stacks, Tag 01TV] both statements say that the ideal is finitely generated
over every affine open, and the ideal of `I * J` there is the product of the two ideals.

This is the finite-presentation clause of [Stacks, Tag 080B]. -/
@[stacks 080B "the centre Y is of finite presentation. Y is the explicit product I * J of \
the first centre with the second-centre ideal that Stacks Lemma 31.32.5, Tag 0803, supplies, \
and a product of a finitely presented centre with a centre of finite type is finitely \
presented"]
theorem finitePresentation_mul_subschemeι (I J : X.IdealSheafData)
    (hI : FinitePresentation I.subschemeι) (hJ : ∀ U : X.affineOpens, (J.ideal U).FG) :
    FinitePresentation (I * J).subschemeι := by
  rw [finitePresentation_iff_fg_ker, Scheme.IdealSheafData.ker_subschemeι] at hI ⊢
  exact fun U ↦ (hI U).mul (hJ U)

/-- The support set of a product of two centres is the union of their support sets. -/
private theorem supportSet_mul_eq_union (I J : X.IdealSheafData) :
    (I * J).supportSet = I.supportSet ∪ J.supportSet :=
  rfl

/-- The support set of an inverse image of a centre is the preimage of its support set. -/
private theorem supportSet_comap_eq_preimage {Y : Scheme.{u}} (f : Y ⟶ X) (J : X.IdealSheafData) :
    (J.comap f).supportSet = f.base ⁻¹' J.supportSet :=
  congrArg (fun T : TopologicalSpace.Closeds Y ↦ (T : Set Y))
    (Scheme.IdealSheafData.support_comap J f)

/-- The image of the support of the second centre lies in the support of `J`: on the blowup the
inverse image of `J` is a multiple of `Z'`, so every point of `Supp Z'` lies in the inverse
image of `Supp J`. -/
theorem image_supportSet_subset_supportSet (I : X.IdealSheafData)
    (Z' : (blowUp I).IdealSheafData) (d : ℕ) (J : X.IdealSheafData)
    (hcomap : J.comap (blowUpToBase I) = exceptionalIdeal I ^ d * Z') :
    (blowUpToBase I).base '' Z'.supportSet ⊆ J.supportSet := by
  rintro x ⟨z, hz, rfl⟩
  have hz' : z ∈ (J.comap (blowUpToBase I)).supportSet := by
    rw [hcomap, supportSet_mul_eq_union]
    exact Set.mem_union_right _ hz
  rwa [supportSet_comap_eq_preimage] at hz'

/-- The support of a product of two centres is the support of the first together with the image
of the support of the inverse image of the second on the blowup of the first. The inclusion of
the second support in the image uses [Stacks, Tag 02OS], that the blowup is an isomorphism away
from its centre. -/
theorem supportSet_mul_eq_union_image_comap (I J : X.IdealSheafData) :
    (I * J).supportSet =
      I.supportSet ∪ (blowUpToBase I).base '' (J.comap (blowUpToBase I)).supportSet := by
  have : IsIso (blowUpToBase I ∣_
      (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)) :=
    isIso_blowUp_restrict_compl_support I
  rw [supportSet_mul_eq_union, supportSet_comap_eq_preimage]
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro (hx | hx)
    · exact Or.inl hx
    · by_cases hi : x ∈ I.support
      · exact Or.inl hi
      · obtain ⟨y, hy⟩ := Surjective.surj
          (f := blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens))
          ⟨x, hi⟩
        have hxy : blowUpToBase I y.val = x := by
          simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hy
        exact Or.inr ⟨y.val, show blowUpToBase I y.val ∈ J.supportSet from hxy.symm ▸ hx, hxy⟩
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr hy

/-- The support of a power of the exceptional ideal lies over the support of the centre. At the
zeroth power the ideal is the unit ideal, whose support is empty; at every other power the
support is that of the exceptional ideal itself. -/
theorem supportSet_exceptionalIdeal_pow_subset (I : X.IdealSheafData) (d : ℕ) :
    (exceptionalIdeal I ^ d).supportSet ⊆ (blowUpToBase I).base ⁻¹' I.supportSet := by
  have hE : (exceptionalIdeal I).supportSet = (blowUpToBase I).base ⁻¹' I.supportSet :=
    supportSet_comap_eq_preimage (blowUpToBase I) I
  cases d with
  | zero =>
    rw [show (exceptionalIdeal I ^ 0).supportSet = (∅ : Set (blowUp I)) from rfl]
    exact Set.empty_subset _
  | succ n =>
    refine Eq.trans_le ?_ hE.le
    exact congrArg (fun T : TopologicalSpace.Closeds (blowUp I) ↦ (T : Set (blowUp I)))
      (Scheme.IdealSheafData.support_pow_succ (exceptionalIdeal I) n)

/-- **The support of the composite centre.** If the inverse image of `J` on the blowup of `X` in
`I` is `E ^ d · Z'`, then the support of the composite centre `I · J` is exactly
`Supp I ∪ b(Supp Z')`.

This is part (1) of [Stacks, Tag 080B] for the explicit product centre, and the hypothesis `hK`
of [Stacks, Tag 080I]. It takes the factorization as an argument, so it is the engine rather
than the tag: `AlgebraicGeometry.exists_centre_supportSet_eq` is part (1) of the tag, with
the pair `(d, J)` supplied by `Stacks.Blowup.exists_secondCentre`. -/
theorem supportSet_mul_eq_union_image (I : X.IdealSheafData)
    (Z' : (blowUp I).IdealSheafData) (d : ℕ) (J : X.IdealSheafData)
    (hcomap : J.comap (blowUpToBase I) = exceptionalIdeal I ^ d * Z') :
    (I * J).supportSet = I.supportSet ∪ (blowUpToBase I).base '' Z'.supportSet := by
  have himg : (blowUpToBase I).base '' (exceptionalIdeal I ^ d).supportSet ⊆ I.supportSet := by
    rintro x ⟨z, hz, rfl⟩
    exact supportSet_exceptionalIdeal_pow_subset I d hz
  rw [supportSet_mul_eq_union_image_comap I J, hcomap, supportSet_mul_eq_union, Set.image_union,
    ← Set.union_assoc, Set.union_eq_self_of_subset_right himg]

/-- **The composite of two blowups is the blowup in the composite centre.** If the inverse image
of `J` on the blowup of `X` in `I` is `E ^ d · Z'`, then blowing `X` up in `I` and then in `Z'`
gives the blowup of `X` in `I · J`, canonically over `X`.

This is part (2) of [Stacks, Tag 080B] for the explicit product centre, and the hypothesis `e`
of [Stacks, Tag 080I]. As with the previous declaration, the factorization is an argument here;
`AlgebraicGeometry.exists_centre_nonempty_blowUpCompositionIso` is part (2) of the tag. -/
theorem nonempty_blowUpCompositionIso (I : X.IdealSheafData)
    (Z' : (blowUp I).IdealSheafData) (d : ℕ) (J : X.IdealSheafData)
    (hcomap : J.comap (blowUpToBase I) = exceptionalIdeal I ^ d * Z') :
    Nonempty (Over.mk (blowUpToBase Z' ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase (I * J))) := by
  set K : (blowUp I).IdealSheafData := exceptionalIdeal I ^ d with hKdef
  have hK : Stacks.Divisors.IsEffectiveCartierDivisor K :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) d
  have hgiso : IsIso (blowUpToBase K) :=
    isIso_blowUpToBase_of_isEffectiveCartierDivisor K hK
  obtain ⟨h, hpb⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (blowUpToBase K) Z'
  have : IsIso h := hpb.isIso_snd_of_isIso
  -- Transport the centre `Z'` across the isomorphism `Bl_K(X') ≅ X'`.
  have eTransport : Over.mk (blowUpToBase (Z'.comap (blowUpToBase K)) ≫ blowUpToBase K) ≅
      Over.mk (blowUpToBase Z') :=
    Over.isoMk (asIso h) hpb.w.symm
  -- Removing the power of the exceptional ideal from the second centre.
  have eFactor : Over.mk (blowUpToBase (K * Z')) ≅ Over.mk (blowUpToBase Z') :=
    (blowUpMulIso K Z').symm ≪≫ eTransport
  have eProduct := blowUpMulIso I J
  rw [show J.comap (blowUpToBase I) = K * Z' from hcomap] at eProduct
  exact ⟨((Over.map (blowUpToBase I)).mapIso eFactor).symm ≪≫ eProduct⟩

/-- **The factorization hypothesis of the two clauses above is satisfiable.**  For `J = I`,
`d = 1` and `Z'` the unit ideal, the inverse image of `J` on the blowup of `X` in `I` is the
exceptional ideal itself, so the three statements above are not vacuous. -/
theorem comap_eq_exceptionalIdeal_pow_one_mul_top (I : X.IdealSheafData) :
    I.comap (blowUpToBase I) = exceptionalIdeal I ^ 1 * (⊤ : (blowUp I).IdealSheafData) := by
  rw [pow_one]
  exact (mul_one _).symm

end AlgebraicGeometry

end
