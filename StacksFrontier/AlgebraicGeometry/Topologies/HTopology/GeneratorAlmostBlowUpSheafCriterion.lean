module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.PrincipalCenter
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare

/-!
# Testing h descent on the one- and two-generator almost blowup squares

Stacks 0EVI characterizes the sheaves on the big h site `(Sch/S)_h` of Stacks 0EU1 by four
conditions on a presheaf `F`:

1. `F` is a sheaf for the Zariski topology;
2. for every morphism `f : X ⟶ Y` of the site with `Y` affine and `f` surjective, flat, proper
   and of finite presentation, `F(Y)` is the equalizer of the two maps `F(X) ⟶ F(X ×_Y X)`;
3. `F` sends an almost blowup square of the site of the shape of Example 0EVG to a cartesian
   diagram of sets;
4. `F` sends an almost blowup square of the site of the shape of Example 0EVH to a cartesian
   diagram of sets.

This refines Stacks 0EVF, whose condition (3) is the cartesianness of the image of *every*
almost blowup square of the site with affine base: only the two explicit shapes need testing.
Conditions (1) and (2) are literally those of Stacks 0EVF, and are reused from
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion`; condition (2)
in the source's equalizer form is
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer`
there.

The square of Example 0EVG is, for a ring `A`, an element `f ∈ A` and a finitely generated
ideal `J ⊆ A` annihilated by a power of `f`, the square with corners `Spec (A/(fA + J))`,
`Spec (A/J)`, `Spec (A/fA)` and `Spec A`.  The square of Example 0EVH is, for `f₁, f₂ ∈ A`, the
square with corners `Proj (A/(f₁,f₂))[T₀,T₁]`, `Proj A[T₀,T₁]/(f₂T₀ - f₁T₁)`,
`Spec (A/(f₁,f₂))` and `Spec A`.

## Main definitions

* `AlgebraicGeometry.IsModelPairOverBase`: a pair of morphisms with common target is carried to
  a prescribed pair by isomorphisms of all three schemes.
* `AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel` and
  `AlgebraicGeometry.IsTwoGeneratorAlmostBlowUpModel`: the modification and the centre have the
  shape of Example 0EVG, resp. of Example 0EVH.
* `AlgebraicGeometry.BigHOver.IsOneGeneratorAlmostBlowUpSheaf` and
  `AlgebraicGeometry.BigHOver.IsTwoGeneratorAlmostBlowUpSheaf`: conditions (3) and (4).
* `AlgebraicGeometry.AffineAlmostBlowUpHSheafCriterion`: the sufficiency direction of Stacks 0EVF
  as a `Prop`, proved beside its statement.
* `AlgebraicGeometry.GeneratorAlmostBlowUpSquaresSuffice`: the reduction of condition (3) of
  Stacks 0EVF to the two shapes, the one input of the sufficiency direction below that this
  development does not have.

Conditions (1) and (2) are `AlgebraicGeometry.BigHOver.IsZariskiSheaf` and
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf`.

## Main results

* `AlgebraicGeometry.isAlmostBlowUpSquare_and_isOneGeneratorAlmostBlowUpModel` and
  `AlgebraicGeometry.isTwoGeneratorAlmostBlowUpModel_proj`: the model squares themselves have the
  two shapes, and the one of Example 0EVG is an almost blowup square.
* `AlgebraicGeometry.BigHOver.isOneGeneratorAlmostBlowUpSheaf_of_isSheaf` and
  `AlgebraicGeometry.BigHOver.isTwoGeneratorAlmostBlowUpSheaf_of_isSheaf`: a sheaf satisfies
  conditions (3) and (4).
* `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf.oneGenerator` and
  `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf.twoGenerator`: conditions (3) and (4)
  are weaker than condition (3) of Stacks 0EVF.
* `AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion`: the sufficiency direction of Stacks 0EVF
  in the `Prop`-valued form consumed here.
* `AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares`:
  the four-condition characterization of Stacks 0EVI, with the sufficiency direction of Stacks
  0EVF and the reduction of its condition (3) to the two shapes carried as hypotheses.
* `BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares_of_reduction`:
  the same characterization with the first of those two hypotheses discharged, so that only the
  reduction is assumed.

## Implementation notes

**The hypothesis list of conditions (3) and (4).**  A square of the site is recorded, exactly as
in condition (3) of Stacks 0EVF, by its base `X`, its modification `b : X' ⟶ X`, its centre
`z : Z ⟶ X` and its exceptional corner `p : E ⟶ X'`, `e : E ⟶ Z`, together with a quasi-coherent
ideal sheaf `I` on the underlying scheme of `X` for which `b` is an almost blowup square with
centre `I`, an identification of `z` with the closed subscheme cut out by `I`, affineness of the
underlying scheme of `X`, and cartesianness of the square underlying `(z, b, e, p)`.  Conditions
(3) and (4) add to this the requirement that the pair `(b, z)` have the shape of Example 0EVG,
resp. of Example 0EVH.

Every one of those hypotheses holds for the squares the source's conditions (3) and (4) range
over: for Example 0EVG the almost blowup property with the centre cut out by `f` is Stacks 0EVG,
`AlgebraicGeometry.isAlmostBlowUpSquare_quotient_of_pow_mul_eq_zero`, and for Example 0EVH it is
the assertion of Stacks 0EVH.  Those statements are about the model squares themselves, and this
development has no transport of `AlgebraicGeometry.IsAlmostBlowUpSquare` along an isomorphism of
the base, so the data is quantified over rather than reconstructed from the shape; in particular
the shape hypothesis is what distinguishes conditions (3) and (4) from condition (3) of Stacks
0EVF, and the remaining hypotheses are shared with it.

**The shape of a square.**  Membership of a shape is invariance of the pair consisting of the
modification and the centre under isomorphisms of their common target, of the modification and
of the centre, rather than equality with a chosen model; this expresses the source's examples
without pinning affine coordinates on the objects of the site.  The exceptional corner of
Example 0EVG is `Spec (A/(fA + J))`, and that of Example 0EVH is
`Proj (A/(f₁,f₂))[T₀,T₁]`; both are the fibre product of the modification and the centre over
the base, which is why the conditions ask for the underlying square to be cartesian rather than
prescribing a shape for the upper-left corner as well.

**What the characterization below still assumes.**  The sufficiency direction of Stacks 0EVF is
available: it is
`AlgebraicGeometry.BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp` in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction`, proved there
from `AlgebraicGeometry.finitePresentationHasAlmostBlowUpFlattening`, and it is restated here as the
`Prop` `AlgebraicGeometry.AffineAlmostBlowUpHSheafCriterion` with
`AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion` proving it.  What the characterization below
still assumes is the reduction of condition (3) of Stacks 0EVF to the two shapes — the induction
on the number of generators of the ideal of the centre, which is the whole content of the proof of
Stacks 0EVI — as `AlgebraicGeometry.GeneratorAlmostBlowUpSquaresSuffice`.  It is stated for every
big h site, every base scheme and every presheaf of sets, so it does not narrow the class of
objects Stacks 0EVI is about.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### The shapes of the two example squares -/

/-- A pair of morphisms with common target is carried to the pair `(bm, zm)` by isomorphisms of
the target, of the source of the first and of the source of the second. -/
public def IsModelPairOverBase {X X' Z Xm X'm Zm : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (bm : X'm ⟶ Xm) (zm : Zm ⟶ Xm) : Prop :=
  ∃ (iX : X ≅ Xm) (iX' : X' ≅ X'm) (iZ : Z ≅ Zm),
    b ≫ iX.hom = iX'.hom ≫ bm ∧ z ≫ iX.hom = iZ.hom ≫ zm

/-- **The shape of Example 0EVG.** The modification is the closed immersion `Spec (A/J) ⟶ Spec A`
for a finitely generated ideal `J` annihilated by a power of an element `f`, and the centre is
the closed subscheme of `Spec A` cut out by `f`. -/
public def IsOneGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) : Prop :=
  ∃ (A : Type u) (hA : CommRing A),
    letI := hA
    ∃ (f : A) (J : Ideal A), J.FG ∧ (∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) ∧
      IsModelPairOverBase b z (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subschemeι

/-- **The shape of Example 0EVH.** The modification is the projective hypersurface
`Proj A[T₀,T₁]/(f₂T₀ - f₁T₁) ⟶ Spec A` attached to two elements `f₁, f₂`, and the centre is
`Spec (A/(f₁,f₂)) ⟶ Spec A`. -/
public def IsTwoGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) : Prop :=
  ∃ (A : Type u) (hA : CommRing A),
    letI := hA
    ∃ f₁ f₂ : A,
      letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
      IsModelPairOverBase b z (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)
        (Stacks.AlmostBlowUp.centerToBase A f₁ f₂)

/-- A pair of morphisms with common target is its own model. -/
public theorem IsModelPairOverBase.refl {X X' Z : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) :
    IsModelPairOverBase b z b z :=
  ⟨Iso.refl X, Iso.refl X', Iso.refl Z, by simp, by simp⟩

/-- **Stacks 0EVG.** The square attached to a finitely generated ideal `J` annihilated by a power
of `f` is an almost blowup square with centre cut out by `f`, and has the one-generator shape. -/
public theorem isAlmostBlowUpSquare_and_isOneGeneratorAlmostBlowUpModel
    (A : Type u) [hA : CommRing A]
    (f : A) (J : Ideal A) (hJ : J.FG) (h : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    IsAlmostBlowUpSquare
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f})))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ∧
      IsOneGeneratorAlmostBlowUpModel (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subschemeι :=
  ⟨isAlmostBlowUpSquare_quotient_of_pow_mul_eq_zero A f J hJ h,
    A, hA, f, J, hJ, h, IsModelPairOverBase.refl _ _⟩

/-- The square of Example 0EVH attached to two elements has the two-generator shape. -/
public theorem isTwoGeneratorAlmostBlowUpModel_proj (A : Type u) [hA : CommRing A] (f₁ f₂ : A) :
    letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
    IsTwoGeneratorAlmostBlowUpModel (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)
      (Stacks.AlmostBlowUp.centerToBase A f₁ f₂) :=
  ⟨A, hA, f₁, f₂, IsModelPairOverBase.refl _ _⟩

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-! ### The two shape conditions of Stacks 0EVI -/

/-- **Condition (3) of Stacks 0EVI.** A presheaf on the big h category over `S` sends every
almost blowup square of the site which has affine base and the shape of Example 0EVG to a
cartesian square of sets. -/
public def IsOneGeneratorAlmostBlowUpSheaf : Prop :=
  ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
      (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
    IsAffine ((BigHOver.toScheme B S hS).obj X) →
    IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
    Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
    IsPullback
      ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map p)
      ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map b) →
    IsOneGeneratorAlmostBlowUpModel
      ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z) →
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op)

/-- **Condition (4) of Stacks 0EVI.** A presheaf on the big h category over `S` sends every
almost blowup square of the site which has affine base and the shape of Example 0EVH to a
cartesian square of sets. -/
public def IsTwoGeneratorAlmostBlowUpSheaf : Prop :=
  ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
      (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
    IsAffine ((BigHOver.toScheme B S hS).obj X) →
    IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
    Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
    IsPullback
      ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map p)
      ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map b) →
    IsTwoGeneratorAlmostBlowUpModel
      ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z) →
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op)

/-! ### A sheaf satisfies the two shape conditions -/

/-- **Stacks 0EVI, a sheaf satisfies condition (3).** A sheaf on the big h site over `S` sends an
almost blowup square of the site of the shape of Example 0EVG to a cartesian square of sets.

Neither the shape nor affineness of the base is used: this is Stacks 0EVD for an arbitrary
almost blowup square of the site. -/
@[stacks 0EVI "only if, condition (3)"]
public theorem isOneGeneratorAlmostBlowUpSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F :=
  fun _ _ _ _ b z p e I _ hb hZ hSquare _ ↦
    isPullback_of_almostBlowUpSquare_bigH B S hS F hF b z p e I hb hZ hSquare

/-- **Stacks 0EVI, a sheaf satisfies condition (4).** A sheaf on the big h site over `S` sends an
almost blowup square of the site of the shape of Example 0EVH to a cartesian square of sets.

Neither the shape nor affineness of the base is used: this is Stacks 0EVD for an arbitrary
almost blowup square of the site. -/
@[stacks 0EVI "only if, condition (4)"]
public theorem isTwoGeneratorAlmostBlowUpSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F :=
  fun _ _ _ _ b z p e I _ hb hZ hSquare _ ↦
    isPullback_of_almostBlowUpSquare_bigH B S hS F hF b z p e I hb hZ hSquare

/-- **Stacks 0EVI, the necessity of all four conditions.** A sheaf on the big h site over `S` is a
sheaf for the Zariski topology, satisfies the equalizer condition for every morphism of the site
with affine target which is flat, proper, surjective and of finite presentation, and sends an
almost blowup square of the shape of Example 0EVG, respectively of Example 0EVH, to a cartesian
square of sets. -/
@[stacks 0EVI "only if, all four conditions"]
public theorem zariski_and_affineFlatProperFP_and_generatorSquares_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsZariskiSheaf B S hS F ∧
      BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
      BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F ∧
      BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F :=
  ⟨isZariskiSheaf_of_isSheaf B S hS F hF,
    isAffineFlatProperFinitePresentationSheaf_of_isSheaf B S hS F hF,
    isOneGeneratorAlmostBlowUpSheaf_of_isSheaf B S hS F hF,
    isTwoGeneratorAlmostBlowUpSheaf_of_isSheaf B S hS F hF⟩

/-! ### Comparison with condition (3) of Stacks 0EVF -/

/-- Condition (3) of Stacks 0EVF implies condition (3) of Stacks 0EVI: the squares tested by the
latter are among those tested by the former. -/
public theorem IsAffineAlmostBlowUpSheaf.oneGenerator
    (hF : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) :
    BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F :=
  fun X X' Z E b z p e I haffine hb hZ hSquare _ ↦ hF X X' Z E b z p e I haffine hb hZ hSquare

/-- Condition (3) of Stacks 0EVF implies condition (4) of Stacks 0EVI: the squares tested by the
latter are among those tested by the former. -/
public theorem IsAffineAlmostBlowUpSheaf.twoGenerator
    (hF : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) :
    BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F :=
  fun X X' Z E b z p e I haffine hb hZ hSquare _ ↦ hF X X' Z E b z p e I haffine hb hZ hSquare

end BigHOver

/-! ### The two carried inputs of the sufficiency direction -/

/-- **The sufficiency direction of Stacks 0EVF.** On every big h site over every base scheme,
the Zariski sheaf condition, descent for flat proper surjections of finite presentation over
affines, and cartesianness of the image of every almost blowup square with affine base together
force a presheaf of sets to be a sheaf for the h topology.

It is stated as a `Prop` so that it can be passed as an explicit hypothesis, and is proved by
`AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion` beside it, from
`AlgebraicGeometry.BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`
in `StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafInduction`.

It carries no `@[stacks 0EVF]` attribute, that tag being registered where the statement it names
is proved. -/
public def AffineAlmostBlowUpHSheafCriterion : Prop :=
  ∀ (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v),
    BigHOver.IsZariskiSheaf B S hS F →
    BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F →
    BigHOver.IsAffineAlmostBlowUpSheaf B S hS F →
    Presheaf.IsSheaf (BigHOver.topology B S hS) F

/-- **The sufficiency direction of Stacks 0EVF**, in the `Prop`-valued form consumed here.
This is `BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`. -/
public theorem affineAlmostBlowUpHSheafCriterion : AffineAlmostBlowUpHSheafCriterion.{u, v} :=
  fun B S hS F hZ h2 h3 ↦
    BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp
      B S hS F hZ h2 h3

/-- **The reduction step in the proof of Stacks 0EVI.** On every big h site over every base
scheme, conditions (1) to (4) of Stacks 0EVI force condition (3) of Stacks 0EVF: cartesianness
of the image of every almost blowup square with affine base follows from cartesianness of the
images of the squares of Examples 0EVG and 0EVH.

This is unproved in this development, and is stated as a `Prop` so that it can be carried as an
explicit hypothesis.  It is the whole content of the proof of Stacks 0EVI: an induction on the
number of generators of the ideal cutting out the centre, started by Example 0EVH for at most
two generators, with Example 0EVG supplying the case of a closed-immersion modification and a
locally principal centre, and the base changes of Stacks 0EVL keeping the two squares produced
at each step almost blowup squares.

It carries no `@[stacks 0EVI]` attribute, because nothing here proves it. -/
public def GeneratorAlmostBlowUpSquaresSuffice : Prop :=
  ∀ (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v),
    BigHOver.IsZariskiSheaf B S hS F →
    BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F →
    BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F →
    BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F →
    BigHOver.IsAffineAlmostBlowUpSheaf B S hS F

namespace BigHOver

/-! ### The characterization -/

/-- **Stacks 0EVI.** A presheaf of sets on the big h category over `S` is a sheaf for the h
topology if and only if it satisfies condition (1), the sheaf condition for Zariski coverings,
condition (2), the sheaf condition for every morphism of the site with affine target which is
flat, proper, surjective and of finite presentation, condition (3), cartesianness of the image
of every almost blowup square of the site with affine base and the shape of Example 0EVG, and
condition (4), the same for the shape of Example 0EVH.

Both inputs of the sufficiency direction are carried, so this statement bears no `@[stacks 0EVI]`
attribute: `hcrit` is the sufficiency direction of Stacks 0EVF and `hind` is the reduction of its
condition (3) to the two shapes, which is the content of the proof of Stacks 0EVI itself.  The tag
is carried instead by the necessity results above, which are unconditional.  `hcrit` is in fact
available here, as `AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion`; the form of this
statement which assumes only `hind` is
`BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares_of_reduction` below.
Condition (2) in the source's equalizer form is
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer`. -/
public theorem isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares
    (hcrit : AffineAlmostBlowUpHSheafCriterion.{u, v})
    (hind : GeneratorAlmostBlowUpSquaresSuffice.{u, v})
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F ↔
      (BigHOver.IsZariskiSheaf B S hS F ∧
        BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
        BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F ∧
        BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F) := by
  exact ⟨zariski_and_affineFlatProperFP_and_generatorSquares_of_isSheaf B S hS F,
    fun ⟨hZ, hP, h1, h2⟩ ↦ hcrit B S hS F hZ hP (hind B S hS F hZ hP h1 h2)⟩

/-- **Stacks 0EVI**, assuming only the reduction of condition (3) of Stacks 0EVF to the two
shapes.  A presheaf of sets on the big h category over `S` is a sheaf for the h topology if and
only if it satisfies condition (1), the sheaf condition for Zariski coverings, condition (2), the
sheaf condition for every morphism of the site with affine target which is flat, proper,
surjective and of finite presentation, condition (3), cartesianness of the image of every almost
blowup square of the site with affine base and the shape of Example 0EVG, and condition (4), the
same for the shape of Example 0EVH.

This is
`AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares` with
its first hypothesis discharged: the sufficiency direction of Stacks 0EVF is available here, as
`AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion`.  So `hind`, the reduction of condition (3)
of Stacks 0EVF to the two shapes, is all that stands between the four conditions and the sheaf
property; it is the content of the proof of Stacks 0EVI itself and is unproved here, which is why
this statement bears no `@[stacks 0EVI]` attribute either — the tag sits on the necessity results
above, which are unconditional. -/
public theorem isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares_of_reduction
    (hind : GeneratorAlmostBlowUpSquaresSuffice.{u, v})
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F ↔
      (BigHOver.IsZariskiSheaf B S hS F ∧
        BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
        BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F ∧
        BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS F) :=
  isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares
    affineAlmostBlowUpHSheafCriterion hind B S hS F

end BigHOver

end AlgebraicGeometry

end
