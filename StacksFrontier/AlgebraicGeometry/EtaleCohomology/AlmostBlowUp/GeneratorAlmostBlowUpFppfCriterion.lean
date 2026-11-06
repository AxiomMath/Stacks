module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpFppfCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AlmostBlowUpFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpReduction

/-!
# The essential image of `Rε_*` on the big fppf site and the squares of Examples 0EVG and 0EVH

Let `B` be a big h site containing a scheme `S` and let `𝒪` be a sheaf of rings for the h
topology on the big h category over `S`. The fppf topology on that category is coarser than the
h topology, so the identity functor is a comparison of ringed sites
`ε : (C_h, 𝒪_h) ⟶ (C_{fppf}, 𝒪_{fppf})` with derived direct image `Rε_*`.

Stacks 0EWR says that an object `K` of `D⁺(𝒪_{fppf})` is in the essential image of `Rε_*` if and
only if the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is a
quasi-isomorphism for every almost blow up square as in More on Flatness, Examples 0EVG and 0EVH,
that is for every almost blow up square of the site whose modification and centre have one of the
two shapes

```
E = Spec(A/(fA + J)) ⟶ X' = Spec(A/J)
        ↓                        ↓
Z = Spec(A/fA)        ⟶ X = Spec(A)
```

for a ring `A`, an element `f` of `A` and a finitely generated ideal `J` of `A` annihilated by a
power of `f`, and

```
E = Proj (A/(f₁,f₂))[T₀,T₁] ⟶ X' = Proj A[T₀,T₁]/(f₂T₀ - f₁T₁)
        ↓                              ↓
Z = Spec(A/(f₁,f₂))         ⟶ X = Spec(A)
```

for two elements `f₁, f₂` of `A`.

## Main definitions

* `AlgebraicGeometry.IsGeneratorAlmostBlowUpModel`: the modification and the centre have the
  shape of Example 0EVG or the shape of Example 0EVH.
* `AlgebraicGeometry.GeneratorAlmostBlowUpSquare`: an almost blow up square of the big h category
  over `S` as in Examples 0EVG and 0EVH, bundled so that these squares form a family indexed by
  a type.

## Main results

* `AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpFamilyDetecting_generator_fppfTopology`: the
  squares of Examples 0EVG and 0EVH detect h sheaves among fppf sheaves of sets.  This is the
  sufficiency direction of More on Flatness, Lemma 0EVI.
* `AlgebraicGeometry.essImage_iff_forall_isCSquareIso_generatorAlmostBlowUp_fppf_bigH`:
  **Stacks 0EWR**.

## Implementation notes

**The family of squares.** The source quantifies over *almost blow up squares* as in Examples
0EVG and 0EVH, so being an almost blow up square is part of the quantifier, exactly as in
conditions (3) and (4) of Stacks 0EVI, `AlgebraicGeometry.BigHOver.IsOneGeneratorAlmostBlowUpSheaf`
and `AlgebraicGeometry.BigHOver.IsTwoGeneratorAlmostBlowUpSheaf`. It restricts neither shape,
because for both of them being an almost blow up square follows from the shape:
`AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair` and
`AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isTwoGeneratorAlmostBlowUpModel`. Membership of a
shape is the existence of isomorphisms of the base, of the modification and of the centre carrying
the pair to the model pair, so no affine coordinates are pinned on the objects of the site.
Affineness of the base is not a field: it follows from the shape, and
`AlgebraicGeometry.GeneratorAlmostBlowUpSquare.toAffineAlmostBlowUpSquare` exhibits the family as a
subfamily of the one tested by Stacks 0EWQ.

**The proof.** The direction "only if" is Stacks 0EWN and the converse is Stacks 0F18, both
packaged in `AlgebraicGeometry.essImageIffAffineAlmostBlowUpFamilyBigH_of_isDetecting`. The
detection hypothesis of Stacks 0F18 is the sufficiency direction of More on Flatness, Lemma 0EVI
for fppf sheaves: an fppf sheaf satisfies conditions (1) and (2) of that lemma, because a Zariski
covering and a flat proper surjective morphism of finite presentation are fppf coverings, and
cartesianness of its images of the squares of the two shapes is conditions (3) and (4). The
reduction of condition (3) of Stacks 0EVF to conditions (3) and (4) of Stacks 0EVI is
`AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice`, and the sufficiency direction of Stacks
0EVF is `AlgebraicGeometry.BigHOver.isSheaf_of_isFppfSheaf_of_isAffineAlmostBlowUpSheaf`.

**The form of the statement.** The characterization is the assertion
`AlgebraicGeometry.EssImageIffAffineAlmostBlowUpFamilyBigH` for the family of squares of the two
shapes, as Stacks 0EWQ is `AlgebraicGeometry.EssImageIffAffineAlmostBlowUpBigH` at the fppf
topology: the derived categories involved do not elaborate afresh in a module importing the
sufficiency direction of Stacks 0EVF.

## References

* [Stacks Project, Tag 0EWR](https://stacks.math.columbia.edu/tag/0EWR)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EWN](https://stacks.math.columbia.edu/tag/0EWN)
* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v r

namespace AlgebraicGeometry

/-! ### The shape of the squares of Examples 0EVG and 0EVH -/

/-- **The shapes of More on Flatness, Examples 0EVG and 0EVH.** A modification and a centre with
a common base have the shape of Example 0EVG — the closed immersion `Spec (A/J) ⟶ Spec A` for a
finitely generated ideal `J` annihilated by a power of an element `f`, with centre the closed
subscheme cut out by `f` — or the shape of Example 0EVH — the projective hypersurface
`Proj A[T₀,T₁]/(f₂T₀ - f₁T₁) ⟶ Spec A` attached to two elements `f₁, f₂`, with centre
`Spec (A/(f₁,f₂))`. -/
def IsGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) : Prop :=
  IsOneGeneratorAlmostBlowUpModel b z ∨ IsTwoGeneratorAlmostBlowUpModel b z

/-- The base of a pair of morphisms with the shape of Example 0EVG or of Example 0EVH is affine:
both model squares have base `Spec A`, and the shape provides an isomorphism of the base with
it. -/
theorem isAffine_of_isGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}} {b : X' ⟶ X} {z : Z ⟶ X}
    (h : IsGeneratorAlmostBlowUpModel b z) : IsAffine X := by
  rcases h with ⟨A, hA, _f, _J, -, -, iX, -⟩ | ⟨A, hA, _f₁, _f₂, iX, -⟩ <;>
    exact IsAffine.of_isIso iX.hom

/-! ### The family of squares tested by Stacks 0EWR -/

/-- An almost blow up square of the big h category over `S` as in More on Flatness, Examples
0EVG and 0EVH: an almost blow up square of the site whose modification and centre have the shape
of one of the two examples, bundled with its centre. The vertices are, in order, the exceptional
corner, the modification, the centre and the base. -/
structure GeneratorAlmostBlowUpSquare (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    where
  /-- The square of the site. -/
  square : Square (BigHOver B S hS)
  /-- The centre, a quasi-coherent ideal sheaf on the underlying scheme of the base. -/
  center : ((BigHOver.toScheme B S hS).obj square.X₄).IdealSheafData
  /-- The centre and the modification form an almost blow up square. -/
  isAlmostBlowUpSquare :
    IsAlmostBlowUpSquare center ((BigHOver.toScheme B S hS).map square.f₂₄)
  /-- The lower-left vertex is the closed subscheme cut out by the centre, over the base. -/
  centerIso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map square.f₃₄) ≅
    Over.mk center.subschemeι)
  /-- The square of underlying schemes is cartesian, so the upper-left vertex is the exceptional
  corner. -/
  isPullback : (square.map (BigHOver.toScheme B S hS)).IsPullback
  /-- The modification and the centre have the shape of Example 0EVG or of Example 0EVH. -/
  isGeneratorModel :
    IsGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map square.f₂₄)
      ((BigHOver.toScheme B S hS).map square.f₃₄)

namespace GeneratorAlmostBlowUpSquare

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base of a square of one of the two shapes is affine. -/
theorem isAffine_base (sq : GeneratorAlmostBlowUpSquare B S hS) :
    IsAffine ((BigHOver.toScheme B S hS).obj sq.square.X₄) :=
  isAffine_of_isGeneratorAlmostBlowUpModel sq.isGeneratorModel

/-- A square of one of the two shapes is an almost blow up square of the site with affine base,
so the family tested by Stacks 0EWR is a subfamily of the one tested by Stacks 0EWQ. -/
def toAffineAlmostBlowUpSquare (sq : GeneratorAlmostBlowUpSquare B S hS) :
    AffineAlmostBlowUpSquare B S hS where
  square := sq.square
  center := sq.center
  isAffine_base := sq.isAffine_base
  isAlmostBlowUpSquare := sq.isAlmostBlowUpSquare
  centerIso := sq.centerIso
  isPullback := sq.isPullback

/-- The square of the site underlying `sq.toAffineAlmostBlowUpSquare` is that of `sq`. -/
@[simp]
theorem toAffineAlmostBlowUpSquare_square (sq : GeneratorAlmostBlowUpSquare B S hS) :
    sq.toAffineAlmostBlowUpSquare.square = sq.square :=
  rfl

end GeneratorAlmostBlowUpSquare

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sufficiency direction of More on Flatness, Lemma 0EVI, for fppf sheaves.** An fppf
sheaf of sets on the big h category over `S` whose restriction maps along every almost blow up
square of the shape of Example 0EVG or of Example 0EVH form a cartesian square is a sheaf for the
h topology.

An fppf sheaf satisfies conditions (1) and (2) of Stacks 0EVI; cartesianness along the squares of
the two shapes is conditions (3) and (4), which give condition (3) of Stacks 0EVF by
`AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice`; and the sufficiency direction of Stacks
0EVF concludes. -/
theorem isAffineAlmostBlowUpFamilyDetecting_generator_fppfTopology :
    IsAffineAlmostBlowUpFamilyDetecting
      (GeneratorAlmostBlowUpSquare.toAffineAlmostBlowUpSquare (B := B) (S := S) (hS := hS))
      (fppfTopology B S hS) := by
  intro F hF
  have key : ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
      (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
      IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
      Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
      IsPullback ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map p)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b) →
      IsGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) →
      IsPullback (F.obj.map z.op) (F.obj.map b.op) (F.obj.map e.op) (F.obj.map p.op) := by
    intro X X' Z E b z p e I hb hZ hSquare hshape
    have hfac : p ≫ b = e ≫ z :=
      (BigHOver.toScheme B S hS).map_injective (by
        simpa only [Functor.map_comp] using hSquare.flip.w)
    exact (hF { square := ⟨p, e, b, z, hfac⟩
                center := I
                isAlmostBlowUpSquare := hb
                centerIso := hZ
                isPullback := hSquare.flip
                isGeneratorModel := hshape }).flip
  have hzar := isZariskiSheaf_of_isFppfSheaf B S hS F.obj F.property
  have hflat := isAffineFlatProperFinitePresentationSheaf_of_isFppfSheaf B S hS F.obj F.property
  refine isSheaf_of_isFppfSheaf_of_isAffineAlmostBlowUpSheaf B S hS F.obj F.property
    (generatorAlmostBlowUpSquaresSuffice B S hS F.obj hzar hflat ?_ ?_) <;>
  exact fun X X' Z E b z p e I _ hb hZ hSquare hshape ↦
    key X X' Z E b z p e I hb hZ hSquare (by tauto)

end BigHOver

/-! ### Stacks 0EWR -/

section

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r})
  [HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{v}]
  [(BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify (BigHOver.fppfTopology B S hS) AddCommGrpCat.{v}]
  [(BigHOver.fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u + 1, v}] [UnivLE.{u, v}] [UnivLE.{r, v}]

/-- **Stacks 0EWR.** Let `𝒪` be a sheaf of rings for the h topology on the big h category over
`S`, and let `ε : (C_h, 𝒪_h) ⟶ (C_{fppf}, 𝒪_{fppf})` be the comparison of ringed sites given by
the identity functor, the fppf topology on that category being coarser than the h topology. Then
an object `K` of `D⁺(𝒪_{fppf})` lies in the essential image of the derived direct image `Rε_*` if
and only if the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is an
isomorphism for every almost blow up square of the site as in More on Flatness, Examples 0EVG
and 0EVH.

This is `AlgebraicGeometry.essImageIffAffineAlmostBlowUpFamilyBigH_of_isDetecting` at the fppf
topology for the family of squares of the two shapes, whose detection of h sheaves among fppf
sheaves of sets is the sufficiency direction of More on Flatness, Lemma 0EVI,
`AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpFamilyDetecting_generator_fppfTopology`. -/
@[stacks 0EWR]
theorem essImage_iff_forall_isCSquareIso_generatorAlmostBlowUp_fppf_bigH :
    EssImageIffAffineAlmostBlowUpFamilyBigH.{u + 1, u, v, r} B S hS O
      (BigHOver.fppfTopology_le_topology B S hS)
      (GeneratorAlmostBlowUpSquare.toAffineAlmostBlowUpSquare (B := B) (S := S) (hS := hS)) :=
  essImageIffAffineAlmostBlowUpFamilyBigH_of_isDetecting B S hS O
    (BigHOver.fppfTopology_le_topology B S hS) _
    (BigHOver.isAffineAlmostBlowUpFamilyDetecting_generator_fppfTopology B S hS)

end

end AlgebraicGeometry

end
