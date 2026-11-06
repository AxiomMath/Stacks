module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.FormalDisk
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.OrbitSeparation

/-!
# A set-theoretically invariant morphism out of the formal disk which is not invariant

Let `k` be a field in which two is invertible and let `X = 𝔸¹_k/R` be the quotient of
`AlgebraicGeometry.AffineLineInvolution` identifying each nonzero point of the affine line
with its negative.  The formal disk `D = Spec k[[t]]` has two morphisms to `X`, obtained by
sending the coordinate of the affine line to `t` and to `-t`.  They agree on every
field-valued point of `D`, because such a point either kills `t` — and then the two
coordinates agree already on the affine line — or inverts it, and then the two coordinates
are the two endpoints of an arrow of `R`.  Yet the two morphisms are different, because an
arrow of `R` out of `D` would have to land in one of the two summands of `R = Δ ⨿ Γ`, the
disk being connected, and neither is possible.

Consequently the hypothesis of local separatedness in the criterion promoting
set-theoretic invariance to invariance (**Stacks 048Y**) cannot be weakened to
quasi-separatedness: `X` is quasi-separated, `D` is reduced, and the pre-relation on `D`
given by the identity and the coordinate involution admits a set-theoretically invariant
morphism to `X` which is not invariant.

Both `X` and `D` are moreover reduced quasi-separated algebraic spaces, so the pair
`a, b : D ⟶ X` is the pair of morphisms of reduced quasi-separated algebraic spaces which
agree on all field-valued points without being equal.

## Main definitions

* `AlgebraicGeometry.Space.involutionProjection` is the projection of the functor of points
  of the affine line onto the quotient sheaf of the involution relation.
* `AlgebraicGeometry.Space.diskToInvolutionQuotient` and
  `AlgebraicGeometry.Space.diskToInvolutionQuotientNeg` are the two morphisms from the
  formal disk to the quotient, the coordinate and its negative followed by the projection.

## Main results

* `AlgebraicGeometry.Space.diskMaps_agree_on_fieldPoints`: the two morphisms agree after
  every field-valued point of the disk.
* `AlgebraicGeometry.Space.diskMaps_ne`: the two morphisms are nevertheless distinct.
* `AlgebraicGeometry.Space.exists_setTheoreticallyInvariant_not_invariant`: the resulting
  pre-relation on the formal disk with a set-theoretically invariant morphism which is not
  invariant, so that quasi-separatedness cannot replace local separatedness in **Stacks
  048Y**.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_involutionQuotient` and
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_siteFormalDisk`: the quotient is
  reduced and the formal disk is quasi-separated, the two assertions of the example not
  already available for the other space.
* `AlgebraicGeometry.Space.exists_agree_on_fieldPoints_ne_and_not_invariant`: the example
  itself — a pair of morphisms of reduced quasi-separated algebraic spaces agreeing on all
  field-valued points but not equal, together with the consequence for **Stacks 048Y**.
* `AlgebraicGeometry.Space.surjective_involutionQuotient_product`,
  `AlgebraicGeometry.Space.etale_involutionQuotient_product` and
  `AlgebraicGeometry.Space.isPullback_involutionRelation_diagonal`: the product of the
  quotient chart with itself is surjective and étale, and the defining relation is the
  pullback of the diagonal of the quotient along it.

## Implementation notes

The formal disk, its two coordinates and its coordinate involution are
`AlgebraicGeometry.formalDisk`, `AlgebraicGeometry.diskCoordinate`,
`AlgebraicGeometry.diskNegativeCoordinate` and `AlgebraicGeometry.diskNegation`; only the
two morphisms to the quotient are new here.

Quasi-separatedness of the quotient is **Stacks 02Z1**, available unconditionally as
`AlgebraicGeometry.AffineLineInvolution.isAbsolutelyQuasiSeparated_involutionQuotient`;
`AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source`, which is
**Stacks 073B** part (2), turns it into quasi-separatedness of the structure morphism.  So
nothing is assumed here beyond the site containing the terminal scheme, which the absolute
separation properties of **Stacks 03BS** need in order to be stated at all.

Reducedness of the quotient comes from smoothness of the quotient over `Spec k`, which is
`AlgebraicGeometry.AffineLineInvolution.isSmooth_involutionQuotient`, together with
`AlgebraicGeometry.Space.isReduced_source_of_isSmooth`.  Quasi-separatedness of the formal
disk is the étale-atlas criterion
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection`
at the identity atlas, the disk being affine.

Distinctness of the two morphisms rests on the relation being the kernel pair of the
projection onto the quotient sheaf.  That is available with no descent hypothesis and no
algebraicity hypothesis on the quotient, because the functors of points of the affine line
and of the relation scheme are already sheaves for the big fppf topology
(`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj`) and
sheafification is left exact.  That square is
`Stacks.Groupoids.isPullback_toQuotientSheaf_self`, whose pointwise input is
`Stacks.Groupoids.toQuotientPresheaf_apply_eq_iff_related`.

## References

* [Stacks Project, Tag 048Z](https://stacks.math.columbia.edu/tag/048Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry.Space

open AffineLineInvolution

/-- A kernel pair is the pullback of the diagonal along the product of the map with
itself. -/
private theorem isPullback_lift_of_isPullback_of_diag {C : Type v} [Category.{w} C]
    [HasBinaryProducts C] {R U X : C} {t s : R ⟶ U} {q : U ⟶ X}
    (h : IsPullback t s q q) :
    IsPullback (prod.lift t s) (t ≫ q) (prod.map q q) (prod.lift (𝟙 X) (𝟙 X)) := by
  have hcomm : prod.lift t s ≫ prod.map q q =
      (t ≫ q) ≫ prod.lift (𝟙 X) (𝟙 X) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, ← Category.assoc, prod.lift_fst, Category.assoc,
        prod.lift_fst, Category.comp_id]
    · rw [Category.assoc, prod.map_snd, ← Category.assoc, prod.lift_snd, Category.assoc,
        prod.lift_snd, Category.comp_id, h.w]
  refine IsPullback.mk' hcomm ?_ ?_
  · intro T φ ψ htop _
    refine h.hom_ext ?_ ?_
    · simpa only [Category.assoc, prod.lift_fst] using
        congrArg (fun f => f ≫ prod.fst) htop
    · simpa only [Category.assoc, prod.lift_snd] using
        congrArg (fun f => f ≫ prod.snd) htop
  · intro T a b hab
    have hfst : (a ≫ prod.fst) ≫ q = b := by
      rw [Category.assoc]
      simpa only [Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id] using
        congrArg (fun f => f ≫ prod.fst) hab
    have hsnd : (a ≫ prod.snd) ≫ q = b := by
      rw [Category.assoc]
      simpa only [Category.assoc, prod.map_snd, prod.lift_snd, Category.comp_id] using
        congrArg (fun f => f ≫ prod.snd) hab
    refine ⟨h.lift (a ≫ prod.fst) (a ≫ prod.snd) (hfst.trans hsnd.symm), ?_, ?_⟩
    · refine prod.hom_ext ?_ ?_
      · simpa only [Category.assoc, prod.lift_fst] using
          h.lift_fst (a ≫ prod.fst) (a ≫ prod.snd) (hfst.trans hsnd.symm)
      · simpa only [Category.assoc, prod.lift_snd] using
          h.lift_snd (a ≫ prod.fst) (a ≫ prod.snd) (hfst.trans hsnd.symm)
    · rw [← Category.assoc, h.lift_fst (a ≫ prod.fst) (a ≫ prod.snd) (hfst.trans hsnd.symm)]
      exact hfst

/-- A property of morphisms of presheaves which is stable under base change and under
composition holds for the product of a morphism with itself as soon as it holds for the
morphism. -/
private theorem presheaf_prod_map {C : Type v} [Category.{w} C]
    (Q : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
    {A X : Cᵒᵖ ⥤ Type u} (f : A ⟶ X) (hf : Q f) : Q (prod.map f f) := by
  have h₁ : Q (prod.map f (𝟙 A)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id f A) hf
  have h₂ : Q (prod.map (𝟙 X) f) := by
    have hpre : Q ((prod.braiding X A).hom ≫ prod.map f (𝟙 X)) :=
      MorphismProperty.RespectsIso.precomp Q (prod.braiding X A).hom _
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (IsPullback.of_prod_fst_with_id f X) hf)
    have hpost : Q ((prod.braiding X A).hom ≫ prod.map f (𝟙 X) ≫
        (prod.braiding X X).hom) :=
      MorphismProperty.RespectsIso.postcomp Q (prod.braiding X X).hom _ hpre
    have heq : (prod.braiding X A).hom ≫ prod.map f (𝟙 X) ≫ (prod.braiding X X).hom =
        prod.map (𝟙 X) f := by
      refine prod.hom_ext ?_ ?_ <;> simp [prod.braiding]
    rwa [← heq]
  have heq : prod.map f (𝟙 A) ≫ prod.map (𝟙 X) f = prod.map f f := by
    refine prod.hom_ext ?_ ?_ <;> simp
  rw [← heq]
  exact MorphismProperty.comp_mem Q _ _ h₁ h₂

/-! ### The quotient chart of the involution relation -/

variable (k : Type u) [Field k]

/-- The projection of the functor of points of the affine line onto the quotient sheaf of
the involution relation. -/
noncomputable abbrev involutionProjection (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :=
  Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS)
    (Over.post B.inclusion) (involutionRelation k)

private theorem isPullback_involutionProjection (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    IsPullback (Stacks.Groupoids.targetMap (Over.post B.inclusion) (involutionRelation k))
      (Stacks.Groupoids.sourceMap (Over.post B.inclusion) (involutionRelation k))
      (involutionProjection k B hS) (involutionProjection k B hS) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation (involutionRelation k) :=
    isEtaleEquivalenceRelation k
  exact Stacks.Groupoids.isPullback_toQuotientSheaf_self _ _ (involutionRelation k)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B _ hS (relationScheme k))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B _ hS (affineLine k))

/-- A property of the quotient chart of the involution relation transfers to the projection
onto the quotient sheaf of the functor of points, the two differing by the canonical
isomorphism identifying the functor of points of the affine line with the presheaf it
represents in the site. -/
private theorem presheaf_involutionProjection (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (P : MorphismProperty Scheme.{u})
    (hP : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
      (yonedaEquiv.symm
        ((involutionProjection k B hS).app (op (affineLineChart k B hS))
          (𝟙 ((Over.post B.inclusion).obj (affineLineChart k B hS)))))) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS))) (involutionProjection k B hS) := by
  have hri : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS))).RespectsIso := inferInstance
  have : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  have hiso : IsIso (Stacks.Groupoids.yonedaToPoints
      (Over.post (X := B.obj hS) B.inclusion) (affineLineChart k B hS)) :=
    Stacks.Groupoids.isIso_yonedaToPoints _ _
  have heq : Stacks.Groupoids.yonedaToPoints (Over.post B.inclusion)
        (affineLineChart k B hS) ≫ involutionProjection k B hS =
      yonedaEquiv.symm
        ((involutionProjection k B hS).app (op (affineLineChart k B hS))
          (𝟙 ((Over.post B.inclusion).obj (affineLineChart k B hS)))) :=
    (Stacks.Groupoids.yonedaEquiv_symm_app_toQuotientSheaf
      (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
      (affineLineChart k B hS) (involutionRelation k)).symm
  rw [← heq] at hP
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
    (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
      (affineLineChart k B hS))
    (involutionProjection k B hS)).mp hP

/-- The product of the projection onto the quotient sheaf with itself inherits a property of
morphisms of schemes which is stable under composition from the quotient chart. -/
private theorem presheaf_prod_map_involutionProjection (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    (hP : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
      (yonedaEquiv.symm
        ((involutionProjection k B hS).app (op (affineLineChart k B hS))
          (𝟙 ((Over.post B.inclusion).obj (affineLineChart k B hS)))))) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
      (prod.map (involutionProjection k B hS) (involutionProjection k B hS)) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B (Spec (.of k)) hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact presheaf_prod_map _ _ (presheaf_involutionProjection k B hS _ hP)

/-- The product of the quotient chart of the involution relation with itself is surjective
after every representable base change. -/
theorem surjective_involutionQuotient_product (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B (Spec (.of k)) hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
      (prod.map (involutionProjection k B hS) (involutionProjection k B hS)) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  have : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => ⟨hg.1.comp hf.1⟩⟩
  exact presheaf_prod_map_involutionProjection k B hS _
    (surjective_toQuotientSheaf B (Spec (.of k)) hS (affineLineChart k B hS)
      (involutionRelation k) hdesc)

/-- The product of the quotient chart of the involution relation with itself is étale after
every representable base change. -/
theorem etale_involutionQuotient_product (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B (Spec (.of k)) hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hS)))
      (prod.map (involutionProjection k B hS) (involutionProjection k B hS)) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  exact presheaf_prod_map_involutionProjection k B hS _
    (etale_toQuotientSheaf B (Spec (.of k)) hS (affineLineChart k B hS)
      (involutionRelation k) hdesc)

/-- Away from characteristic two, the involution relation is the inverse image of the
diagonal of the quotient along the product of the quotient chart with itself. -/
theorem isPullback_involutionRelation_diagonal (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    IsPullback
      (prod.lift
        (Stacks.Groupoids.targetMap (Over.post B.inclusion) (involutionRelation k))
        (Stacks.Groupoids.sourceMap (Over.post B.inclusion) (involutionRelation k)))
      (Stacks.Groupoids.targetMap (Over.post B.inclusion) (involutionRelation k) ≫
        involutionProjection k B hS)
      (prod.map (involutionProjection k B hS) (involutionProjection k B hS))
      (prod.lift (𝟙 _) (𝟙 _)) :=
  isPullback_lift_of_isPullback_of_diag (isPullback_involutionProjection k hchar B hS)

/-! ### The two morphisms from the formal disk to the quotient -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  (hD : B.Contains (Spec (.of (PowerSeries k))))

/-- **Stacks 048Z.** The morphism from the formal disk to the quotient of the affine line by
the involution relation given by the power-series variable. -/
@[stacks 048Z "the coordinate map to the quotient"]
noncomputable def diskToInvolutionQuotient
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    yoneda.obj (siteFormalDisk k B hS hD) ⟶ (involutionQuotient k B hS).obj :=
  yonedaEquiv.symm
    ((involutionProjection k B hS).app (op (siteFormalDisk k B hS hD)) (diskCoordinate k))

/-- **Stacks 048Z.** The morphism from the formal disk to the quotient of the affine line by
the involution relation given by the negative of the power-series variable. -/
@[stacks 048Z "the negated coordinate map to the quotient"]
noncomputable def diskToInvolutionQuotientNeg
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    yoneda.obj (siteFormalDisk k B hS hD) ⟶ (involutionQuotient k B hS).obj :=
  yonedaEquiv.symm
    ((involutionProjection k B hS).app (op (siteFormalDisk k B hS hD))
      (diskNegativeCoordinate k))

/-! ### Agreement on field-valued points -/

private theorem diskCoordinate_appTop_coord :
    (diskCoordinate k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      (Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem diskNegativeCoordinate_appTop_coord :
    (diskNegativeCoordinate k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      (Scheme.ΓSpecIso (.of (PowerSeries k))).inv (-PowerSeries.X) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem appTop_coord_comp_affineLineNeg {T : Over (Spec (.of k))}
    (f : T ⟶ affineLine k) :
    (f ≫ affineLineNeg k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      -f.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) := by
  have hn : (affineLineNeg k).left.appTop
      (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
        -AffineSpace.coord (Spec (.of k)) PUnit.unit :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  show (f.left ≫ (affineLineNeg k).left).appTop _ = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hn, map_neg]

private theorem diskCoordinate_comp_affineLineNeg :
    diskCoordinate k ≫ affineLineNeg k = diskNegativeCoordinate k := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_)
  · exact (diskCoordinate k ≫ affineLineNeg k).w.trans (diskNegativeCoordinate k).w.symm
  · intro i
    cases i
    rw [appTop_coord_comp_affineLineNeg k (diskCoordinate k), diskCoordinate_appTop_coord k,
      diskNegativeCoordinate_appTop_coord k, map_neg]

private theorem diskNegation_comp_diskCoordinate :
    diskNegation k ≫ diskCoordinate k = diskNegativeCoordinate k := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_)
  · exact (diskNegation k ≫ diskCoordinate k).w.trans (diskNegativeCoordinate k).w.symm
  · intro i
    simp only [Over.comp_left, diskCoordinate, diskNegativeCoordinate, Over.homMk_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord]
    show (Spec.map (CommRingCat.ofHom (PowerSeries.rescale (-1 : k)))).appTop
      ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X) = _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- A morphism to the affine line whose coordinate is invertible factors through the
punctured affine line. -/
private theorem exists_puncturedAffineLine_lift {T : Over (Spec (.of k))}
    (f : T ⟶ affineLine k)
    (hf : IsUnit (f.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))) :
    ∃ l : T ⟶ puncturedAffineLine k, l ≫ puncturedAffineLineInclusion k = f := by
  have hr : Set.range f.left ⊆ Set.range (puncturedAffineLineOpen k).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h := Scheme.preimage_basicOpen_top f.left
      (AffineSpace.coord (Spec (.of k)) PUnit.unit)
    rw [T.left.basicOpen_of_isUnit hf] at h
    exact (show x ∈ f.left ⁻¹ᵁ puncturedAffineLineOpen k from h.symm ▸ Set.mem_univ x)
  have hl : IsOpenImmersion.lift (puncturedAffineLineOpen k).ι f.left hr ≫
      (puncturedAffineLineOpen k).ι = f.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (IsOpenImmersion.lift (puncturedAffineLineOpen k).ι f.left hr) ?_,
    Over.OverMorphism.ext hl⟩
  show IsOpenImmersion.lift (puncturedAffineLineOpen k).ι f.left hr ≫
    ((puncturedAffineLineOpen k).ι ≫ (affineLine k).hom) = T.hom
  rw [← Category.assoc, hl, f.w]

/-- **Stacks 048Z.** The two morphisms from the formal disk to the quotient agree after
every field-valued point of the disk. -/
@[stacks 048Z "agreement on field-valued points"]
theorem diskMaps_agree_on_fieldPoints
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (β : Spec (.of K) ⟶ Spec (.of k))
    (g : (Over.mk (ObjectProperty.homMk β : B.obj hK ⟶ B.obj hS) :
      BigFppfOver B (Spec (.of k)) hS) ⟶ siteFormalDisk k B hS hD) :
    yoneda.map g ≫ diskToInvolutionQuotient k B hS hD =
      yoneda.map g ≫ diskToInvolutionQuotientNeg k B hS hD := by
  let T : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (ObjectProperty.homMk β : B.obj hK ⟶ B.obj hS)
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) :=
    Over.post (X := B.obj hS) B.inclusion
  let f : F.obj T ⟶ affineLine k := F.map g ≫ diskCoordinate k
  let q := involutionProjection k B hS
  have hneg : F.map g ≫ diskNegativeCoordinate k = f ≫ affineLineNeg k :=
    ((congrArg (fun z => F.map g ≫ z) (diskCoordinate_comp_affineLineNeg k)).symm.trans
      (Category.assoc _ _ _).symm)
  have heq : q.app (op T) f = q.app (op T) (f ≫ affineLineNeg k) := by
    by_cases hz : f.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = 0
    · refine congrArg (q.app (op T)) (Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_))
      · exact f.w.trans (f ≫ affineLineNeg k).w.symm
      · intro i
        cases i
        rw [appTop_coord_comp_affineLineNeg, hz, neg_zero]
    · have hu : IsUnit (f.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) := by
        refine (isUnit_map_iff (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv _).mp
          (isUnit_iff_ne_zero.mpr fun h => hz ?_)
        exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
          (h.trans (map_zero _).symm)
      obtain ⟨l, hl⟩ := exists_puncturedAffineLine_lift k f hu
      have h : q.app (op T) ((l ≫ coprod.inr) ≫ (involutionRelation k).source) =
          q.app (op T) ((l ≫ coprod.inr) ≫ (involutionRelation k).target) :=
        congrArg (fun z => z.app (op T) (l ≫ coprod.inr))
          (Stacks.Groupoids.sourceMap_toQuotientSheaf
            (BigFppfOver.topology B (Spec (.of k)) hS) F
            (involutionRelation k))
      have ht : (l ≫ coprod.inr) ≫ (involutionRelation k).target = f := by
        rw [involutionRelation_target, Category.assoc, coprod.inr_desc, hl]
      have hs : (l ≫ coprod.inr) ≫ (involutionRelation k).source =
          f ≫ affineLineNeg k := by
        rw [involutionRelation_source, Category.assoc, coprod.inr_desc, ← Category.assoc, hl]
      exact (congrArg (q.app (op T)) ht).symm.trans
        (h.symm.trans (congrArg (q.app (op T)) hs))
  rw [diskToInvolutionQuotient, diskToInvolutionQuotientNeg, yonedaEquiv_symm_naturality_left,
    yonedaEquiv_symm_naturality_left]
  refine congrArg yonedaEquiv.symm ?_
  calc
    _ = q.app (op T) f := (q.naturality_apply g.op (diskCoordinate k)).symm
    _ = q.app (op T) (F.map g ≫ diskNegativeCoordinate k) := by rwa [hneg]
    _ = _ := q.naturality_apply g.op (diskNegativeCoordinate k)

/-! ### Distinctness of the two morphisms -/

/-- A morphism from a connected scheme to a binary coproduct factors through one of the two
summands. -/
private theorem exists_coprod_factorization {T X Y : Scheme.{u}}
    [PreconnectedSpace T] (r : T ⟶ X ⨿ Y) :
    (∃ f : T ⟶ X, f ≫ coprod.inl = r) ∨ (∃ f : T ⟶ Y, f ≫ coprod.inr = r) := by
  have hc : IsClopen (Set.range (coprod.inl : X ⟶ X ⨿ Y)) := by
    refine ⟨?_, (coprod.inl : X ⟶ X ⨿ Y).opensRange.isOpen⟩
    rw [(isCompl_range_inl_inr X Y).eq_compl]
    exact (coprod.inr : Y ⟶ X ⨿ Y).opensRange.isOpen.isClosed_compl
  rcases isClopen_iff.mp (hc.preimage r.continuous) with he | hu
  · right
    have hr : Set.range r ⊆ Set.range (coprod.inr : Y ⟶ X ⨿ Y) := by
      rintro _ ⟨t, rfl⟩
      have ht : r t ∉ Set.range (coprod.inl : X ⟶ X ⨿ Y) := fun h => by
        simpa only [he, Set.mem_empty_iff_false] using
          (show t ∈ r ⁻¹' Set.range (coprod.inl : X ⟶ X ⨿ Y) from h)
      simpa only [(isCompl_range_inl_inr X Y).eq_compl, Set.mem_compl_iff, not_not] using ht
    exact ⟨IsOpenImmersion.lift _ r hr, IsOpenImmersion.lift_fac _ r hr⟩
  · left
    have hr : Set.range r ⊆ Set.range (coprod.inl : X ⟶ X ⨿ Y) := by
      rintro _ ⟨t, rfl⟩
      exact (show t ∈ r ⁻¹' Set.range (coprod.inl : X ⟶ X ⨿ Y) from
        hu.symm ▸ Set.mem_univ t)
    exact ⟨IsOpenImmersion.lift _ r hr, IsOpenImmersion.lift_fac _ r hr⟩

/-- A morphism over a base from an object with connected underlying space to a binary
coproduct factors through one of the two summands. -/
private theorem exists_over_coprod_factorization {S : Scheme.{u}} {T X Y : Over S}
    [PreconnectedSpace T.left] (r : T ⟶ X ⨿ Y) :
    (∃ f : T ⟶ X, f ≫ coprod.inl = r) ∨ (∃ f : T ⟶ Y, f ≫ coprod.inr = r) := by
  let e := PreservesColimitPair.iso (Over.forget S) X Y
  have key : ∀ {Z : Over S} (ι : Z ⟶ X ⨿ Y) (c : (Over.forget S).obj Z ⟶ _),
      c ≫ e.hom = ι.left → (∃ f : T.left ⟶ Z.left, f ≫ c = r.left ≫ e.inv) →
        ∃ f : T ⟶ Z, f ≫ ι = r := by
    rintro Z ι c hc ⟨f, hf⟩
    have hf' : f ≫ ι.left = r.left := by
      rw [← hc, ← Category.assoc, hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ⟨Over.homMk f (by rw [← ι.w, ← Category.assoc, hf', r.w]),
      Over.OverMorphism.ext hf'⟩
  rcases exists_coprod_factorization (r.left ≫ e.inv) with h | h
  · exact Or.inl (key _ coprod.inl
      (by rw [PreservesColimitPair.iso_hom]; exact coprodComparison_inl (Over.forget S) X Y) h)
  · exact Or.inr (key _ coprod.inr
      (by rw [PreservesColimitPair.iso_hom]; exact coprodComparison_inr (Over.forget S) X Y) h)

/-- Away from characteristic two, the coordinate of the formal disk differs from its
negative. -/
private theorem diskCoordinate_ne_diskNegativeCoordinate (hchar : (2 : k) ≠ 0) :
    diskCoordinate k ≠ diskNegativeCoordinate k := by
  intro h
  have hx := congrArg (fun f : formalDisk k ⟶ affineLine k =>
    f.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
  rw [diskCoordinate_appTop_coord k, diskNegativeCoordinate_appTop_coord k] at hx
  have hx' : (PowerSeries.X : PowerSeries k) = -PowerSeries.X :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (PowerSeries k))).inv).1 hx
  have hcoeff : (1 : k) = -1 := by simpa using congrArg (PowerSeries.coeff 1) hx'
  exact hchar (by linear_combination hcoeff)

/-- The coordinate of the formal disk does not factor through the punctured affine line: the
power-series variable lies in the kernel of the constant-term map. -/
private theorem diskCoordinate_not_puncturedAffineLine
    (f : formalDisk k ⟶ puncturedAffineLine k) :
    f ≫ puncturedAffineLineInclusion k ≠ diskCoordinate k := by
  intro hf
  have hp : (diskCoordinate k).left ⁻¹ᵁ puncturedAffineLineOpen k = ⊤ := by
    rw [← hf]
    ext x
    simp [puncturedAffineLineInclusion]
  rw [puncturedAffineLineOpen, Scheme.preimage_basicOpen_top,
    diskCoordinate_appTop_coord k] at hp
  change (Spec (.of (PowerSeries k))).basicOpen
    ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X) = ⊤ at hp
  rw [basicOpen_eq_of_affine] at hp
  have hx : (⟨RingHom.ker PowerSeries.constantCoeff, RingHom.ker_isPrime _⟩ :
      PrimeSpectrum (PowerSeries k)) ∈
      PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries k) :=
    hp.symm ▸ Set.mem_univ _
  exact hx (by simp [RingHom.mem_ker])

/-- Away from characteristic two, two points of the affine line with the same image in the
quotient are the target and the source of a point of the relation scheme. -/
private theorem exists_involutionRelation_of_quotient_eq (hchar : (2 : k) ≠ 0)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (T : BigFppfOver B (Spec (.of k)) hS)
    (f g : (Over.post B.inclusion).obj T ⟶ affineLine k)
    (he : (involutionProjection k B hS).app (op T) f =
      (involutionProjection k B hS).app (op T) g) :
    ∃ r : (Over.post B.inclusion).obj T ⟶ relationScheme k,
      r ≫ (involutionRelation k).target = f ∧
        r ≫ (involutionRelation k).source = g :=
  Types.exists_of_isPullback
    ((isPullback_involutionProjection k hchar B hS).map
      ((evaluation (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ (Type u)).obj (op T))) f g he

/-- **Stacks 048Z.** Away from characteristic two, the two morphisms from the formal disk to
the quotient are nevertheless distinct. -/
@[stacks 048Z "distinct morphisms"]
theorem diskMaps_ne (hchar : (2 : k) ≠ 0)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    diskToInvolutionQuotient k B hS hD ≠ diskToInvolutionQuotientNeg k B hS hD := by
  intro he
  obtain ⟨r, ht, hs⟩ := exists_involutionRelation_of_quotient_eq k B hS hchar
    (siteFormalDisk k B hS hD) (diskCoordinate k) (diskNegativeCoordinate k)
    (yonedaEquiv.symm.injective he)
  have : PreconnectedSpace (formalDisk k).left := by
    show PreconnectedSpace (PrimeSpectrum (PowerSeries k))
    infer_instance
  rcases exists_over_coprod_factorization
      (show formalDisk k ⟶ relationScheme k from r) with ⟨f, hf⟩ | ⟨f, hf⟩
  · have ht' : (f ≫ coprod.inl) ≫ (involutionRelation k).target = diskCoordinate k :=
      (congrArg (fun z : formalDisk k ⟶ relationScheme k =>
        z ≫ (involutionRelation k).target) hf).trans ht
    have hs' : (f ≫ coprod.inl) ≫ (involutionRelation k).source =
        diskNegativeCoordinate k :=
      (congrArg (fun z : formalDisk k ⟶ relationScheme k =>
        z ≫ (involutionRelation k).source) hf).trans hs
    rw [Category.assoc, involutionRelation_target, coprod.inl_desc, Category.comp_id] at ht'
    rw [Category.assoc, involutionRelation_source, coprod.inl_desc, Category.comp_id] at hs'
    exact diskCoordinate_ne_diskNegativeCoordinate k hchar (ht'.symm.trans hs')
  · have ht' : (f ≫ coprod.inr) ≫ (involutionRelation k).target = diskCoordinate k :=
      (congrArg (fun z : formalDisk k ⟶ relationScheme k =>
        z ≫ (involutionRelation k).target) hf).trans ht
    rw [Category.assoc, involutionRelation_target, coprod.inr_desc] at ht'
    exact diskCoordinate_not_puncturedAffineLine k f ht'

/-! ### Quasi-separatedness does not suffice in the invariance criterion -/

/-- Negation on the formal disk followed by the coordinate map to the quotient is the
negated coordinate map. -/
private theorem siteDiskNegation_comp_diskToInvolutionQuotient
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    yoneda.map (siteDiskNegation k B hS hD) ≫ diskToInvolutionQuotient k B hS hD =
      diskToInvolutionQuotientNeg k B hS hD := by
  rw [diskToInvolutionQuotient, diskToInvolutionQuotientNeg, yonedaEquiv_symm_naturality_left,
    ← diskNegation_comp_diskCoordinate]
  exact congrArg yonedaEquiv.symm
    ((involutionProjection k B hS).naturality_apply (siteDiskNegation k B hS hD).op
      (diskCoordinate k)).symm

include hD in
/-- **Stacks 048Z.** Quasi-separatedness of the target cannot replace local separatedness in
the criterion `AlgebraicGeometry.Space.isInvariant_of_isSetTheoreticallyInvariant_of_reduced`
(**Stacks 048Y**): over a field in which two is invertible there is a pre-relation on a
reduced algebraic space, with quasi-separated target, carrying a set-theoretically invariant
morphism which is not invariant.

The relation is the formal disk, acting on itself by the identity and by negation of the
coordinate, and the morphism is the coordinate map to the quotient of the affine line by the
involution relation.  Quasi-separatedness of that quotient is **Stacks 02Z1**, taken from
`AlgebraicGeometry.AffineLineInvolution.isAbsolutelyQuasiSeparated_involutionQuotient` and
converted to quasi-separatedness of the structure morphism by **Stacks 073B** part (2). -/
@[stacks 048Z "quasi-separatedness does not suffice"]
theorem exists_setTheoreticallyInvariant_not_invariant (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    ∃ (Z : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u) (R U X : Over Z)
      (j : PreRelation R U) (φ : U ⟶ X),
      HasEtaleLocalProperty B (Spec (.of k)) hS R.left (fun T : Scheme.{u} ↦ IsReduced T) ∧
        IsQuasiSeparated B (Spec (.of k)) hS X.hom ∧
        IsSetTheoreticallyInvariant j φ.left ∧ ¬ IsInvariant j φ.left := by
  have hqs : IsQuasiSeparated B (Spec (.of k)) hS
      (terminal.from (involutionQuotient k B hS).obj) :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (Spec (.of k)) hS hZ
      (isAlgebraicSpace_involutionQuotient k hchar B hS)
      (isAbsolutelyQuasiSeparated_involutionQuotient k B hS hchar hZ) _
  let D : Over (⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)) :=
    Over.mk (terminal.from (yoneda.obj (siteFormalDisk k B hS hD)))
  let Q : Over (⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)) :=
    Over.mk (terminal.from (involutionQuotient k B hS).obj)
  let n : D ⟶ D := Over.homMk (yoneda.map (siteDiskNegation k B hS hD))
    (terminal.hom_ext _ _)
  let j : PreRelation D D := prod.lift n (𝟙 D)
  let φ : D ⟶ Q := Over.homMk (diskToInvolutionQuotient k B hS hD) (terminal.hom_ext _ _)
  have hs : j.source = 𝟙 D := prod.lift_snd _ _
  have ht : j.target = n := prod.lift_fst _ _
  have hna := siteDiskNegation_comp_diskToInvolutionQuotient k B hS hD
  refine ⟨_, D, D, Q, j, φ, formalDisk_hasEtaleLocalProperty_isReduced k B hS hD, hqs,
    ?_, ?_⟩
  · rintro p x y ⟨r, hx, hy⟩
    rw [← hx, ← hy, congrArg Over.Hom.left ht, congrArg Over.Hom.left hs]
    show (r.1 ≫ yoneda.map (siteDiskNegation k B hS hD)) ≫
        diskToInvolutionQuotient k B hS hD =
      (r.1 ≫ 𝟙 _) ≫ diskToInvolutionQuotient k B hS hD
    rw [Category.assoc, hna, Category.comp_id, ← Yoneda.fullyFaithful.map_preimage r.1]
    exact (diskMaps_agree_on_fieldPoints k B hS hD p.val.carrier p.val.contained
      p.val.toBase (Yoneda.fullyFaithful.preimage r.1)).symm
  · intro hinv
    change j.target.left ≫ φ.left = j.source.left ≫ φ.left at hinv
    rw [congrArg Over.Hom.left ht, congrArg Over.Hom.left hs, Over.id_left,
      Category.id_comp] at hinv
    change yoneda.map (siteDiskNegation k B hS hD) ≫ diskToInvolutionQuotient k B hS hD =
      diskToInvolutionQuotient k B hS hD at hinv
    rw [hna] at hinv
    exact diskMaps_ne k B hS hD hchar hinv.symm

/-! ### The two spaces are reduced and quasi-separated -/

/-- The scheme underlying the formal disk, $\operatorname{Spec} k[[t]]$, is affine. -/
instance isAffine_siteFormalDisk :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (siteFormalDisk k B hS hD)) := by
  change IsAffine (Spec (.of (PowerSeries k)))
  infer_instance

include hD in
/-- The formal disk, as an object of the big fppf site, is quasi-separated over the terminal
scheme: it is an affine scheme. -/
private theorem quasiSeparated_siteFormalDisk :
    QuasiSeparated (B.inclusion.map (siteFormalDisk k B hS hD).hom ≫
      terminal.from (Spec (.of k))) := by
  have h := (quasiSeparatedSpace_iff_quasiSeparated
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (siteFormalDisk k B hS hD))).mp
      inferInstance
  rwa [terminal.hom_ext
    (terminal.from ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj
      (siteFormalDisk k B hS hD)))
    (B.inclusion.map (siteFormalDisk k B hS hD).hom ≫ terminal.from (Spec (.of k)))] at h

include hD in
/-- **Stacks 048Z.** The formal disk is a quasi-separated algebraic space: it is represented
by an affine scheme, so its identity is a surjective étale atlas whose kernel pair is the
identity again, and the criterion of **Stacks 07S4** applies. -/
theorem isAbsolutelyQuasiSeparated_siteFormalDisk (hZ : B.Contains (⊤_ Scheme.{u})) :
    IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ
      (yoneda.obj (siteFormalDisk k B hS hD)) := by
  have hR : IsPullback (yoneda.map (𝟙 (siteFormalDisk k B hS hD)))
      (yoneda.map (𝟙 (siteFormalDisk k B hS hD)))
      (𝟙 (yoneda.obj (siteFormalDisk k B hS hD)))
      (𝟙 (yoneda.obj (siteFormalDisk k B hS hD))) := by
    rw [CategoryTheory.Functor.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hiso : ∀ ⦃X Y : BigFppfOver B (Spec (.of k)) hS⦄ (f : X ⟶ Y), IsIso f →
      IsIso ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f) := fun _ _ _ hf => by
    have := hf
    infer_instance
  refine isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    B (Spec (.of k)) hS hZ (isAlgebraicSpace_yoneda B (Spec (.of k)) hS _) ?_ ?_
    (quasiSeparated_siteFormalDisk k B hS hD) hR inferInstance
  · refine presheaf_id_of_iso B _ hS _ ?_ _
    intro _ _ f hf
    have := hiso f hf
    show Surjective ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f)
    infer_instance
  · refine presheaf_id_of_iso B _ hS _ ?_ _
    intro _ _ f hf
    have := hiso f hf
    show Etale ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f)
    infer_instance

/-- **Stacks 048Z.** The quotient of the affine line by the involution relation is a reduced
algebraic space: it is smooth over `Spec k`, which is reduced. -/
theorem hasEtaleLocalProperty_isReduced_involutionQuotient (hchar : (2 : k) ≠ 0)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    HasEtaleLocalProperty B (Spec (.of k)) hS (involutionQuotient k B hS).obj
      (fun T : Scheme.{u} ↦ IsReduced T) := by
  let V : BigFppfOver B (Spec (.of k)) hS := Over.mk (𝟙 (B.obj hS))
  have hVterminal : IsTerminal (yoneda.obj V) :=
    (Over.mkIdTerminal : IsTerminal V).isTerminalObj yoneda _
  let eV : yoneda.obj V ≅ ⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u) :=
    hVterminal.uniqueUpToIso terminalIsTerminal
  have hV : IsReduced ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj V) := by
    show IsReduced (Spec (.of k))
    exact (affine_isReduced_iff _).2 inferInstance
  have hTerm : IsAlgebraicSpace B (Spec (.of k)) hS
      (⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B (Spec (.of k)) hS eV
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hS V)
  have hTermRed : HasEtaleLocalProperty B (Spec (.of k)) hS
      (⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} ↦ IsReduced T) :=
    hasEtaleLocalProperty_of_representable B (Spec (.of k)) hS _
      (fun T : Scheme.{u} ↦ IsReduced T) V eV.symm hV
  exact isReduced_source_of_isSmooth B (Spec (.of k)) hS
    (isAlgebraicSpace_involutionQuotient k hchar B hS) hTerm _
    (isSmooth_involutionQuotient k hchar B hS) hTermRed

include hD in
/-- **Stacks 048Z.** Over a field in which two is invertible there are reduced
quasi-separated algebraic spaces `X`, `Y` and two morphisms `a, b : Y ⟶ X` which agree on
every field-valued point of `Y` yet are not equal; consequently quasi-separatedness of the
target cannot replace local separatedness in the criterion
`AlgebraicGeometry.Space.isInvariant_of_isSetTheoreticallyInvariant_of_reduced` (**Stacks
048Y**), because there is a pre-relation on a reduced algebraic space with quasi-separated
target carrying a set-theoretically invariant morphism which is not invariant.

The spaces are `Y = Spec k[[x]]` and `X = 𝔸¹_k/(Δ ⨿ {(x, -x) | x ≠ 0})`, the algebraic space
of **Stacks 02Z1**, and the two morphisms are the coordinate and its negative followed by the
projection to the quotient.  The pre-relation witnessing the second assertion is `Y` acting
on itself by the identity and by negation of the coordinate. -/
@[stacks 048Z]
theorem exists_agree_on_fieldPoints_ne_and_not_invariant (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    (∃ (X Y : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u) (a b : Y ⟶ X),
        IsAlgebraicSpace B (Spec (.of k)) hS X ∧
        IsAlgebraicSpace B (Spec (.of k)) hS Y ∧
        HasEtaleLocalProperty B (Spec (.of k)) hS X (fun T : Scheme.{u} ↦ IsReduced T) ∧
        HasEtaleLocalProperty B (Spec (.of k)) hS Y (fun T : Scheme.{u} ↦ IsReduced T) ∧
        IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ X ∧
        IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ Y ∧
        (∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
            (β : Spec (.of K) ⟶ Spec (.of k))
            (g : yoneda.obj (Over.mk (ObjectProperty.homMk β : B.obj hK ⟶ B.obj hS) :
              BigFppfOver B (Spec (.of k)) hS) ⟶ Y),
          g ≫ a = g ≫ b) ∧
        a ≠ b) ∧
      ∃ (Z : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u) (R U X : Over Z)
        (j : PreRelation R U) (φ : U ⟶ X),
        HasEtaleLocalProperty B (Spec (.of k)) hS R.left
            (fun T : Scheme.{u} ↦ IsReduced T) ∧
          IsQuasiSeparated B (Spec (.of k)) hS X.hom ∧
          IsSetTheoreticallyInvariant j φ.left ∧ ¬ IsInvariant j φ.left := by
  refine ⟨⟨(involutionQuotient k B hS).obj, yoneda.obj (siteFormalDisk k B hS hD),
    diskToInvolutionQuotient k B hS hD, diskToInvolutionQuotientNeg k B hS hD,
    isAlgebraicSpace_involutionQuotient k hchar B hS,
    isAlgebraicSpace_yoneda B (Spec (.of k)) hS _,
    hasEtaleLocalProperty_isReduced_involutionQuotient k B hS hchar,
    formalDisk_hasEtaleLocalProperty_isReduced k B hS hD,
    isAbsolutelyQuasiSeparated_involutionQuotient k B hS hchar hZ,
    isAbsolutelyQuasiSeparated_siteFormalDisk k B hS hD hZ, ?_,
    diskMaps_ne k B hS hD hchar⟩,
    exists_setTheoreticallyInvariant_not_invariant k B hS hD hchar hZ⟩
  · intro K _ hK β g
    rw [← Yoneda.fullyFaithful.map_preimage g]
    exact diskMaps_agree_on_fieldPoints k B hS hD K hK β (Yoneda.fullyFaithful.preimage g)

end AlgebraicGeometry.Space

end
