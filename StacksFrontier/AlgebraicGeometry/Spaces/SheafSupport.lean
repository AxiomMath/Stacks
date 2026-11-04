module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# The support of a sheaf and of a section on the small étale site of an algebraic space

Let `F` be an abelian sheaf on the small étale site of a presheaf `X` on the big fppf site of
`S` — in the intended application an algebraic space over `S`.

The *support of a section* `σ` of `F` over an étale chart `U` of `X` is the complement, in the
point set of the chart, of the largest open subset on which `σ` restricts to zero. That open
subset exists: it is the set of points of `U` lying in the image of some étale chart over `U`
on which `σ` restricts to zero, and the content of the construction is that `σ` already
restricts to zero on every chart whose image is contained in that set.

The *support of the sheaf* is the set of points of `X` at which the stalk at some geometric
point lying over that point is nonzero.

## Main definitions

* `AlgebraicGeometry.Space.ImageInOpen` is the condition on a morphism of étale charts that
  the image of its source lands inside a prescribed set of points of its target.
* `AlgebraicGeometry.Space.zeroImages` is the set of points of a chart in the image of some
  chart over it on which the section vanishes, and
  `AlgebraicGeometry.Space.largestOpenZeroLocus` is that set as an open set.
* `AlgebraicGeometry.Space.supportOfSection` is its complement, the support of the section.
* `AlgebraicGeometry.Space.supportOfSheaf` is the support of the sheaf.
* `AlgebraicGeometry.Space.openSub`, `AlgebraicGeometry.Space.openSubHom` and
  `AlgebraicGeometry.Space.openChart`, `AlgebraicGeometry.Space.openChartInclusion` read a
  Zariski open of the scheme underlying an object of the site, respectively of an étale chart
  of `X`, as an object of the site, respectively as an étale chart of `X`.

## Main results

* `AlgebraicGeometry.Space.largestOpenZeroLocus_restrict_iff` is the restriction criterion:
  a section restricts to zero on a chart exactly when the image of that chart lies in the
  largest open zero locus.
* `AlgebraicGeometry.Space.largestOpenZeroLocus_maximal` is maximality, and
  `AlgebraicGeometry.Space.exists_largestOpenZeroLocus` packages the two.
* `AlgebraicGeometry.Space.mem_supportOfSection_iff`,
  `AlgebraicGeometry.Space.isClosed_supportOfSection` and
  `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_exists` are the membership criteria and the
  closedness of the support of a section.
* `AlgebraicGeometry.Space.largestOpenZeroLocus_mono_of_restrict` and
  `AlgebraicGeometry.Space.largestOpenZeroLocus_inf_le_of_restrict` transfer zero loci along
  an operation on sections which is compatible with restriction.
* `AlgebraicGeometry.Space.supportOfSection_zero`,
  `AlgebraicGeometry.Space.supportOfSection_add_subset` and
  `AlgebraicGeometry.Space.supportOfSection_neg`: the zero section has empty support, the
  support of a sum lies in the union of the supports, and negation preserves the support.
* `AlgebraicGeometry.Space.supportOfSection_restrict` identifies the support of a restriction
  with the preimage of the support, and
  `AlgebraicGeometry.Space.supportOfSection_subset_of_isCovering` says that containment of the
  support in a set is local on a covering family.
* `AlgebraicGeometry.Space.supportOfSection_map_subset` and
  `AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono` are the functoriality of the two
  supports: a morphism of abelian sheaves does not enlarge the support of a section, and a
  monomorphism of abelian sheaves does not enlarge the support of the sheaf.

## Implementation notes

The topology on the point sets is `AlgebraicGeometry.Space.pointTopology`, installed as a
local instance; it takes no algebraicity hypothesis, so none of the statements here need one.

The support of the sheaf is stated with the *set-valued* stalk of Tag 04JY, nonvanishing being
the failure of `Subsingleton`; this keeps the universe of the sheaf's abelian groups
independent of the universe of the étale site. That nonvanishing is independent of the choice
of geometric point over a given point is **not** proved here.

## References

* [Stacks Project, Definition 66.21.1 (Tag 04KA)](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Lemma 66.21.2 (Tag 04KB)](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

attribute [local instance] pointTopology

/-- The property of a morphism `f : V ⟶ U` of étale charts of `X` that the image of a chart
`W` of `X` over `V` lands inside a prescribed set of points of `U`. -/
def ImageInOpen {U : SmallEtale B S hS X}
    (W : Set (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))))
    {V : SmallEtale B S hS X} (f : V ⟶ U) : Prop :=
  ∀ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)),
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
      (yoneda.map ((SmallEtale.toOver B S hS X).map f)) y ∈ W

/-- Every morphism of étale charts of `X` is étale after Yoneda. -/
theorem presheaf_etale_toOver_map {U V : SmallEtale B S hS X} (f : V ⟶ U) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map ((SmallEtale.toOver B S hS X).map f)) :=
  SmallEtale.presheaf_etale_yoneda_map B S hS ((SmallEtale.toOver B S hS X).map f)
    V.property U.property (CostructuredArrow.w f.hom)

/-- The points of a chart `U` lying in the image of some étale chart over `U` on which a
section restricts to zero. -/
def zeroImages (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    Set (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))) :=
  {x | ∃ (V : SmallEtale B S hS X) (f : V ⟶ U), F.obj.map f.op σ = 0 ∧
    ∃ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) y = x}

/-- The zero images of a section form an open set. -/
theorem isOpen_zeroImages (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    IsOpen (zeroImages B S hS X F U σ) := by
  rw [show zeroImages B S hS X F U σ =
      ⋃ V : SmallEtale B S hS X, ⋃ f : V ⟶ U,
        {x | F.obj.map f.op σ = 0 ∧ x ∈ Set.range
          (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
            (yoneda.map ((SmallEtale.toOver B S hS X).map f)))} by
    ext x
    simp only [zeroImages, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]]
  refine isOpen_iUnion fun V ↦ isOpen_iUnion fun f ↦ ?_
  by_cases hf : F.obj.map f.op σ = 0
  · simp only [hf, true_and]
    exact (isOpenMap_pointsMap_of_presheafEtale B S hS
      (yoneda.map ((SmallEtale.toOver B S hS X).map f))
      (presheaf_etale_toOver_map B S hS X f)).isOpen_range
  · simp [hf]

/-- Restriction along a composite is the iterated restriction. -/
private theorem map_comp_op_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (σ : F.obj (op U)) :
    F.map (g ≫ f).op σ = F.map g.op (F.map f.op σ) := by
  rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]

/-- A section of a sheaf on the small étale site vanishing after restriction along every
member of a covering family of charts is zero. -/
theorem section_zero_of_covering
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (V : SmallEtale B S hS X) (E : PreZeroHypercover.{u + 1} V)
    (hE : SmallEtale.IsCovering B S hS X ⟨V, E⟩)
    (s : F.obj.obj (op V)) (hz : ∀ i, F.obj.map (E.f i).op s = 0) :
    s = 0 := by
  have htop : Sieve.generate E.presieve₀ ∈ SmallEtale.topology B S hS X V := by
    rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of V E.presieve₀
      ((SmallEtale.mem_precoverage_iff B S hS X).2 ⟨E, rfl, hE⟩)
  refine F.property.isSeparated V (Sieve.generate E.presieve₀) htop s 0 ?_
  rintro Y g ⟨Z, k, hk, ⟨i⟩, rfl⟩
  rw [map_comp_op_apply, hz i]
  simp

section OpenChart

variable {B S hS X} in
/-- A Zariski open of the scheme underlying an object of the big fppf site of `S`, as an
object of that site: the open subscheme is small enough to belong to `Sch_κ`, and it is
taken over `S` through the inclusion of the open. -/
noncomputable def openSub (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage
    (show B.inclusion.obj ⟨(O : Scheme),
        lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) A.left.property⟩ ⟶
      B.inclusion.obj A.left from O.ι) ≫ A.hom)

variable {B S hS X} in
/-- The inclusion of `AlgebraicGeometry.Space.openSub` into the ambient object of the site. -/
noncomputable def openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) : openSub A O ⟶ A :=
  Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj ⟨(O : Scheme),
        lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) A.left.property⟩ ⟶
      B.inclusion.obj A.left from O.ι)) rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.openSubHom` is the
inclusion of the open. -/
theorem toScheme_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    (BigFppfOver.toScheme B S hS).map (openSubHom A O) = O.ι :=
  B.inclusion.map_preimage _

/-- The inclusion of an open subscheme of an object of the big fppf site of `S` is étale. -/
theorem etale_toScheme_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    Etale ((BigFppfOver.toScheme B S hS).map (openSubHom A O)) := by
  rw [toScheme_map_openSubHom]
  exact inferInstanceAs (Etale O.ι)

/-- A Zariski open of the scheme underlying an étale chart of `X`, read as an étale chart
of `X`. -/
noncomputable def openChart (U : SmallEtale B S hS X)
    (O : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj U)).Opens) :
    SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk (yoneda.map (openSubHom _ O) ≫ U.1.hom),
    etale_comp_of_scheme B S hS _ U.1.hom (etale_toScheme_map_openSubHom B S hS _ O)
      U.property⟩

/-- The inclusion of `AlgebraicGeometry.Space.openChart` into the ambient étale chart. -/
noncomputable def openChartInclusion (U : SmallEtale B S hS X)
    (O : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj U)).Opens) :
    openChart B S hS X U O ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (openSubHom _ O) rfl)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.openChartInclusion` is
the inclusion of the open. -/
theorem toScheme_map_toOver_map_openChartInclusion (U : SmallEtale B S hS X)
    (O : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj U)).Opens) :
    (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X).map (openChartInclusion B S hS X U O)) = O.ι :=
  toScheme_map_openSubHom B S hS _ O

end OpenChart

/-- The underlying morphism of schemes of a morphism of étale charts is étale. -/
theorem etale_toScheme_toOver_map {U V : SmallEtale B S hS X} (f : V ⟶ U) :
    Etale ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X).map f)) :=
  MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda) (presheaf_etale_toOver_map B S hS X f)

/-- A section restricts to zero along a chart `f : V ⟶ U` whose image lies in the zero images
of the section. -/
theorem eq_zero_of_imageInOpen_zeroImages
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS X) (f : V ⟶ U)
    (himage : ImageInOpen B S hS X (zeroImages B S hS X F U σ) f) :
    F.obj.map f.op σ = 0 := by
  classical
  let I := Σ Z : SmallEtale B S hS X, {g : Z ⟶ U // F.obj.map g.op σ = 0}
  let E₀ : PreZeroHypercover.{u + 1} V :=
    ⟨I, fun i ↦ pullback f i.2.1, fun i ↦ pullback.fst f i.2.1⟩
  let T := (SmallEtale.toSchemes B S hS X).obj V
  let Ebase := E₀.map (SmallEtale.toSchemes B S hS X)
  have hsurj : ∀ x : B.inclusion.obj T,
      ∃ i : I, ∃ y : B.inclusion.obj (Ebase.X i),
        (B.inclusion.map (Ebase.f i)).base y = x := by
    intro x
    let A := (SmallEtale.toOver B S hS X).obj V
    obtain ⟨qx, hqx⟩ := surjective_pointsToScheme B S hS A x
    obtain ⟨Z, g, hg, z, hzy⟩ := himage qx
    refine ⟨⟨Z, ⟨g, hg⟩⟩, ?_⟩
    have hsq : IsPullback
        (yoneda.map ((SmallEtale.toOver B S hS X).map (pullback.fst f g)))
        (yoneda.map ((SmallEtale.toOver B S hS X).map (pullback.snd f g)))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f))
        (yoneda.map ((SmallEtale.toOver B S hS X).map g)) :=
      ((IsPullback.of_hasPullback f g).map (SmallEtale.toOver B S hS X)).map yoneda
    obtain ⟨w, hwp, -⟩ := exists_points_of_isPullback B S hS hsq qx z hzy.symm
    refine ⟨pointsToScheme B S hS
      ((SmallEtale.toOver B S hS X).obj (pullback f g)) w, ?_⟩
    show (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X).map (pullback.fst f g)) _ = _
    rw [← pointsToScheme_pointsMap_yoneda B S hS
      ((SmallEtale.toOver B S hS X).map (pullback.fst f g)) w, hwp]
    exact hqx
  have heta : IsEtaleCovering (⟨T, Ebase⟩ : Covering B.Schemes) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      (Ebase.map B.inclusion)).2 ⟨hsurj, fun i ↦ ?_⟩
    exact etale_toScheme_toOver_map B S hS X (E₀.f i)
  obtain ⟨⟨T', Rfam⟩, hR, hbase, hcomb⟩ :=
    exists_chosen_etaleCovering B ⟨T, Ebase⟩ heta
  obtain rfl : T = T' := hbase
  obtain ⟨α, hX, hf⟩ :=
    (hcomb : PreZeroHypercover.CombinatoriallyEquivalent Ebase Rfam).symm.1
  have hRetale : ∀ j, Etale (B.inclusion.map (Rfam.f j)) := fun j ↦
    ((Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (Rfam.map B.inclusion)).1 hR.2).2 j
  let Rsmall : PreZeroHypercover.{u + 1} V :=
    { I₀ := Rfam.I₀
      X j := ⟨CostructuredArrow.mk (yoneda.map
          (Over.homMk (U := Over.mk (Rfam.f j ≫ ((SmallEtale.toOver B S hS X).obj V).hom))
            (Rfam.f j) rfl : _ ⟶ (SmallEtale.toOver B S hS X).obj V) ≫ V.1.hom),
        etale_comp_of_scheme B S hS _ V.1.hom (hRetale j) V.property⟩
      f j := ObjectProperty.homMk (CostructuredArrow.homMk
        (Over.homMk (U := Over.mk (Rfam.f j ≫ ((SmallEtale.toOver B S hS X).obj V).hom))
          (Rfam.f j) rfl : _ ⟶ (SmallEtale.toOver B S hS X).obj V) rfl) }
  have hRsmall : SmallEtale.IsCovering B S hS X ⟨V, Rsmall⟩ := by
    show B.etaleCovering ⟨T, Rsmall.map (SmallEtale.toSchemes B S hS X)⟩
    rwa [show Rsmall.map (SmallEtale.toSchemes B S hS X) = Rfam by ext <;> rfl]
  have hzraw : ∀ i : I, F.obj.map (E₀.f i).op (F.obj.map f.op σ) = 0 := fun i ↦ by
    have hzcomp : F.obj.map (E₀.f i ≫ f).op σ = 0 := by
      rw [show E₀.f i ≫ f = pullback.snd f i.2.1 ≫ i.2.1 from pullback.condition,
        map_comp_op_apply, i.2.2, map_zero]
    rwa [map_comp_op_apply] at hzcomp
  refine section_zero_of_covering B S hS X F V Rsmall hRsmall (F.obj.map f.op σ) fun j ↦ ?_
  let k : I := α j
  let ebase : Rfam.X j ⟶ ((SmallEtale.toOver B S hS X).obj (E₀.X k)).left := eqToHom (hX j)
  have hebase : ebase ≫ (E₀.f k).hom.left.left = Rfam.f j := (hf j).symm
  let eover : (Rsmall.X j).obj.left ⟶ (E₀.X k).obj.left :=
    Over.homMk ebase (by
      show ebase ≫ (E₀.X k).obj.left.hom = Rfam.f j ≫ V.obj.left.hom
      rw [← (E₀.f k).hom.left.w, ← Category.assoc, hebase])
  have heover : eover ≫ (E₀.f k).hom.left = (Rsmall.f j).hom.left :=
    Over.OverMorphism.ext hebase
  let e : Rsmall.X j ⟶ E₀.X k :=
    ObjectProperty.homMk (CostructuredArrow.homMk eover (by
      rw [← CostructuredArrow.w (E₀.f k).hom, ← Category.assoc, ← Functor.map_comp, heover]
      exact CostructuredArrow.w (Rsmall.f j).hom))
  have heq : Rsmall.f j = e ≫ E₀.f k :=
    InducedCategory.hom_ext (CostructuredArrow.ext _ _ heover.symm)
  rw [heq, map_comp_op_apply, hzraw k, map_zero]

/-- The zero images of a section contain every open set on which the section vanishes, in the
sense that every chart whose image lies in that open kills the section. -/
theorem le_zeroImages_of_forall_imageInOpen
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (W : TopologicalSpace.Opens
      (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))))
    (hW : ∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
      ImageInOpen B S hS X W.1 f → F.obj.map f.op σ = 0) :
    W.1 ⊆ zeroImages B S hS X F U σ := by
  intro x hx
  let A := (SmallEtale.toOver B S hS X).obj U
  let O : ((BigFppfOver.toScheme B S hS).obj A).Opens :=
    ⟨pointsToScheme B S hS A '' W.1,
      (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS A W.1).1 W.2⟩
  have hmem : ∀ q : points B S hS (yoneda.obj A),
      q ∈ W.1 ↔ pointsToScheme B S hS A q ∈ O := fun q ↦
    (injective_pointsToScheme B S hS A).mem_set_image.symm
  let V := openChart B S hS X U O
  let j := openChartInclusion B S hS X U O
  have himage : ImageInOpen B S hS X W.1 j := by
    intro y
    refine (hmem _).2 ?_
    rw [pointsToScheme_pointsMap_yoneda B S hS
      ((SmallEtale.toOver B S hS X).map j) y,
      toScheme_map_toOver_map_openChartInclusion]
    exact (pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj V) y).property
  obtain ⟨y, hy⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X).obj V) ⟨pointsToScheme B S hS A x, (hmem x).1 hx⟩
  refine ⟨V, j, hW V j himage, y, (injective_pointsToScheme B S hS A) ?_⟩
  rw [pointsToScheme_pointsMap_yoneda B S hS ((SmallEtale.toOver B S hS X).map j) y,
    toScheme_map_toOver_map_openChartInclusion, hy]
  rfl

/-! ### The support of a section -/

/-- The largest open subset of an étale chart of an algebraic space on which a section of an
abelian sheaf on the small étale site restricts to zero: the set of points of the chart in the
image of some chart over it on which the section restricts to zero. -/
@[sga "4 VIII 6.6"]
def largestOpenZeroLocus (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    TopologicalSpace.Opens
      (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))) :=
  ⟨zeroImages B S hS X F U σ, isOpen_zeroImages B S hS X F U σ⟩

/-- The underlying set of the largest open zero locus is the set of zero images. -/
@[simp]
theorem coe_largestOpenZeroLocus
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    (largestOpenZeroLocus B S hS X F U σ).1 = zeroImages B S hS X F U σ := rfl

/-- Restriction to an étale chart vanishes exactly when its image lies in the largest open
zero locus. -/
theorem largestOpenZeroLocus_restrict_iff
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS X) (f : V ⟶ U) :
    F.obj.map f.op σ = 0 ↔
      ImageInOpen B S hS X (largestOpenZeroLocus B S hS X F U σ).1 f :=
  ⟨fun hzero y ↦ ⟨V, f, hzero, y, rfl⟩,
    eq_zero_of_imageInOpen_zeroImages B S hS X F U σ V f⟩

/-- Every open on which the section restricts to zero is contained in its largest open zero
locus. -/
theorem largestOpenZeroLocus_maximal
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    ∀ W : TopologicalSpace.Opens
        (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      (∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
        ImageInOpen B S hS X W.1 f → F.obj.map f.op σ = 0) →
      W ≤ largestOpenZeroLocus B S hS X F U σ :=
  le_zeroImages_of_forall_imageInOpen B S hS X F U σ

/-- A chart has an open zero locus characterized by restriction along all étale charts, and
this open is maximal among opens with that property. -/
theorem exists_largestOpenZeroLocus
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    ∃ W : TopologicalSpace.Opens
        (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      (∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
        (F.obj.map f.op σ = 0 ↔ ImageInOpen B S hS X W.1 f)) ∧
      (∀ W' : TopologicalSpace.Opens
          (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
        (∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
          ImageInOpen B S hS X W'.1 f → F.obj.map f.op σ = 0) → W' ≤ W) :=
  ⟨largestOpenZeroLocus B S hS X F U σ,
    largestOpenZeroLocus_restrict_iff B S hS X F U σ,
    largestOpenZeroLocus_maximal B S hS X F U σ⟩

/-- The *support* of a section of an abelian sheaf on the small étale site of an algebraic
space over an étale chart: the complement of the largest open on which the section restricts
to zero. -/
@[stacks 04KA "support of a section", sga "4 VIII 6.6" "support of a section"]
abbrev supportOfSection (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    Set (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))) :=
  (largestOpenZeroLocus B S hS X F U σ).1ᶜ

/-- A point lies in the support of a section exactly when it is outside the maximal open zero
locus. -/
@[simp]
theorem mem_supportOfSection_iff
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))) :
    x ∈ supportOfSection B S hS X F U σ ↔
      x ∉ (largestOpenZeroLocus B S hS X F U σ).1 :=
  Set.mem_compl_iff _ _

/-- The support of a section is closed. -/
@[stacks 04KB "closed_section_support"]
theorem isClosed_supportOfSection
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    IsClosed (supportOfSection B S hS X F U σ) :=
  (largestOpenZeroLocus B S hS X F U σ).2.isClosed_compl

/-! ### Supports and the algebra of sections -/

/-- Transfer of zero loci along an operation on sections which is compatible with
restriction: if every restriction killing `σ` kills `τ`, then the zero locus of `σ` is
contained in that of `τ`. -/
theorem largestOpenZeroLocus_mono_of_restrict
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ τ : F.obj.obj (op U))
    (h : ∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
      F.obj.map f.op σ = 0 → F.obj.map f.op τ = 0) :
    largestOpenZeroLocus B S hS X F U σ ≤ largestOpenZeroLocus B S hS X F U τ :=
  largestOpenZeroLocus_maximal B S hS X F U τ _ fun V f hf ↦
    h V f ((largestOpenZeroLocus_restrict_iff B S hS X F U σ V f).2 hf)

/-- The binary form of `AlgebraicGeometry.Space.largestOpenZeroLocus_mono_of_restrict`: if
every restriction killing both `σ` and `τ` kills `ρ`, then the intersection of the zero loci
of `σ` and `τ` is contained in that of `ρ`. -/
theorem largestOpenZeroLocus_inf_le_of_restrict
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ τ ρ : F.obj.obj (op U))
    (h : ∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
      F.obj.map f.op σ = 0 → F.obj.map f.op τ = 0 → F.obj.map f.op ρ = 0) :
    largestOpenZeroLocus B S hS X F U σ ⊓ largestOpenZeroLocus B S hS X F U τ ≤
      largestOpenZeroLocus B S hS X F U ρ :=
  largestOpenZeroLocus_maximal B S hS X F U ρ _ fun V f hf ↦
    h V f
      ((largestOpenZeroLocus_restrict_iff B S hS X F U σ V f).2 fun y ↦ (hf y).1)
      ((largestOpenZeroLocus_restrict_iff B S hS X F U τ V f).2 fun y ↦ (hf y).2)

/-- The dual of `AlgebraicGeometry.Space.largestOpenZeroLocus_mono_of_restrict` for
supports. -/
theorem supportOfSection_subset_of_restrict
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ τ : F.obj.obj (op U))
    (h : ∀ (V : SmallEtale B S hS X) (f : V ⟶ U),
      F.obj.map f.op σ = 0 → F.obj.map f.op τ = 0) :
    supportOfSection B S hS X F U τ ⊆ supportOfSection B S hS X F U σ :=
  Set.compl_subset_compl.2 (largestOpenZeroLocus_mono_of_restrict B S hS X F U σ τ h)

/-- The zero section has empty support. -/
@[simp]
theorem supportOfSection_zero
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) :
    supportOfSection B S hS X F U 0 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  refine hx (largestOpenZeroLocus_maximal B S hS X F U 0 ⊤ (fun _ _ _ ↦ by simp) ?_)
  exact Set.mem_univ x

/-- The support of a sum is contained in the union of the supports. -/
@[stacks 04KB "support_sum"]
theorem supportOfSection_add_subset
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ τ : F.obj.obj (op U)) :
    supportOfSection B S hS X F U (σ + τ) ⊆
      supportOfSection B S hS X F U σ ∪ supportOfSection B S hS X F U τ := by
  have h := largestOpenZeroLocus_inf_le_of_restrict B S hS X F U σ τ (σ + τ)
    fun V f hσ hτ ↦ by rw [map_add, hσ, hτ, add_zero]
  intro x hx
  by_contra hmem
  simp only [Set.mem_union, not_or, mem_supportOfSection_iff, not_not] at hmem
  exact hx (h ⟨hmem.1, hmem.2⟩)

/-- Negation does not change the support of a section. -/
@[simp]
theorem supportOfSection_neg
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    supportOfSection B S hS X F U (-σ) = supportOfSection B S hS X F U σ :=
  subset_antisymm
    (supportOfSection_subset_of_restrict B S hS X F U σ (-σ)
      fun _ _ h ↦ by rw [map_neg, h, neg_zero])
    (supportOfSection_subset_of_restrict B S hS X F U (-σ) σ
      fun _ _ h ↦ by rw [map_neg] at h; simpa using neg_eq_zero.2 h)

/-- A morphism of abelian sheaves cannot enlarge the support of a section: the support of the
image of `σ` under `φ` is contained in the support of `σ`. -/
@[stacks 04KB "support_image_section"]
theorem supportOfSection_map_subset
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (φ : F ⟶ G)
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    supportOfSection B S hS X G U (φ.hom.app (op U) σ) ⊆
      supportOfSection B S hS X F U σ :=
  Set.compl_subset_compl.2 <|
    largestOpenZeroLocus_maximal B S hS X G U (φ.hom.app (op U) σ) _ fun V f hf ↦ by
      rw [← NatTrans.naturality_apply φ.hom f.op σ,
        (largestOpenZeroLocus_restrict_iff B S hS X F U σ V f).2 hf, map_zero]

/-- The zero images of a restriction are exactly the preimage of the zero images. -/
theorem zeroImages_restrict
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS X) (f : V ⟶ U) :
    zeroImages B S hS X F V (F.obj.map f.op σ) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) ⁻¹'
          zeroImages B S hS X F U σ := by
  refine subset_antisymm ?_ ?_
  · rintro y ⟨V', g, hg, z, rfl⟩
    exact ⟨V', g ≫ f, by rw [map_comp_op_apply, hg], z, by
      rw [Functor.map_comp, Functor.map_comp, pointsMap_comp_apply]⟩
  · have hopen : IsOpen (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) ⁻¹'
          (largestOpenZeroLocus B S hS X F U σ).1) :=
      (continuous_pointsMap B S hS
        (yoneda.map ((SmallEtale.toOver B S hS X).map f))).isOpen_preimage _
        (largestOpenZeroLocus B S hS X F U σ).2
    exact largestOpenZeroLocus_maximal B S hS X F V (F.obj.map f.op σ)
      ⟨_, hopen⟩ fun V' g hg ↦ by
        have hzero : F.obj.map (g ≫ f).op σ = 0 :=
          (largestOpenZeroLocus_restrict_iff B S hS X F U σ V' (g ≫ f)).2 fun y ↦ by
            rw [Functor.map_comp, Functor.map_comp, pointsMap_comp_apply]
            exact hg y
        rwa [map_comp_op_apply] at hzero

/-- The support of a restriction is exactly the preimage of the support. -/
theorem supportOfSection_restrict
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS X) (f : V ⟶ U) :
    supportOfSection B S hS X F V (F.obj.map f.op σ) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) ⁻¹'
          supportOfSection B S hS X F U σ :=
  Set.ext fun x ↦ by
    show x ∉ zeroImages B S hS X F V (F.obj.map f.op σ) ↔
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) x ∉
          zeroImages B S hS X F U σ
    rw [zeroImages_restrict B S hS X F U σ V f]
    rfl

/-- The support of a restriction is contained in the preimage of the support. -/
theorem supportOfSection_restrict_subset_preimage
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS X) (f : V ⟶ U) :
    supportOfSection B S hS X F V (F.obj.map f.op σ) ⊆
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f)) ⁻¹'
          supportOfSection B S hS X F U σ :=
  (supportOfSection_restrict B S hS X F U σ V f).subset

/-- A covering family of étale charts is jointly surjective on the points of its target. -/
theorem exists_pointsMap_eq_of_isCovering
    (U : SmallEtale B S hS X) (E : PreZeroHypercover.{u + 1} U)
    (hE : SmallEtale.IsCovering B S hS X ⟨U, E⟩)
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))) :
    ∃ (i : E.I₀)
      (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj (E.X i)))),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj (E.X i)))
        (yoneda.map ((SmallEtale.toOver B S hS X).map (E.f i))) y = x := by
  obtain ⟨i, y₀, hy₀⟩ := ((Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
    ((E.map (SmallEtale.toSchemes B S hS X)).map B.inclusion)).1 hE.2).1
      (pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj U) x)
  obtain ⟨y, rfl⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X).obj (E.X i)) y₀
  exact ⟨i, y, (injective_pointsToScheme B S hS _)
    ((pointsToScheme_pointsMap_yoneda B S hS _ y).trans hy₀)⟩

/-- Membership of the support in a prescribed subset is local on a covering family of charts:
if on each member of a covering family the support of the restriction lands in the preimage of
a set `Z`, then the support itself lands in `Z`. -/
theorem supportOfSection_subset_of_isCovering
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U))
    (Z : Set (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))))
    (E : PreZeroHypercover.{u + 1} U) (hE : SmallEtale.IsCovering B S hS X ⟨U, E⟩)
    (h : ∀ i, supportOfSection B S hS X F (E.X i) (F.obj.map (E.f i).op σ) ⊆
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj (E.X i)))
        (yoneda.map ((SmallEtale.toOver B S hS X).map (E.f i))) ⁻¹' Z) :
    supportOfSection B S hS X F U σ ⊆ Z := by
  intro x hx
  obtain ⟨i, y, rfl⟩ := exists_pointsMap_eq_of_isCovering B S hS X U E hE x
  exact h i ((supportOfSection_restrict B S hS X F U σ (E.X i) (E.f i)).symm ▸ hx)

/-! ### The support of a sheaf -/

/-- The *support* of an abelian sheaf on the small étale site of an algebraic space: the set
of points at which the stalk at some geometric point lying over that point is nonzero, that is,
at which the set-valued stalk is not a subsingleton. -/
@[stacks 04KA "support of a sheaf", sga "4 VIII 6.6" "support of a sheaf"]
def supportOfSheaf (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Set (points B S hS X) :=
  {x | ∃ p : GeometricPoint B S hS X, p.LiesOver x ∧
    ¬ Subsingleton (stalkSet p (F.obj ⋙ forget AddCommGrpCat.{v}))}

/-- The defining criterion of membership in the support of a sheaf. -/
@[simp]
theorem mem_supportOfSheaf_iff_exists
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) (x : points B S hS X) :
    x ∈ supportOfSheaf B S hS X F ↔
      ∃ p : GeometricPoint B S hS X, p.LiesOver x ∧
        ¬ Subsingleton (stalkSet p (F.obj ⋙ forget AddCommGrpCat.{v})) :=
  Iff.rfl

/-- The support of an abelian subsheaf is contained in the support of the ambient sheaf: a
monomorphism `f : F ⟶ G` of abelian sheaves on the small étale site cannot enlarge the support
of its source. -/
@[stacks 04KB "support_injection"]
theorem supportOfSheaf_subset_of_mono (hX : IsAlgebraicSpace B S hS X)
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] :
    supportOfSheaf B S hS X F ⊆ supportOfSheaf B S hS X G := by
  intro x hx
  rw [mem_supportOfSheaf_iff_exists] at hx ⊢
  obtain ⟨p, hp, hF⟩ := hx
  set fSet := (sheafCompose (SmallEtale.topology B S hS X) (forget AddCommGrpCat.{v})).map f
  have hinj : ∀ U : SmallEtale B S hS X, Function.Injective (fSet.hom.app (op U)) := by
    intro U a b hab
    have hm : Mono (f.hom.app (op U)) :=
      (NatTrans.mono_iff_mono_app _).1
        (Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{v}) f) _
    exact (AddCommGrpCat.mono_iff_injective _).1 hm hab
  refine ⟨p, hp, fun hG ↦ hF ⟨fun a b ↦ ?_⟩⟩
  exact (injective_iff_stalkSetMap_injective B S hS X hX fSet).1 hinj p (hG.elim _ _)

end AlgebraicGeometry.Space

end
