module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# The normalization of an algebraic space in another, glued along an étale presentation

Let `f : X ⟶ Y` be a relatively representable morphism of presheaves on the big fppf site of a
scheme `S`, let `w : h_U ⟶ Y` be a surjective étale chart of `Y` and let `pr₁, pr₂ : R ⟶ U`
exhibit `R` as `U ×_Y U`. The chart normalizations `N(R) ⇉ N(U)` form an étale equivalence
relation, `AlgebraicGeometry.Space.NormalizationGluing.isEtaleEquivalenceRelation_normRel`; this
file forms its quotient sheaf and equips it with the two legs of a factorization of `f`.

The quotient is an algebraic space by Tag 02WW, the quotient map `h_{N(U)} ⟶ N(U)/N(R)` is a
surjective étale atlas with the relation as its kernel pair, and the quotient is therefore the
coequalizer of the relation in sheaves. Both legs of the factorization are built by that
universal property, and so is the identification of the fibre product of the quotient with the
chart `U`: the chart normalization `N(U)` *is* `(N(U)/N(R)) ×_Y U`.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationGluing.normQuot` is the quotient sheaf `N(U)/N(R)`,
  with `AlgebraicGeometry.Space.NormalizationGluing.normQuotMap` the quotient map from `N(U)`.
* `AlgebraicGeometry.Space.NormalizationGluing.normQuotToBase` is the normalization morphism
  `N(U)/N(R) ⟶ Y`, and `AlgebraicGeometry.Space.NormalizationGluing.toNormQuot` the canonical
  morphism `X ⟶ N(U)/N(R)`.

## Main results

* `AlgebraicGeometry.Space.NormalizationGluing.toNormQuot_comp_normQuotToBase`: the two legs
  factor `f`.
* `AlgebraicGeometry.Space.NormalizationGluing.isPullback_normQuotMap`: the quotient map exhibits
  `N(U)` as the fibre product of the quotient with the chart, which is the chart condition of
  `AlgebraicGeometry.Space.NormalizationInData` at the chart the quotient was built from.

## Implementation notes

The cartesianness of the chart square is proved by showing that the comparison morphism
`h_{N(U)} ⟶ (N(U)/N(R)) ×_Y U` is a monomorphism and locally surjective. Monomorphy is an
honest computation with the kernel pair of the quotient map and the diagonal of the relation,
with no locality: two points of `N(U)` with the same image in the quotient differ by a point of
`N(R)`, and if they also agree in `U` then that point lies on the diagonal. Local surjectivity
is the base change of local surjectivity of the quotient map, which is Tag 05VM.

## References

* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.NormalizationGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  (hrep : yoneda.relativelyRepresentable f)
  {U R : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Y) (pr₁ pr₂ : R ⟶ U)
  (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  (hwet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)

/-! ### The quotient sheaf and its atlas -/

/-- **The normalization of `Y` in `X`, glued along the presentation `R ⇉ U` of `Y`**: the
quotient sheaf of the étale equivalence relation formed by the chart normalizations. -/
def normQuot : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (normRelFst B S hS hrep w pr₁)
      (normRelSnd B S hS hrep w pr₁ pr₂ hsq))).obj

/-- The quotient map from the chart normalization onto the glued normalization. -/
def normQuotMap : yoneda.obj (chartNorm B S hS (hrep.snd w)) ⟶
    normQuot B S hS hrep w pr₁ pr₂ hsq :=
  quotientMap B S hS (normRelFst B S hS hrep w pr₁) (normRelSnd B S hS hrep w pr₁ pr₂ hsq)

include hsq hwet in
/-- **Stacks 02WW.** The glued normalization is an algebraic space over `S`. -/
theorem isAlgebraicSpace_normQuot :
    IsAlgebraicSpace B S hS (normQuot B S hS hrep w pr₁ pr₂ hsq) := by
  have _ := isEtaleEquivalenceRelation_normRel B S hS hrep w pr₁ pr₂ hsq hwet
  exact isAlgebraicSpace_quotient_unconditional B S hS _ _

include hsq hwet in
/-- **Stacks 02WV.** The relation is the kernel pair of the quotient map. -/
theorem isPullback_normQuotMap_self :
    IsPullback (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq))
      (yoneda.map (normRelFst B S hS hrep w pr₁)) (normQuotMap B S hS hrep w pr₁ pr₂ hsq)
      (normQuotMap B S hS hrep w pr₁ pr₂ hsq) := by
  have _ := isEtaleEquivalenceRelation_normRel B S hS hrep w pr₁ pr₂ hsq hwet
  exact quotientMap_isPullback B S hS _ _

include hsq hwet in
/-- **Stacks 02WV.** The quotient map is surjective. -/
theorem surjective_normQuotMap :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (normQuotMap B S hS hrep w pr₁ pr₂ hsq) := by
  have _ := isEtaleEquivalenceRelation_normRel B S hS hrep w pr₁ pr₂ hsq hwet
  exact quotientMap_surjective_unconditional B S hS _ _

include hsq hwet in
/-- **Stacks 02WV.** The quotient map is étale. -/
theorem etale_normQuotMap :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (normQuotMap B S hS hrep w pr₁ pr₂ hsq) := by
  have _ := isEtaleEquivalenceRelation_normRel B S hS hrep w pr₁ pr₂ hsq hwet
  exact quotientMap_etale_unconditional B S hS _ _


/-! ### The chart of `f` over `U` as an atlas of the source -/

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
  (hwsurj : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)

/-- Any property of morphisms of presheaves on the big fppf site, induced by a property of
schemes, is stable under base change. -/
private theorem presheaf_of_isPullback (P : MorphismProperty Scheme.{u})
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : A ⟶ C} {g : D ⟶ C} {f' : E ⟶ D}
    {g' : E ⟶ A} (sq : IsPullback f' g' g f)
    (hg : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf g' := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) (F := yoneda)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hg

include hwsurj in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))] in
/-- The projection of the chart of `f` over `U` to the source is surjective, being a base
change of the chart of `Y`. -/
theorem surjective_chartFst :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst w) := by
  exact presheaf_of_isPullback B S hS _ (hrep.isPullback w).flip hwsurj

include hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))] in
/-- The projection of the chart of `f` over `U` to the source is étale, being a base change of
the chart of `Y`. -/
theorem etale_chartFst :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst w) := by
  exact presheaf_of_isPullback B S hS _ (hrep.isPullback w).flip hwet

include hsq in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- **The chart of `f` over `R` is the kernel pair of the chart of `f` over `U`.** -/
theorem isPullback_chartFst_self :
    IsPullback (yoneda.map (chartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁)))
      (yoneda.map (chartMap B S hS hrep pr₂ (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq)))
      (hrep.fst w) (hrep.fst w) := by
  have step1 := (isPullback_chartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁)).map
    yoneda
  have houter := step1.paste_vert hsq
  rw [← CategoryTheory.Functor.map_comp, ← chartMap_comp_snd B S hS hrep pr₂
      (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq), CategoryTheory.Functor.map_comp,
    ← (hrep.isPullback w).w] at houter
  refine houter.of_bot ?_ (hrep.isPullback w)
  rw [yoneda_map_chartMap_comp_fst, yoneda_map_chartMap_comp_fst]

/-! ### The two legs of the factorization -/

include hsq hwet hY in
/-- The glued normalization maps to `Y`: the normalization morphisms of the charts are
invariant under the relation, so they descend along the quotient map. -/
theorem existsUnique_normQuotToBase :
    ∃! d : normQuot B S hS hrep w pr₁ pr₂ hsq ⟶ Y,
      normQuotMap B S hS hrep w pr₁ pr₂ hsq ≫ d =
        yoneda.map (chartNormProj B S hS (hrep.snd w)) ≫ w := by
  refine existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_normQuot B S hS hrep w pr₁ pr₂ hsq hwet).isSheaf _
    (isPullback_normQuotMap_self B S hS hrep w pr₁ pr₂ hsq hwet)
    (surjective_normQuotMap B S hS hrep w pr₁ pr₂ hsq hwet)
    (etale_normQuotMap B S hS hrep w pr₁ pr₂ hsq hwet) hY.isSheaf _ ?_
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, normRelSnd, normRelFst,
    normChartMap_comp_chartNormProj, normChartMap_comp_chartNormProj,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, hsq.w]

/-- **The normalization morphism of the glued normalization.** -/
def normQuotToBase : normQuot B S hS hrep w pr₁ pr₂ hsq ⟶ Y :=
  (existsUnique_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY).choose

/-- The normalization morphism of the glued normalization restricts, along the quotient map, to
the normalization morphism of the chart followed by the chart. -/
@[reassoc]
lemma normQuotMap_comp_normQuotToBase :
    normQuotMap B S hS hrep w pr₁ pr₂ hsq ≫ normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY =
      yoneda.map (chartNormProj B S hS (hrep.snd w)) ≫ w :=
  (existsUnique_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY).choose_spec.1

include hsq hwet hX hwsurj in
/-- The canonical morphism from the source to the glued normalization: the canonical morphisms
of the charts are invariant under the relation, so they descend along the chart of `f`. -/
theorem existsUnique_toNormQuot :
    ∃! d : X ⟶ normQuot B S hS hrep w pr₁ pr₂ hsq,
      hrep.fst w ≫ d = yoneda.map (chartNormUnit B S hS (hrep.snd w)) ≫
        normQuotMap B S hS hrep w pr₁ pr₂ hsq := by
  refine existsUnique_desc_of_surjective_etale_atlas B S hS hX.isSheaf _
    (isPullback_chartFst_self B S hS hrep w pr₁ pr₂ hsq)
    (surjective_chartFst B S hS hrep w hwsurj) (etale_chartFst B S hS hrep w hwet)
    (isAlgebraicSpace_normQuot B S hS hrep w pr₁ pr₂ hsq hwet).isSheaf _ ?_
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    ← chartNormUnit_comp_normChartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁),
    ← chartNormUnit_comp_normChartMap B S hS hrep pr₂
      (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq),
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (fun m => yoneda.map (chartNormUnit B S hS (hrep.snd (relBase B S hS w pr₁)))
    ≫ m) (isPullback_normQuotMap_self B S hS hrep w pr₁ pr₂ hsq hwet).w.symm

/-- **The canonical morphism from the source into the glued normalization.** -/
def toNormQuot : X ⟶ normQuot B S hS hrep w pr₁ pr₂ hsq :=
  (existsUnique_toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj).choose

/-- The canonical morphism into the glued normalization restricts, along the chart of `f`, to
the canonical morphism of the chart followed by the quotient map. -/
@[reassoc]
lemma chartFst_comp_toNormQuot :
    hrep.fst w ≫ toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj =
      yoneda.map (chartNormUnit B S hS (hrep.snd w)) ≫
        normQuotMap B S hS hrep w pr₁ pr₂ hsq :=
  (existsUnique_toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj).choose_spec.1

include hsq hwet hX hY hwsurj in
/-- **The two legs factor `f`.** -/
theorem toNormQuot_comp_normQuotToBase :
    toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj ≫
        normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY = f := by
  refine hom_ext_of_etale_atlas B S hS hX.isSheaf hY.isSheaf (hrep.fst w)
    (surjective_chartFst B S hS hrep w hwsurj) (etale_chartFst B S hS hrep w hwet) ?_
  rw [← Category.assoc, chartFst_comp_toNormQuot, Category.assoc,
    normQuotMap_comp_normQuotToBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    chartNormUnit_comp_chartNormProj]
  exact (hrep.isPullback w).w.symm


/-! ### The chart condition at the chart the quotient was built from -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_NormalizationAtlasQuotient :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_NormalizationAtlasQuotient
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The comparison morphism from the chart normalization to the fibre product of the glued
normalization with the chart. -/
def normQuotChartComparison :
    yoneda.obj (chartNorm B S hS (hrep.snd w)) ⟶
      Limits.pullback (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w :=
  Limits.pullback.lift (normQuotMap B S hS hrep w pr₁ pr₂ hsq)
    (yoneda.map (chartNormProj B S hS (hrep.snd w)))
    (normQuotMap_comp_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY)

/-- The first component of the comparison morphism is the quotient map. -/
@[reassoc]
lemma normQuotChartComparison_comp_fst :
    normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY ≫
        Limits.pullback.fst (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w =
      normQuotMap B S hS hrep w pr₁ pr₂ hsq :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of the comparison morphism is the normalization morphism of the
chart. -/
@[reassoc]
lemma normQuotChartComparison_comp_snd :
    normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY ≫
        Limits.pullback.snd (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w =
      yoneda.map (chartNormProj B S hS (hrep.snd w)) :=
  Limits.pullback.lift_snd _ _ _

include hsq hwet hY in
/-- **The comparison morphism is a monomorphism.** Two points of the chart normalization with
the same image in the glued normalization differ by a point of the relation, by Tag 02WV; if
they moreover agree in the chart, that point lies on the diagonal of the relation, and the two
points are equal. -/
theorem mono_normQuotChartComparison :
    Mono (normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY) := by
  have hker := isPullback_normQuotMap_self B S hS hrep w pr₁ pr₂ hsq hwet
  have hA := (isPullback_normRelFst B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda
  have hBq := (isPullback_normRelSnd B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda
  have hdiagProj := normChartMap_comp_chartNormProj B S hS hrep
    (relDiag B S hS w pr₁ pr₂ hsq) (yoneda_map_relDiag_comp B S hS w pr₁ pr₂ hsq)
  have hdiag1 : normRelDiag B S hS hrep w pr₁ pr₂ hsq ≫
      chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)) ≫ pr₁ =
        chartNormProj B S hS (hrep.snd w) := by
    rw [← Category.assoc, normRelDiag, hdiagProj, Category.assoc, relDiag_comp_pr₁,
      Category.comp_id]
  have hdiag2 : normRelDiag B S hS hrep w pr₁ pr₂ hsq ≫
      chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)) ≫ pr₂ =
        chartNormProj B S hS (hrep.snd w) := by
    rw [← Category.assoc, normRelDiag, hdiagProj, Category.assoc, relDiag_comp_pr₂,
      Category.comp_id]
  refine ⟨fun {Z} a b hab => ?_⟩
  have h1 : a ≫ normQuotMap B S hS hrep w pr₁ pr₂ hsq =
      b ≫ normQuotMap B S hS hrep w pr₁ pr₂ hsq := by
    rw [← normQuotChartComparison_comp_fst B S hS hrep w pr₁ pr₂ hsq hwet hY,
      ← Category.assoc, hab, Category.assoc]
  have h2 : a ≫ yoneda.map (chartNormProj B S hS (hrep.snd w)) =
      b ≫ yoneda.map (chartNormProj B S hS (hrep.snd w)) := by
    rw [← normQuotChartComparison_comp_snd B S hS hrep w pr₁ pr₂ hsq hwet hY,
      ← Category.assoc, hab, Category.assoc]
  have hr1 : hker.lift a b h1 ≫ yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq) = a :=
    hker.lift_fst _ _ _
  have hr2 : hker.lift a b h1 ≫ yoneda.map (normRelFst B S hS hrep w pr₁) = b :=
    hker.lift_snd _ _ _
  have hlift : ∀ (p : R ⟶ U) (k : chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) ⟶
        chartNorm B S hS (hrep.snd w)) (c : Z ⟶ yoneda.obj (chartNorm B S hS (hrep.snd w))),
      normRelDiag B S hS hrep w pr₁ pr₂ hsq ≫
        chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)) ≫ p =
          chartNormProj B S hS (hrep.snd w) →
      yoneda.map (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁))) ≫ yoneda.map p =
        yoneda.map k ≫ yoneda.map (chartNormProj B S hS (hrep.snd w)) →
      hker.lift a b h1 ≫ yoneda.map k = c →
      c ≫ yoneda.map (chartNormProj B S hS (hrep.snd w)) =
        b ≫ yoneda.map (chartNormProj B S hS (hrep.snd w)) →
      (hker.lift a b h1 ≫ yoneda.map (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)))) ≫
          yoneda.map p =
        ((b ≫ yoneda.map (normRelDiag B S hS hrep w pr₁ pr₂ hsq)) ≫
          yoneda.map (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)))) ≫ yoneda.map p := by
    intro p k c hd hw hk hc
    rw [Category.assoc, hw, ← Category.assoc, hk, hc, Category.assoc, Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hd]
  have key : hker.lift a b h1 =
      b ≫ yoneda.map (normRelDiag B S hS hrep w pr₁ pr₂ hsq) := by
    refine hA.hom_ext ?_ (hsq.hom_ext ?_ ?_)
    · rw [hr2, Category.assoc, ← CategoryTheory.Functor.map_comp,
        normRelDiag_comp_normRelFst, CategoryTheory.Functor.map_id, Category.comp_id]
    · exact hlift pr₁ _ b hdiag1 hA.w.symm hr2 rfl
    · exact hlift pr₂ _ a hdiag2 hBq.w.symm hr1 h2
  rw [← hr1, key, Category.assoc, ← CategoryTheory.Functor.map_comp,
    normRelDiag_comp_normRelSnd, CategoryTheory.Functor.map_id, Category.comp_id]

include hsq hwet hY in
/-- **The relation is the base change of the quotient map along the fibre product with the
chart.** -/
theorem isPullback_normRelSnd_comp_comparison :
    IsPullback (yoneda.map (normRelFst B S hS hrep w pr₁))
      (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq) ≫
        normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY)
      (normQuotMap B S hS hrep w pr₁ pr₂ hsq)
      (Limits.pullback.fst (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w) := by
  have hker := isPullback_normQuotMap_self B S hS hrep w pr₁ pr₂ hsq hwet
  have hA := (isPullback_normRelFst B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda
  have hB := normChartMap_comp_chartNormProj B S hS hrep pr₂
    (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq)
  have hpb : IsPullback
      (Limits.pullback.fst (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w)
      (Limits.pullback.snd (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w)
      (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w := IsPullback.of_hasPullback _ _
  have houter := hA.paste_vert hsq
  have hsnd : yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq) ≫
      normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY ≫
      Limits.pullback.snd (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w =
        yoneda.map (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁))) ≫
          yoneda.map pr₂ := by
    rw [normQuotChartComparison_comp_snd, ← CategoryTheory.Functor.map_comp, normRelSnd, hB,
      CategoryTheory.Functor.map_comp]
  rw [← hsnd, ← Category.assoc,
    ← normQuotMap_comp_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY] at houter
  refine houter.of_bot ?_ hpb
  rw [Category.assoc, normQuotChartComparison_comp_fst]
  exact hker.w.symm


/-- A monomorphism of presheaves of types which is locally surjective and whose source and
target are sheaves is an isomorphism: it is locally injective because it is injective on
sections, and a locally bijective morphism of sheaves of sets is invertible. -/
theorem isIso_of_mono_of_isLocallySurjective_of_isSheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (φ : F ⟶ G) (hmono : Mono φ)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ) : IsIso φ := by
  let J := BigFppfOver.topology B S hS
  let ψ : (⟨F, hF⟩ : Sheaf J (Type u)) ⟶ ⟨G, hG⟩ := ObjectProperty.homMk φ
  have hi : Sheaf.IsLocallyInjective ψ :=
    Presheaf.isLocallyInjective_of_injective J φ
      (fun T ↦ (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app φ).1 hmono T))
  have _ : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨hi, hloc⟩
  exact (sheafToPresheaf J (Type u)).map_isIso ψ

include hsq hwet hY in
/-- The relation's chart normalization is a representable surjective étale cover of the fibre
product of the glued normalization with the chart. -/
theorem isLocallySurjective_normRelSnd_comp_comparison :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq) ≫
        normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY) := by
  have hbc := isPullback_normRelSnd_comp_comparison B S hS hrep w pr₁ pr₂ hsq hwet hY
  exact isLocallySurjective_of_surjective_etale B S hS _
    (presheaf_of_isPullback B S hS _ hbc
      (surjective_normQuotMap B S hS hrep w pr₁ pr₂ hsq hwet))
    (presheaf_of_isPullback B S hS _ hbc
      (etale_normQuotMap B S hS hrep w pr₁ pr₂ hsq hwet))

include hsq hwet hY in
/-- **The comparison morphism is an isomorphism**, being a monomorphism which is locally
surjective between sheaves. -/
theorem isIso_normQuotChartComparison :
    IsIso (normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY) := by
  have hQ := isAlgebraicSpace_normQuot B S hS hrep w pr₁ pr₂ hsq hwet
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hpb : IsAlgebraicSpace B S hS
      (Limits.pullback (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w) :=
    isAlgebraicSpace_pullback B S hS _ w hQ hUspace hY
  have _ := isLocallySurjective_normRelSnd_comp_comparison B S hS hrep w pr₁ pr₂ hsq hwet hY
  exact isIso_of_mono_of_isLocallySurjective_of_isSheaf B S hS
    (isAlgebraicSpace_yoneda B S hS (chartNorm B S hS (hrep.snd w))).isSheaf hpb.isSheaf _
    (mono_normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY)
    (Presheaf.isLocallySurjective_of_isLocallySurjective (BigFppfOver.topology B S hS)
      (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq))
      (normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY))

include hsq hwet hY in
/-- **The chart condition at the chart the quotient was built from**: the chart normalization
`N(U)` is the fibre product of the glued normalization with the chart `U`, compatibly with both
legs. -/
theorem isPullback_normQuotMap :
    IsPullback (normQuotMap B S hS hrep w pr₁ pr₂ hsq)
      (yoneda.map (chartNormProj B S hS (hrep.snd w)))
      (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY) w := by
  have _ := isIso_normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY
  exact IsPullback.of_iso_pullback
    ⟨normQuotMap_comp_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY⟩
    (asIso (normQuotChartComparison B S hS hrep w pr₁ pr₂ hsq hwet hY))
    (normQuotChartComparison_comp_fst B S hS hrep w pr₁ pr₂ hsq hwet hY)
    (normQuotChartComparison_comp_snd B S hS hrep w pr₁ pr₂ hsq hwet hY)

end AlgebraicGeometry.Space.NormalizationGluing

end
