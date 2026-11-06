module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFibreIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaces
import all StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated

/-!
# The space of sections of an étale morphism (Stacks 05XR)

Let `Z ⟶ U` be a finite morphism of schemes, let `W` be an algebraic space over `U` and let
`w : W ⟶ Z` be étale. Stacks 05XR asserts that the functor `F` on `(Sch/U)_{fppf}` of sections of
`W_T ⟶ Z_T` is an algebraic space, étale over `U`. The separated case is
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated`; this file proves the
general case.

## The shape of the argument

The source deduces the general case from the separated one by the bootstrap theorem
Stacks 04S6, applied to the map `F' ⟶ F` from the space of sections of a separated étale cover
`W' ⟶ W`. This file avoids the bootstrap theorem by computing the diagonal of `F` directly.

* `F` is a sheaf: it is the subfunctor of the sheaf `T ↦ W(Z × T)` cut out by the condition that a
  section lies over `Z`, and that condition is local.
* Two sections `σ, τ` of `W_T ⟶ Z_T` agree exactly over an open subscheme of `T`: they agree on
  the inverse image `E` in `Z_T` of the diagonal of `w`, which is open because `w` is unramified,
  and the locus over which `Z_T ⟶ T` lands in `E` is open because `Z_T ⟶ T` is closed. So the
  diagonal of `F` is representable by open immersions.
* Composing a scheme atlas of `F'` with `F' ⟶ F` gives an atlas of `F`. It is étale because its
  base changes are open subschemes of base changes of `F' ⟶ U`, and surjective by Stacks 05XQ.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_and_isEtale`: **Stacks 05XR**.
* `AlgebraicGeometry.Space.isSheaf_sectionSpace_of_isSheaf`: the space of sections is a sheaf as
  soon as the source is.
* `AlgebraicGeometry.Space.isOpenSubspace_sectionEqualizer` and
  `AlgebraicGeometry.Space.mem_sectionEqualizer_iff`: the locus where two sections agree is an
  open subspace.
* `AlgebraicGeometry.Space.exists_lift_sectionsOver`: étale-locally on the base, a section lifts
  along a surjective étale chart; this is Stacks 05XQ in the relative form
  `AlgebraicGeometry.Space.exists_surjective_etale_lift_of_isFinite`.
* `AlgebraicGeometry.Space.exists_atlas_sectionSpace`: a surjective étale atlas of the space of
  sections.

## Implementation notes

The source asks `Z ⟶ U` to be finite locally free. Only finiteness is used: it makes `Z_T ⟶ T`
closed, which is what the open locus of agreement of two sections needs, and it is what
Stacks 05XQ and the separated case need.

## References

* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B U hU`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SectionSpaceEtale
    (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U) :
    HasPullbacks ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SectionSpaceEtale
    {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
    {X Y Z : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SectionSpaceEtale B U hU).has_limit _

/-- Discrete limits of presheaves on `BigFppfOver B U hU`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_SectionSpaceEtale
    {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}

/-! ### The space of sections is a sheaf -/

section Sheaf

variable (Z : BigFppfOver B U hU) (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)

/-- The presheaf `T ↦ W(Z × T)` on the big fppf site of `U`. -/
@[simps]
noncomputable def sectionAmbient : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u where
  obj T := W.obj (op (Z ⨯ T.unop))
  map f := W.map (prod.map (𝟙 Z) f.unop).op
  map_id T := by simp
  map_comp f g := by simp [← W.map_comp, ← op_comp, prod.map_map]

/-- `T ↦ W(Z × T)` is a sheaf when `W` is: it is `W` composed with `T ↦ Z × T`, which is
`Over.star Z` followed by `Over.forget Z` and therefore continuous. -/
theorem isSheaf_sectionAmbient (hW : Presheaf.IsSheaf (BigFppfOver.topology B U hU) W) :
    Presheaf.IsSheaf (BigFppfOver.topology B U hU) (sectionAmbient Z W) := by
  have := Functor.isContinuous_comp (Over.star Z) (Over.forget Z) (BigFppfOver.topology B U hU)
    ((BigFppfOver.topology B U hU).over Z) (BigFppfOver.topology B U hU)
  exact Functor.op_comp_isSheaf_of_isSheaf (Over.star Z ⋙ Over.forget Z)
    (BigFppfOver.topology B U hU) (BigFppfOver.topology B U hU) W hW

/-- The subfunctor of `T ↦ W(Z × T)` whose sections lie over the first projection to `Z`. -/
noncomputable def sectionSubfunctor : Subfunctor (sectionAmbient Z W) where
  obj T := {s | w.app (op (Z ⨯ T.unop)) s = (prod.fst : Z ⨯ T.unop ⟶ Z)}
  map {T T'} f s hs := by
    simp only [Set.mem_setOf_eq] at hs ⊢
    have h := NatTrans.naturality_apply w (prod.map (𝟙 Z) f.unop).op s
    refine h.trans ?_
    rw [hs]
    change prod.map (𝟙 Z) f.unop ≫ prod.fst = prod.fst
    rw [prod.map_fst, Category.comp_id]

variable {Z} in
/-- `yoneda.obj (Z ⨯ T) ≅ yoneda.obj T ⨯ yoneda.obj Z`. -/
noncomputable def prodYonedaIso (T : BigFppfOver B U hU) :
    yoneda.obj (Z ⨯ T) ≅ yoneda.obj T ⨯ yoneda.obj Z :=
  yoneda.mapIso (prod.braiding Z T) ≪≫ PreservesLimitPair.iso yoneda T Z

variable {Z} in
/-- The second component of `prodYonedaIso T` is `yoneda.map` of the first projection
`Z ⨯ T ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem prodYonedaIso_hom_snd (T : BigFppfOver B U hU) :
    (prodYonedaIso T).hom ≫ prod.snd = yoneda.map (prod.fst : Z ⨯ T ⟶ Z) := by
  simp only [prodYonedaIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    PreservesLimitPair.iso_hom, prodComparison_snd, ← yoneda.map_comp, prod.braiding_hom,
    prod.lift_snd]

variable {Z} in
/-- The first component of `prodYonedaIso T` is `yoneda.map` of the second projection
`Z ⨯ T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem prodYonedaIso_hom_fst (T : BigFppfOver B U hU) :
    (prodYonedaIso T).hom ≫ prod.fst = yoneda.map (prod.snd : Z ⨯ T ⟶ T) := by
  simp only [prodYonedaIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    PreservesLimitPair.iso_hom, prodComparison_fst, ← yoneda.map_comp, prod.braiding_hom,
    prod.lift_fst]

variable {Z} in
/-- The isomorphism `prodYonedaIso T` is natural in `T`. -/
theorem prodYonedaIso_naturality {T T' : BigFppfOver B U hU} (f : T' ⟶ T) :
    yoneda.map (prod.map (𝟙 Z) f) ≫ (prodYonedaIso T).hom =
      (prodYonedaIso T').hom ≫ prod.map (yoneda.map f) (𝟙 _) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodYonedaIso_hom_fst, Category.assoc, prod.map_fst,
      prodYonedaIso_hom_fst_assoc, ← yoneda.map_comp, ← yoneda.map_comp, prod.map_snd]
  · rw [Category.assoc, prodYonedaIso_hom_snd, Category.assoc, prod.map_snd, Category.comp_id,
      prodYonedaIso_hom_snd, ← yoneda.map_comp, prod.map_fst, Category.comp_id]

variable {Z W w} in
/-- A section of `W_T → Z_T`, read as an element of `W(Z × T)` lying over the first projection. -/
noncomputable def sectionsOverEquiv (T : BigFppfOver B U hU) :
    SectionsOver B U hU Z T W w ≃ (sectionSubfunctor Z W w).obj (op T) where
  toFun σ := ⟨yonedaEquiv (X := Z ⨯ T) (F := W) ((prodYonedaIso T).hom ≫ σ.1), by
    change w.app (op (Z ⨯ T)) (yonedaEquiv ((prodYonedaIso T).hom ≫ σ.1)) = prod.fst
    rw [← yonedaEquiv_comp, Category.assoc, σ.2, prodYonedaIso_hom_snd, yonedaEquiv_yoneda_map]⟩
  invFun s := ⟨(prodYonedaIso T).inv ≫ (yonedaEquiv (X := Z ⨯ T) (F := W)).symm s.1, by
    have hs : w.app (op (Z ⨯ T)) s.1 = (prod.fst : Z ⨯ T ⟶ Z) := s.2
    have h := yonedaEquiv_symm_naturality_right (Z ⨯ T) w s.1
    rw [Category.assoc, h, hs, Iso.inv_comp_eq, prodYonedaIso_hom_snd]
    rfl⟩
  left_inv σ := by
    ext1
    simp only [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  right_inv s := by
    ext1
    simp only [Iso.hom_inv_id_assoc]
    exact Equiv.apply_symm_apply _ _

variable {Z W w} in
/-- `AlgebraicGeometry.Space.sectionsOverEquiv` intertwines restriction of sections with the
restriction maps of `T ↦ W(Z × T)`. -/
theorem sectionsOverEquiv_restrict {T T' : BigFppfOver B U hU} (f : T' ⟶ T)
    (σ : SectionsOver B U hU Z T W w) :
    (sectionsOverEquiv T' (SectionsOver.restrict f σ)).1 =
      (sectionAmbient Z W).map f.op (sectionsOverEquiv T σ).1 := by
  show yonedaEquiv ((prodYonedaIso T').hom ≫ prod.map (yoneda.map f) (𝟙 _) ≫ σ.1) =
    W.map (prod.map (𝟙 Z) f).op (yonedaEquiv ((prodYonedaIso T).hom ≫ σ.1))
  rw [yonedaEquiv_naturality, ← Category.assoc, ← prodYonedaIso_naturality, Category.assoc]

/-- The space of sections of `w : W ⟶ h_Z` is the subfunctor of `T ↦ W(Z × T)` of the elements
lying over the first projection. -/
noncomputable def sectionSpaceIsoSubfunctor :
    sectionSpace B U hU Z W w ≅ (sectionSubfunctor Z W w).toFunctor :=
  NatIso.ofComponents (fun T => Equiv.toIso
    ((sectionSpaceEquiv B U hU Z T.unop W w).trans (sectionsOverEquiv T.unop))) (by
    intro T T' f
    ext s
    exact Subtype.ext <| (congrArg (fun σ => (sectionsOverEquiv T'.unop σ).1)
      (sectionSpaceEquiv_restrict w f.unop s)).trans (sectionsOverEquiv_restrict f.unop _))

/-- **The space of sections of a morphism to a representable presheaf is a sheaf** as soon as the
source is. -/
theorem isSheaf_sectionSpace_of_isSheaf (hW : Presheaf.IsSheaf (BigFppfOver.topology B U hU) W) :
    Presheaf.IsSheaf (BigFppfOver.topology B U hU) (sectionSpace B U hU Z W w) := by
  rw [Presheaf.isSheaf_of_iso_iff (sectionSpaceIsoSubfunctor Z W w), isSheaf_iff_isSheaf_of_type]
  have hA := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_sectionAmbient Z W hW)
  have hZ := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_sectionAmbient Z (yoneda.obj Z)
    (isAlgebraicSpace_yoneda B U hU Z).isSheaf)
  refine ((sectionSubfunctor Z W w).isSheaf_iff hA).2 fun T s hs =>
    (hZ _ hs).isSeparatedFor.ext fun Y g hg => ?_
  have hg' : w.app (op (Z ⨯ Y)) ((sectionAmbient Z W).map g.op s) = (prod.fst : Z ⨯ Y ⟶ Z) := hg
  have h := NatTrans.naturality_apply w (prod.map (𝟙 Z) g).op s
  change w.app (op (Z ⨯ Y)) ((sectionAmbient Z W).map g.op s) = _ at h
  refine h.symm.trans (hg'.trans ?_)
  show (prod.fst : Z ⨯ Y ⟶ Z) = prod.map (𝟙 Z) g ≫ prod.fst
  rw [prod.map_fst, Category.comp_id]

end Sheaf

/-! ### The locus where two sections agree -/

section Equalizer

variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- Two sections of `W_T ⟶ Z_T`, as one morphism to the fibre square of `w`. -/
noncomputable def sectionPairLift {T : BigFppfOver B U hU} (σ τ : SectionsOver B U hU Z T W w) :
    yoneda.obj T ⨯ yoneda.obj Z ⟶ pullback w w :=
  pullback.lift σ.1 τ.1 (by rw [σ.2, τ.2])

/-- **The locus in `T` over which two sections of `W_T ⟶ Z_T` agree**: the locus over which
`Z_T ⟶ W ×_Z W` lands in the diagonal. -/
noncomputable def sectionEqualizer {T : BigFppfOver B U hU} (σ τ : SectionsOver B U hU Z T W w) :
    Subfunctor (yoneda.obj T) :=
  factorizationLocus B U hU (pullback.diagonal w) (sectionPairLift σ τ) prod.fst

/-- The projection `T × Z ⟶ T` is closed when `Z ⟶ U` is finite. -/
theorem isClosedMorphism_prod_fst (T : BigFppfOver B U hU)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsClosedMorphism B U hU (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) :=
  isClosed_of_universallyClosed B U hU (isAlgebraicSpace_yoneda B U hU T) _
    ((isFinite_iff_isAffineHom_and_isProper B U hU (isAlgebraicSpace_yoneda_prod_yoneda T Z)
      (isAlgebraicSpace_yoneda B U hU T) _).mp (isFinite_prod_fst T Z hZfin)).2.2.2

/-- The diagonal of an étale morphism of algebraic spaces is an open immersion. -/
theorem isOpenImmersion_diagonal_of_isEtale (hW : IsAlgebraicSpace B U hU W)
    (hw : IsEtale B U hU w) : IsOpenImmersion B U hU (pullback.diagonal w) :=
  isOpenImmersion_diagonal_of_isUnramified B U hU hW (isAlgebraicSpace_yoneda B U hU Z) w
    (isUnramified_of_isEtale B U hU hw)

/-- **The locus where two sections agree is an open subspace** when `w` is étale and `Z ⟶ U` is
finite. -/
theorem isOpenSubspace_sectionEqualizer (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ τ : SectionsOver B U hU Z T W w) :
    IsOpenSubspace B U hU (sectionEqualizer σ τ) :=
  isOpenSubspace_factorizationLocus B U hU (isAlgebraicSpace_yoneda B U hU T)
    (isOpenImmersion_diagonal_of_isEtale hW hw) _ (isClosedMorphism_prod_fst T hZfin)

/-- A morphism to the fibre square of `w` factors through the diagonal exactly when its two
components agree. -/
theorem exists_comp_diagonal_iff {P : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (m : P ⟶ pullback w w) :
    (∃ l : P ⟶ W, l ≫ pullback.diagonal w = m) ↔ m ≫ pullback.fst w w = m ≫ pullback.snd w w := by
  constructor
  · rintro ⟨l, rfl⟩
    simp
  · intro h
    refine ⟨m ≫ pullback.fst w w, pullback.hom_ext ?_ ?_⟩
    · simp
    · simp [h]

/-- **A morphism `T' ⟶ T` lies in the locus where two sections agree exactly when the two
sections agree after restriction to `T'`.** -/
theorem mem_sectionEqualizer_iff (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T T' : BigFppfOver B U hU} (σ τ : SectionsOver B U hU Z T W w) (x : T' ⟶ T) :
    x ∈ (sectionEqualizer σ τ).obj (op T') ↔
      SectionsOver.restrict x σ = SectionsOver.restrict x τ := by
  have hP := isAlgebraicSpace_pullback B U hU w w hW hW (isAlgebraicSpace_yoneda B U hU Z)
  rw [mem_subfunctor_iff, sectionEqualizer,
    factorsThrough_factorizationLocus_iff B U hU hW hP (isAlgebraicSpace_yoneda_prod_yoneda T Z)
      (isAlgebraicSpace_yoneda B U hU T) (isOpenImmersion_diagonal_of_isEtale hW hw) _
      (isClosedMorphism_prod_fst T hZfin) (isAlgebraicSpace_yoneda B U hU T') (yoneda.map x),
    exists_comp_diagonal_iff, Category.assoc, Category.assoc, sectionPairLift, pullback.lift_fst,
    pullback.lift_snd, Subtype.ext_iff, SectionsOver.restrict_coe, SectionsOver.restrict_coe]
  have hpb := (isPullback_prod_map_fst x Z).flip
  set e := hpb.isoPullback
  have hefst : e.hom ≫ pullback.fst _ _ = prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)) :=
    hpb.isoPullback_hom_fst
  constructor
  · intro h
    rw [← hefst, Category.assoc, Category.assoc, h]
  · intro h
    refine (cancel_epi e.hom).1 ?_
    rw [← Category.assoc, ← Category.assoc, hefst, h]

end Equalizer

/-! ### The fibre products of points of the space of sections -/

section Chart

variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- The locus in `T` over which two points of the space of sections over `T` agree. -/
noncomputable def sectionSpaceEqualizer {T : BigFppfOver B U hU}
    (s t : (sectionSpace B U hU Z W w).obj (op T)) : Subfunctor (yoneda.obj T) :=
  sectionEqualizer (sectionSpaceEquiv B U hU Z T W w s) (sectionSpaceEquiv B U hU Z T W w t)

/-- A morphism `x : T' ⟶ T` lies in the locus where two points `s`, `t` of the space of sections
over `T` agree exactly when their restrictions along `x` coincide. -/
theorem mem_sectionSpaceEqualizer_iff (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T T' : BigFppfOver B U hU} (s t : (sectionSpace B U hU Z W w).obj (op T)) (x : T' ⟶ T) :
    x ∈ (sectionSpaceEqualizer s t).obj (op T') ↔
      (sectionSpace B U hU Z W w).map x.op s = (sectionSpace B U hU Z W w).map x.op t := by
  rw [sectionSpaceEqualizer, mem_sectionEqualizer_iff hW hw hZfin, ← sectionSpaceEquiv_restrict,
    ← sectionSpaceEquiv_restrict, (sectionSpaceEquiv B U hU Z T' W w).apply_eq_iff_eq]

/-- The value of a morphism out of a representable presheaf is the restriction of the section
naming it. -/
theorem app_eq_map_yonedaEquiv {F : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {A T : BigFppfOver B U hU}
    (ξ : yoneda.obj A ⟶ F) (a : T ⟶ A) : ξ.app (op T) a = F.map a.op (yonedaEquiv ξ) := by
  rw [yonedaEquiv_naturality, yonedaEquiv_apply]
  simp

/-- **The chart of the fibre product of two points of the space of sections**: the locus in
`A × A'` over which the two points, pulled back along the two projections, agree. -/
noncomputable def sectionSpaceChart {A A' : BigFppfOver B U hU}
    (ξ : yoneda.obj A ⟶ sectionSpace B U hU Z W w)
    (ξ' : yoneda.obj A' ⟶ sectionSpace B U hU Z W w) :
    Subfunctor (yoneda.obj (A ⨯ A')) :=
  sectionSpaceEqualizer ((sectionSpace B U hU Z W w).map (prod.fst : A ⨯ A' ⟶ A).op (yonedaEquiv ξ))
    ((sectionSpace B U hU Z W w).map (prod.snd : A ⨯ A' ⟶ A').op (yonedaEquiv ξ'))

/-- A morphism `x : T ⟶ A ⨯ A'` lies in `sectionSpaceChart ξ ξ'` exactly when `ξ` and `ξ'` take
the same value on the respective components of `x`. -/
theorem mem_sectionSpaceChart_iff (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {A A' T : BigFppfOver B U hU}
    (ξ : yoneda.obj A ⟶ sectionSpace B U hU Z W w) (ξ' : yoneda.obj A' ⟶ sectionSpace B U hU Z W w)
    (x : T ⟶ A ⨯ A') :
    x ∈ (sectionSpaceChart ξ ξ').obj (op T) ↔
      ξ.app (op T) (x ≫ prod.fst) = ξ'.app (op T) (x ≫ prod.snd) := by
  rw [sectionSpaceChart, mem_sectionSpaceEqualizer_iff hW hw hZfin, app_eq_map_yonedaEquiv,
    app_eq_map_yonedaEquiv, op_comp, op_comp, Functor.map_comp_apply,
    Functor.map_comp_apply]

/-- **The chart of the fibre product of two points of the space of sections is that fibre
product.** -/
theorem isPullback_sectionSpaceChart (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) {A A' : BigFppfOver B U hU}
    (ξ : yoneda.obj A ⟶ sectionSpace B U hU Z W w)
    (ξ' : yoneda.obj A' ⟶ sectionSpace B U hU Z W w) :
    IsPullback ((sectionSpaceChart ξ ξ').ι ≫ yoneda.map prod.fst)
      ((sectionSpaceChart ξ ξ').ι ≫ yoneda.map prod.snd) ξ ξ' := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨x, hx⟩
    exact (mem_sectionSpaceChart_iff hW hw hZfin ξ ξ' x).1 hx
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h₁, h₂⟩
    exact Subtype.ext (prod.hom_ext h₁ h₂)
  · intro a a' h
    refine ⟨⟨prod.lift a a', ?_⟩, ?_, ?_⟩
    · rwa [mem_sectionSpaceChart_iff hW hw hZfin ξ ξ', prod.lift_fst, prod.lift_snd]
    · exact prod.lift_fst (a : T.unop ⟶ A) (a' : T.unop ⟶ A')
    · exact prod.lift_snd (a : T.unop ⟶ A) (a' : T.unop ⟶ A')

end Chart

/-! ### The diagonal of the space of sections -/

section Diagonal

variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- **The fibre product of two points of the space of sections is represented by an open
subscheme of the product of their sources.** -/
theorem exists_isPullback_sectionSpace (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) {A A' : BigFppfOver B U hU}
    (ξ : yoneda.obj A ⟶ sectionSpace B U hU Z W w)
    (ξ' : yoneda.obj A' ⟶ sectionSpace B U hU Z W w) :
    ∃ (c : BigFppfOver B U hU) (m : c ⟶ A ⨯ A'),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B U hU).map m) ∧
      IsPullback (yoneda.map (m ≫ prod.fst)) (yoneda.map (m ≫ prod.snd)) ξ ξ' := by
  set E := sectionSpaceChart ξ ξ'
  have hE : IsOpenSubspace B U hU E := isOpenSubspace_sectionEqualizer hW hw hZfin _ _
  have hrep := isRepresentable_of_isOpenSubspace_yoneda B U hU (A ⨯ A') E hE
  let e : yoneda.obj E.toFunctor.reprX ≅ E.toFunctor := E.toFunctor.reprW
  let m : E.toFunctor.reprX ⟶ A ⨯ A' := yoneda.preimage (e.hom ≫ E.ι)
  have hm : yoneda.map m = e.hom ≫ E.ι := yoneda.map_preimage _
  refine ⟨E.toFunctor.reprX, m, ?_, ?_⟩
  · have hoi : IsOpenImmersion B U hU (yoneda.map m) := by
      rw [hm]
      exact MorphismProperty.RespectsIso.precomp _ e.hom _ hE.2
    exact MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B U hU)) hoi
  · refine (isPullback_sectionSpaceChart hW hw hZfin ξ ξ').of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp [hm]
      rfl
    · simp [hm]
      rfl

end Diagonal

/-! ### Products with a scheme of the site -/

section Products

/-- The morphism of an object of the site to the terminal object `U`. -/
noncomputable abbrev toBase (A : BigFppfOver B U hU) : A ⟶ Over.mk (𝟙 (B.obj hU)) :=
  Over.mkIdTerminal.from A

/-- The product in the site is the fibre product over the terminal object, and so is its image
in schemes. -/
theorem isPullback_toScheme_prod (A A' : BigFppfOver B U hU) :
    IsPullback ((BigFppfOver.toScheme B U hU).map (prod.fst : A ⨯ A' ⟶ A))
      ((BigFppfOver.toScheme B U hU).map (prod.snd : A ⨯ A' ⟶ A'))
      ((BigFppfOver.toScheme B U hU).map (toBase A))
      ((BigFppfOver.toScheme B U hU).map (toBase A')) :=
  (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd A A') Over.mkIdTerminal).map _

/-- A property of morphisms of schemes stable under base change passes from the structure
morphism of `A` to the second projection `A × A' ⟶ A'`. -/
theorem prop_toScheme_prod_snd {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {A A' : BigFppfOver B U hU} (h : P ((BigFppfOver.toScheme B U hU).map (toBase A))) :
    P ((BigFppfOver.toScheme B U hU).map (prod.snd : A ⨯ A' ⟶ A')) :=
  MorphismProperty.of_isPullback (isPullback_toScheme_prod A A') h

/-- A property of morphisms of schemes stable under base change passes from the structure
morphism of `A'` to the first projection `A × A' ⟶ A`. -/
theorem prop_toScheme_prod_fst {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {A A' : BigFppfOver B U hU} (h : P ((BigFppfOver.toScheme B U hU).map (toBase A'))) :
    P ((BigFppfOver.toScheme B U hU).map (prod.fst : A ⨯ A' ⟶ A)) :=
  MorphismProperty.of_isPullback (isPullback_toScheme_prod A A').flip h

/-- The image in schemes of the morphism to the terminal object is the structure morphism. -/
theorem toScheme_map_toBase (A : BigFppfOver B U hU) :
    (BigFppfOver.toScheme B U hU).map (toBase A) = B.inclusion.map A.hom := by
  have h : toBase A = Over.homMk A.hom := Over.mkIdTerminal.hom_ext _ _
  rw [h]
  rfl

end Products

/-! ### Lifting sections along an étale cover -/

section Lift

variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- The comparison `T' × Z ⟶ T × Z` of products of representable presheaves is the image of the
comparison of products in the site. -/
theorem preservesLimitPair_iso_inv_comp_map_comp_hom {T T' : BigFppfOver B U hU} (g : T' ⟶ T) :
    (PreservesLimitPair.iso yoneda T' Z).inv ≫ yoneda.map (prod.map g (𝟙 Z)) ≫
      (PreservesLimitPair.iso yoneda T Z).hom = prod.map (yoneda.map g) (𝟙 (yoneda.obj Z)) := by
  rw [Iso.inv_comp_eq]
  refine prod.hom_ext ?_ ?_
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst, prod.map_fst,
      prodComparison_fst_assoc, ← yoneda.map_comp]
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd, prod.map_snd,
      ← yoneda.map_comp, Category.comp_id]

/-- **Étale-locally, a section of `w` lifts along a surjective étale chart of `W`.** This is
Stacks 05XQ for the base change of the chart along the section, a surjective étale morphism of
schemes to the finite `T × Z`. -/
theorem exists_lift_sectionsOver
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) {V : BigFppfOver B U hU}
    (p : yoneda.obj V ⟶ W)
    (hpS : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B U hU)).presheaf p)
    (hpE : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B U hU)).presheaf p)
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    ∃ (T' : BigFppfOver B U hU) (g : T' ⟶ T) (σ' : SectionsOver B U hU Z T' (yoneda.obj V) (p ≫ w)),
      _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B U hU).map g) ∧
        _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B U hU).map g) ∧
          SectionsOver.pushforward (g := p) rfl σ' = SectionsOver.restrict g σ := by
  let G := BigFppfOver.toScheme B U hU
  let e := PreservesLimitPair.iso yoneda T Z
  let χ : yoneda.obj (T ⨯ Z) ⟶ W := e.hom ≫ σ.1
  let hrep := hpE.rep
  have hsq : IsPullback (hrep.fst χ) (yoneda.map (hrep.snd χ)) p χ := hrep.isPullback χ
  have hS : _root_.AlgebraicGeometry.Surjective (G.map (hrep.snd χ)) := hpS.property _ _ _ hsq
  have hE : _root_.AlgebraicGeometry.Etale (G.map (hrep.snd χ)) := hpE.property _ _ _ hsq
  have hfin : _root_.AlgebraicGeometry.IsFinite (G.map (prod.fst : T ⨯ Z ⟶ T)) :=
    prop_toScheme_prod_fst (P := @_root_.AlgebraicGeometry.IsFinite)
      (by rwa [toScheme_map_toBase])
  obtain ⟨T', g, t, hgS, hgE, ht⟩ := Space.exists_surjective_etale_lift_of_isFinite B U hU
    (prod.fst : T ⨯ Z ⟶ T) (hrep.snd χ)
  let k : T' ⨯ Z ⟶ pullback (prod.fst : T ⨯ Z ⟶ T) g :=
    pullback.lift (prod.map g (𝟙 Z)) prod.fst (by simp)
  let e' := PreservesLimitPair.iso yoneda T' Z
  let τ : yoneda.obj T' ⨯ yoneda.obj Z ⟶ yoneda.obj V := e'.inv ≫ yoneda.map (k ≫ t) ≫ hrep.fst χ
  have hkt : k ≫ t ≫ hrep.snd χ = prod.map g (𝟙 Z) := by
    rw [ht, pullback.lift_fst]
  have hτp : τ ≫ p = prod.map (yoneda.map g) (𝟙 _) ≫ σ.1 := by
    calc τ ≫ p = e'.inv ≫ yoneda.map (k ≫ t) ≫ yoneda.map (hrep.snd χ) ≫ χ := by
          simp only [τ, Category.assoc, hsq.w]
      _ = e'.inv ≫ yoneda.map (prod.map g (𝟙 Z)) ≫ e.hom ≫ σ.1 := by
          rw [← yoneda.map_comp_assoc, Category.assoc, hkt]
      _ = prod.map (yoneda.map g) (𝟙 _) ≫ σ.1 := by
          rw [← preservesLimitPair_iso_inv_comp_map_comp_hom g]
          simp only [Category.assoc, e, e']
  refine ⟨T', g, ⟨τ, ?_⟩, hgS, hgE, Subtype.ext hτp⟩
  rw [← Category.assoc, hτp, Category.assoc, σ.2, prod.map_snd, Category.comp_id]

end Lift

/-! ### Stacks 05XR -/

section Main

variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- The representable presheaf of the terminal object of the site is terminal. -/
noncomputable def isTerminal_yoneda_base : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hU)))) :=
  (Over.mkIdTerminal (X := B.obj hU)).isTerminalObj yoneda _

/-- A morphism from a representable presheaf to the terminal presheaf is étale exactly when the
structure morphism of the representing object is. -/
theorem presheaf_etale_terminal_from_iff (A : BigFppfOver B U hU)
    (φ : yoneda.obj A ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B U hU)).presheaf φ ↔
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B U hU).map (toBase A)) := by
  let iT := (isTerminal_yoneda_base (B := B) (U := U) (hU := hU)).uniqueUpToIso terminalIsTerminal
  have hφ : φ = yoneda.map (toBase A) ≫ iT.hom := terminal.hom_ext _ _
  have := inverseImage_isStableUnderBaseChange B U hU
    _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  rw [hφ, MorphismProperty.cancel_right_of_respectsIso (P := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B U hU))), presheaf_yoneda_map_etale_iff]

/-- **A surjective étale atlas of the space of sections, by an object étale over `U`.** It is a
scheme atlas of the space of sections of a separated étale cover of `W`, which is an algebraic
space étale over `U` by the separated case of Stacks 05XR, followed by the morphism to the space
of sections of `w`. -/
theorem exists_atlas_sectionSpace (hW : IsAlgebraicSpace B U hU W) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    ∃ (V₀ : BigFppfOver B U hU) (f : yoneda.obj V₀ ⟶ sectionSpace B U hU Z W w),
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B U hU).map (toBase V₀)) ∧
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B U hU)).presheaf f ∧
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B U hU)).presheaf f := by
  let G := BigFppfOver.toScheme B U hU
  obtain ⟨V, p, hVsep, hpS, hpE⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover B U hU W hW
  have hw' : IsEtale B U hU (p ≫ w) := isEtale_comp B U hU (isEtale_of_presheaf_etale B U hU hpE) hw
  have hwsep : IsSeparated B U hU (p ≫ w) :=
    isSeparated_of_isEtale_of_scheme_isSeparated B U hU (yoneda.obj Z)
      (isAlgebraicSpace_yoneda B U hU Z) V hVsep (p ≫ w) hw'
  have hV := isAlgebraicSpace_yoneda B U hU V
  have hF' := isAlgebraicSpace_sectionSpace_of_isSeparated hV hw' hwsep hZfin
  have hF'et := isEtale_sectionSpace_of_isSeparated hV hw' hwsep hZfin
  obtain ⟨V₀, a, haS, haE⟩ := hF'.exists_atlas
  let π := sectionSpaceMap (g := p) (w₁ := p ≫ w) (w₂ := w) rfl
  have hV₀ : _root_.AlgebraicGeometry.Etale (G.map (toBase V₀)) :=
    (presheaf_etale_terminal_from_iff V₀ _).1 (hF'et V₀ a haE)
  have hSbc := inverseImage_isStableUnderBaseChange B U hU
    (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.Surjective.{u}))
  have hEbc := inverseImage_isStableUnderBaseChange B U hU
    _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  refine ⟨V₀, a ≫ π, hV₀, ?_, ?_⟩
  · refine MorphismProperty.relative.of_exists fun T ξ => ?_
    obtain ⟨c, m, -, hsq⟩ := exists_isPullback_sectionSpace hW hw hZfin (a ≫ π) ξ
    refine ⟨c, yoneda.map (m ≫ prod.fst), m ≫ prod.snd, hsq, ?_⟩
    -- lift the section named by `ξ` along the cover, étale-locally on `T`
    set σ := sectionSpaceEquiv B U hU Z T W w (yonedaEquiv ξ)
    obtain ⟨T', g, σ', hgS, -, hσ'⟩ := exists_lift_sectionsOver hZfin p hpS hpE σ
    let ξ' : yoneda.obj T' ⟶ sectionSpace B U hU Z (yoneda.obj V) (p ≫ w) :=
      yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T' (yoneda.obj V) (p ≫ w)).symm σ')
    have hξ' : ξ' ≫ π = yoneda.map g ≫ ξ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      apply (sectionSpaceEquiv B U hU Z T' W w).injective
      rw [sectionSpaceEquiv_sectionSpaceMap, Equiv.apply_symm_apply, hσ',
        sectionSpaceEquiv_restrict w g (yonedaEquiv ξ)]
    -- the atlas of the separated space of sections is surjective over `T'`
    have hsq' := haS.rep.isPullback ξ'
    have hQS : _root_.AlgebraicGeometry.Surjective (G.map (haS.rep.snd ξ')) :=
      haS.property _ _ _ hsq'
    let l := yoneda.preimage (hsq.lift (haS.rep.fst ξ') (yoneda.map (haS.rep.snd ξ' ≫ g)) (by
      rw [← Category.assoc, hsq'.w, yoneda.map_comp, Category.assoc, Category.assoc, hξ']))
    have hl : l ≫ m ≫ prod.snd = haS.rep.snd ξ' ≫ g := by
      apply yoneda.map_injective
      rw [yoneda.map_comp, yoneda.map_preimage]
      exact hsq.lift_snd _ _ _
    have : _root_.AlgebraicGeometry.Surjective (G.map l ≫ G.map (m ≫ prod.snd)) := by
      rw [← G.map_comp, hl, G.map_comp]
      infer_instance
    exact _root_.AlgebraicGeometry.Surjective.of_comp (G.map l) (G.map (m ≫ prod.snd))
  · refine MorphismProperty.relative.of_exists fun T ξ => ?_
    obtain ⟨c, m, hm, hsq⟩ := exists_isPullback_sectionSpace hW hw hZfin (a ≫ π) ξ
    refine ⟨c, yoneda.map (m ≫ prod.fst), m ≫ prod.snd, hsq, ?_⟩
    have : _root_.AlgebraicGeometry.Etale (G.map (prod.snd : V₀ ⨯ T ⟶ T)) :=
      prop_toScheme_prod_snd (P := @_root_.AlgebraicGeometry.Etale) hV₀
    show _root_.AlgebraicGeometry.Etale (G.map (m ≫ prod.snd))
    rw [G.map_comp]
    infer_instance

/-- **Stacks 05XR.** Let `Z ⟶ U` be a finite morphism of schemes, let `W` be an algebraic space
over `U` and let `w : W ⟶ Z` be étale. Then the functor of sections of `W_T ⟶ Z_T` over `T/U` is an
algebraic space, and its structure morphism to `U` is étale.

The source asks `Z ⟶ U` to be finite locally free; only finiteness is used. -/
@[stacks 05XR]
theorem isAlgebraicSpace_sectionSpace_and_isEtale (hW : IsAlgebraicSpace B U hU W)
    (hw : IsEtale B U hU w) (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) ∧
      IsEtale B U hU (terminal.from (sectionSpace B U hU Z W w)) := by
  obtain ⟨V₀, f, hV₀, hS, hE⟩ := exists_atlas_sectionSpace hW hw hZfin
  have hF : IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) :=
    isAlgebraicSpace_of_surjective_etale_atlas B U hU
      (isSheaf_sectionSpace_of_isSheaf Z W w hW.isSheaf) V₀ f hS hE
  refine ⟨hF, isEtale_of_comp_surjective_isEtale B U hU (isAlgebraicSpace_yoneda B U hU V₀) hF
    (isAlgebraicSpace_terminal B U hU) f (f ≫ terminal.from _) _ rfl
    (isSurjective_of_presheafSurjective B U hU f hS) (isEtale_of_presheaf_etale B U hU hE) ?_⟩
  intro X φ hφ
  rw [presheaf_etale_terminal_from_iff]
  have hφ' : φ = yoneda.map (yoneda.preimage φ) := (yoneda.map_preimage φ).symm
  rw [hφ', presheaf_yoneda_map_etale_iff] at hφ
  have h : toBase X = yoneda.preimage φ ≫ toBase V₀ := Over.mkIdTerminal.hom_ext _ _
  rw [h, Functor.map_comp]
  infer_instance

end Main

end AlgebraicGeometry.Space

end
