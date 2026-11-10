module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# Representability of separated locally quasi-finite morphisms of algebraic spaces

An algebraic space over `S` which admits a separated, locally quasi-finite morphism to a
representable algebraic space is itself representable; consequently a separated, locally
quasi-finite morphism between arbitrary algebraic spaces over `S` is relatively representable
along the Yoneda embedding of the big fppf site.

The argument is local on the source. Around a point of the source, Tag 0ADU produces an étale
neighbourhood of the target over which the base change splits off a clopen part that is finite
over the neighbourhood and carries a point above the chosen one. Shrinking the neighbourhood to
an affine étale chart and the clopen part to an affine open, Tag 03XW identifies the image of
that open in the source as a quasi-compact representable open subspace still containing the
chosen point. So every point of the source lies in a representable open subspace, the schematic
locus of Tag 03JH is therefore surjective on points and hence the whole of the source, and the
source is representable. The general statement follows by base change, both hypotheses being
stable under it.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated`: **Stacks 03XX**.
  An algebraic space separated and locally quasi-finite over a representable algebraic space
  over `S` is representable.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated`:
  **Stacks 0418**. A separated, locally quasi-finite morphism of algebraic spaces over `S` is
  relatively representable along the Yoneda embedding.

## Implementation notes

Algebraic spaces are presheaves on the big fppf site over the base scheme, and representability
of such a presheaf is representability by a scheme over the base. Both hypotheses are properties
of the underlying natural transformation, so nothing is bundled into the category of algebraic
spaces of Tag 02X2 except where an input is stated there.

Tag 03JH enters through the unconditional form
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`,
whose cofinal family is the family of all representable open subspaces. Surjectivity of the
inclusion of the schematic locus on points is upgraded to equality with the whole space through
the order isomorphism of Tag 03BZ between open subspaces and open subsets of the point space.

The subspace produced by Tag 03XW is the one cut out by a set of points, so the point of the
source is recovered in it through
`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`, which identifies the point set
of that subspace with the given set.

## References

* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site is found only after a deep search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_qfSepRep (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_qfSepRep
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The map on points of a composite of morphisms of presheaves, applied to a point. -/
private theorem pointsMap_comp_apply_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    (x : points B S hS F) :
    pointsMap B S hS F (α ≫ β) x = pointsMap B S hS G β (pointsMap B S hS F α x) :=
  congrFun (pointsMap_comp B S hS F α β) x

/-- The inverse image along the forgetful functor of a base-change-stable property of
morphisms of schemes is stable under base change. -/
local instance property_inverseImage_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange where
  of_isPullback hp hf := P.of_isPullback (hp.map (BigFppfOver.toScheme B S hS)) hf

/-- A morphism of the big fppf site over `S` satisfying a base-change-stable property of
schemes satisfies it after every represented base change. -/
private theorem presheaf_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : BigFppfOver B S hS} (i : U ⟶ V) (hi : P ((BigFppfOver.toScheme B S hS).map i)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
  let _ := property_inverseImage_baseChange B S hS P
  MorphismProperty.relative_map hi

/-- An open immersion of the big fppf site over `S` is an open immersion of algebraic
spaces. -/
private theorem openImmersion_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (i : U ⟶ V)
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)) :
    IsOpenImmersion B S hS (yoneda.map i) :=
  MorphismProperty.relative_map hi

/-- Every point of a representable algebraic space over `S` is hit by an affine open of the
representing object. -/
private theorem exists_affine_open_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (x : points B S hS (yoneda.obj U)) :
    ∃ (A : BigFppfOver B S hS) (i : A ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      ∃ a : points B S hS (yoneda.obj A),
        pointsMap B S hS (yoneda.obj A) (yoneda.map i) a = x := by
  classical
  induction x using Quot.inductionOn with | h x =>
  let P := BigFppfOver.toScheme B S hS
  let p : Spec (.of x.carrier) ⟶ P.obj U := P.map x.value
  obtain ⟨O, hO, hxO, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := P.obj U) (x := p (IsLocalRing.closedPoint x.carrier)) (U := ⊤) trivial
  let A₀ : B.Schemes := ⟨O.toScheme, (Scheme.size_coe_opens_le _ O).trans_lt U.left.2⟩
  let i₀ : A₀ ⟶ U.left := ObjectProperty.homMk O.ι
  let A : BigFppfOver B S hS := Over.mk (i₀ ≫ U.hom)
  let i : A ⟶ U := Over.homMk i₀
  have hr : Set.range p ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z = IsLocalRing.closedPoint x.carrier := Subsingleton.elim _ _
    change p z ∈ O
    rw [hz]
    exact hxO
  let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift O.ι p hr
  have hl : l ≫ O.ι = p := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hr
  let a₀ : x.siteObject ⟶ A := Over.homMk (ObjectProperty.homMk l) (by
    apply B.inclusion.map_injective
    change l ≫ O.ι ≫ B.inclusion.map U.hom = B.inclusion.map x.siteObject.hom
    rw [← Category.assoc, hl]
    exact congrArg B.inclusion.map x.value.w)
  have hai : a₀ ≫ i = x.value := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl)
  let a : FieldValuedPoint B S hS (yoneda.obj A) :=
    { carrier := x.carrier, contained := x.contained, toBase := x.toBase, value := a₀ }
  refine ⟨A, i, hO,
    (show _root_.AlgebraicGeometry.IsOpenImmersion O.ι from inferInstance),
    FieldValuedPoint.class B S hS (yoneda.obj A) a, ?_⟩
  change Quot.mk _ (FieldValuedPoint.map B S hS _ (yoneda.map i) a) = Quot.mk _ x
  congr 1
  change
    ({ carrier := x.carrier, contained := x.contained, toBase := x.toBase,
       value := a₀ ≫ i } : FieldValuedPoint B S hS (yoneda.obj U)) = x
  rw [hai]

/-- Every point of an algebraic space over `S` is hit by an étale chart with affine
underlying scheme. -/
private theorem exists_affine_etale_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      ∃ p : points B S hS (yoneda.obj A),
        pointsMap B S hS (yoneda.obj A) a p = x := by
  obtain ⟨U, a, hsurj, het⟩ := hX.exists_atlas
  obtain ⟨u, hu⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp hsurj x
  obtain ⟨A, i, hA, hi, p, hp⟩ := exists_affine_open_chart B S hS U u
  have hiEt := presheaf_yoneda_map B S hS (@_root_.AlgebraicGeometry.Etale.{u}) i inferInstance
  let Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  refine ⟨A, yoneda.map i ≫ a, hA, MorphismProperty.comp_mem Q.presheaf _ _ hiEt het, p, ?_⟩
  rw [pointsMap_comp_apply_eq, hp, hu]

/-- A finite morphism of algebraic spaces over `S` is quasi-affine. -/
private theorem isQuasiAffineHom_of_isFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsFinite B S hS f) : IsQuasiAffineHom B S hS f := by
  intro Z g
  obtain ⟨W, p, i, hW, _, hp⟩ := hf Z.obj Z.property g
  exact ⟨W, inferInstance, ⟨hp.flip.isoPullback⟩⟩

/-- A base change of an open immersion of presheaves on the big fppf site of `S` is an open
immersion. -/
private theorem isOpenImmersion_of_isPullback_presheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {i : W ⟶ X} {p : W ⟶ A} {f : X ⟶ Y} {g : A ⟶ Y}
    (hp : IsPullback i p f g) (hf : IsOpenImmersion B S hS f) :
    IsOpenImmersion B S hS p := by
  let Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback hp hf

/-- Around a point of the source of a separated, locally quasi-finite morphism of algebraic
spaces over `S` there is an étale neighbourhood of the target with a clopen part of the base
change which is finite over it. -/
private theorem exists_etale_finite_neighborhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyQuasiFinite B S hS f) (hs : IsSeparated B S hS f)
    (x : points B S hS X) :
    ∃ (U : AlgebraicSpaces B S hS) (g : U.obj ⟶ Y) (V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧ IsOpenSubspace B S hS V ∧
      IsFinite B S hS (V.ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x := by
  obtain ⟨U, g, u, W, V, hg, _, _, _, hV, _, _, _, hfin, v, hv, _⟩ :=
    exists_etale_finite_clopen_part B S hS
      (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (Y := (⟨Y, hY⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk f) x
      (fun U V a b h ha hb hw => (hf U V a b h ha hb hw).1) hs
      (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hX hf x)
  exact ⟨U, g.hom, V, hg, hV, hfin, v, hv⟩

/-- Around a point of the source of a separated, locally quasi-finite morphism of algebraic
spaces over `S` there is an affine étale chart of the target and an affine open of the base
change along it which is finite over the chart. -/
private theorem exists_finite_affine_open_after_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyQuasiFinite B S hS f) (hs : IsSeparated B S hS f)
    (x : points B S hS X) :
    ∃ (A C : BigFppfOver B S hS) (a : yoneda.obj A ⟶ Y) (p : C ⟶ A)
      (j : yoneda.obj C ⟶ pullback a f),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj C) ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      IsOpenImmersion B S hS j ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
      j ≫ pullback.fst a f = yoneda.map p ∧
      ∃ c : points B S hS (yoneda.obj C),
        pointsMap B S hS (yoneda.obj C) (j ≫ pullback.snd a f) c = x := by
  obtain ⟨U, g, V, hg, hV, hfin, v, hv⟩ :=
    exists_etale_finite_neighborhood B S hS hX hY f hf hs x
  obtain ⟨A, a, hA, ha, z, hz⟩ := exists_affine_etale_chart B S hS U.obj U.property
    (pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v)
  obtain ⟨C, p, i, hC, hpfin, hp⟩ := hfin A hA a
  let r : pullback (a ≫ g) f ⟶ pullback g f :=
    pullback.lift (pullback.fst (a ≫ g) f ≫ a) (pullback.snd (a ≫ g) f)
      (by simp only [Category.assoc, pullback.condition])
  have hr : IsPullback r (pullback.fst (a ≫ g) f) (pullback.fst g f) a := by
    have houter : IsPullback (r ≫ pullback.snd g f) (pullback.fst (a ≫ g) f)
        f (a ≫ g) := by
      simpa only [r, pullback.lift_snd] using (IsPullback.of_hasPullback (a ≫ g) f).flip
    exact houter.of_right (by simp only [r, pullback.lift_fst])
      (IsPullback.of_hasPullback g f).flip
  let j : yoneda.obj C ⟶ pullback (a ≫ g) f := hr.lift (i ≫ V.ι) (yoneda.map p) hp.w
  have hjr : j ≫ r = i ≫ V.ι := hr.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd (a ≫ g) f = i ≫ V.ι ≫ pullback.snd g f := by
    simpa only [r, Category.assoc, pullback.lift_snd] using
      congrArg (fun k => k ≫ pullback.snd g f) hjr
  obtain ⟨c, hcv, _⟩ := exists_point_of_isPullback_presheaf B S hS hp v z hz.symm
  refine ⟨A, C, a ≫ g, p, j, hA, hC, hg A a ha,
    isOpenImmersion_of_isPullback_presheaf B S hS (hp.of_bot' hr) hV.2, hpfin,
    hr.lift_snd _ _ _, c, ?_⟩
  rwa [hjsnd, pointsMap_comp_apply_eq, hcv]

/-- An algebraic space over `S` each of whose points lies in a representable open subspace is
representable: its schematic locus is the whole of it. -/
private theorem isRepresentable_of_schematic_neighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (h : ∀ x : points B S hS X, ∃ V : Subfunctor X,
      IsOpenSubspace B S hS V ∧ V.toFunctor.IsRepresentable ∧
        x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    X.IsRepresentable := by
  let _ : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  obtain ⟨hL, hLrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  have hsurj : Function.Surjective (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) := by
    intro x
    obtain ⟨V, hV, hrep, v, hv⟩ := h x
    have hle : V ≤ schematicLocus B S hS X := le_schematicLocus B S hS X V hV hrep
    refine ⟨pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hle) v, ?_⟩
    rwa [← pointsMap_comp_apply_eq, Subfunctor.homOfLe_ι]
  have htop : IsOpenSubspace B S hS (⊤ : Subfunctor X) :=
    ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS (⊤ : Subfunctor X).ι
      (Functor.relativelyRepresentable.of_isIso yoneda (⊤ : Subfunctor X).ι) hX,
      isOpenImmersion_of_isIso B S hS (⊤ : Subfunctor X).ι⟩
  have hLt : schematicLocus B S hS X = ⊤ := by
    let e := openSubspacesOrderIso B S hS X hX
    have he : e ⟨schematicLocus B S hS X, hL⟩ = e ⟨⊤, htop⟩ := by
      apply SetLike.coe_injective
      change (e ⟨schematicLocus B S hS X, hL⟩).1 = (e ⟨⊤, htop⟩).1
      dsimp only [e]
      rw [openSubspacesOrderIso_apply, openSubspacesOrderIso_apply,
        Set.range_eq_univ.mpr hsurj,
        Set.range_eq_univ.mpr (pointsMap_surjective_of_isIso B S hS _)]
    exact congrArg Subtype.val (e.injective he)
  have _ : IsIso (schematicLocus B S hS X).ι :=
    (Subfunctor.eq_top_iff_isIso (schematicLocus B S hS X)).mp hLt
  exact isRepresentable_of_natIso _ (asIso (schematicLocus B S hS X).ι)

/-- The range of an open immersion into an algebraic space over `S` is an open subspace. -/
private theorem isOpenSubspace_range
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsOpenImmersion B S hS f) :
    IsOpenSubspace B S hS (Subfunctor.range f) := by
  have _ := mono_of_isOpenImmersion B S hS f hf
  have hi : IsOpenImmersion B S hS (Subfunctor.range f).ι := by
    apply (MorphismProperty.cancel_left_of_respectsIso _ (Subfunctor.toRange f) _).mp
    simpa only [Subfunctor.toRange_ι] using hf
  exact ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS _ hi.1 hY, hi⟩

/-- A finite morphism of the big fppf site over `S` is finite as a morphism of algebraic
spaces. -/
private theorem isFinite_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {C A : BigFppfOver B S hS} (p : C ⟶ A)
    (hp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p)) :
    IsFinite B S hS (yoneda.map p) := by
  let Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have h : Q.presheaf (yoneda.map p) :=
    presheaf_yoneda_map B S hS (@_root_.AlgebraicGeometry.IsFinite.{u}) p hp
  intro U hU a
  obtain ⟨V, q, i, hs⟩ := h.rep a
  have hq : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q) :=
    h.property a i q hs
  exact ⟨V, q, i, isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map q), hq, hs⟩

/-- A separated, locally quasi-finite algebraic space over an affine object of the big fppf
site over `S` is representable. -/
private theorem isRepresentable_over_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj T) (hlqf : IsLocallyQuasiFinite B S hS f)
    (hsep : IsSeparated B S hS f) : X.IsRepresentable := by
  apply isRepresentable_of_schematic_neighborhoods B S hS X hX
  intro x
  obtain ⟨A, C, a, p, j, hA, hC, ha, hj, hp, hjp, c, hc⟩ :=
    exists_finite_affine_open_after_etale B S hS hX
      (isAlgebraicSpace_yoneda B S hS T) f hlqf hsep x
  obtain ⟨t, rfl⟩ := yoneda.map_surjective a
  have ht : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ha
  have _ := mono_of_isOpenImmersion B S hS j hj
  have hV : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_range B S hS
      (isAlgebraicSpace_pullback B S hS (yoneda.map t) f
        (isAlgebraicSpace_yoneda B S hS A) hX
        (isAlgebraicSpace_yoneda B S hS T)) j hj
  have he : Subfunctor.toRange j ≫ (Subfunctor.range j).ι ≫
      pullback.fst (yoneda.map t) f = yoneda.map p := by
    simpa only [Subfunctor.toRange_ι_assoc] using hjp
  have hpb : IsPullback (inv (Subfunctor.toRange j))
      ((Subfunctor.range j).ι ≫ pullback.fst (yoneda.map t) f) (yoneda.map p) (𝟙 _) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [← he]
    simp only [IsIso.inv_hom_id_assoc, Category.comp_id]
  have hVqa : IsQuasiAffineHom B S hS
      ((Subfunctor.range j).ι ≫ pullback.fst (yoneda.map t) f) :=
    isQuasiAffineHom_of_isFinite B S hS _
      (isFinite_of_isPullback B S hS hpb (isFinite_yoneda_map B S hS p hp))
  obtain ⟨hUopen, -, hUrep⟩ :=
    isOpenSubspace_isQuasiCompactSpace_isRepresentable_image (B := B) (S := S) (hS := hS)
      (T := T) (T' := A) hT hA (t := t) ht hX hsep hlqf (Subfunctor.range j) hV hVqa
  refine ⟨_, hUopen, hUrep, ?_⟩
  rw [range_pointsMap_ι_openSubspaceOfPoints]
  refine ⟨pointsMap B S hS (yoneda.obj C) (Subfunctor.toRange j) c, ?_⟩
  rwa [← pointsMap_comp_apply_eq, Subfunctor.toRange_ι_assoc]

/-- **Stacks 03XX.** A separated, locally quasi-finite algebraic space over a representable
algebraic space over `S` is representable. -/
@[stacks 03XX]
theorem isRepresentable_of_locallyQuasiFinite_separated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hT : IsAlgebraicSpace B S hS T)
    (f : X ⟶ T)
    (hTrep : T.IsRepresentable)
    (hlqf : IsLocallyQuasiFinite B S hS f)
    (hsep : IsSeparated B S hS f) :
    X.IsRepresentable := by
  classical
  apply isRepresentable_of_schematic_neighborhoods B S hS X hX
  intro x
  obtain ⟨y, hy⟩ := pointsMap_surjective_of_isIso B S hS T.reprW.hom
    (pointsMap B S hS X f x)
  obtain ⟨A, i, hA, hi, a, ha⟩ := exists_affine_open_chart B S hS T.reprX y
  have hg : IsOpenImmersion B S hS (yoneda.map i ≫ T.reprW.hom) :=
    MorphismProperty.RespectsIso.postcomp _ T.reprW.hom (yoneda.map i)
      (openImmersion_yoneda_map B S hS i hi)
  have hga : pointsMap B S hS (yoneda.obj A) (yoneda.map i ≫ T.reprW.hom) a =
      pointsMap B S hS X f x := by
    rw [pointsMap_comp_apply_eq, ha, hy]
  have hP : IsAlgebraicSpace B S hS (pullback f (yoneda.map i ≫ T.reprW.hom)) :=
    isAlgebraicSpace_pullback B S hS f (yoneda.map i ≫ T.reprW.hom) hX
      (isAlgebraicSpace_yoneda B S hS A) hT
  have hlqf' : IsLocallyQuasiFinite B S hS
      (pullback.snd f (yoneda.map i ≫ T.reprW.hom)) :=
    IsLocallyQuasiFinite.of_isPullback B S hS
      (IsPullback.of_hasPullback f (yoneda.map i ≫ T.reprW.hom)).flip hX hT hlqf
  have hsep' : IsSeparated B S hS (pullback.snd f (yoneda.map i ≫ T.reprW.hom)) :=
    isSeparated_pullback B S hS f (yoneda.map i ≫ T.reprW.hom) hsep
  have _ : (pullback f (yoneda.map i ≫ T.reprW.hom)).IsRepresentable :=
    isRepresentable_over_affine B S hS A hA _ hP
      (pullback.snd f (yoneda.map i ≫ T.reprW.hom)) hlqf' hsep'
  have hfst : IsOpenImmersion B S hS (pullback.fst f (yoneda.map i ≫ T.reprW.hom)) :=
    isOpenImmersion_of_isPullback_presheaf B S hS
      (IsPullback.of_hasPullback f (yoneda.map i ≫ T.reprW.hom)).flip hg
  have _ := mono_of_isOpenImmersion B S hS
    (pullback.fst f (yoneda.map i ≫ T.reprW.hom)) hfst
  refine ⟨Subfunctor.range (pullback.fst f (yoneda.map i ≫ T.reprW.hom)),
    isOpenSubspace_range B S hS hX _ hfst,
    isRepresentable_of_natIso _
      (asIso (Subfunctor.toRange (pullback.fst f (yoneda.map i ≫ T.reprW.hom)))), ?_⟩
  obtain ⟨z, hz, _⟩ := exists_point_of_isPullback_presheaf B S hS
    (IsPullback.of_hasPullback f (yoneda.map i ≫ T.reprW.hom)) x a hga.symm
  refine ⟨pointsMap B S hS (pullback f (yoneda.map i ≫ T.reprW.hom))
    (Subfunctor.toRange (pullback.fst f (yoneda.map i ≫ T.reprW.hom))) z, ?_⟩
  rwa [← pointsMap_comp_apply_eq, Subfunctor.toRange_ι]

/-- **Stacks 0418.** A separated, locally quasi-finite morphism of algebraic spaces over `S`
is relatively representable along the Yoneda embedding of the big fppf site. -/
@[stacks 0418]
theorem relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyQuasiFinite B S hS f)
    (hs : IsSeparated B S hS f) :
    yoneda.relativelyRepresentable f := by
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro U ξ
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hP : IsAlgebraicSpace B S hS (pullback f (yonedaEquiv.symm ξ)) :=
    isAlgebraicSpace_pullback B S hS f (yonedaEquiv.symm ξ) hX hU hY
  have hrep : (pullback f (yonedaEquiv.symm ξ)).IsRepresentable :=
    isRepresentable_of_locallyQuasiFinite_separated B S hS _ (yoneda.obj U) hP hU
      (pullback.snd f (yonedaEquiv.symm ξ)) inferInstance
      (IsLocallyQuasiFinite.of_isPullback B S hS
        (IsPullback.of_hasPullback f (yonedaEquiv.symm ξ)).flip hX hY hf)
      (isSeparated_pullback B S hS f (yonedaEquiv.symm ξ) hs)
  exact isRepresentable_of_natIso (pullback f (yonedaEquiv.symm ξ))
    (pullbackSymmetry f (yonedaEquiv.symm ξ))

end AlgebraicGeometry.Space

end
