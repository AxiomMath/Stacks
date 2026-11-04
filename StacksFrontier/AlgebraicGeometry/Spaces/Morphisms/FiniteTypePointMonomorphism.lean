module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# A finite type point is the image of a locally finite type monomorphism (Stacks 06EL)

A finite type point `x` of an algebraic space `X` over `S` is the image of a morphism
`f : Z ⟶ X` which is a monomorphism and locally of finite type, from an algebraic space `Z`
admitting a surjective étale morphism `Spec k ⟶ Z` for a field `k`. This is the implication
from condition (1) to condition (3) of **Stacks 06EL**, and completes that tag: the
equivalence of its conditions (1) and (2), and the implication from its condition (3) to its
condition (1), are
`AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_singleton_space` and
`AlgebraicGeometry.Space.isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint` in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PointsOfFiniteType.lean`.

## Main results

* `AlgebraicGeometry.Space.exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint`
  is **Stacks 06EL, condition (1) implies condition (3)**.

## Implementation notes

The space `Z` is the residual space of `X` at `x` of **Stacks 06QZ**, whose existence is
`AlgebraicGeometry.Space.exists_isResidualSpaceAt`: it is built there as the quotient of the
disjoint union of the spectra of the residue fields of a chart at the points over `x` by the
restricted relation, which is the construction of the source of this tag carried out at a
whole chart fibre instead of a single point. That construction is unconditional because
Stacks 02WW is, by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`; an older note in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PointsOfFiniteType.lean` said otherwise.

What remains is to produce from `Z` the *field* spectrum of condition (3) and the local
finite type of `f`, and this is where the hypothesis that `x` be of finite type enters —
Stacks 06QZ alone gives neither. The argument is the one of the source read through the
residual space:

* A locally finite type representative `p` of `x` is in addition *unramified* over `X`: by
  Stacks 06EH it may be taken to be the residue field at a closed point of an affine étale
  chart, where the morphism from the residue field spectrum is a closed immersion.
* Since `f` is a monomorphism and the point of `|Z|` maps to `x = |p|`, the morphism
  `Spec p.carrier ⟶ X` factors through `f`, by Stacks 06MG applied to the base change of `f`
  along it. Call the factorisation `g`.
* `g` is flat because `Z` is reduced with one point, by Stacks 06QW and Stacks 06QV; it is
  unramified and locally of finite type by cancellation (Stacks 06G6 and Stacks 03XG) from
  `p`, hence locally of finite presentation because `Z` is locally Noetherian
  (Stacks 06G4), hence étale (Stacks 06LU). It is surjective because `|Z|` is a singleton.
* `f` is then locally of finite type by condition (6) of Stacks 040Y, the surjective étale
  chart being `g`.

## References

* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 06EH](https://stacks.math.columbia.edu/tag/06EH)
* [Stacks Project, Tag 06EL](https://stacks.math.columbia.edu/tag/06EL)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 06QV](https://stacks.math.columbia.edu/tag/06QV)
* [Stacks Project, Tag 06QW](https://stacks.math.columbia.edu/tag/06QW)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Auxiliary constructions -/

/-- The morphism from the spectrum of the residue field at a closed point of a scheme is
unramified and locally of finite type, because it is a closed immersion. -/
private theorem unramified_and_locallyOfFiniteType_fromSpecResidueField
    {Y : Scheme.{u}} {y : Y} (hy : IsClosed ({y} : Set Y)) :
    AlgebraicGeometry.Unramified (Y.fromSpecResidueField y) ∧
      AlgebraicGeometry.LocallyOfFiniteType (Y.fromSpecResidueField y) := by
  have : AlgebraicGeometry.IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  exact ⟨(AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified _).2
    ⟨inferInstance, inferInstance⟩, inferInstance⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The tautological field-valued point of the presheaf represented by the site object of a
field-valued point: the identity section over that object. -/
private noncomputable def selfFieldValuedPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS F)) :=
  ⟨p.carrier, p.contained, p.toBase, 𝟙 _⟩

/-- Any morphism from the site object of a field-valued point to a presheaf whose point set is
a subsingleton is surjective on points. -/
private theorem isSurjective_of_subsingleton_points
    {F Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [Subsingleton (points B S hS Z)]
    (p : FieldValuedPoint B S hS F) (f : yoneda.obj (p.siteObject B S hS F) ⟶ Z) :
    IsSurjective B S hS f :=
  fun _ ↦ ⟨(selfFieldValuedPoint B S hS p).class B S hS _, Subsingleton.elim _ _⟩

/-- A morphism from a field spectrum to an algebraic space `X` factors through a
monomorphism `f : Z ⟶ X` as soon as `|Z|` has a point above the point it defines.

The base change of `f` along the morphism is a monomorphism to the field spectrum with a
point above it, hence an isomorphism by **Stacks 06MG**; its inverse followed by the other
projection is the factorisation. -/
private theorem exists_factorisation_of_mono
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X) [Mono f]
    (p : FieldValuedPoint B S hS X) (z : points B S hS Z)
    (hz : pointsMap B S hS Z f z = p.class B S hS X) :
    ∃ g : yoneda.obj (p.siteObject B S hS X) ⟶ Z, g ≫ f = yonedaEquiv.symm p.value := by
  classical
  set T := p.siteObject B S hS X
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ts : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let fs : Zs ⟶ Xs := ObjectProperty.homMk f
  let gs : Ts ⟶ Xs := ObjectProperty.homMk (yonedaEquiv.symm p.value)
  let W := AlgebraicSpaces.fiberProduct B S hS fs gs
  let a : W ⟶ Zs := ObjectProperty.homMk (pullback.fst f gs.hom)
  let b : W ⟶ Ts := ObjectProperty.homMk (pullback.snd f gs.hom)
  have sq : IsPullback a b fs gs := AlgebraicSpaces.isPullback_fiberProduct B S hS fs gs
  have hcompat : pointsMap B S hS Zs.1 fs.hom z =
      pointsMap B S hS Ts.1 gs.hom
        ((selfFieldValuedPoint B S hS p).class B S hS (yoneda.obj T)) :=
    hz.trans (FieldValuedPoint.pointsMap_eq_class B S hS p _).symm
  obtain ⟨w, -, -⟩ := exists_point_of_isPullback B S hS sq z
    ((selfFieldValuedPoint B S hS p).class B S hS (yoneda.obj T)) hcompat
  have : Mono b.hom := inferInstanceAs (Mono (pullback.snd f gs.hom))
  obtain hempty | _ := isEmpty_points_or_isIso_of_mono_to_fieldSpectrum B S hS (k := p.carrier) T
    (Iso.refl _) W.property b.hom
  · exact (hempty.false w).elim
  refine ⟨inv b.hom ≫ a.hom, ?_⟩
  rw [Category.assoc, show a.hom ≫ f = b.hom ≫ gs.hom from pullback.condition,
    IsIso.inv_hom_id_assoc]
  rfl

/-- Every morphism from a field spectrum to a reduced algebraic space with exactly one point
is flat.

By **Stacks 06QW** the space carries a surjective flat morphism from the spectrum of a field;
transporting it along the identification of the covering site object with that spectrum makes
it the morphism presented by a field-valued point, and **Stacks 06QV** then gives flatness of
every field-valued point. -/
private theorem isFlat_fieldValuedPoint_of_isReduced_of_singleton
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hred : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} ↦ IsReduced T))
    (hne : Nonempty (points B S hS Z)) (hsub : Subsingleton (points B S hS Z))
    (p : FieldValuedPoint B S hS Z) :
    IsFlat B S hS (yonedaEquiv.symm p.value) := by
  classical
  obtain ⟨T, k, hk, ⟨e⟩, c, hcsurj, hcflat⟩ :=
    (isReduced_and_singleton_points_iff_hasFlatFieldCover B S hS Z hZ).1 ⟨hred, hne, hsub⟩
  have hkB : B.Contains (Spec (.of k)) := by
    show (Spec (.of k)).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact T.left.property
  let a : B.obj hkB ⟶ T.left := B.inclusion.preimage e.inv
  let K : BigFppfOver B S hS := Over.mk (a ≫ T.hom)
  let v : K ⟶ T := Over.homMk a
  have hv : (BigFppfOver.toScheme B S hS).map v = e.inv := B.inclusion.map_preimage _
  let q : FieldValuedPoint B S hS Z :=
    ⟨k, hkB, B.inclusion.map (a ≫ T.hom), yonedaEquiv (yoneda.map v ≫ c)⟩
  have hq : yonedaEquiv.symm q.value = yoneda.map v ≫ c := yonedaEquiv.symm_apply_apply _
  have hvflat : IsFlat B S hS (yoneda.map v) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget v).2 (hv ▸ inferInstance)
  have hqflat : IsFlat B S hS (yonedaEquiv.symm q.value) := by
    rw [hq]
    exact isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS K)
      (isAlgebraicSpace_yoneda B S hS T) hZ _ _ hvflat hcflat
  exact isFlat_of_fieldCover B S hS Z hZ q.carrier q.contained q.toBase
    (yonedaEquiv.symm q.value) (isSurjective_of_subsingleton_points B S hS q _) hqflat
    p.carrier p.contained p.toBase (yonedaEquiv.symm p.value)

/-- A finite type point of an algebraic space over `S` has a representative whose morphism to
the space is both unramified and locally of finite type.

By **Stacks 06EH** the point is the image of a closed point of an affine scheme étale over
the space; the morphism from the spectrum of the residue field at that closed point is a
closed immersion, hence unramified and locally of finite type, and the étale chart is both as
well. -/
private theorem exists_isUnramified_isLocallyOfFiniteType_fieldValuedPoint
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (hx : IsFiniteTypePoint B S hS X x) :
    ∃ p : FieldValuedPoint B S hS X, p.class B S hS X = x ∧
      IsUnramified B S hS (yonedaEquiv.symm p.value) ∧
      IsLocallyOfFiniteType B S hS (yonedaEquiv.symm p.value) := by
  obtain ⟨U, φ, p₀, -, hφ, hclosed, hp₀x⟩ :=
    (isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart B S hS X hX x).1 hx
  set q := schemePointRepresentative B S hS U (schemePoint B S hS U p₀)
  have hqmap : (BigFppfOver.toScheme B S hS).map q.siteHom =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
        (schemePoint B S hS U p₀) :=
    toScheme_map_siteHom_schemePointRepresentative B S hS U _
  obtain ⟨hunS, hftS⟩ := unramified_and_locallyOfFiniteType_fromSpecResidueField hclosed
  have hqun : IsUnramified B S hS (yoneda.map q.siteHom) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      unramified_isEtaleLocalOnSourceAndTarget q.siteHom).2 (hqmap ▸ hunS)
  have hqft : IsLocallyOfFiniteType B S hS (yoneda.map q.siteHom) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget q.siteHom).2
      (hqmap ▸ hftS)
  have hvalue : yonedaEquiv.symm (FieldValuedPoint.map B S hS (yoneda.obj U) φ q).value =
      yoneda.map q.siteHom ≫ φ := fieldMorphism_map_yoneda B S hS X φ q
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj U) φ q, ?_, ?_, ?_⟩
  · rw [← hp₀x, pointsMap_class]
    exact congrArg (pointsMap B S hS (yoneda.obj U) φ)
      (schemePointRepresentative_class B S hS U p₀)
  · rw [hvalue]
    exact isUnramified_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS U) hX _ _ hqun
      (isUnramified_of_isEtale B S hS hφ)
  · rw [hvalue]
    exact isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS U) hX _ _ hqft
      (isLocallyOfFiniteType_of_isEtale B S hS hX hφ)

/-! ### Condition (3) of Stacks 06EL -/

/-- **Stacks 06EL, condition (1) implies condition (3).** A finite type point `x` of an
algebraic space `X` over `S` is the image of a point of an algebraic space `Z` under a
morphism `f : Z ⟶ X` which is a monomorphism and locally of finite type, where `Z` carries a
surjective étale morphism from the spectrum of a field.

Take for `Z` the residual space of `X` at `x` of Stacks 06QZ, with its monomorphism `f`. A
locally finite type representative `p` of `x` is unramified over `X`, and factors through the
monomorphism `f` because `|Z|` sits over `x`; the factorisation `g` is flat since `Z` is
reduced with a single point, unramified and locally of finite type by cancellation, hence
locally of finite presentation since `Z` is locally Noetherian, hence étale, and surjective
since `|Z|` is a singleton. Local finite type of `f` then follows from that of `g ≫ f` by
condition (6) of Stacks 040Y. -/
theorem exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (hx : IsFiniteTypePoint B S hS X x) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ X)
      (z : FieldValuedPoint B S hS Z),
      IsSurjective B S hS (yonedaEquiv.symm z.value) ∧
        IsEtale B S hS (yonedaEquiv.symm z.value) ∧
        IsLocallyOfFiniteType B S hS f ∧ Mono f ∧
        x = pointsMap B S hS Z f (z.class B S hS Z) := by
  classical
  obtain ⟨p, hpx, hpun, hpft⟩ :=
    exists_isUnramified_isLocallyOfFiniteType_fieldValuedPoint B S hS hX x hx
  obtain ⟨Z, f, hZ, hmono, hred, hnoeth, hne, hsub, hsupp⟩ :=
    exists_isResidualSpaceAt B S hS (X := X) hX x
  obtain ⟨g, hg⟩ := exists_factorisation_of_mono B S hS hZ hX f p (Classical.choice hne)
    ((hsupp _).trans hpx.symm)
  let z : FieldValuedPoint B S hS Z :=
    ⟨p.carrier, p.contained, p.toBase, yonedaEquiv g⟩
  have hzg : yonedaEquiv.symm z.value = g := yonedaEquiv.symm_apply_apply _
  have hyg : IsAlgebraicSpace B S hS (yoneda.obj (p.siteObject B S hS X)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hcompft : IsLocallyOfFiniteType B S hS (g ≫ f) := by rwa [hg]
  have hgft : IsLocallyOfFiniteType B S hS g :=
    isLocallyOfFiniteType_of_comp B S hS hyg hZ hX g f hcompft
  have hgun : IsUnramified B S hS g := isUnramified_of_comp B S hS hyg hZ hX g f (by rwa [hg])
  have hglfp : IsLocallyOfFinitePresentation B S hS g :=
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hyg hZ g hnoeth hgft
  have hgflat : IsFlat B S hS g := by
    have h := isFlat_fieldValuedPoint_of_isReduced_of_singleton B S hS hZ hred hne hsub z
    rwa [hzg] at h
  have hget : IsEtale B S hS g :=
    isEtale_of_isFlat_of_isUnramified B S hS hyg hZ g hglfp hgflat hgun
  have hgsurj : IsSurjective B S hS g :=
    isSurjective_of_subsingleton_points B S hS p g
  have hfft : IsLocallyOfFiniteType B S hS f :=
    (isLocallyOfFiniteType_iff_exists_surjective_etale_source_chart B S hS hZ hX f).2
      ⟨p.siteObject B S hS X, g,
        (presheafSurjective_iff_isSurjective_yoneda B S hS Z hZ _ g).2 hgsurj,
        (isEtale_iff_presheaf_of_yoneda B S hS g).1 hget, hcompft⟩
  refine ⟨Z, hZ, f, z, ?_, ?_, hfft, hmono, (hsupp (z.class B S hS Z)).symm⟩ <;>
    rwa [hzg]

end AlgebraicGeometry.Space

end
