module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SinglePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Finite field-valued points of a decent algebraic space

Let `X` be an algebraic space over a scheme `S` and let `Spec k ⟶ X ⟶ S` be a commutative
diagram, that is a field-valued point of `X` in the sense of Stacks 03BU. **Stacks 08AL** says
that if `X` is decent, the image point `s` of `Spec k ⟶ S` is closed in `S` and the residue
field extension `κ(s) ⟶ k` is finite, then `Spec k ⟶ X` is a finite morphism; and that if
moreover `κ(s) = k` then it is a closed immersion.

The argument is the one in the source. The image `x` of `Spec k ⟶ X` is a closed point of `|X|`
by Stacks 07U5, so it carries a reduced closed subspace `Z ⊆ X` with `|Z| = {x}`, Stacks 03IQ.
That subspace is decent by Stacks 0ABT, and a decent reduced algebraic space with one point is
the spectrum of a field `k'` by Stacks 047Z. The point factors as `Spec k ⟶ Z ⟶ X` because
`Spec k` is reduced and its image lies in `|Z|`, Stacks 03JJ, and `κ(s) ⟶ k' ⟶ k` is a tower of
fields with `k` finite over `κ(s)`, so `k` is finite over `k'` and `Spec k ⟶ Z` is finite.
Composing with the closed immersion `Z ⟶ X`, which is finite, gives Stacks 03ZR. When
`κ(s) = k` the map `k' ⟶ k` is an isomorphism, so `Spec k ⟶ Z` is an isomorphism and the point
is a closed immersion.

## Main results

* `AlgebraicGeometry.Space.isFinite_fieldMorphism_of_moduleFinite_residueField`: **Stacks
  08AL**, the finiteness statement.
* `AlgebraicGeometry.Space.isClosedImmersion_fieldMorphism_of_isIso_residueField`: **Stacks
  08AL**, the closed-immersion statement in the case of a rational point.

## Implementation notes

The point `s` and the residue field embedding `κ(s) ⟶ k` are the two components of
`AlgebraicGeometry.Scheme.SpecToEquivOfField` applied to the structure morphism
`Spec k ⟶ S` of the field-valued point, which reads a morphism from the spectrum of a field as
a point of the target together with an embedding of its residue field. This is the shape in
which `AlgebraicGeometry.Space.isClosed_singleton_class_of_isAlgebraic_residueField` reads the
same hypotheses for Stacks 07U5. The finiteness hypothesis is finiteness of `k` as a module
over `κ(s)` for that embedding, and the rational-point hypothesis is that the embedding is an
isomorphism.

The closed-subspace clause of Stacks 03IQ needs effective descent for closed immersions along
the surjective étale morphisms of the site. That input is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, which is
proved outright, so no descent hypothesis survives into the statements below.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
* [Stacks Project, Tag 047Z](https://stacks.math.columbia.edu/tag/047Z)
* [Stacks Project, Tag 07U5](https://stacks.math.columbia.edu/tag/07U5)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 08AL](https://stacks.math.columbia.edu/tag/08AL)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Towers of fields -/

/-- Finiteness passes to the upper step of a tower of rings: if `L` is a finite `F`-module for
the composite map and the composite factors through `K`, then `L` is a finite `K`-module. -/
private theorem moduleFinite_of_comp_eq {F K L : Type u} [CommRing F] [CommRing K] [CommRing L]
    (e : F →+* K) (φ : K →+* L) (h : F →+* L) (hcomp : φ.comp e = h)
    (hfinite : letI := h.toAlgebra; Module.Finite F L) :
    letI := φ.toAlgebra
    Module.Finite K L := by
  let : Algebra F K := e.toAlgebra
  let : Algebra K L := φ.toAlgebra
  let : Algebra F L := h.toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Module.Finite F L := hfinite
  exact Module.Finite.of_restrictScalars_finite F K L

/-- The upper step of a tower of fields is an isomorphism as soon as the composite is: it is
injective because its source is a field, and surjective because the composite is. -/
private theorem isIso_of_isIso_comp {R : CommRingCat.{u}} {K L : Type u} [Field K] [Field L]
    (e : R ⟶ CommRingCat.of K) (φ : CommRingCat.of K ⟶ CommRingCat.of L)
    (h : IsIso (e ≫ φ)) : IsIso φ := by
  have hsurj : Function.Surjective φ.hom := by
    intro z
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (e ≫ φ)).2 z
    exact ⟨e.hom x, by simpa using hx⟩
  exact (ConcreteCategory.isIso_iff_bijective φ).2 ⟨RingHom.injective φ.hom, hsurj⟩

/-- A morphism of spectra is the spectrum of the ring map it determines. -/
private theorem spec_map_preimage_unop_eq {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) : Spec.map (Scheme.Spec.preimage f).unop = f := by
  simpa using Scheme.Spec.map_preimage f

/-- A morphism of spectra of fields over `S` factors the residue field embedding read off the
composite structure morphism: if `f ≫ b = g` with `f : Spec L ⟶ Spec K`, then the embedding
`κ(s) ⟶ L` determined by `g` is the embedding `κ(s) ⟶ K` determined by `b` followed by the ring
map presenting `f`, where `s` is the common image point. -/
private theorem exists_residueField_factor {K L : Type u} [Field K] [Field L] {S : Scheme.{u}}
    (f : Spec (.of L) ⟶ Spec (.of K)) (b : Spec (.of K) ⟶ S) (g : Spec (.of L) ⟶ S)
    (hbase : f ≫ b = g) :
    ∃ e : S.residueField (S.SpecToEquivOfField L g).1 ⟶ CommRingCat.of K,
      (S.SpecToEquivOfField L g).2 = e ≫ (Scheme.Spec.preimage f).unop := by
  classical
  let φ : CommRingCat.of K ⟶ CommRingCat.of L := (Scheme.Spec.preimage f).unop
  have hspec : Spec.map φ = f := spec_map_preimage_unop_eq f
  have hpt : (S.SpecToEquivOfField K b).1 = (S.SpecToEquivOfField L g).1 := by
    rw [Scheme.SpecToEquivOfField_apply_fst, Scheme.SpecToEquivOfField_apply_fst, ← hbase]
    exact congrArg b.base (Subsingleton.elim _ _)
  set e : S.residueField (S.SpecToEquivOfField L g).1 ⟶ CommRingCat.of K :=
    (S.residueFieldCongr hpt).inv ≫ (S.SpecToEquivOfField K b).2 with he
  refine ⟨e, ?_⟩
  have hb : Spec.map (S.SpecToEquivOfField K b).2 ≫
      S.fromSpecResidueField (S.SpecToEquivOfField K b).1 = b := by
    simpa only [Scheme.SpecToEquivOfField_symm_apply] using
      (Scheme.SpecToEquivOfField K S).symm_apply_apply b
  have hcongr : Spec.map (S.residueFieldCongr hpt).inv ≫
      S.fromSpecResidueField (S.SpecToEquivOfField L g).1 =
        S.fromSpecResidueField (S.SpecToEquivOfField K b).1 := by
    show Spec.map (S.residueFieldCongr hpt.symm).hom ≫ _ = _
    exact Scheme.residueFieldCongr_fromSpecResidueField hpt.symm
  have hfactor : Spec.map (e ≫ φ) ≫
      S.fromSpecResidueField (S.SpecToEquivOfField L g).1 = g := by
    simp only [he, Spec.map_comp, Category.assoc]
    rw [hcongr, hb, hspec, hbase]
  have hpair : (S.SpecToEquivOfField L g) =
      ⟨(S.SpecToEquivOfField L g).1, e ≫ φ⟩ := by
    have hfun : (Scheme.SpecToEquivOfField L S).symm
        ⟨(S.SpecToEquivOfField L g).1, e ≫ φ⟩ = g := by
      simpa only [Scheme.SpecToEquivOfField_symm_apply] using hfactor
    exact ((Scheme.SpecToEquivOfField L S).symm_apply_eq.mp hfun).symm
  obtain ⟨hfst, hsnd⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hpair
  have hfst' : hfst = rfl := Subsingleton.elim _ _
  rw [hfst'] at hsnd
  simpa using hsnd

/-! ### Finiteness of a representable morphism of algebraic spaces -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site whose underlying morphism of schemes is finite induces a
finite morphism of algebraic spaces. -/
private theorem isFinite_yoneda_map {M N : BigFppfOver B S hS} (q : M ⟶ N)
    (hq : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q)) :
    IsFinite B S hS (yoneda.map q) := by
  intro U hU ξ
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let g : U ⟶ N := yoneda.preimage ξ
  have hξ : yoneda.map g = ξ := yoneda.map_preimage ξ
  have hpbSite : IsPullback (pullback.fst g q) (pullback.snd g q) g q :=
    IsPullback.of_hasPullback g q
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hpbScheme : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst g q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd g q))
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map q) :=
    hpbSite.map (BigFppfOver.toScheme B S hS)
  have hfst : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (pullback.fst g q)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbScheme.flip hq
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback g q)) := by
    have _ : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (pullback.fst g q)) := hfst.toIsAffineHom
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    exact _root_.AlgebraicGeometry.isAffine_of_isAffineHom
      ((BigFppfOver.toScheme B S hS).map (pullback.fst g q))
  exact ⟨pullback g q, pullback.fst g q, yoneda.map (pullback.snd g q), hVaff, hfst, by
    simpa only [hξ] using (hpbSite.map yoneda).flip⟩

/-! ### The reduced closed point subspace of a field-valued point -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The factorisation of a field-valued point through the reduced closed subspace supported on
its image, together with the presentation of that subspace by the spectrum of a field.

This is the common core of the two halves of Stacks 08AL: the point factors as
`Spec k ⟶ Z ⟶ X` with `Z ⟶ X` a closed immersion, the subspace `Z` is presented by `Spec K`
for a field `K`, and the resulting morphism `f : Spec k ⟶ Spec K` of field spectra over `S`
transfers finiteness and invertibility to `Spec k ⟶ Z`. -/
private theorem exists_closedSubspace_fieldFactor (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hclosed : IsClosed ({p.class B S hS X} : Set (points B S hS X))) :
    ∃ (Z : Subfunctor X) (g : yoneda.obj p.siteObject ⟶ Z.toFunctor) (K : Type u) (_ : Field K)
      (b : Spec (.of K) ⟶ S) (f : Spec (.of p.carrier) ⟶ Spec (.of K)),
      IsClosedSubspace B S hS Z ∧ g ≫ Z.ι = fieldMorphism B S hS X p ∧ f ≫ b = p.toBase ∧
        (_root_.AlgebraicGeometry.IsFinite f → IsFinite B S hS g) ∧ (IsIso f → IsIso g) := by
  classical
  have hcarrier : Subsingleton
      ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS X)) := by
    show Subsingleton (Spec (.of p.carrier))
    infer_instance
  -- the reduced closed subspace supported on the image point
  let Z : Subfunctor X := reducedClosedSubspace B S hS X hX {p.class B S hS X} hclosed
  have hZci : IsClosedSubspace B S hS Z :=
    isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X hX _ hclosed
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
  have hZrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = {p.class B S hS X} :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ hclosed
  have hZred : HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} ↦ IsReduced Y) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ hclosed
  -- the point factors through it, its source being reduced with image in `|Z|`
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hTred : HasEtaleLocalProperty B S hS (yoneda.obj p.siteObject)
      (fun V : Scheme.{u} ↦ IsReduced V) := by
    refine (exists_atlas_iff_of_representable B S hS (yoneda.obj p.siteObject)
      (fun V : Scheme.{u} ↦ IsReduced V) p.siteObject (Iso.refl _)).mpr ?_
    show IsReduced (Spec (.of p.carrier))
    infer_instance
  have hrange : Set.range (pointsMap B S hS (yoneda.obj p.siteObject)
      (fieldMorphism B S hS X p)) ⊆ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rw [hZrange]
    rintro _ ⟨y, rfl⟩
    have hsub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
      (schemePointsHomeomorph B S hS p.siteObject).toEquiv.subsingleton
    rw [Set.mem_singleton_iff,
      Subsingleton.elim y ((p.tautologicalPoint B S hS X).class B S hS
        (yoneda.obj p.siteObject))]
    exact pointsMap_fieldMorphism_tautologicalPoint B S hS X p
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX hTalg Z
    hZci hTred (fieldMorphism B S hS X p)).mpr hrange
  -- the subspace is decent with exactly one point, hence the spectrum of a field
  have hZdec : IsDecentSpace B S hS Z.toFunctor :=
    isDecentSpace_of_relativelyRepresentable B S hS hZci.1 Z.ι hZci.2.1 hdec
  have hmono : Mono Z.ι := mono_of_isClosedImmersion B S hS Z.ι hZci.2
  have hinj := pointsMap_injective_of_mono B S hS Z.ι
  have hzne : Nonempty (points B S hS Z.toFunctor) := by
    have hmem : p.class B S hS X ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
      rw [hZrange]
      exact Set.mem_singleton _
    exact ⟨hmem.choose⟩
  have hzsub : Subsingleton (points B S hS Z.toFunctor) := by
    refine ⟨fun y y' ↦ hinj ?_⟩
    have h1 := Set.mem_range_self (f := pointsMap B S hS Z.toFunctor Z.ι) y
    have h2 := Set.mem_range_self (f := pointsMap B S hS Z.toFunctor Z.ι) y'
    rw [hZrange, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  obtain ⟨M, K, hK, ⟨ε⟩, ⟨e⟩⟩ := exists_iso_yoneda_spec_of_subsingleton_points B S hS hZci.1
    hZdec hzne hzsub hZred
  -- the induced morphism of field spectra
  let q : p.siteObject ⟶ M := yoneda.preimage (g ≫ e.hom)
  have hq : yoneda.map q = g ≫ e.hom := yoneda.map_preimage _
  have hgq : yoneda.map q ≫ e.inv = g := by
    rw [hq, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hfq : (BigFppfOver.toScheme B S hS).map q =
      ((BigFppfOver.toScheme B S hS).map q ≫ ε.hom) ≫ ε.inv := by
    simp
  refine ⟨Z, g, K, hK, ε.inv ≫ B.inclusion.map M.hom,
    (BigFppfOver.toScheme B S hS).map q ≫ ε.hom, hZci, hg, ?_, ?_, ?_⟩
  · calc ((BigFppfOver.toScheme B S hS).map q ≫ ε.hom) ≫ ε.inv ≫ B.inclusion.map M.hom
        = (BigFppfOver.toScheme B S hS).map q ≫ B.inclusion.map M.hom := by simp
      _ = p.toBase := congrArg B.inclusion.map q.w
  · intro hf
    have _hri : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hqf : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q) := by
      rw [hfq]
      exact (MorphismProperty.cancel_right_of_respectsIso
        (@_root_.AlgebraicGeometry.IsFinite.{u}) _ ε.inv).mpr hf
    rw [← hgq]
    exact isFinite_comp B S hS (isFinite_yoneda_map B S hS q hqf)
      (isFinite_of_isClosedImmersion B S hS e.inv (isClosedImmersion_of_isIso B S hS e.inv))
  · intro hf
    have : IsIso ((BigFppfOver.toScheme B S hS).map q) := IsIso.of_isIso_comp_right _ ε.hom
    have : IsIso q := isIso_of_reflects_iso q (BigFppfOver.toScheme B S hS)
    rw [← hgq]
    infer_instance

/-! ### Stacks 08AL -/

/-- The image of a field-valued point is closed in `|X|` when `X` is decent, the image point in
`S` is closed and the residue field extension is finite. -/
private theorem isClosed_singleton_class_of_moduleFinite (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hs : IsClosed ({(S.SpecToEquivOfField p.carrier p.toBase).1} : Set S))
    (hfin : letI := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      Module.Finite (S.residueField (S.SpecToEquivOfField p.carrier p.toBase).1) p.carrier) :
    IsClosed ({p.class B S hS X} : Set (points B S hS X)) :=
  isClosed_singleton_class_of_isAlgebraic_residueField B S hS hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) p hs (by
      let := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      have := hfin
      exact Algebra.IsAlgebraic.of_finite _ _)

/-- **Stacks 08AL, the finite case.** Let `X` be a decent algebraic space over a scheme `S` and
let `p` be a field-valued point of `X` with field of definition `k`, so a commutative diagram
`Spec k ⟶ X ⟶ S`. If the image point `s` of `Spec k ⟶ S` is a closed point of `S` and `k` is
finite over the residue field `κ(s)`, then `Spec k ⟶ X` is a finite morphism. -/
@[stacks 08AL "finite morphism"]
theorem isFinite_fieldMorphism_of_moduleFinite_residueField (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hs : IsClosed ({(S.SpecToEquivOfField p.carrier p.toBase).1} : Set S))
    (hfin : letI := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      Module.Finite (S.residueField (S.SpecToEquivOfField p.carrier p.toBase).1) p.carrier) :
    IsFinite B S hS (fieldMorphism B S hS X p) := by
  have hclosed : IsClosed ({p.class B S hS X} : Set (points B S hS X)) :=
    isClosed_singleton_class_of_moduleFinite B S hS hX hdec p hs hfin
  obtain ⟨Z, g, K, hK, b, f, hZci, hg, hfb, hfinite, -⟩ :=
    exists_closedSubspace_fieldFactor B S hS hX hdec p hclosed
  obtain ⟨e, he⟩ := exists_residueField_factor f b p.toBase hfb
  have hmod : let := ((Scheme.Spec.preimage f).unop).hom.toAlgebra
      Module.Finite K p.carrier :=
    moduleFinite_of_comp_eq e.hom ((Scheme.Spec.preimage f).unop).hom
      (S.SpecToEquivOfField p.carrier p.toBase).2.hom (by rw [he]; rfl) hfin
  have hff : _root_.AlgebraicGeometry.IsFinite f := by
    let : Algebra K p.carrier := ((Scheme.Spec.preimage f).unop).hom.toAlgebra
    rw [← spec_map_preimage_unop_eq f, _root_.AlgebraicGeometry.IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hmod
  rw [← hg]
  exact isFinite_comp B S hS (hfinite hff) (isFinite_of_isClosedImmersion B S hS Z.ι hZci.2)

/-- **Stacks 08AL, the closed-immersion case.** Let `X` be a decent algebraic space over a
scheme `S` and let `p` be a field-valued point of `X` with field of definition `k`, so a
commutative diagram `Spec k ⟶ X ⟶ S`. If the image point `s` of `Spec k ⟶ S` is a closed point
of `S` and the residue field embedding `κ(s) ⟶ k` is an isomorphism, then `Spec k ⟶ X` is a
closed immersion. -/
@[stacks 08AL "closed immersion"]
theorem isClosedImmersion_fieldMorphism_of_isIso_residueField (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hs : IsClosed ({(S.SpecToEquivOfField p.carrier p.toBase).1} : Set S))
    (hrat : IsIso (S.SpecToEquivOfField p.carrier p.toBase).2) :
    IsClosedImmersion B S hS (fieldMorphism B S hS X p) := by
  have hclosed : IsClosed ({p.class B S hS X} : Set (points B S hS X)) :=
    isClosed_singleton_class_of_moduleFinite B S hS hX hdec p hs (by
      let := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      exact Module.Finite.of_surjective
        (Algebra.linearMap (S.residueField (S.SpecToEquivOfField p.carrier p.toBase).1)
          p.carrier)
        (ConcreteCategory.bijective_of_isIso (S.SpecToEquivOfField p.carrier p.toBase).2).2)
  obtain ⟨Z, g, K, hK, b, f, hZci, hg, hfb, -, hiso⟩ :=
    exists_closedSubspace_fieldFactor B S hS hX hdec p hclosed
  obtain ⟨e, he⟩ := exists_residueField_factor f b p.toBase hfb
  have hφ : IsIso ((Scheme.Spec.preimage f).unop) :=
    isIso_of_isIso_comp e _ (by rw [← he]; exact hrat)
  have hfiso : IsIso f := by rw [← spec_map_preimage_unop_eq f]; infer_instance
  have : IsIso g := hiso hfiso
  rw [← hg]
  exact isClosedImmersion_comp B S hS g Z.ι (isClosedImmersion_of_isIso B S hS g) hZci.2

end AlgebraicGeometry.Space

end
