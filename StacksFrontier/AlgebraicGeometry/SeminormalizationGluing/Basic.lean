module

public import StacksFrontier.AlgebraicGeometry.Scheme.AffineZariskiRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksFrontier.AlgebraicGeometry.SeminormalizationIsoIff.Basic
public import StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# The seminormalization of an arbitrary scheme

For a scheme `X`, the *subintegral* morphisms to `X` -- those which are universal
homeomorphisms and induce isomorphisms on all residue fields -- form a category
`AlgebraicGeometry.SeminormalizationCategory X`.  This file constructs its initial object, the
seminormalization of `X`, for an arbitrary `X`, and shows that the object so constructed is a
seminormal scheme.  Those two facts are the whole of Tag 0EUS for seminormalization.

## Main results

* `AlgebraicGeometry.hasInitial_seminormalizationCategory`: the seminormalization category of an
  arbitrary scheme has an initial object.
* `AlgebraicGeometry.isSeminormal_initial_seminormalizationCategory`: the chosen initial object
  is a seminormal scheme.
* `AlgebraicGeometry.isIso_initialTo_iff_isSeminormal`: the canonical morphism from the
  seminormalization of `X` to a subintegral `Y ⟶ X` is an isomorphism exactly when `Y` is
  seminormal.

## Implementation notes

The construction is affine-local on `X` and glued, exactly as
`StacksDraft.AlgebraicGeometry.F3.AbsoluteWeakNormalizationInitial` does for the absolute weak
normalization.  On an affine open `U` the candidate is the spectrum of the ring-level
seminormalization of `Γ(X, U)`; its functoriality
(`AlgebraicGeometry.existsUnique_seminormalizationMap`) makes these fit together into a diagram
over the small affine Zariski site of `X`, and the base-change statement
`AlgebraicGeometry.exists_seminormalization_tensorProduct_equiv` supplies the coequifiberedness
that `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` requires.

Two things must be checked about the glued morphism `toBase` rather than one, because the
objects of this category carry a second condition that the absolute weak normalization's do
not.  Being a universal homeomorphism is Zariski-local at the target, as in the absolute case.
Inducing isomorphisms on residue fields is handled on the *source* instead: every point of the
glued scheme lies in the image of one chart, the chart inclusion is an open immersion and
therefore induces isomorphisms on residue fields, and composing the chart inclusion with
`toBase` gives the chart's own structure morphism followed by an open immersion.  So the
condition at a point is read off from the chart containing it -- see
`AlgebraicGeometry.isIso_residueFieldMap_of_comp_isOpenImmersion`.

Initiality is uniqueness of a map into an arbitrary subintegral `Z ⟶ X`, proved chart by chart:
over an affine open the target is affine, so the map is the ring-level terminal map of Tag 0EUR,
whose universal property also gives its uniqueness.  The local target is a subintegral algebra
because both of its conditions are stable under base change -- the residue-field half being
`AlgebraicGeometry.pullback_snd_residueFieldMap_isIso`.

Seminormality of the glued object needs no further geometry: it is affine-local by Tag 0EUP and
each chart is the spectrum of a ring-level seminormalization, which is a seminormal ring by
`AlgebraicGeometry.isSeminormalRing_seminormalization`.  This is why the equivalence of Tag 0EUS
falls out here and not in
`StacksDraft.AlgebraicGeometry.F3.SeminormalizationIsoIff`: that file could only carry the
seminormality of the initial object as a hypothesis, because the initial object was supplied to
it as an opaque instance and nothing was known about its charts.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: `X` is an arbitrary scheme, with no Noetherian,
reducedness, separatedness or finiteness assumption, and `Y` an arbitrary object of the
seminormalization category.

## References

* [Stacks Project, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-! ### Residue fields along a composite -/

/-- A composite of morphisms inducing isomorphisms on residue fields induces isomorphisms on
residue fields.

`AlgebraicGeometry.isIso_residueFieldMap_comp` is the same conclusion from the weaker
hypothesis that the two factors induce isomorphisms at the single point in question; this is
the form in which the hypotheses are available below, where they hold at every point. -/
theorem isIso_residueFieldMap_comp_of_forall {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ x : X, IsIso (f.residueFieldMap x))
    (hg : ∀ y : Y, IsIso (g.residueFieldMap y)) (x : X) :
    IsIso ((f ≫ g).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (hg (f x)) (hf x)

/-- An open immersion induces isomorphisms on all residue fields.  This names Mathlib's
anonymous instance so that it can be applied where the open-immersion hypothesis is a term
rather than an instance in scope. -/
theorem isIso_residueFieldMap_of_isOpenImmersion {V Y : Scheme.{u}} (j : V ⟶ Y)
    (hj : IsOpenImmersion j) (v : V) : IsIso (j.residueFieldMap v) :=
  have _ : IsOpenImmersion j := hj
  inferInstance

/-- Inducing an isomorphism on the residue field at a point in the image of an open immersion is
detected after precomposition with that open immersion: the open immersion's own residue field
maps are isomorphisms, so they cancel. -/
theorem isIso_residueFieldMap_of_comp_isOpenImmersion {V Y Z : Scheme.{u}} (j : V ⟶ Y)
    (hj : IsOpenImmersion j) (f : Y ⟶ Z) (v : V)
    (h : IsIso ((j ≫ f).residueFieldMap v)) : IsIso (f.residueFieldMap (j v)) := by
  rw [Scheme.residueFieldMap_comp] at h
  have hji : IsIso (j.residueFieldMap v) := isIso_residueFieldMap_of_isOpenImmersion j hj v
  have hcomp : IsIso (f.residueFieldMap (j v) ≫ j.residueFieldMap v) := h
  exact IsIso.of_isIso_comp_right (f.residueFieldMap (j v)) (j.residueFieldMap v)

section Proof

open MorphismProperty
open TopologicalSpace
open Scheme.AffineZariskiSite

open Algebra
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The affine-local diagram of seminormalizations -/

private noncomputable def snAffineDiagram (X : Scheme.{u}) :
    X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (Algebra.seminormalization Γ(X, U.unop.1))
  map {V U} i := CommRingCat.ofHom (seminormalizationMap (restrictionRingMap X i.unop))
  map_id U := by
    apply CommRingCat.hom_ext
    change seminormalizationMap (restrictionRingMap X (𝟙 (Opposite.unop U))) = _
    rw [restrictionRingMap_id, seminormalizationMap_id]
    simp
  map_comp i j := by
    apply CommRingCat.hom_ext
    change seminormalizationMap (restrictionRingMap X ((i ≫ j).unop)) =
      (seminormalizationMap (restrictionRingMap X j.unop)).comp
        (seminormalizationMap (restrictionRingMap X i.unop))
    rw [show (i ≫ j).unop = j.unop ≫ i.unop by rfl,
      restrictionRingMap_comp, ← seminormalizationMap_comp]

private noncomputable def snAffineDiagramMap (X : Scheme.{u}) :
    (toOpensFunctor X).op ⋙ X.presheaf ⟶ snAffineDiagram X where
  app U := CommRingCat.ofHom
    (algebraMap Γ(X, U.unop.1) (Algebra.seminormalization Γ(X, U.unop.1)))
  naturality {U V} i := by
    apply CommRingCat.hom_ext
    exact (seminormalizationMap_spec (restrictionRingMap X i.unop)).symm

private theorem snAffineDiagramMap_coequifibered (X : Scheme.{u}) :
    (snAffineDiagramMap X).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let A := Γ(X, U.1)
  let B := Γ(X, X.basicOpen r)
  let N := Algebra.seminormalization A
  let N' := Algebra.seminormalization B
  let _ : Algebra A B := Scheme.algebra_section_section_basicOpen r
  let φ : A →+* B := algebraMap A B
  let φ' : A →+* B := restrictionRingMap X (homOfLE (U.basicOpen_le r))
  have hφ : φ = φ' := by
    ext x
    rfl
  let _ : IsLocalization.Away r B := U.2.isLocalization_basicOpen r
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    IsOpenImmersion.of_isLocalization r
  let _ : Algebra A N := inferInstance
  let haux := exists_seminormalization_tensorProduct_equiv A B
  let e : (B ⊗[A] N) ≃+* N' := Classical.choose haux
  have he :
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := N)).toRingHom)) = seminormalizationMap φ :=
    ((Classical.choose_spec haux).1).2
  have he' :
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := N)).toRingHom)) = seminormalizationMap φ' := by
    rw [he, hφ]
  let _ : Algebra N N' :=
    ((snAffineDiagram X).map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  let eAlg : (B ⊗[A] N) ≃ₐ[N] N' := AlgEquiv.ofRingEquiv (R := N) (f := e)
    fun n => congrArg (fun f : N →+* N' => f n) he'
  let _ : IsLocalization.Away (algebraMap A N (r : A)) (B ⊗[A] N) := inferInstance
  show IsLocalization.Away (algebraMap A N (r : A)) N'
  exact IsLocalization.isLocalization_of_algEquiv _ eAlg

private noncomputable def snRelativeGluingData (X : Scheme.{u}) :=
  Scheme.AffineZariskiSite.relativeGluingData (snAffineDiagramMap_coequifibered X)

private instance snRelativeGluingData_isLocallyDirected (X : Scheme.{u}) :
    ((snRelativeGluingData X).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-! ### The glued morphism is subintegral -/

private theorem snRelativeGluingData_local_universalHomeomorphism
    (X : Scheme.{u}) (U : X.AffineZariskiSite) :
    UniversalHomeomorphism ((snRelativeGluingData X).natTrans.app U) := by
  constructor
  show (topologically @IsHomeomorph).universally
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (Algebra.seminormalization Γ(X, U.1)))) ≫ U.2.isoSpec.inv)
  rw [MorphismProperty.cancel_right_of_respectsIso
    (P := (topologically @IsHomeomorph).universally) _ U.2.isoSpec.inv]
  exact (seminormalization_universalHomeomorphism Γ(X, U.1)).universally_isHomeomorph

private theorem snRelativeGluingData_local_residueFieldIsomorphisms
    (X : Scheme.{u}) (U : X.AffineZariskiSite)
    (z : (snRelativeGluingData X).functor.obj U) :
    IsIso (((snRelativeGluingData X).natTrans.app U).residueFieldMap z) := by
  show IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (Algebra.seminormalization Γ(X, U.1)))) ≫
        U.2.isoSpec.inv).residueFieldMap z)
  refine isIso_residueFieldMap_comp_of_forall _ _ ?_ (fun _ => inferInstance) z
  exact seminormalization_inducesResidueFieldIsomorphisms Γ(X, U.1)

private theorem snRelativeGluingData_toBase_universalHomeomorphism (X : Scheme.{u}) :
    UniversalHomeomorphism (snRelativeGluingData X).toBase := by
  constructor
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (topologically @IsHomeomorph).universally)
    (Scheme.AffineZariskiSite.directedCover X)]
  intro U
  have hPB := (snRelativeGluingData X).isPullback_natTrans_ι_toBase U
  let _ : HasPullback (snRelativeGluingData X).toBase
      ((Scheme.AffineZariskiSite.directedCover X).f U) := hPB.flip.hasPullback
  rw [Scheme.Cover.pullbackHom]
  let e : CategoryTheory.Arrow.mk (pullback.snd (snRelativeGluingData X).toBase
        ((Scheme.AffineZariskiSite.directedCover X).f U)) ≅
    CategoryTheory.Arrow.mk ((snRelativeGluingData X).natTrans.app U) :=
    CategoryTheory.Arrow.isoMk hPB.flip.isoPullback.symm (Iso.refl _)
      (hPB.flip.isoPullback_inv_snd.trans (Category.comp_id _).symm)
  exact (MorphismProperty.arrow_iso_iff _ e).2
    (snRelativeGluingData_local_universalHomeomorphism X U).universally_isHomeomorph

/-- Every point of the glued scheme lies in one chart, so the residue-field condition on
`toBase` is read off from that chart's own structure morphism. -/
private theorem snRelativeGluingData_toBase_residueFieldIsomorphisms (X : Scheme.{u}) :
    ∀ t : (snRelativeGluingData X).glued,
      IsIso ((snRelativeGluingData X).toBase.residueFieldMap t) := by
  classical
  intro t
  let d := snRelativeGluingData X
  let i := d.cover.idx t
  obtain ⟨y, hy⟩ := d.cover.covers t
  have hres : IsIso ((colimit.ι d.functor i ≫ d.toBase).residueFieldMap y) := by
    rw [d.ι_toBase i]
    exact isIso_residueFieldMap_comp_of_forall _ _
      (snRelativeGluingData_local_residueFieldIsomorphisms X i)
      (isIso_residueFieldMap_of_isOpenImmersion _
        ((Scheme.AffineZariskiSite.directedCover X).map_prop i)) y
  have hpt : colimit.ι d.functor i y = t := hy
  have hgoal : IsIso (d.toBase.residueFieldMap (colimit.ι d.functor i y)) :=
    isIso_residueFieldMap_of_comp_isOpenImmersion (colimit.ι d.functor i) (d.cover.map_prop i)
      d.toBase y hres
  rwa [hpt] at hgoal

private noncomputable def snSchemeOver (X : Scheme.{u}) : Over X :=
  Over.mk (snRelativeGluingData X).toBase

private theorem snSchemeOver_property (X : Scheme.{u}) :
    IsSeminormalizationCandidate X (snSchemeOver X) :=
  ⟨snRelativeGluingData_toBase_universalHomeomorphism X,
    snRelativeGluingData_toBase_residueFieldIsomorphisms X⟩

/-! ### The ring-level terminal map -/

private noncomputable def snCandidateMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsSeminormalizationCandidateAlgebra A (CommAlgCat.of A B)) :
    B →+* Algebra.seminormalization A :=
  (((seminormalizationAlgebraObject_isTerminal A).from
    ⟨CommAlgCat.of A B, hB⟩).hom.hom).toRingHom

private theorem snCandidateMap_comp (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsSeminormalizationCandidateAlgebra A (CommAlgCat.of A B)) :
    (snCandidateMap A B hB).comp (algebraMap A B) =
      algebraMap A (Algebra.seminormalization A) := by
  let f := (seminormalizationAlgebraObject_isTerminal A).from
    (⟨CommAlgCat.of A B, hB⟩ : SeminormalizationAlgebraCategory A)
  show (f.hom.hom.toRingHom).comp (algebraMap A B) =
    algebraMap A (Algebra.seminormalization A)
  ext a
  exact f.hom.hom.commutes a

private theorem snCandidateMap_unique (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsSeminormalizationCandidateAlgebra A (CommAlgCat.of A B))
    (ψ : B →+* Algebra.seminormalization A)
    (hψ : ψ.comp (algebraMap A B) = algebraMap A (Algebra.seminormalization A)) :
    ψ = snCandidateMap A B hB := by
  let C₀ : CommAlgCat A := CommAlgCat.of A B
  let C : SeminormalizationAlgebraCategory A := ⟨C₀, hB⟩
  let t := seminormalizationAlgebraObject_isTerminal A
  let Nobj := seminormalizationAlgebraObject A
  let eψ : B →ₐ[A] Algebra.seminormalization A :=
    { toRingHom := ψ
      commutes' := fun a => by
        have h := congrArg (fun k : A →+* Algebra.seminormalization A => k a) hψ
        show ψ (algebraMap A B a) = algebraMap A (Algebra.seminormalization A) a
        exact h }
  let g : C ⟶ Nobj := ObjectProperty.homMk (CommAlgCat.ofHom eψ)
  have heq := t.hom_ext g (t.from C)
  show ψ = snCandidateMap A B hB
  ext b
  have hb := congrArg (fun q => q.hom.hom b) heq
  show ψ b = (t.from C).hom.hom b
  exact hb

/-! ### Initiality -/

/-- On an affine open `U`, the ring map `Γ(U, ⊤) → Γ(Z, ⊤)` of an affine base change
`Z → U` corresponds to the composite `Spec Γ(Z, ⊤) ≅ Z → U → Spec Γ(U, ⊤)`. -/
private theorem spec_map_snd_appTop_comp_topIso_inv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.AffineZariskiSite) [IsAffine (pullback f U.1.ι)] :
    Spec.map (CommRingCat.ofHom
      ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)) =
      (pullback f U.1.ι).isoSpec.inv ≫ pullback.snd f U.1.ι ≫ U.1.toSpecΓ := by
  let _ : IsAffine U.1.toScheme := U.2
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hnat : Spec.map ((pullback.snd f U.1.ι).appTop) ≫ U.1.toScheme.isoSpec.inv =
      (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) :=
    Scheme.isoSpec_inv_naturality (pullback.snd f U.1.ι)
  calc
    _ = (Spec.map ((pullback.snd f U.1.ι).appTop) ≫ U.1.toScheme.isoSpec.inv) ≫
          U.1.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom U.1.topIso.inv.hom) := by
      simp
      rfl
    _ = ((pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι)) ≫
          U.1.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom U.1.topIso.inv.hom) := by
      rw [hnat]
    _ = (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ := by
      exact congrArg (fun g => (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ g)
        U.2.isoSpec_hom

private theorem snLocalTarget_candidate {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) (U : X.AffineZariskiSite)
    (φ : Γ(X, U.1) →+* Γ(pullback f U.1.ι, ⊤))
    [Algebra Γ(X, U.1) Γ(pullback f U.1.ι, ⊤)]
    (hφ : algebraMap Γ(X, U.1) Γ(pullback f U.1.ι, ⊤) = φ)
    (hφ' : φ = (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom) :
    IsSeminormalizationCandidateAlgebra (Γ(X, U.1))
      (CommAlgCat.of (Γ(X, U.1)) (Γ(pullback f U.1.ι, ⊤))) := by
  have hfU : UniversalHomeomorphism f := hf.1
  have hfres : ∀ y : Y, IsIso (f.residueFieldMap y) := hf.2
  let Z := pullback f U.1.ι
  let _ : IsAffineHom f := hf.isAffineHom
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsAffine Z := inferInstance
  have hlocal : (topologically @IsHomeomorph).universally (pullback.snd f U.1.ι) :=
    MorphismProperty.pullback_snd f U.1.ι hfU.universally_isHomeomorph
  have hspecEq : Spec.map (CommRingCat.ofHom φ) =
      Z.isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ := by
    rw [hφ']
    exact spec_map_snd_appTop_comp_topIso_inv f U
  have hright : IsIso U.1.toSpecΓ := by
    dsimp [Scheme.Opens.toSpecΓ]
    infer_instance
  refine ⟨?_, ?_⟩
  · constructor
    show (topologically @IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    rw [hφ, hspecEq]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (topologically @IsHomeomorph).universally) Z.isoSpec.inv _).mpr
        ((MorphismProperty.cancel_right_of_respectsIso
          (P := (topologically @IsHomeomorph).universally) (pullback.snd f U.1.ι)
            U.1.toSpecΓ).mpr hlocal)
  · intro z
    show IsIso ((Spec.map (CommRingCat.ofHom (algebraMap _ _))).residueFieldMap z)
    rw [hφ, hspecEq]
    refine isIso_residueFieldMap_comp_of_forall _ _ (fun _ => inferInstance) ?_ z
    intro w
    refine isIso_residueFieldMap_comp_of_forall _ _ ?_ (fun _ => inferInstance) w
    exact fun v => pullback_snd_residueFieldMap_isIso f U.1.ι v
      (hfres (pullback.fst f U.1.ι v))

private noncomputable def snLocalMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) (U : X.AffineZariskiSite) :
    (snRelativeGluingData X).functor.obj U ⟶ pullback f U.1.ι := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let Z := pullback f U.1.ι
  let _ : IsAffineHom f := hf.isAffineHom
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let _ : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := snLocalTarget_candidate f hf U φ hφ rfl
  let ψ := snCandidateMap A B hB
  change Spec (CommRingCat.of (Algebra.seminormalization A)) ⟶ Z
  exact Spec.map (CommRingCat.ofHom ψ) ≫ (pullback f U.1.ι).isoSpec.inv

private theorem snLocalMap_snd {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) (U : X.AffineZariskiSite) :
    snLocalMap f hf U ≫ pullback.snd f U.1.ι =
      (snRelativeGluingData X).natTrans.app U := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let Z := pullback f U.1.ι
  let _ : IsAffineHom f := hf.isAffineHom
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let _ : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := snLocalTarget_candidate f hf U φ hφ rfl
  let ψ := snCandidateMap A B hB
  have hψ := snCandidateMap_comp A B hB
  have hspec : Spec.map (CommRingCat.ofHom φ) =
      Z.isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ :=
    spec_map_snd_appTop_comp_topIso_inv f U
  show Spec.map (CommRingCat.ofHom ψ) ≫ Z.isoSpec.inv ≫ (pullback.snd f U.1.ι) =
    Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A))) ≫
      U.2.isoSpec.inv
  refine (cancel_mono U.2.isoSpec.hom).mp ?_
  calc
    _ = Spec.map (CommRingCat.ofHom ψ) ≫
          (Z.isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ) := by
            simp [Category.assoc, U.2.isoSpec_hom]
    _ = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
          rw [← hspec]
    _ = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
          rw [← Spec.map_comp]
          congr 1
    _ = Spec.map
          (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A))) := by
          congr 1
          apply CommRingCat.hom_ext
          show ψ.comp φ = algebraMap A (Algebra.seminormalization A)
          rw [← hφ]
          exact hψ
    _ = (Spec.map
          (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A))) ≫
            U.2.isoSpec.inv) ≫ U.2.isoSpec.hom := by simp [Category.assoc]

private theorem snLocalMap_unique {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) (U : X.AffineZariskiSite)
    (g : (snRelativeGluingData X).functor.obj U ⟶ pullback f U.1.ι)
    (hg : g ≫ pullback.snd f U.1.ι = (snRelativeGluingData X).natTrans.app U) :
    g = snLocalMap f hf U := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let N := Algebra.seminormalization A
  let Z := pullback f U.1.ι
  change Spec (CommRingCat.of N) ⟶ Z at g
  change g ≫ pullback.snd f U.1.ι =
    Spec.map (CommRingCat.ofHom (algebraMap A N)) ≫ U.2.isoSpec.inv at hg
  let _ : IsAffineHom f := hf.isAffineHom
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let _ : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := snLocalTarget_candidate f hf U φ hφ rfl
  let θ := Scheme.ΓSpecIso (CommRingCat.of N)
  let ψ : B →+* N := θ.hom.hom.comp g.appTop.hom
  have hnat : (snRelativeGluingData X).natTrans.app U =
      Spec.map (CommRingCat.ofHom (algebraMap A N)) ≫ U.2.isoSpec.inv := rfl
  have htop := congrArg (fun k => k.appTop) hg
  have hcompRaw := congrArg
    (fun k : CommRingCat.Hom _ _ => (k ≫ θ.hom).hom.comp U.1.topIso.inv.hom) htop
  have hcomp : θ.hom.hom.comp
      (g.appTop.hom.comp ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)) =
      θ.hom.hom.comp
        (((snRelativeGluingData X).natTrans.app U).appTop.hom.comp U.1.topIso.inv.hom) := by
    rw [Scheme.Hom.comp_appTop] at hcompRaw
    change _ = _ at hcompRaw
    exact hcompRaw
  have hnatRing : θ.hom.hom.comp
      (((snRelativeGluingData X).natTrans.app U).appTop.hom.comp U.1.topIso.inv.hom) =
      θ.hom.hom.comp
      ((Spec.map (CommRingCat.ofHom (algebraMap A N))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    have hcancel : U.1.topIso.inv ≫ U.2.isoSpec.inv.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
      rw [U.2.isoSpec_inv_appTop]
      rw [← Category.assoc, U.1.topIso.inv_hom_id, Category.id_comp]
      rfl
    have hcancelRing : U.2.isoSpec.inv.appTop.hom.comp U.1.topIso.inv.hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
      congrArg CommRingCat.Hom.hom hcancel
    rw [hnat]
    show θ.hom.hom.comp
      ((Spec.map (CommRingCat.ofHom (algebraMap A N))).appTop.hom.comp
        (U.2.isoSpec.inv.appTop.hom.comp U.1.topIso.inv.hom)) = _
    rw [hcancelRing]
  have hGammaSpec := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A N))
  have hGammaSpecRing : θ.hom.hom.comp
      ((Spec.map (CommRingCat.ofHom (algebraMap A N))).appTop.hom) =
      (algebraMap A N).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
    congrArg CommRingCat.Hom.hom hGammaSpec
  have hGammaSpec_map : θ.hom.hom.comp
      ((Spec.map (CommRingCat.ofHom (algebraMap A N))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = algebraMap A N := by
    calc
      _ = ((algebraMap A N).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
        simpa [RingHom.comp_assoc] using congrArg
          (fun q : Γ(Spec (CommRingCat.of A), ⊤) →+* N =>
            q.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) hGammaSpecRing
      _ = algebraMap A N := by
        have hIso : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id _ :=
          congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
        rw [RingHom.comp_assoc, hIso, RingHom.comp_id]
  have hψ : ψ.comp φ = algebraMap A N := by
    show θ.hom.hom.comp (g.appTop.hom.comp
      ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)) = _
    exact hcomp.trans (hnatRing.trans hGammaSpec_map)
  have hψeq := snCandidateMap_unique A B hB ψ hψ
  have hmaps : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (snCandidateMap A B hB)) := by
    congr 1
    apply CommRingCat.hom_ext
    exact hψeq
  show g = Spec.map (CommRingCat.ofHom (snCandidateMap A B hB)) ≫ Z.isoSpec.inv
  apply (cancel_mono Z.isoSpec.hom).mp
  calc
    g ≫ Z.isoSpec.hom = Spec.map (CommRingCat.ofHom ψ) := by
      rw [← Scheme.isoSpec_hom_naturality]
      simp [ψ, θ, SpecMap_ΓSpecIso_hom]
    _ = Spec.map (CommRingCat.ofHom (snCandidateMap A B hB)) := hmaps
    _ = (Spec.map (CommRingCat.ofHom (snCandidateMap A B hB)) ≫ Z.isoSpec.inv) ≫
          Z.isoSpec.hom := by simp

private noncomputable def snLocalLift {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) (U : X.AffineZariskiSite) :
    (snRelativeGluingData X).functor.obj U ⟶ Y :=
  snLocalMap f hf U ≫ pullback.fst f U.1.ι

private theorem snLocalLift_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) {U V : X.AffineZariskiSite}
    (i : U ⟶ V) :
    (snRelativeGluingData X).functor.map i ≫ snLocalLift f hf V = snLocalLift f hf U := by
  let d := snRelativeGluingData X
  let 𝒰 := Scheme.AffineZariskiSite.directedCover X
  let e : U.1.toScheme ⟶ V.1.toScheme := 𝒰.trans i
  have hNat : d.functor.map i ≫ d.natTrans.app V = d.natTrans.app U ≫ e :=
    d.natTrans.naturality i
  have hcover : e ≫ V.1.ι = U.1.ι := 𝒰.trans_map i
  let g : d.functor.obj U ⟶ pullback f U.1.ι :=
    pullback.lift
      (d.functor.map i ≫ snLocalMap f hf V ≫ pullback.fst f V.1.ι)
      (d.natTrans.app U) (by
        calc
          (d.functor.map i ≫ snLocalMap f hf V ≫ pullback.fst f V.1.ι) ≫ f =
              (d.functor.map i ≫ snLocalMap f hf V) ≫
                (pullback.fst f V.1.ι ≫ f) := by simp only [Category.assoc]
          _ = (d.functor.map i ≫ snLocalMap f hf V) ≫
                (pullback.snd f V.1.ι ≫ V.1.ι) := by rw [pullback.condition]
          _ = (d.functor.map i ≫ (snLocalMap f hf V ≫ pullback.snd f V.1.ι)) ≫ V.1.ι :=
                congrArg (fun t => t ≫ V.1.ι) (Category.assoc _ _ _)
          _ = (d.functor.map i ≫ d.natTrans.app V) ≫ V.1.ι :=
                congrArg (fun t => (d.functor.map i ≫ t) ≫ V.1.ι) (snLocalMap_snd f hf V)
          _ = (d.natTrans.app U ≫ e) ≫ V.1.ι :=
                congrArg (fun t => t ≫ V.1.ι) hNat
          _ = d.natTrans.app U ≫ e ≫ V.1.ι := Category.assoc _ _ _
          _ = d.natTrans.app U ≫ U.1.ι :=
                congrArg (fun t => d.natTrans.app U ≫ t) hcover)
  calc
    d.functor.map i ≫ snLocalLift f hf V =
        d.functor.map i ≫ snLocalMap f hf V ≫ pullback.fst f V.1.ι := rfl
    _ = g ≫ pullback.fst f U.1.ι := (pullback.lift_fst _ _ _).symm
    _ = snLocalMap f hf U ≫ pullback.fst f U.1.ι := by
      rw [snLocalMap_unique f hf U g (pullback.lift_snd _ _ _)]
    _ = snLocalLift f hf U := rfl

private noncomputable def snSchemeCocone {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) :
    CategoryTheory.Limits.Cocone (snRelativeGluingData X).functor where
  pt := Y
  ι :=
    { app := snLocalLift f hf
      naturality := fun _ _ i => snLocalLift_naturality f hf i }

private noncomputable def snSchemeMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) :
    (snRelativeGluingData X).glued ⟶ Y :=
  colimit.desc (snRelativeGluingData X).functor (snSchemeCocone f hf)

private theorem snSchemeMap_over {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f)) :
    snSchemeMap f hf ≫ f = (snRelativeGluingData X).toBase := by
  let d := snRelativeGluingData X
  refine colimit.hom_ext fun U => ?_
  show (colimit.ι d.functor U ≫ colimit.desc d.functor (snSchemeCocone f hf)) ≫ f =
      colimit.ι d.functor U ≫ d.toBase
  rw [colimit.ι_desc, d.ι_toBase]
  show snLocalLift f hf U ≫ f = d.natTrans.app U ≫ U.1.ι
  rw [snLocalLift, Category.assoc, pullback.condition, ← Category.assoc, snLocalMap_snd]
  rfl

private theorem snSchemeMap_unique {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsSeminormalizationCandidate X (Over.mk f))
    (g : (snRelativeGluingData X).glued ⟶ Y)
    (hg : g ≫ f = (snRelativeGluingData X).toBase) :
    g = snSchemeMap f hf := by
  let d := snRelativeGluingData X
  refine colimit.hom_ext fun U => ?_
  let gU : d.functor.obj U ⟶ pullback f U.1.ι := pullback.lift
    (colimit.ι d.functor U ≫ g) (d.natTrans.app U) (by
      rw [Category.assoc, hg, d.ι_toBase]
      rfl)
  calc
    colimit.ι d.functor U ≫ g = gU ≫ pullback.fst f U.1.ι := (pullback.lift_fst _ _ _).symm
    _ = snLocalLift f hf U := by
      rw [snLocalMap_unique f hf U gU (pullback.lift_snd _ _ _)]
      rfl
    _ = colimit.ι d.functor U ≫ snSchemeMap f hf := by
      show snLocalLift f hf U =
        colimit.ι d.functor U ≫ colimit.desc d.functor (snSchemeCocone f hf)
      rw [colimit.ι_desc]
      rfl

/-! ### The glued scheme is seminormal -/

private theorem snSchemeOver_isSeminormal (X : Scheme.{u}) :
    IsSeminormal (snSchemeOver X).left := by
  classical
  let d := snRelativeGluingData X
  intro x
  let i := d.cover.idx x
  obtain ⟨y, hy⟩ := d.cover.covers x
  have hmap : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  let U := i.1
  let A := Γ(X, U)
  let N := Algebra.seminormalization A
  let _ : IsAffine (d.functor.obj i) := by
    show IsAffine (Spec (CommRingCat.of N))
    infer_instance
  let V : d.glued.Opens := (d.cover.f i).opensRange
  have hRange : Set.range (d.cover.f i) = Set.range V.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  let e : d.functor.obj i ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (f := d.cover.f i) (g := V.ι) (H := hmap) hRange
  have hAffineV : IsAffineOpen V := IsAffine.of_isIso e.inv
  have hxV : x ∈ V := by
    show ∃ z, d.cover.f i z = x
    exact ⟨y, by simpa [i] using hy⟩
  refine ⟨⟨V, hAffineV⟩, hxV, ?_⟩
  show IsSeminormalRing Γ(d.glued, V)
  have himg : e.hom ''ᵁ (⊤ : (d.functor.obj i).Opens) = (⊤ : V.toScheme.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let eΓ : Γ(V.toScheme, ⊤) ≃+* N :=
    ((eqToIso (congrArg (fun W : V.toScheme.Opens => CommRingCat.of Γ(V.toScheme, W))
        himg.symm) ≪≫ e.hom.appIso ⊤) ≪≫
      Scheme.ΓSpecIso (CommRingCat.of N)).commRingCatIsoToRingEquiv
  let eV : Γ(d.glued, V) ≃+* Γ(V.toScheme, ⊤) := V.topIso.symm.commRingCatIsoToRingEquiv
  exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv (eV.trans eΓ).symm
    (isSeminormalRing_seminormalization A)

/-! ### The initial object -/

private noncomputable def snOverObject (X : Scheme.{u}) : SeminormalizationCategory X :=
  ⟨snSchemeOver X, snSchemeOver_property X⟩

private noncomputable def snOverMap (X : Scheme.{u}) (Z : SeminormalizationCategory X) :
    snOverObject X ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (snSchemeMap Z.obj.hom Z.property)
    (snSchemeMap_over Z.obj.hom Z.property))

private noncomputable def snOverObject_isInitial (X : Scheme.{u}) :
    IsInitial (snOverObject X) := by
  refine IsInitial.ofUniqueHom (fun Z => snOverMap X Z) fun Z g => ?_
  apply ObjectProperty.hom_ext
  apply CategoryTheory.CostructuredArrow.hom_ext
  exact snSchemeMap_unique Z.obj.hom Z.property g.hom.left (by
    simp [snOverObject, snSchemeOver])

end Proof

/-! ### Tag 0EUS for seminormalization -/

/-- **Stacks Project, Tag 0EUS.** The category of universal homeomorphisms to a scheme which
induce isomorphisms on all residue fields has an initial object, the seminormalization of that
scheme. -/
@[stacks 0EUS "seminormalization_initial"]
noncomputable instance hasInitial_seminormalizationCategory (X : Scheme.{u}) :
    HasInitial (SeminormalizationCategory X) :=
  (snOverObject_isInitial X).hasInitial

/-- Tag 0EUS's `seminormalization_initial` assertion, restated with the binder of the tag's statement, to record
that nothing is assumed about `X`. -/
example (X : Scheme.{u}) : HasInitial (SeminormalizationCategory X) :=
  hasInitial_seminormalizationCategory X

/-- **Stacks Project, Tag 0EUS.** The seminormalization of a scheme is a seminormal scheme.  The
chosen initial object is isomorphic to the glued one, whose charts are the spectra of the
ring-level seminormalizations. -/
theorem isSeminormal_initial_seminormalizationCategory (X : Scheme.{u}) :
    IsSeminormal (initial (SeminormalizationCategory X)).obj.left := by
  let eCat : snOverObject X ≅ initial (SeminormalizationCategory X) :=
    (snOverObject_isInitial X).uniqueUpToIso initialIsInitial
  let eScheme : (snOverObject X).obj.left ≅
      (initial (SeminormalizationCategory X)).obj.left :=
    asIso ((Over.forget X).map ((ObjectProperty.ι _).map eCat.hom))
  exact isSeminormal_of_isIso eScheme.hom (snSchemeOver_isSeminormal X)

/-- **Stacks Project, Tag 0EUS.** The canonical morphism from the seminormalization of `X` to a
universal homeomorphism `Y ⟶ X` inducing isomorphisms on all residue fields is an isomorphism
precisely when `Y` is seminormal. -/
@[stacks 0EUS "seminormalization_iso_iff"]
theorem isIso_initialTo_iff_isSeminormal (X : Scheme.{u})
    (Y : SeminormalizationCategory X) :
    IsIso (initial.to Y).hom.left ↔ IsSeminormal Y.obj.left :=
  isIso_initialTo_iff_isSeminormal_of_isSeminormal_initial X
    (isSeminormal_initial_seminormalizationCategory X) Y

/-- Tag 0EUS's `seminormalization_iso_iff` assertion, restated with every binder explicit and in
the order the tag states them, to record that no hypothesis beyond the tag's two is used. -/
example (X : Scheme.{u}) (Y : SeminormalizationCategory X) :
    IsIso (initial.to Y).hom.left ↔ IsSeminormal Y.obj.left :=
  isIso_initialTo_iff_isSeminormal X Y

end AlgebraicGeometry
