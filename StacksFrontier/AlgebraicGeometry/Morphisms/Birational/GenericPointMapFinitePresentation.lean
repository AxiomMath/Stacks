module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapInjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtensionFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic-point data for a target locally of finite presentation

Let `X` and `Y` be schemes over `S`, where `X` has finitely many irreducible components with
chosen generic points. If `Y` is locally of finite presentation over `S`, then rational maps from
`X` to `Y` over `S` are in bijection with their induced points and local maps on stalks at those
generic points.

## Main results

* `bijective_genericPointMapForRationalMaps_of_locallyOfFinitePresentation`, in the namespace
  `AlgebraicGeometry.GenericPointMapContext`, states that the generic-point map for rational maps
  is bijective when the target is locally of finite presentation over the base.

## Implementation notes

The map and its codomain are those of `AlgebraicGeometry.GenericPointMapContext`; its value at
each generic point records both the image point and the compatible local map on stalks.

Injectivity is `AlgebraicGeometry.GenericPointMapContext.genericPointMapForRationalMaps_injective`,
available because local finite presentation implies local finite type. Surjectivity is
componentwise, through
`AlgebraicGeometry.GenericPointMapContext.surjective_genericPointMap_iff_components`: on one
component piece the chosen generic point is the generic point of the whole piece, so the
prescribed local homomorphism extends to a morphism on an open neighbourhood by
`AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation`, and
that neighbourhood is automatically dense. The resulting partial map realizes the prescribed
datum; the two components of the datum are matched by `Function.update`, which is why only one
index needs to be hit at a time.

The name carries the hypothesis it uses, because the same conclusion also follows from a reduced
source and a target only locally of finite type:
`AlgebraicGeometry.GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_isReduced`.
Neither hypothesis implies the other, so neither statement is a special case of the other and
neither takes the unsuffixed name.

## References

* [Stacks Project, Lemma 29.49.9 (Tag 0BX8)](https://stacks.math.columbia.edu/tag/0BX8)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace GenericPointMapContext

variable (C : GenericPointMapContext.{u})

private lemma heq_of_eqToHom_stalk {Y : Scheme.{u}} {x y : Y}
    {R : CommRingCat} {f : Y.presheaf.stalk x ⟶ R} {g : Y.presheaf.stalk y ⟶ R}
    (h : x = y)
    (H : f = eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) h) ≫ g) : HEq f g := by
  cases h
  simpa using H

private lemma cancelPrecompOfLeftInverse {C : Type*} [Category C]
    {A B D : C} (e : A ⟶ B) (es : B ⟶ A) (t : A ⟶ D) (g : B ⟶ D)
    (he : e ≫ es = 𝟙 A) (h : es ≫ t = g) : t = e ≫ g := by
  rw [← h, ← Category.assoc, he, Category.id_comp]

private lemma stalkMap_comp_stalkIso_hom {X : Scheme.{u}} (U : X.Opens) (D : U.toScheme.Opens)
    (x : D.toScheme) :
    (D.ι ≫ U.ι).stalkMap x ≫ (D.stalkIso x).hom ≫ (U.stalkIso (D.ι x)).hom = 𝟙 _ := by
  rw [Scheme.Hom.stalkMap_comp, ← Scheme.Opens.stalkIso_inv U (D.ι x),
    ← Scheme.Opens.stalkIso_inv D x]
  calc
    _ = ((U.stalkIso (D.ι x)).inv ≫ ((D.stalkIso x).inv ≫ (D.stalkIso x).hom)) ≫
          (U.stalkIso (D.ι x)).hom := by cat_disch
    _ = ((U.stalkIso (D.ι x)).inv ≫ 𝟙 _) ≫ (U.stalkIso (D.ι x)).hom :=
        congrArg (fun k ↦ ((U.stalkIso (D.ι x)).inv ≫ k) ≫ (U.stalkIso (D.ι x)).hom)
          (D.stalkIso x).inv_hom_id
    _ = _ := by
        rw [Category.comp_id, (U.stalkIso (D.ι x)).inv_hom_id]
        congr 1

private lemma genericPointLocalMap_eq_of_heq {i : Fin C.numberOfComponents}
    {a b : C.GenericPointLocalMap i} (hp : a.point = b.point)
    (hs : HEq a.stalkMap b.stalkMap) : a = b := by
  obtain ⟨p, _, s, _, _⟩ := a
  obtain ⟨p', _, s', _, _⟩ := b
  obtain rfl : p = p' := hp
  obtain rfl : s = s' := eq_of_heq hs
  rfl

private noncomputable def componentPoint (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) : (R.componentOpen i).toScheme :=
  ⟨⟨C.genericPoint i, genericPoint_mem_dense_open (C := C) R.denseOpen R.dense_denseOpen i⟩, by
    change _ ∈ (R.componentOpen i : Set R.denseOpen.toScheme)
    rw [R.componentOpen_carrier]
    exact (C.isGenericPoint i).mem⟩

private lemma isGenericPoint_of_eq_genericPoint (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) (x : (R.componentOpen i).toScheme)
    (hx : ((R.componentOpen i).ι ≫ R.denseOpen.ι) x = C.genericPoint i) :
    IsGenericPoint x (Set.univ : Set (R.componentOpen i).toScheme) := by
  let q : (R.componentOpen i).toScheme ⟶ C.X := (R.componentOpen i).ι ≫ R.denseOpen.ι
  rw [isGenericPoint_def]
  refine Set.eq_univ_iff_forall.mpr fun z ↦ mem_closure_iff.mpr fun W hW hzW ↦ ?_
  let W' : (R.componentOpen i).toScheme.Opens := ⟨W, hW⟩
  have hWcomp : ((C.components i : Set C.X) ∩ (q ''ᵁ W' : Set C.X)).Nonempty := by
    refine ⟨q z, ?_, ⟨z, hzW, rfl⟩⟩
    have hzD : z.1 ∈ (R.componentOpen i : Set R.denseOpen.toScheme) := z.2
    rw [R.componentOpen_carrier] at hzD
    exact hzD
  obtain ⟨z', hz'W, hz'q⟩ := (C.isGenericPoint i).mem_open_set_iff (q ''ᵁ W').2 |>.2 hWcomp
  have hz'x : z' = x := q.isOpenEmbedding.injective (hz'q.trans hx.symm)
  exact ⟨x, by simpa [W'] using hz'x ▸ hz'W, rfl⟩

private lemma stalkMap_comp_baseTarget_eq (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) (di : C.GenericPointLocalMap i)
    (hsX : (((R.componentOpen i).ι ≫ R.denseOpen.ι) ≫ C.toBaseSource) (C.componentPoint R i) =
      C.toBaseSource (C.genericPoint i)) :
    ((((R.componentOpen i).ι ≫ R.denseOpen.ι).stalkMap (C.componentPoint R i)).hom.comp
        di.stalkMap.hom).comp
      ((C.toBaseTarget.stalkMap di.point).hom.comp
        (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) di.mapsTo).symm).hom) =
      ((((R.componentOpen i).ι ≫ R.denseOpen.ι) ≫ C.toBaseSource).stalkMap
          (C.componentPoint R i)).hom.comp
        (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) hsX).symm).hom := by
  let D := R.componentOpen i
  let x : D.toScheme := C.componentPoint R i
  let q : D.toScheme ⟶ C.X := D.ι ≫ R.denseOpen.ι
  let pX : D.toScheme ⟶ C.S := q ≫ C.toBaseSource
  have hx : q x = C.genericPoint i := rfl
  have hy := di.mapsTo
  let qmap := (q.stalkMap x).hom
  let dmap := di.stalkMap.hom
  let pYmap := (C.toBaseTarget.stalkMap di.point).hom
  let eY := (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) hy).symm).hom
  let pXSmap := (C.toBaseSource.stalkMap (C.genericPoint i)).hom
  let eHy := (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) hy)).hom
  have he : eHy.comp eY = RingHom.id _ := by
    ext b
    simp [eHy, eY, ← CommRingCat.hom_comp, eqToHom_trans]
  have hdi : dmap.comp pYmap = pXSmap.comp eHy := congrArg (fun f => f.hom) di.commutes
  ext a
  have hdi_a : dmap (pYmap (eY a)) = pXSmap a := by
    have h := DFunLike.congr_fun hdi (eY a)
    change dmap (pYmap (eY a)) = pXSmap (eHy (eY a)) at h
    have hcancel : eHy (eY a) = a := by
      simpa [RingHom.comp_apply] using DFunLike.congr_fun he a
    rwa [hcancel] at h
  change qmap (dmap (pYmap (eY a))) = _
  rw [hdi_a]
  have hpx : (pX.stalkMap x).hom.comp
      (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) hsX).symm).hom =
      qmap.comp pXSmap := by
    have hpxCat :
        eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) hsX).symm ≫ pX.stalkMap x =
          C.toBaseSource.stalkMap (C.genericPoint i) ≫ q.stalkMap x := by
      cases hx
      rw [Subsingleton.elim hsX rfl]
      dsimp [pX]
      rw [Scheme.Hom.stalkMap_comp]
      cat_disch
    exact (congrArg CommRingCat.Hom.hom hpxCat).trans (CommRingCat.hom_comp _ _)
  exact (DFunLike.congr_fun hpx a).symm

private lemma stalkMap_comp_stalkIso_eq (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) (di : C.GenericPointLocalMap i)
    {V : (R.componentOpen i).toScheme.Opens} (hxV : C.componentPoint R i ∈ V)
    (f : V.toScheme ⟶ C.Y) (hfy : f ⟨C.componentPoint R i, hxV⟩ = di.point)
    (hstalk : (V.stalkIso ⟨C.componentPoint R i, hxV⟩).hom.hom.comp
        ((f.stalkMap ⟨C.componentPoint R i, hxV⟩).hom.comp
          (eqToHom (congrArg (fun z ↦ C.Y.presheaf.stalk z) hfy).symm).hom) =
      (((R.componentOpen i).ι ≫ R.denseOpen.ι).stalkMap (C.componentPoint R i)).hom.comp
        di.stalkMap.hom) :
    f.stalkMap ⟨C.componentPoint R i, hxV⟩ ≫ (V.stalkIso ⟨C.componentPoint R i, hxV⟩).hom ≫
        ((R.componentOpen i).stalkIso (C.componentPoint R i)).hom ≫
          (R.denseOpen.stalkIso ((R.componentOpen i).ι (C.componentPoint R i))).hom =
      eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy) ≫ di.stalkMap := by
  let D := R.componentOpen i
  let x : D.toScheme := C.componentPoint R i
  let q : D.toScheme ⟶ C.X := D.ι ≫ R.denseOpen.ι
  have hlocalCat :
      eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy.symm) ≫
          f.stalkMap ⟨x, hxV⟩ ≫ (V.stalkIso ⟨x, hxV⟩).hom =
        di.stalkMap ≫ q.stalkMap x := by
    apply CommRingCat.hom_ext
    change ((V.stalkIso ⟨x, hxV⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxV⟩).hom.comp
            (eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy.symm)).hom)) =
        (q.stalkMap x).hom.comp di.stalkMap.hom
    exact hstalk
  have hincq : q.stalkMap x ≫ (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom =
      𝟙 (C.X.presheaf.stalk (C.genericPoint i)) := stalkMap_comp_stalkIso_hom R.denseOpen D x
  have hlocalChain :
      eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy.symm) ≫
          f.stalkMap ⟨x, hxV⟩ ≫ (V.stalkIso ⟨x, hxV⟩).hom ≫
            (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom =
        di.stalkMap := by
    have hpost :
        eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy.symm) ≫
            f.stalkMap ⟨x, hxV⟩ ≫ (V.stalkIso ⟨x, hxV⟩).hom ≫
              (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom =
          (di.stalkMap ≫ q.stalkMap x) ≫
            (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom := by
      simpa [Category.assoc] using congrArg
        (fun g ↦ g ≫ (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom) hlocalCat
    exact hpost.trans ((Category.assoc _ _ _).trans
      ((congrArg (di.stalkMap ≫ ·) hincq).trans (Category.comp_id _)))
  exact cancelPrecompOfLeftInverse _ _ _ _ (by simp [eqToHom_trans]) hlocalChain

private theorem component_map_exists
    (R : IrreducibleComponentReduction C)
    (d : ∀ j, C.GenericPointLocalMap j)
    (i : Fin C.numberOfComponents) [LocallyOfFinitePresentation C.toBaseTarget] :
    ∃ r : ComponentRationalMapsOver C R.denseOpen (R.componentOpen i),
      R.componentGenericPointMap i r = d i := by
  classical
  let di := d i
  let D := R.componentOpen i
  let x : D.toScheme := C.componentPoint R i
  let q : D.toScheme ⟶ C.X := D.ι ≫ R.denseOpen.ι
  let pX : D.toScheme ⟶ C.S := q ≫ C.toBaseSource
  have : IsIso (q.stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion q)).2 x
  have hsX : pX x = C.toBaseSource (C.genericPoint i) := rfl
  have hy : C.toBaseTarget di.point = C.toBaseSource (C.genericPoint i) := di.mapsTo
  let phi : C.Y.presheaf.stalk di.point →+* D.toScheme.presheaf.stalk x :=
    (q.stalkMap x).hom.comp di.stalkMap.hom
  have hphi : IsLocalHom phi := @RingHom.isLocalHom_comp _ _ _ _ _ _
    (q.stalkMap x).hom di.stalkMap.hom (isLocalHom_of_isIso _) di.isLocalHom
  obtain ⟨V, hxV, f, hf, hfy, hstalk⟩ :=
    exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation
      pX C.toBaseTarget (C.toBaseSource (C.genericPoint i)) x di.point hsX hy phi hphi
      (C.stalkMap_comp_baseTarget_eq R i di hsX)
      (inferInstance : LocallyOfFinitePresentation C.toBaseTarget)
  have hxgeneric := C.isGenericPoint_of_eq_genericPoint R i x rfl
  have hVdense : Dense (V : Set D.toScheme) := dense_iff_inter_open.mpr fun W hW ⟨z, hz⟩ ↦
    ⟨x, (hxgeneric.mem_open_set_iff hW).2 ⟨z, Set.mem_univ _, hz⟩, hxV⟩
  let m : D.toScheme.PartialMap C.Y := ⟨V, hVdense, f⟩
  let : D.toScheme.Over C.S := ⟨pX⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  let : m.IsOver C.S := by
    rw [Scheme.PartialMap.isOver_iff]
    exact hf
  have hmo : m.toRationalMap.IsOver C.S := inferInstance
  have hrat : m.toRationalMap.compHom C.toBaseTarget = pX.toRationalMap := by
    have hrat := (Scheme.RationalMap.isOver_iff).mp hmo
    change m.toRationalMap.compHom C.toBaseTarget = pX.toRationalMap at hrat
    simpa [pX, q] using hrat
  let r : ComponentRationalMapsOver C R.denseOpen D := ⟨m.toRationalMap, hrat⟩
  refine ⟨r, ?_⟩
  let z : m.domain := ⟨x, hxV⟩
  have hover : m.hom ≫ C.toBaseTarget =
      m.domain.ι ≫ D.ι ≫ R.denseOpen.ι ≫ C.toBaseSource := by
    change f ≫ C.toBaseTarget = V.ι ≫ D.ι ≫ R.denseOpen.ι ≫ C.toBaseSource
    simpa [pX, q, Category.assoc] using hf
  have hz : z.1.1.1 = C.genericPoint i := rfl
  have hpoint := R.componentGenericPointMap_point i r m rfl hover z hz
  have hstalkR := R.componentGenericPointMap_stalk i r m rfl hover z hz
  have hlocalChainEq :
      m.hom.stalkMap z ≫ (m.domain.stalkIso z).hom ≫
          (D.stalkIso x).hom ≫ (R.denseOpen.stalkIso (D.ι x)).hom =
        eqToHom (congrArg (fun y ↦ C.Y.presheaf.stalk y) hfy) ≫ di.stalkMap :=
    C.stalkMap_comp_stalkIso_eq R i di hxV f hfy hstalk
  exact C.genericPointLocalMap_eq_of_heq (hpoint.trans hfy)
    (hstalkR.trans (heq_of_eqToHom_stalk hfy hlocalChainEq))

/-- When the target is locally of finite presentation over the base, every
compatible collection of points and local maps at the generic points comes
from a unique rational map over the base. -/
@[stacks 0BX8 "finite_presentation_bijectivity",
  ega "IV 20.3.7" "bijectivity (fin pres)",
  ega "I 7.1.11" "bijectivity"]
public theorem bijective_genericPointMapForRationalMaps_of_locallyOfFinitePresentation
    [LocallyOfFinitePresentation C.toBaseTarget] :
    Function.Bijective C.genericPointMapForRationalMaps := by
  classical
  refine ⟨genericPointMapForRationalMaps_injective C, fun d ↦ ?_⟩
  obtain ⟨R⟩ := nonempty_irreducibleComponentReduction C
  refine (surjective_genericPointMap_iff_components (C := C) R).2 (Or.inr fun i di ↦ ?_) d
  obtain ⟨r, hr⟩ := component_map_exists (C := C) R (Function.update d i di) i
  exact ⟨r, by simpa using hr⟩

end GenericPointMapContext

end AlgebraicGeometry

end
