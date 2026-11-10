module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalUniqueness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity of the generic-point map for rational maps

For schemes `X` and `Y` over `S`, where `X` has finitely many irreducible components with chosen
generic points, evaluation at those generic points is injective on rational maps over `S` as soon
as `Y ⟶ S` is locally of finite type.

## Main results

* `AlgebraicGeometry.GenericPointMapContext.genericPointMapForRationalMaps_injective`: the
  generic-point map for rational maps over the base is injective.

## Implementation notes

The map is `AlgebraicGeometry.GenericPointMapContext.genericPointMapForRationalMaps`; its
codomain records both the image point and the induced local homomorphism at each chosen generic
point.

Two rational maps agreeing there are compared on a single dense open: representatives of both are
restricted to the intersection of their domains, which still contains every chosen generic point.
At each of those points the two representatives have the same image and the same stalk map, so
`AlgebraicGeometry.exists_open_eq_of_stalkMap_eq` produces a neighbourhood on which they agree,
and the union of those neighbourhoods is dense because it meets every component in its generic
point. Agreeing on a dense open is equality of rational maps.

## References

* [Stacks Project, Lemma 29.49.9 (Tag 0BX8)](https://stacks.math.columbia.edu/tag/0BX8)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace GenericPointMapContext



private lemma eq_of_heq_stalk_hom {Y : Scheme.{u}} {x y : Y}
    {R : CommRingCat} {f : Y.presheaf.stalk x ⟶ R} {g : Y.presheaf.stalk y ⟶ R}
    (h : x = y) (H : HEq f g) :
    f = (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ g := by
  cases h
  simpa using eq_of_heq H

/-- Restricting a partial map to a smaller dense open preserves its rational map and the
compatibility with the structure maps over the base. -/
private lemma restrict_partialMap_spec (C : GenericPointMapContext.{u})
    {f : C.X.RationalMap C.Y} {a : C.X.PartialMap C.Y} (ha : a.toRationalMap = f)
    (haBase : a.hom ≫ C.toBaseTarget = a.domain.ι ≫ C.toBaseSource)
    {D : C.X.Opens} (hD : Dense (D : Set C.X)) (hle : D ≤ a.domain) :
    (⟨D, hD, C.X.homOfLE hle ≫ a.hom⟩ : C.X.PartialMap C.Y).toRationalMap = f ∧
      (C.X.homOfLE hle ≫ a.hom) ≫ C.toBaseTarget = D.ι ≫ C.toBaseSource := by
  refine ⟨?_, by rw [Category.assoc, haBase, Scheme.homOfLE_ι_assoc]⟩
  rw [← ha, Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨D, hD, le_rfl, hle, by simp [Scheme.PartialMap.restrict]⟩

/-- A rational map over the base is determined by its values and induced local
maps at the generic points of the irreducible components when the target is
locally of finite type over the base. -/
@[stacks 0BX8 "injectivity",
  ega "IV 20.2.11" "(i)",
  ega "IV 20.3.7" "injectivity",
  ega "I 7.1.11" "injectivity"]
public theorem genericPointMapForRationalMaps_injective
    (C : GenericPointMapContext.{u}) [LocallyOfFiniteType C.toBaseTarget] :
    Function.Injective C.genericPointMapForRationalMaps := by
  intro f g hfg
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  have hfOver : f.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr f.2
  have hgOver : g.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr g.2
  obtain ⟨a, haOver, ha⟩ := f.1.exists_partialMap_over C.S
  obtain ⟨b, hbOver, hb⟩ := g.1.exists_partialMap_over C.S
  have haBase : a.hom ≫ C.toBaseTarget = a.domain.ι ≫ C.toBaseSource :=
    (Scheme.PartialMap.isOver_iff).mp haOver
  have hbBase : b.hom ≫ C.toBaseTarget = b.domain.ι ≫ C.toBaseSource :=
    (Scheme.PartialMap.isOver_iff).mp hbOver
  let D : C.X.Opens := a.domain ⊓ b.domain
  have hD : Dense (D : Set C.X) :=
    a.dense_domain.inter_of_isOpen_left b.dense_domain a.domain.2
  let aD : C.X.PartialMap C.Y :=
    ⟨D, hD, C.X.homOfLE inf_le_left ≫ a.hom⟩
  let bD : C.X.PartialMap C.Y :=
    ⟨D, hD, C.X.homOfLE inf_le_right ≫ b.hom⟩
  obtain ⟨haD, haDBase⟩ := C.restrict_partialMap_spec ha haBase hD (inf_le_left : D ≤ a.domain)
  obtain ⟨hbD, hbDBase⟩ := C.restrict_partialMap_spec hb hbBase hD (inf_le_right : D ≤ b.domain)
  have memD (i : Fin C.numberOfComponents) : C.genericPoint i ∈ D :=
    C.genericPoint_mem_dense_open D hD i
  have hloc : ∀ i : Fin C.numberOfComponents,
      ∃ U : D.toScheme.Opens, (⟨C.genericPoint i, memD i⟩ : D.toScheme) ∈ U ∧
        U.ι ≫ aD.hom = U.ι ≫ bD.hom := by
    intro i
    let q : D.toScheme := ⟨C.genericPoint i, memD i⟩
    let y : C.Y := C.genericPointMapForRationalMaps f i |>.point
    have hdataPair := Sigma.mk.inj_iff.mp (congrArg
      (fun z : C.GenericPointLocalMap i =>
        (⟨z.point, z.stalkMap⟩ :
          Σ y : C.Y, C.Y.presheaf.stalk y ⟶ C.X.presheaf.stalk (C.genericPoint i)))
      (congrFun hfg i))
    have hpoint : y = (C.genericPointMapForRationalMaps g i).point := by
      simpa [y] using hdataPair.1
    have hxs : (D.ι ≫ C.toBaseSource) q = C.toBaseSource (C.genericPoint i) := rfl
    have hys : C.toBaseTarget y = C.toBaseSource (C.genericPoint i) :=
      (C.genericPointMapForRationalMaps f i).mapsTo
    have hfx : aD.hom q = y := by
      change aD.hom ⟨C.genericPoint i, memD i⟩ = y
      simpa [y] using
        (C.genericPointMapForRationalMaps.map_point f aD haD haDBase memD i).symm
    have hgx : bD.hom q = y := by
      change bD.hom ⟨C.genericPoint i, memD i⟩ = y
      exact (C.genericPointMapForRationalMaps.map_point g bD hbD hbDBase memD i).symm.trans
        hpoint.symm
    have hstalk : aD.hom.stalkMap q =
        C.Y.presheaf.stalkSpecializes
          (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes ≫ bD.hom.stalkMap q := by
      have hdataStalk : HEq (C.genericPointMapForRationalMaps f i).stalkMap
          (C.genericPointMapForRationalMaps g i).stalkMap := hdataPair.2
      have hmA := C.genericPointMapForRationalMaps.map_stalk
        f aD haD haDBase memD i
      have hmB := C.genericPointMapForRationalMaps.map_stalk
        g bD hbD hbDBase memD i
      have hrep : HEq
          (aD.hom.stalkMap q ≫ (D.stalkIso ⟨C.genericPoint i, memD i⟩).hom)
          (bD.hom.stalkMap q ≫ (D.stalkIso ⟨C.genericPoint i, memD i⟩).hom) :=
        hmA.symm.trans (hdataStalk.trans hmB)
      have hpoints : aD.hom q = bD.hom q := hfx.trans hgx.symm
      have hcomp := eq_of_heq_stalk_hom hpoints hrep
      have hcomp' : aD.hom.stalkMap q ≫ (D.stalkIso ⟨C.genericPoint i, memD i⟩).hom =
          (C.Y.presheaf.stalkSpecializes
            (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes ≫
            bD.hom.stalkMap q) ≫ (D.stalkIso ⟨C.genericPoint i, memD i⟩).hom := by
        simpa only [hpoints, TopCat.Presheaf.stalkCongr_hom, Category.assoc] using hcomp
      exact (cancel_mono (D.stalkIso ⟨C.genericPoint i, memD i⟩).hom).mp hcomp'
    exact exists_open_eq_of_stalkMap_eq
      (D.ι ≫ C.toBaseSource) C.toBaseTarget aD.hom bD.hom haDBase hbDBase
      (C.toBaseSource (C.genericPoint i)) q y hxs hys hfx hgx hstalk (Or.inl inferInstance)
  let U : Fin C.numberOfComponents → D.toScheme.Opens := fun i => Classical.choose (hloc i)
  have hUeq (i : Fin C.numberOfComponents) : (U i).ι ≫ aD.hom = (U i).ι ≫ bD.hom :=
    (Classical.choose_spec (hloc i)).2
  let V : D.toScheme.Opens := ⨆ i, U i
  let W : C.X.Opens := D.ι ''ᵁ V
  have hWpt (i : Fin C.numberOfComponents) : C.genericPoint i ∈ W := by
    change C.genericPoint i ∈ D.ι ''ᵁ V
    exact ⟨⟨C.genericPoint i, memD i⟩,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (Classical.choose_spec (hloc i)).1⟩, rfl⟩
  have hW : Dense (W : Set C.X) := dense_of_generic_points_mem_open C W hWpt
  have hWD : W ≤ D := Scheme.Opens.ι_image_le D V
  have hVeq : V.ι ≫ aD.hom = V.ι ≫ bD.hom := by
    refine (Scheme.Opens.iSupOpenCover U).hom_ext
      (V.ι ≫ aD.hom) (V.ι ≫ bD.hom) fun i => ?_
    simpa only [Scheme.Opens.iSupOpenCover, V, Scheme.homOfLE_ι_assoc] using hUeq i
  have hWrestr : (aD.restrict W hW hWD).hom = (bD.restrict W hW hWD).hom := by
    dsimp [Scheme.PartialMap.restrict]
    rw [← Scheme.Opens.isoImage_ι_inv_ι D V]
    simpa [Category.assoc] using congrArg (fun k => (D.ι.isoImage V).inv ≫ k) hVeq
  exact Subtype.ext <| haD.symm.trans <|
    (Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨W, hW, hWD, hWD, hWrestr⟩).trans hbD

end GenericPointMapContext

end AlgebraicGeometry

end
