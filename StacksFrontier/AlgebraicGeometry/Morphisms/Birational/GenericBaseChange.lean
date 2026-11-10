module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Birational morphisms over a generic point

A birational morphism between schemes with finitely many irreducible components becomes an
isomorphism after base change to the spectrum of the local ring at a generic point of the
target.

## Main results

* `AlgebraicGeometry.isIso_stalkMap_fromSpecStalk_closedPoint`: the morphism
  `Spec 𝒪_{X, x} ⟶ X` is an isomorphism on stalks at the closed point.
* `AlgebraicGeometry.isIso_pullback_snd_fromSpecStalk_of_isBirational`: the generic base change
  of a birational morphism is an isomorphism.

## References

* [Stacks Project, Tag 0BAB](https://stacks.math.columbia.edu/tag/0BAB)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

private lemma range_fromSpecStalk_eq_singleton {X : Scheme.{u}} (x : X)
    (hx : x ∈ genericPoints X) :
    Set.range (X.fromSpecStalk x) = {x} := by
  rw [Scheme.range_fromSpecStalk]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hz => (hz.antisymm ?_).eq, by rintro rfl; exact specializes_rfl⟩
  exact specializes_iff_mem_closure.mpr (hx.2 isIrreducible_singleton.closure hz.closure_subset
    (subset_closure (Set.mem_singleton z)))

private lemma subsingleton_spec_stalk_of_mem_genericPoints {X : Scheme.{u}} (x : X)
    (hx : x ∈ genericPoints X) : Subsingleton (Spec (X.presheaf.stalk x)) :=
  have hc := Set.range_subset_singleton.mp (range_fromSpecStalk_eq_singleton x hx).subset
  ⟨fun a b => (X.fromSpecStalk x).isEmbedding.injective
    ((congrFun hc a).trans (congrFun hc b).symm)⟩

private lemma exists_generic_preimage_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hy : y ∈ genericPoints Y) (hxy : f x = y) :
    ∃ g : X, g ∈ genericPoints X ∧ f g = y ∧ g ⤳ x := by
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closure {x})
      isIrreducible_singleton.closure
  let g : genericPoints X := genericPoints.ofComponent ⟨Z, hZ⟩
  have hgx : g.1 ⤳ x := by
    rw [specializes_iff_mem_closure, (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).def]
    exact hxZ (subset_closure (Set.mem_singleton x))
  have hmem : f g.1 ∈ ({y} : Set Y) := by
    rw [← range_fromSpecStalk_eq_singleton y hy, Scheme.range_fromSpecStalk]
    simpa only [hxy, Set.mem_ofPred_eq] using hgx.map f.continuous
  exact ⟨g.1, g.2, hmem, hgx⟩

private lemma exists_generic_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) [IsIso (f.stalkMap x)] :
    ∃ s : Spec (Y.presheaf.stalk y) ⟶ X,
      s ≫ f = Y.fromSpecStalk y ∧ s (closedPoint _) = x := by
  subst y
  refine ⟨Spec.map (inv (f.stalkMap x)) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x), Spec.map_inv,
      IsIso.inv_hom_id_assoc]
  · change X.fromSpecStalk x ((Spec.map (inv (f.stalkMap x))) (closedPoint _)) = x
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The morphism `Spec 𝒪_{X, x} ⟶ X` is an isomorphism on stalks at the closed point. -/
theorem isIso_stalkMap_fromSpecStalk_closedPoint (X : Scheme.{u}) (x : X) :
    IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x))) := by
  have : IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x)) ≫
      (stalkClosedPointIso (X.presheaf.stalk x)).hom) := by
    rw [← Scheme.stalkClosedPointTo, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (X.presheaf.stalk x)).hom

private lemma surjective_pullback_snd_stalkMap_of_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsPreimmersion g] (z : ↑(pullback f g))
    [IsIso (f.stalkMap (pullback.fst f g z))]
    [IsIso (g.stalkMap (pullback.snd f g z))] :
    Function.Surjective ((pullback.snd f g).stalkMap z).hom := by
  have hsurj : Function.Surjective ((pullback.snd f g ≫ g).stalkMap z).hom := by
    rw [← pullback.condition, Scheme.Hom.stalkMap_comp]
    exact ((pullback.fst f g).stalkMap_surjective z).comp
      (ConcreteCategory.bijective_of_isIso (f.stalkMap _)).2
  rw [Scheme.Hom.stalkMap_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

private lemma generic_lift_point_specializes_all {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsBirational f) (y : Y) (hy : y ∈ genericPoints Y)
    (x₀ : X) (hx₀ : x₀ ∈ genericPoints X) (hx₀y : f x₀ = y)
    (p₀ z : ↑(pullback f (Y.fromSpecStalk y)))
    (hp₀ : pullback.fst f (Y.fromSpecStalk y) p₀ = x₀) : p₀ ⤳ z := by
  have hfz : f (pullback.fst f (Y.fromSpecStalk y) z) = y := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      ← Set.mem_singleton_iff, ← range_fromSpecStalk_eq_singleton y hy]
    exact Set.mem_range_self _
  obtain ⟨x, hx, hxy, hxz⟩ := exists_generic_preimage_specializes f _ y hy hfz
  apply ((pullback.fst f _).isEmbedding.isInducing.specializes_iff).mp
  rw [hp₀, ← hf.bijOn.injOn hx hx₀ (hxy.trans hx₀y.symm)]
  exact hxz

private lemma isIso_stalkMap_of_section_of_surjective
    {P S : Scheme.{u}} (r : P ⟶ S) (p : S ⟶ P)
    (hp : p ≫ r = 𝟙 S) (t : S)
    (hsurj : Function.Surjective (r.stalkMap (p t)).hom) :
    IsIso (r.stalkMap (p t)) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab => ?_, hsurj⟩
  have : IsIso ((p ≫ r).stalkMap t) := by
    rw [hp]
    infer_instance
  have : IsIso (r.stalkMap (p t) ≫ p.stalkMap t) := Scheme.Hom.stalkMap_comp p r t ▸ this
  apply (ConcreteCategory.bijective_of_isIso (r.stalkMap (p t) ≫ p.stalkMap t)).1
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using
    congrArg (p.stalkMap t).hom hab

/-- The base change of a birational morphism to the spectrum of the local ring at a generic
point of an irreducible component of the target is an isomorphism. -/
@[stacks 0BAB]
lemma isIso_pullback_snd_fromSpecStalk_of_isBirational
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f) (y : Y) (hy : y ∈ genericPoints Y) :
    IsIso (pullback.snd f (Y.fromSpecStalk y)) := by
  let g := Y.fromSpecStalk y
  let : Subsingleton (Spec (Y.presheaf.stalk y)) :=
    subsingleton_spec_stalk_of_mem_genericPoints y hy
  obtain ⟨x₀, hx₀, hx₀y⟩ := hf.bijOn.surjOn hy
  let : IsIso (f.stalkMap x₀) := hf.isIso_stalkMap x₀ hx₀
  obtain ⟨s, hs, hsx⟩ := exists_generic_section f x₀ y hx₀y
  let p : Spec (Y.presheaf.stalk y) ⟶ pullback f g :=
    pullback.lift s (𝟙 _) (by simpa only [Category.id_comp] using hs)
  have hp : p ≫ pullback.snd f g = 𝟙 _ := pullback.lift_snd _ _ _
  have hp_fst : p ≫ pullback.fst f g = s := pullback.lift_fst _ _ _
  have hp₀ : pullback.fst f g (p (closedPoint _)) = x₀ := by
    change (p ≫ pullback.fst f g) (closedPoint _) = x₀
    rw [hp_fst, hsx]
  let : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id (pullback.snd f g) p hp
  have hpoint (z : ↑(pullback f g)) : z = p (closedPoint _) := by
    obtain ⟨t, rfl⟩ : z ∈ Set.range p :=
      p.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨closedPoint _, rfl⟩)
        (specializes_iff_mem_closure.mp
          (generic_lift_point_specializes_all f hf y hy x₀ hx₀ hx₀y _ z hp₀))
    rw [Subsingleton.elim t (closedPoint _)]
  have : Subsingleton ↑(pullback f g) :=
    ⟨fun a b => (hpoint a).trans (hpoint b).symm⟩
  have hbij_base : Function.Bijective (pullback.snd f g) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun t =>
      ⟨p t, by rw [← Scheme.Hom.comp_apply, hp]; rfl⟩⟩
  have hopen : IsOpenMap (pullback.snd f g) := fun _ _ =>
    Subsingleton.set_cases (p := IsOpen) isOpen_empty isOpen_univ _
  have hbase : IsIso (pullback.snd f g).base :=
    TopCat.isIso_of_bijective_of_isOpenMap _ hbij_base hopen
  have hp_snd : (pullback.snd f g) (p (closedPoint _)) = closedPoint _ := by
    change (p ≫ pullback.snd f g) (closedPoint _) = closedPoint _
    rw [hp]
    rfl
  have : IsIso (f.stalkMap (pullback.fst f g (p (closedPoint _)))) := by
    rw [hp₀]
    infer_instance
  have : IsIso (g.stalkMap (pullback.snd f g (p (closedPoint _)))) := by
    change IsIso ((Y.fromSpecStalk y).stalkMap (pullback.snd f g (p (closedPoint _))))
    rw [hp_snd]
    exact isIso_stalkMap_fromSpecStalk_closedPoint Y y
  have hstalk := isIso_stalkMap_of_section_of_surjective (pullback.snd f g) p hp _
    (surjective_pullback_snd_stalkMap_of_isIso f g (p (closedPoint _)))
  rw [isIso_iff_isIso_stalkMap]
  exact ⟨hbase, fun z => by rw [hpoint z]; exact hstalk⟩

end AlgebraicGeometry
