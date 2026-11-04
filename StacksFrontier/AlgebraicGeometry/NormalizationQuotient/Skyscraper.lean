module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs

/-!
# Stalkwise criteria for comparing modules with skyscrapers

A module on a scheme whose stalks are concentrated on a closed discrete subset ought to be the
direct sum of the skyscrapers of those stalks; that decomposition is the sheaf-theoretic input to
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2), where the subset is the
singular locus of a one-dimensional Nagata scheme.  This file collects the stalkwise criteria the
decomposition is assembled from: all of them say that a map of modules, or of presheaves of
modules, is an isomorphism as soon as it is one on stalks, or that a biproduct comparison over a
discrete index is an isomorphism as soon as all but one factor vanishes.

## Main results

* `module_isIso_of_stalk_map_isIso` detects an isomorphism of modules on stalks.
* `stalk_map_isIso_of_locally_isIso` and `stalk_isZero_of_locally_isZero` compute a stalk from
  the behaviour on arbitrarily small opens around the point.
* `isIso_fan_π_of_isZero`, `isIso_cofan_ι_of_isZero` and `map_coproductToProduct_isIso` are the
  discrete-index biproduct comparisons.
* `exists_open_meets_closed_discrete_at_most_one` is the topological input that makes those
  comparisons applicable: a closed discrete subset meets a small enough neighbourhood of any
  point at most once.
* `skyscraperPOM_obj_isZero_of_not_mem`: a skyscraper vanishes on opens missing its point.

## Implementation notes

`map_coproductToProduct_isIso` is stated for a functor `G` out of the ambient category rather
than for the categories themselves, because the application evaluates a presheaf of modules on
one open at a time: over an open meeting the discrete subset at most once, all but one of the
skyscrapers evaluate to zero, so the comparison is an isomorphism there even when the index set
is infinite and the biproduct therefore not finite.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

/-- A projection out of a product over a discrete index is an isomorphism when all the other
factors vanish. -/
public theorem isIso_fan_π_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} {F : Discrete ι ⥤ C} (c : Cone F) (hc : IsLimit c)
    (i : ι) (h : ∀ j, j ≠ i → IsZero (F.obj ⟨j⟩)) : IsIso (c.π.app ⟨i⟩) := by
  classical
  let s : Cone F := ⟨F.obj ⟨i⟩, Discrete.natTrans fun ⟨j⟩ =>
    if e : i = j then eqToHom (congrArg (fun k => F.obj ⟨k⟩) e) else 0⟩
  refine ⟨⟨hc.lift s, ?_, ?_⟩⟩
  · apply hc.hom_ext
    intro ⟨j⟩
    by_cases e : j = i
    · subst j
      simp [Category.assoc, hc.fac, s]
    · exact (h j e).eq_of_tgt _ _
  · simp [s, hc.fac]

/-- An inclusion into a coproduct over a discrete index is an isomorphism when all the other
summands vanish. -/
public theorem isIso_cofan_ι_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} {F : Discrete ι ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (i : ι) (h : ∀ j, j ≠ i → IsZero (F.obj ⟨j⟩)) : IsIso (c.ι.app ⟨i⟩) := by
  classical
  let s : Cocone F := ⟨F.obj ⟨i⟩, Discrete.natTrans fun ⟨j⟩ =>
    if e : j = i then eqToHom (congrArg (fun k => F.obj ⟨k⟩) e) else 0⟩
  refine ⟨⟨hc.desc s, ?_, ?_⟩⟩
  · simp [s, hc.fac]
  · apply hc.hom_ext
    intro ⟨j⟩
    by_cases e : j = i
    · subst j
      simp [← Category.assoc, hc.fac, s]
    · exact (h j e).eq_of_src _ _

/-- A presheaf map that is an isomorphism on all small enough opens around `x` is an isomorphism
on the stalk at `x`. -/
public theorem stalk_map_isIso_of_locally_isIso {X : TopCat.{u}}
    {F G : X.Presheaf AddCommGrpCat.{u}} (f : F ⟶ G) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (h : ∀ V ≤ U, x ∈ V → IsIso (f.app (op V))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f) := by
  have hbij : ∀ V ≤ U, x ∈ V → Function.Bijective (f.app (op V)) := fun V hV hxV =>
    have _ := h V hV hxV
    ConcreteCategory.bijective_of_isIso _
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun b => ?_⟩
  · obtain ⟨V, hVU, hxV, a, rfl⟩ := F.exists_le_germ_eq a hx
    obtain ⟨W, hWU, hxW, b, rfl⟩ := F.exists_le_germ_eq b hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hab
    obtain ⟨Z, hxZ, iV, iW, heq⟩ := G.germ_eq x hxV hxW _ _ hab
    have heq' : F.map iV.op a = F.map iW.op b := by
      apply (hbij Z ((leOfHom iV).trans hVU) hxZ).1
      simpa only [← ConcreteCategory.comp_apply, f.naturality] using heq
    exact F.germ_ext Z hxZ iV iW heq'
  · obtain ⟨V, hVU, hxV, b, rfl⟩ := G.exists_le_germ_eq b hx
    obtain ⟨a, rfl⟩ := (hbij V hVU hxV).2 b
    exact ⟨F.germ V x hxV a, TopCat.Presheaf.stalkFunctor_map_germ_apply ..⟩

/-- A functor sends the canonical map from a coproduct to a product to an isomorphism as soon as
it kills all but one of the factors. -/
public theorem map_coproductToProduct_isIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject D]
    {ι : Type*} [DecidableEq ι] (F : ι → C) [HasProduct F] [HasCoproduct F]
    (G : C ⥤ D) [PreservesLimit (Discrete.functor F) G]
    [PreservesColimit (Discrete.functor F) G]
    (h : ∀ i j, ¬ IsZero (G.obj (F i)) → ¬ IsZero (G.obj (F j)) → i = j) :
    IsIso (G.map (Sigma.desc (Pi.ι F))) := by
  classical
  have hc := isColimitOfPreserves G (colimit.isColimit (Discrete.functor F))
  have hl := isLimitOfPreserves G (limit.isLimit (Discrete.functor F))
  by_cases hn : ∃ i, ¬ IsZero (G.obj (F i))
  · obtain ⟨i, hi⟩ := hn
    have hz (j) (hji : j ≠ i) : IsZero (G.obj (F j)) := by_contra fun hj => hji (h j i hj hi)
    have _ : IsIso (G.map (Sigma.ι F i)) := isIso_cofan_ι_of_isZero _ hc i hz
    have _ : IsIso (G.map (Pi.π F i)) := isIso_fan_π_of_isZero _ hl i hz
    have heq : G.map (Sigma.ι F i) ≫ G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F i) = 𝟙 _ := by
      rw [← G.map_comp, ← G.map_comp]
      simp
    have _ : IsIso (G.map (Sigma.desc (Pi.ι F)) ≫ G.map (Pi.π F i)) :=
      IsIso.of_isIso_fac_left heq
    exact IsIso.of_isIso_comp_right (G.map (Sigma.desc (Pi.ι F))) (G.map (Pi.π F i))
  · have hz : IsZero (Discrete.functor F ⋙ G) :=
      (Functor.isZero_iff _).2 fun ⟨i⟩ => by simpa using not_exists.mp hn i
    exact (hc.isZero_pt hz).isIso (hl.isZero_pt hz) _

/-- A skyscraper presheaf of modules vanishes on opens missing its point. -/
public theorem skyscraperPOM_obj_isZero_of_not_mem {X : Scheme.{u}} (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∉ U) :
    IsZero ((OXModule.skyscraperPOM x N).obj (Opposite.op U)) := by
  change IsZero (OXModule.skyscraperObj x N (Opposite.op U))
  rw [OXModule.skyscraperObj, dite_eq_right hx]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- A module map that is an isomorphism on every stalk is an isomorphism. -/
public theorem module_isIso_of_stalk_map_isIso {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map f.val))) : IsIso f := by
  let _ : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) := h
  have _ : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  have _ : IsIso ((PresheafOfModules.toPresheaf _).map f.val) :=
    Functor.map_isIso (sheafToPresheaf _ _) ((SheafOfModules.toSheaf X.ringCatSheaf).map f)
  have _ : IsIso f.val := isIso_of_reflects_iso f.val (PresheafOfModules.toPresheaf _)
  exact ⟨⟨⟨inv f.val⟩, SheafOfModules.hom_ext (IsIso.hom_inv_id f.val),
    SheafOfModules.hom_ext (IsIso.inv_hom_id f.val)⟩⟩

/-- A presheaf vanishing on all small enough opens around `x` has vanishing stalk at `x`. -/
public theorem stalk_isZero_of_locally_isZero {X : TopCat.{u}}
    (F : X.Presheaf AddCommGrpCat.{u}) (x : X) (U : Opens X) (hx : x ∈ U)
    (h : ∀ V ≤ U, x ∈ V → IsZero (F.obj (op V))) : IsZero (F.stalk x) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq (0 : F.stalk x)
  intro a
  obtain ⟨V, hVU, hxV, s, rfl⟩ := F.exists_le_germ_eq a hx
  have _ := AddCommGrpCat.isZero_iff_subsingleton.mp (h V hVU hxV)
  rw [Subsingleton.elim s 0, map_zero]

/-- Every point of a space has an open neighbourhood meeting a closed discrete subset in at most
one point. -/
public theorem exists_open_meets_closed_discrete_at_most_one {X : Type u} [TopologicalSpace X]
    (Z : Set X) (hZ : IsClosed Z) [DiscreteTopology Z] (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ z ∈ Z, z ∈ U → z = x := by
  classical
  by_cases hx : x ∈ Z
  · obtain ⟨U, hU, heq⟩ := discreteTopology_subtype_iff'.mp
      (inferInstance : DiscreteTopology Z) x hx
    refine ⟨⟨U, hU⟩, ?_, ?_⟩
    · have hmem : x ∈ U ∩ Z := by
        rw [heq]
        exact Set.mem_singleton x
      exact hmem.1
    · intro z hz hzu
      have hmem : z ∈ U ∩ Z := ⟨hzu, hz⟩
      rwa [heq, Set.mem_singleton_iff] at hmem
  · exact ⟨⟨Zᶜ, hZ.isOpen_compl⟩, hx, fun z hz hzu => (hzu hz).elim⟩

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
