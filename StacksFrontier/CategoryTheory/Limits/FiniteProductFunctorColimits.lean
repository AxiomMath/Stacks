module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite products of functors commute with colimits

In a preadditive category with finite biproducts a finite product is a finite coproduct, so the
finite product of a family of functors each of which preserves the colimits of a shape `K` again
preserves them. Together with a family of functors which jointly reflect isomorphisms this gives
a way of checking that a functor preserves colimits "stalkwise".

## Main definitions

* `CategoryTheory.Limits.piObjFunctor`: the pointwise product `N ↦ ∏ᵢ Sᵢ N` of a family of
  functors.
* `CategoryTheory.Limits.piFunctorIsoSigmaFunctor`: for a finite index type, the product functor
  `(ι → C) ⥤ C` is isomorphic to the coproduct functor.

## Main results

* `CategoryTheory.Limits.preservesColimitsOfShape_piFunctor`: in a preadditive category with
  finite biproducts, finite products commute with colimits.
* `CategoryTheory.Limits.preservesColimitsOfShape_pi'_comp_piFunctor`,
  `CategoryTheory.Limits.preservesColimitsOfShape_piObjFunctor`: the finite product
  `N ↦ ∏ᵢ Sᵢ N` of functors preserving colimits of shape `K` preserves them.
* `CategoryTheory.JointlyReflectIsomorphisms.preservesColimitsOfShape`: a functor `F` preserves
  colimits of shape `K` as soon as `F ⋙ s i` does for every member of a family `s` of functors
  which preserve colimits of shape `K` and jointly reflect isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Limits

/-- The pointwise product `N ↦ ∏ᵢ Sᵢ N` of a family of functors. -/
@[simps]
abbrev piObjFunctor {C : Type u} [Category.{v} C] {ι : Type w} [HasProductsOfShape ι C]
    {D : Type*} [Category* D] (S : ι → D ⥤ C) : D ⥤ C where
  obj N := ∏ᶜ fun i => (S i).obj N
  map g := Limits.Pi.map fun i => (S i).map g

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (ι : Type w) [Finite ι]

/-- In a preadditive category with finite biproducts the product functor `(ι → C) ⥤ C` of a
finite index type is isomorphic to the coproduct functor, through the biproduct. -/
def piFunctorIsoSigmaFunctor : Pi.functor (C := C) ι ≅ Sigma.functor ι :=
  NatIso.ofComponents (fun f => (biproduct.isoProduct f).symm ≪≫ biproduct.isoCoproduct f)
    fun {f g} t => by
      have := Fintype.ofFinite ι
      change Pi.map t ≫ (biproduct.isoProduct g).inv ≫ (biproduct.isoCoproduct g).hom =
        ((biproduct.isoProduct f).inv ≫ (biproduct.isoCoproduct f).hom) ≫ Sigma.map t
      rw [← cancel_epi (biproduct.isoProduct f).hom, ← cancel_mono (biproduct.isoCoproduct g).inv]
      refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      classical
      by_cases h : i = j
      · subst h; simp
      · simp [biproduct.ι_π_ne_assoc _ h, biproduct.ι_π_ne _ h]

variable {K : Type*} [Category* K] [HasColimitsOfShape K C]

/-- The coproduct functor `(ι → C) ⥤ C` preserves colimits. -/
instance preservesColimitsOfShape_sigmaFunctor :
    PreservesColimitsOfShape K (Sigma.functor (C := C) ι) :=
  inferInstanceAs (PreservesColimitsOfShape K ((piEquivalenceFunctorDiscrete ι C).functor ⋙ colim))

/-- In a preadditive category with finite biproducts the finite product functor `(ι → C) ⥤ C`
preserves colimits. -/
instance preservesColimitsOfShape_piFunctor :
    PreservesColimitsOfShape K (Pi.functor (C := C) ι) :=
  preservesColimitsOfShape_of_natIso (piFunctorIsoSigmaFunctor ι).symm

omit [HasColimitsOfShape K C] in
/-- **A finite product of functors which preserve the colimits of a shape preserves them**, in a
preadditive category with finite biproducts: `N ↦ ∏ᵢ Sᵢ N` preserves colimits of shape `K` if
every `Sᵢ` does. -/
theorem preservesColimitsOfShape_pi'_comp_piFunctor {D : Type*} [Category* D]
    (S : ι → D ⥤ C) [∀ i, PreservesColimitsOfShape K (S i)] :
    PreservesColimitsOfShape K (Functor.pi' S ⋙ Pi.functor ι) := by
  have : PreservesColimitsOfShape K
      (Functor.pi' S ⋙ (piEquivalenceFunctorDiscrete ι C).functor) :=
    preservesColimitsOfShape_of_evaluation _ K fun i =>
      preservesColimitsOfShape_of_natIso (Functor.isoWhiskerLeft (Functor.pi' S)
        (piEquivalenceFunctorDiscreteCompEvaluationIso C i.as) ≪≫ Functor.pi'CompEval S i.as).symm
  have : PreservesColimitsOfShape K (Functor.pi' S ⋙ Sigma.functor ι) :=
    inferInstanceAs (PreservesColimitsOfShape K
      ((Functor.pi' S ⋙ (piEquivalenceFunctorDiscrete ι C).functor) ⋙ colim))
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (Functor.pi' S) (piFunctorIsoSigmaFunctor ι)).symm

omit [HasColimitsOfShape K C] in
/-- **A finite product of functors which preserve the colimits of a shape preserves them**:
the version of `preservesColimitsOfShape_pi'_comp_piFunctor` for `piObjFunctor`. -/
theorem preservesColimitsOfShape_piObjFunctor {D : Type*} [Category* D]
    (S : ι → D ⥤ C) [∀ i, PreservesColimitsOfShape K (S i)] :
    PreservesColimitsOfShape K (piObjFunctor S) :=
  preservesColimitsOfShape_pi'_comp_piFunctor ι S

end CategoryTheory.Limits

namespace CategoryTheory.JointlyReflectIsomorphisms

variable {C D : Type*} [Category* C] [Category* D] {I : Type*} {A : I → Type*}
  [∀ i, Category* (A i)] {K : Type*} [Category* K]

/-- A functor `F` preserves colimits of shape `K` as soon as, for a family of functors `s i`
which preserve colimits of shape `K` and jointly reflect isomorphisms, each composite
`F ⋙ s i` preserves them. -/
theorem preservesColimitsOfShape (F : C ⥤ D) {s : ∀ i, D ⥤ A i}
    (hs : JointlyReflectIsomorphisms s) [HasColimitsOfShape K C] [HasColimitsOfShape K D]
    [∀ i, HasColimitsOfShape K (A i)] [∀ i, PreservesColimitsOfShape K (s i)]
    [∀ i, PreservesColimitsOfShape K (F ⋙ s i)] : PreservesColimitsOfShape K F where
  preservesColimit {G} := by
    have : ∀ i, IsIso ((s i).map (colimit.post G F)) := fun i => by
      have h : (s i).map (colimit.post G F) =
          inv (colimit.post (G ⋙ F) (s i)) ≫ colimit.post G (F ⋙ s i) := by
        rw [← colimit.post_post G F (s i), IsIso.inv_hom_id_assoc]
      rw [h]
      infer_instance
    have := hs.isIso (colimit.post G F)
    exact preservesColimit_of_isIso_post F G

end CategoryTheory.JointlyReflectIsomorphisms

end
