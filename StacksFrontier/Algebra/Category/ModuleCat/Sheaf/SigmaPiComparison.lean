module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Coproduct

/-!
# The comparison from a direct sum of sheaves of modules to the product

Let `F : ι → SheafOfModules R` be a family of sheaves of modules and let `f : ∐ F ⟶ ∏ᶜ F` be a
morphism whose components are the identity on the diagonal and zero off it — the canonical
comparison `CategoryTheory.Limits.sigmaPiComparison`.  This file proves the two halves of its
local bijectivity which are formal:

* `f` is **locally injective**.  The comparison from the sectionwise direct sum to the direct sum
  is locally surjective, because the direct sum of sheaves is the sheafification of the
  sectionwise direct sum; and the composite of the two is sectionwise injective, because on each
  object it is the comparison of a direct sum of modules with their product.
* a section of `∏ᶜ F` over an object with only **finitely many nonzero components** is in the
  image of `f`, by the finite sum of its components.

Local surjectivity of `f` is not formal: it needs an index-wise finiteness statement.

## Main results

* `Stacks.SheafOfModules.isLocallyInjective_of_comparison`: local injectivity.
* `Stacks.SheafOfModules.exists_preimage_of_finite_support`: a section with finitely many nonzero
  components is in the image.

## Implementation notes

Local surjectivity of the comparison `sigmaComparison` from the sectionwise direct sum is read
off from the fact that sheafification inverts it: sheafification of presheaves of modules
preserves coproducts, so the comparison becomes an isomorphism after sheafification, and the
morphisms inverted by sheafification are exactly the locally bijective ones.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u u'

namespace Stacks.SheafOfModules

/-- **A morphism out of a direct sum of modules whose components are the identity on the diagonal
and zero off it is injective.**  It agrees with the comparison of the coproduct with the
`DFinsupp` direct sum followed by the projections. -/
theorem module_coproduct_injective {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]
    (F : ι → ModuleCat.{v} R) {P : ModuleCat.{v} R} (f : (∐ F) ⟶ P) (p : ∀ i, P ⟶ F i)
    (h : ∀ i j, Sigma.ι F i ≫ f ≫ p j = if h : i = j then eqToHom (congrArg F h) else 0) :
    Function.Injective f := by
  classical
  let e := ModuleCat.coprodIsoDirectSum F
  have hp (j : ι) : f ≫ p j = e.hom ≫ ModuleCat.ofHom (DFinsupp.lapply j) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [h, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
    by_cases hij : i = j
    · subst j
      simp only [dite_true]
      ext a
      show a = (DFinsupp.single (β := fun k => F k) i a) i
      simp
    · simp only [dite_eq_right hij]
      ext a
      show 0 = (DFinsupp.single (β := fun k => F k) i a) j
      simp [hij]
  intro a b hab
  refine (ConcreteCategory.bijective_of_isIso e.hom).injective (DFinsupp.ext fun j => ?_)
  have hh : (f ≫ p j) a = (f ≫ p j) b := congrArg (fun z => p j z) hab
  rwa [hp] at hh

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Coproducts of presheaves of modules, supplied directly: instance search for them times out. -/
local instance hasColimitsOfShape_discrete_presheafOfModules (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (PresheafOfModules.{u} R.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- Coproducts of sheaves of modules, supplied directly: instance search for them times out. -/
local instance hasColimitsOfShape_discrete_sheafOfModules [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (_root_.SheafOfModules.{u} R) :=
  @_root_.SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    _ _ _ R _ _ _ _ (hasColimitsOfShape_discrete_presheafOfModules ι)

/-- Coproducts of families of presheaves of modules, supplied directly. -/
local instance hasCoproduct_presheafOfModules {ι : Type u}
    (F : ι → PresheafOfModules.{u} R.obj) : HasCoproduct F :=
  (hasColimitsOfShape_discrete_presheafOfModules ι).has_colimit _

/-- Coproducts of families of sheaves of modules, supplied directly. -/
local instance hasCoproduct_sheafOfModules [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u}
    (F : ι → _root_.SheafOfModules.{u} R) : HasCoproduct F :=
  (hasColimitsOfShape_discrete_sheafOfModules ι).has_colimit _

/-- **The comparison from the sectionwise direct sum to the direct sum of sheaves of modules is
locally surjective.**  Sheafification preserves coproducts, so it inverts the comparison, and the
morphisms it inverts are the locally bijective ones. -/
theorem isLocallySurjective_sigmaComparison [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u}
    (F : ι → _root_.SheafOfModules.{u} R) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map
      (sigmaComparison (_root_.SheafOfModules.forget R) F)) := by
  have hcounit :
      IsIso (PresheafOfModules.sheafificationAdjunction.{u, v, w, u'} (𝟙 R.obj)).counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{u} R)]
    rw [PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app]
    exact isIso_sheafificationAdjunction_counit
      ((_root_.SheafOfModules.toSheaf.{u} R).obj M)
  let e : _root_.SheafOfModules.forget.{u} R ⋙ PresheafOfModules.sheafification (𝟙 R.obj) ≅
      𝟭 (_root_.SheafOfModules.{u} R) :=
    @asIso _ _ _ _ _ hcounit
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := _root_.SheafOfModules.forget.{u} R
  have : PreservesColimitsOfShape (Discrete ι) (G ⋙ L) :=
    preservesColimitsOfShape_of_natIso e.symm
  have heq : sigmaComparison L (fun i => G.obj (F i)) ≫ L.map (sigmaComparison G F) =
      sigmaComparison (G ⋙ L) F := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [ι_comp_sigmaComparison_assoc, ← L.map_comp, ι_comp_sigmaComparison]
    exact (ι_comp_sigmaComparison (G ⋙ L) F i).symm
  have hi : IsIso (L.map (sigmaComparison G F)) := by
    have : IsIso (sigmaComparison L (fun i => G.obj (F i)) ≫ L.map (sigmaComparison G F)) := by
      rw [heq]; infer_instance
    exact IsIso.of_isIso_comp_left (sigmaComparison L (fun i => G.obj (F i))) _
  have hw : J.W ((PresheafOfModules.toPresheaf R.obj).map (sigmaComparison G F)) :=
    (congrArg (fun W => W (sigmaComparison G F))
      (PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
        (𝟙 R.obj))).mpr hi
  exact hw.isLocallySurjective

/-- **A morphism from a direct sum of sheaves of modules to their product whose components are
the identity on the diagonal and zero off it is locally injective.**  The comparison from the
sectionwise direct sum is locally surjective, and the composite with the given morphism is
sectionwise injective by `Stacks.SheafOfModules.module_coproduct_injective`. -/
theorem isLocallyInjective_of_comparison [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [DecidableEq ι]
    (F : ι → _root_.SheafOfModules.{u} R) [HasProduct F] [HasCoproduct F]
    (f : (∐ F) ⟶ (∏ᶜ F))
    (h : ∀ i j, Sigma.ι F i ≫ f ≫ Pi.π F j =
      if h : i = j then eqToHom (congrArg F h) else 0) :
    PresheafOfModules.IsLocallyInjective J f.val := by
  let G := _root_.SheafOfModules.forget R
  let T := PresheafOfModules.toPresheaf R.obj
  let c := sigmaComparison G F
  have hc : Presheaf.IsLocallySurjective J (T.map c) := isLocallySurjective_sigmaComparison F
  have hinj : Presheaf.IsLocallyInjective J (T.map c ≫ T.map (G.map f)) := by
    refine Presheaf.isLocallyInjective_of_injective J _ fun U => ?_
    let E := PresheafOfModules.evaluation R.obj U
    let Q := fun i => G.obj (F i)
    let e := sigmaComparison E Q
    have hi : Function.Injective (e ≫ E.map (c ≫ G.map f)) := by
      refine module_coproduct_injective (fun i => E.obj (Q i)) _
        (fun j => E.map (G.map (Pi.π F j))) fun i j => ?_
      simp only [Category.assoc]
      rw [ι_comp_sigmaComparison_assoc, ← E.map_comp, ← E.map_comp]
      show E.map ((Sigma.ι Q i ≫ c ≫ G.map f) ≫ G.map (Pi.π F j)) = _
      rw [ι_comp_sigmaComparison_assoc, ← G.map_comp, ← G.map_comp, Category.assoc, h]
      by_cases hij : i = j
      · subst j
        simp only [eqToHom_refl]
        exact E.map_id _
      · rw [dite_eq_right hij, dite_eq_right hij, G.map_zero, E.map_zero]
    have he : Function.Surjective e := (ConcreteCategory.bijective_of_isIso e).surjective
    intro a b hab
    obtain ⟨a', rfl⟩ := he a
    obtain ⟨b', rfl⟩ := he b
    exact congrArg e (hi hab)
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    J (T.map c) (T.map (G.map f))

/-- **A section of a product of sheaves of modules with only finitely many nonzero components is
in the image of a morphism from the direct sum** whose components are the identity on the
diagonal and zero off it: it is the image of the finite sum of its components. -/
theorem exists_preimage_of_finite_support {ι : Type u} [DecidableEq ι]
    (F : ι → _root_.SheafOfModules.{u} R) [HasProduct F] [HasCoproduct F]
    (f : (∐ F) ⟶ (∏ᶜ F))
    (h : ∀ i j, Sigma.ι F i ≫ f ≫ Pi.π F j =
      if h : i = j then eqToHom (congrArg F h) else 0)
    (U : Cᵒᵖ) (b : (∏ᶜ F).val.obj U) (s : Finset ι)
    (hb : ∀ i, i ∉ s → (Pi.π F i).val.app U b = 0) :
    ∃ a : (∐ F).val.obj U, f.val.app U a = b := by
  classical
  let E := _root_.SheafOfModules.evaluation R U
  refine ⟨∑ i ∈ s, (Sigma.ι F i).val.app U ((Pi.π F i).val.app U b), ?_⟩
  apply Concrete.isLimit_ext _ (isLimitOfPreserves E (limit.isLimit (Discrete.functor F)))
  rintro ⟨j⟩
  show (Pi.π F j).val.app U (f.val.app U
    (∑ i ∈ s, (Sigma.ι F i).val.app U ((Pi.π F i).val.app U b))) = (Pi.π F j).val.app U b
  simp only [map_sum]
  have he (i : ι) : (Pi.π F j).val.app U
      (f.val.app U ((Sigma.ι F i).val.app U ((Pi.π F i).val.app U b))) =
      if i = j then (Pi.π F j).val.app U b else 0 := by
    have hh := congrArg (fun g : F i ⟶ F j => (E.map g) ((Pi.π F i).val.app U b)) (h i j)
    by_cases hij : i = j
    · subst j
      simp only [dite_true, eqToHom_refl, Functor.map_comp] at hh
      change (Pi.π F i).val.app U (f.val.app U
        ((Sigma.ι F i).val.app U ((Pi.π F i).val.app U b))) = (Pi.π F i).val.app U b at hh
      simpa using hh
    · simp only [dite_eq_right hij, Functor.map_comp] at hh
      change (Pi.π F j).val.app U (f.val.app U
        ((Sigma.ι F i).val.app U ((Pi.π F i).val.app U b))) = 0 at hh
      simpa only [ite_eq_right hij] using hh
  simp only [he]
  by_cases hj : j ∈ s
  · simp [hj]
  · simp [hb j hj]

end Stacks.SheafOfModules

end
