module

public import StacksCore.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Extension
public import StacksCore.Tactic.StacksAttribute

/-!
# Monoidal extension from the finitely presented modules

Finitely presented modules are closed under tensor products and contain the tensor unit, so
their full subcategory inherits the monoidal structure of the ambient module category. A monoidal
functor on finitely presented modules then extends monoidally to all modules, along its
filtered-colimit-preserving extension.

## Main results

* `ModuleCat.finitelyPresentedModule_isMonoidal` equips the finitely presented modules with the
  inherited tensor product.
* `ModuleCat.filteredColimitExtension_monoidal`: a filtered-colimit-preserving extension of a
  monoidal functor on finitely presented modules carries a compatible monoidal structure.

## Implementation notes

The theorem applies to an arbitrary filtered-colimit-preserving extension rather than to a
particular choice of one; uniqueness up to compatible isomorphism is
`ModuleCat.FilteredColimitExtension.existsUnique_iso`. The multiplication of the monoidal
structure is obtained by extending the multiplication of the original functor one variable at a
time, and each coherence axiom is an equality of natural transformations out of a
filtered-colimit-preserving functor, so it is detected on the finitely presented objects alone.

## References

* [Stacks Project, Tag 0GP5](https://stacks.math.columbia.edu/tag/0GP5)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits

universe u v w x

namespace ModuleCat

private lemma hom_ext_on_finitelyPresented (A : Type u) [Ring A]
    {D : Type w} [Category.{x} D]
    (G : ModuleCat.{max u v} A ⥤ D)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} G]
    {M : ModuleCat.{max u v} A} {N : D} (f g : G.obj M ⟶ N)
    (h : ∀ (X : FinitelyPresentedModuleCat.{u, max u v} A)
      (a : X.obj ⟶ M), G.map a ≫ f = G.map a ≫ g) : f = g := by
  obtain ⟨J, hJ, hf, p, hp⟩ := ind_finitelyPresentedModule A M
  let := hJ
  let := hf
  exact (isColimitOfPreserves G p.isColimit).hom_ext fun j => h ⟨p.diag.obj j, hp j⟩ (p.ι.app j)

private lemma natTrans_ext_on_finitelyPresented (A : Type u) [Ring A]
    {D : Type w} [Category.{x} D]
    {G H : ModuleCat.{max u v} A ⥤ D}
    [PreservesFilteredColimitsOfSize.{max u v, max u v} G]
    (f g : G ⟶ H)
    (h : ∀ X : FinitelyPresentedModuleCat.{u, max u v} A,
      f.app X.obj = g.app X.obj) : f = g := by
  ext M
  refine hom_ext_on_finitelyPresented A G _ _ fun X a => ?_
  rw [f.naturality, g.naturality, h X]

private lemma exists_iso_of_restriction (A : Type u) [Ring A]
    {D : Type w} [Category.{x} D]
    (G H : ModuleCat.{max u v} A ⥤ D)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} G]
    [PreservesFilteredColimitsOfSize.{max u v, max u v} H]
    (e : (finitelyPresentedModule.{u, max u v} A).ι ⋙ G ≅
      (finitelyPresentedModule.{u, max u v} A).ι ⋙ H) :
    ∃ i : G ≅ H,
      Functor.whiskerLeft (finitelyPresentedModule.{u, max u v} A).ι i.hom = e.hom := by
  let E₁ : FilteredColimitExtension A
      ((finitelyPresentedModule.{u, max u v} A).ι ⋙ H) := ⟨G, inferInstance, e⟩
  let E₂ : FilteredColimitExtension A
      ((finitelyPresentedModule.{u, max u v} A).ι ⋙ H) := ⟨H, inferInstance, Iso.refl _⟩
  obtain ⟨i, hi, _⟩ := FilteredColimitExtension.existsUnique_iso A E₁ E₂
  exact ⟨i, by simpa [E₁, E₂] using hi⟩

private lemma exists_iso_of_restriction₂ (A : Type u) [Ring A]
    {D : Type w} [Category.{x} D]
    (G H : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A ⥤ D)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} G]
    [PreservesFilteredColimitsOfSize.{max u v, max u v} H]
    [∀ X, PreservesFilteredColimitsOfSize.{max u v, max u v} (G.obj X)]
    [∀ X, PreservesFilteredColimitsOfSize.{max u v, max u v} (H.obj X)]
    (e : ∀ X Y : FinitelyPresentedModuleCat.{u, max u v} A,
      (G.obj X.obj).obj Y.obj ≅ (H.obj X.obj).obj Y.obj)
    (nat_left : ∀ {X X' : FinitelyPresentedModuleCat.{u, max u v} A} (f : X ⟶ X') Y,
      (G.map f.hom).app Y.obj ≫ (e X' Y).hom = (e X Y).hom ≫ (H.map f.hom).app Y.obj)
    (nat_right : ∀ X {Y Y' : FinitelyPresentedModuleCat.{u, max u v} A} (f : Y ⟶ Y'),
      (G.obj X.obj).map f.hom ≫ (e X Y').hom = (e X Y).hom ≫ (H.obj X.obj).map f.hom) :
    ∃ β : G ≅ H, ∀ X Y, (β.hom.app X.obj).app Y.obj = (e X Y).hom := by
  have inner (X : FinitelyPresentedModuleCat.{u, max u v} A) :
      ∃ i : G.obj X.obj ≅ H.obj X.obj, ∀ Y, i.hom.app Y.obj = (e X Y).hom := by
    obtain ⟨i, hi⟩ := exists_iso_of_restriction.{u, v} A (G.obj X.obj) (H.obj X.obj)
      (NatIso.ofComponents (e X) fun f => nat_right X f)
    exact ⟨i, fun Y => NatTrans.congr_app hi Y⟩
  choose i hi using inner
  obtain ⟨β, hβ⟩ := exists_iso_of_restriction.{u, v} A G H (NatIso.ofComponents i (by
    intro X X' f
    refine natTrans_ext_on_finitelyPresented.{u, v} A (G := G.obj X.obj) _ _ fun Y => ?_
    change (G.map f.hom).app Y.obj ≫ (i X').hom.app Y.obj =
      (i X).hom.app Y.obj ≫ (H.map f.hom).app Y.obj
    rw [hi, hi]
    exact nat_left f Y))
  exact ⟨β, fun X Y => (congrArg (fun t => (t.app X).app Y.obj) hβ).trans (hi X Y)⟩

private def moduleCat_tensorLeftIsoTensorRight {A : Type u} [CommRing A]
    (M : ModuleCat.{max u v} A) : tensorLeft M ≅ tensorRight M :=
  NatIso.ofComponents (fun N => (TensorProduct.comm A M N).toModuleIso)
    (by
      intro N N' f
      ext : 1
      exact TensorProduct.ext' fun _ _ => rfl)

private lemma moduleCat_tensorRight_preservesColimitsOfShape
    {A : Type u} [CommRing A] (M : ModuleCat.{max u v} A)
    (J : Type*) [Category J] : PreservesColimitsOfShape J (tensorRight M) :=
  preservesColimitsOfShape_of_natIso (moduleCat_tensorLeftIsoTensorRight M)

private lemma moduleCat_tensorRight_preservesFilteredColimits
    {A : Type u} [CommRing A] (M : ModuleCat.{max u v} A) :
    PreservesFilteredColimitsOfSize.{w, x} (tensorRight M) :=
  ⟨fun J _ _ => moduleCat_tensorRight_preservesColimitsOfShape M J⟩

-- Tensoring on the right preserves the colimits it is asked about below only through the
-- symmetry isomorphism, so the two transported statements are supplied as local instances.
attribute [local instance] moduleCat_tensorRight_preservesColimitsOfShape
  moduleCat_tensorRight_preservesFilteredColimits

variable (R : Type u) [CommRing R]

-- The monoidal structure on `ModuleCat.{max u v} R` for a ring `R : Type u` is the one
-- transported along the universe lift, which has to win over the same-universe instance.
attribute [local instance 2000] ModuleCat.liftedModuleMonoidal

/-- Finitely presented modules form a monoidal full subcategory of modules. -/
@[stacks 0GP5 "monoidal structure on finitely presented modules"]
instance finitelyPresentedModule_isMonoidal :
    (finitelyPresentedModule.{u, max u v} R).IsMonoidal where
  prop_unit := by
    change Module.FinitePresentation R (ULift.{v} R)
    exact Module.FinitePresentation.of_equiv (ULift.moduleEquiv (R := R)).symm
  prop_tensor := by
    intro M N hM hN
    have : Module.FinitePresentation R M := hM
    have : Module.FinitePresentation R N := hN
    exact Module.FinitePresentation.tensorProduct (R := R)

variable (S : Type w) [CommRing S]

section Bifunctor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

private def tensorObjBifunctor (Φ : C ⥤ D) : C ⥤ C ⥤ D where
  obj X := Φ ⋙ tensorLeft (Φ.obj X)
  map f := Functor.whiskerLeft Φ ((curriedTensor D).map (Φ.map f))
  map_id X := by
    ext Y
    simp
  map_comp f g := by
    ext Y
    simp

private def objTensorBifunctor (Φ : C ⥤ D) : C ⥤ C ⥤ D where
  obj X := tensorLeft X ⋙ Φ
  map f := Functor.whiskerRight ((curriedTensor C).map f) Φ
  map_id X := by
    ext Y
    simp
  map_comp f g := by
    ext Y
    simp

private abbrev bifunctorμ {Φ : C ⥤ D} (β : tensorObjBifunctor Φ ≅ objTensorBifunctor Φ)
    (X Y : C) : Φ.obj X ⊗ Φ.obj Y ≅ Φ.obj (X ⊗ Y) :=
  (β.app X).app Y

end Bifunctor

section Coherence

variable {R S} (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{max w x} S)
  [PreservesFilteredColimitsOfSize.{max u v, max u v} Φ]

private theorem tensorObjBifunctor_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{max u v, max u v} (tensorObjBifunctor Φ) :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation (tensorObjBifunctor Φ) J fun Y => by
    change PreservesColimitsOfShape J (Φ ⋙ tensorRight (Φ.obj Y))
    infer_instance⟩

private theorem objTensorBifunctor_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{max u v, max u v} (objTensorBifunctor Φ) :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation (objTensorBifunctor Φ) J fun Y => by
    change PreservesColimitsOfShape J (tensorRight Y ⋙ Φ)
    infer_instance⟩

private theorem tensorObjBifunctor_obj_preservesFilteredColimits (X : ModuleCat.{max u v} R) :
    PreservesFilteredColimitsOfSize.{max u v, max u v} ((tensorObjBifunctor Φ).obj X) := by
  change PreservesFilteredColimitsOfSize.{max u v, max u v} (Φ ⋙ tensorLeft (Φ.obj X))
  infer_instance

private theorem objTensorBifunctor_obj_preservesFilteredColimits (X : ModuleCat.{max u v} R) :
    PreservesFilteredColimitsOfSize.{max u v, max u v} ((objTensorBifunctor Φ).obj X) := by
  change PreservesFilteredColimitsOfSize.{max u v, max u v} (tensorLeft X ⋙ Φ)
  infer_instance

private lemma bifunctorμ_associativity (β : tensorObjBifunctor Φ ≅ objTensorBifunctor Φ)
    (hfp : ∀ X Y Z : FinitelyPresentedModuleCat.{u, max u v} R,
      (bifunctorμ β X.obj Y.obj).hom ▷ Φ.obj Z.obj ≫ (bifunctorμ β (X.obj ⊗ Y.obj) Z.obj).hom ≫
          Φ.map (α_ X.obj Y.obj Z.obj).hom =
        (α_ (Φ.obj X.obj) (Φ.obj Y.obj) (Φ.obj Z.obj)).hom ≫
          Φ.obj X.obj ◁ (bifunctorμ β Y.obj Z.obj).hom ≫
            (bifunctorμ β X.obj (Y.obj ⊗ Z.obj)).hom)
    (X Y Z : ModuleCat.{max u v} R) :
    (bifunctorμ β X Y).hom ▷ Φ.obj Z ≫ (bifunctorμ β (X ⊗ Y) Z).hom ≫ Φ.map (α_ X Y Z).hom =
      (α_ (Φ.obj X) (Φ.obj Y) (Φ.obj Z)).hom ≫
        Φ.obj X ◁ (bifunctorμ β Y Z).hom ≫ (bifunctorμ β X (Y ⊗ Z)).hom := by
  let C := ModuleCat.{max u v} R
  let D := ModuleCat.{max w x} S
  let T : D ⥤ C ⥤ D := curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj Φ
  let U : C ⥤ D ⥤ D := Φ ⋙ curriedTensor D
  let L := bifunctorComp₁₂ (tensorObjBifunctor Φ) T
  let H := bifunctorComp₂₃ (objTensorBifunctor Φ) (curriedTensor C)
  let l : L ⟶ H := (bifunctorComp₁₂Functor.map β.hom).app T ≫
    (bifunctorComp₁₂Functor.obj (curriedTensor C)).map β.hom ≫
      (Functor.postcompose₃.obj Φ).map (curriedAssociatorNatIso C).hom
  let r : L ⟶ H :=
    (Functor.whiskeringLeft₃ObjObjObj D Φ Φ Φ).map (curriedAssociatorNatIso D).hom ≫
      (bifunctorComp₂₃Functor.obj U).map β.hom ≫
        (bifunctorComp₂₃Functor.map β.hom).app (curriedTensor C)
  have hL : PreservesFilteredColimitsOfSize.{max u v, max u v} L :=
    ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation L J fun Y =>
      preservesColimitsOfShape_of_evaluation _ J fun Z => by
        change PreservesColimitsOfShape J (Φ ⋙ tensorRight (Φ.obj Y) ⋙ tensorRight (Φ.obj Z))
        infer_instance⟩
  have hLx (X : C) : PreservesFilteredColimitsOfSize.{max u v, max u v} (L.obj X) :=
    ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation (L.obj X) J fun Z => by
      change PreservesColimitsOfShape J (Φ ⋙ tensorLeft (Φ.obj X) ⋙ tensorRight (Φ.obj Z))
      infer_instance⟩
  have hLxy (X Y : C) :
      PreservesFilteredColimitsOfSize.{max u v, max u v} ((L.obj X).obj Y) := by
    change PreservesFilteredColimitsOfSize.{max u v, max u v}
      (Φ ⋙ tensorLeft (Φ.obj X ⊗ Φ.obj Y))
    infer_instance
  have hlr : l = r := natTrans_ext_on_finitelyPresented.{u, v} R _ _ fun X =>
    natTrans_ext_on_finitelyPresented.{u, v} R _ _ fun Y =>
      natTrans_ext_on_finitelyPresented.{u, v} R _ _ fun Z => hfp X Y Z
  exact congrArg (fun t => ((t.app X).app Y).app Z) hlr

private lemma bifunctorμ_left_unitality (β : tensorObjBifunctor Φ ≅ objTensorBifunctor Φ)
    (ε : 𝟙_ (ModuleCat.{max w x} S) ≅ Φ.obj (𝟙_ (ModuleCat.{max u v} R)))
    (hfp : ∀ Y : FinitelyPresentedModuleCat.{u, max u v} R,
      (λ_ (Φ.obj Y.obj)).hom = ε.hom ▷ Φ.obj Y.obj ≫
        (bifunctorμ β (𝟙_ _) Y.obj).hom ≫ Φ.map (λ_ Y.obj).hom)
    (X : ModuleCat.{max u v} R) :
    (λ_ (Φ.obj X)).hom = ε.hom ▷ Φ.obj X ≫ (bifunctorμ β (𝟙_ _) X).hom ≫ Φ.map (λ_ X).hom := by
  let C := ModuleCat.{max u v} R
  let D := ModuleCat.{max w x} S
  let l : Φ ⋙ tensorLeft (𝟙_ D) ⟶ Φ := Functor.whiskerLeft Φ (leftUnitorNatIso D).hom
  let r : Φ ⋙ tensorLeft (𝟙_ D) ⟶ Φ :=
    Functor.whiskerLeft Φ ((curriedTensor D).map ε.hom) ≫
      β.hom.app (𝟙_ C) ≫ Functor.whiskerRight (leftUnitorNatIso C).hom Φ
  exact NatTrans.congr_app (natTrans_ext_on_finitelyPresented.{u, v} R l r hfp) X

private lemma bifunctorμ_right_unitality (β : tensorObjBifunctor Φ ≅ objTensorBifunctor Φ)
    (ε : 𝟙_ (ModuleCat.{max w x} S) ≅ Φ.obj (𝟙_ (ModuleCat.{max u v} R)))
    (hfp : ∀ Y : FinitelyPresentedModuleCat.{u, max u v} R,
      (ρ_ (Φ.obj Y.obj)).hom = Φ.obj Y.obj ◁ ε.hom ≫
        (bifunctorμ β Y.obj (𝟙_ _)).hom ≫ Φ.map (ρ_ Y.obj).hom)
    (X : ModuleCat.{max u v} R) :
    (ρ_ (Φ.obj X)).hom = Φ.obj X ◁ ε.hom ≫ (bifunctorμ β X (𝟙_ _)).hom ≫ Φ.map (ρ_ X).hom := by
  let C := ModuleCat.{max u v} R
  let D := ModuleCat.{max w x} S
  let l : Φ ⋙ tensorRight (𝟙_ D) ⟶ Φ := Functor.whiskerLeft Φ (rightUnitorNatIso D).hom
  let r : Φ ⋙ tensorRight (𝟙_ D) ⟶ Φ :=
    Functor.whiskerLeft Φ ((tensoringRight D).map ε.hom) ≫
      Functor.whiskerRight β.hom ((evaluation C D).obj (𝟙_ C)) ≫
        Functor.whiskerRight (rightUnitorNatIso C).hom Φ
  exact NatTrans.congr_app (natTrans_ext_on_finitelyPresented.{u, v} R l r hfp) X

end Coherence

/-- A monoidal functor on finitely presented modules has a monoidal
filtered-colimit-preserving extension to all modules. -/
@[stacks 0GP5 "monoidal extension"]
theorem filteredColimitExtension_monoidal
    (F : FinitelyPresentedModuleCat.{u, max u v} R ⥤
      FinitelyPresentedModuleCat.{w, max w x} S)
    [F.Monoidal]
    (E : FilteredColimitExtension R
      (F ⋙ (finitelyPresentedModule.{w, max w x} S).ι)) :
    ∃ h : E.functor.Monoidal,
      letI := h
      NatTrans.IsMonoidal E.iso.hom := by
  let P := finitelyPresentedModule.{u, max u v} R
  let G := P.ι ⋙ E.functor
  let : G.Monoidal := Functor.Monoidal.transport E.iso.symm
  have he : NatTrans.IsMonoidal E.iso.hom := by
    let : NatTrans.IsMonoidal E.iso.symm.hom :=
      Functor.Monoidal.natTransIsMonoidal_of_transport E.iso.symm
    exact inferInstanceAs (NatTrans.IsMonoidal E.iso.symm.inv)
  have := tensorObjBifunctor_preservesFilteredColimits E.functor
  have := objTensorBifunctor_preservesFilteredColimits E.functor
  have := tensorObjBifunctor_obj_preservesFilteredColimits E.functor
  have := objTensorBifunctor_obj_preservesFilteredColimits E.functor
  obtain ⟨β, hβ⟩ := exists_iso_of_restriction₂.{u, v} R (tensorObjBifunctor E.functor)
    (objTensorBifunctor E.functor) (fun X Y => Functor.Monoidal.μIso G X Y)
    (fun f Y => Functor.LaxMonoidal.μ_natural_left (F := G) f Y)
    (fun X _ _ f => Functor.LaxMonoidal.μ_natural_right (F := G) X f)
  have μ_fac (X Y : P.FullSubcategory) :
      (bifunctorμ β X.obj Y.obj).hom = Functor.LaxMonoidal.μ G X Y :=
    hβ X Y
  let ε : 𝟙_ (ModuleCat.{max w x} S) ≅ E.functor.obj (𝟙_ (ModuleCat.{max u v} R)) :=
    Functor.Monoidal.εIso G
  let c : E.functor.CoreMonoidal := {
    εIso := ε
    μIso := bifunctorμ β
    μIso_hom_natural_left f Z := NatTrans.congr_app (β.hom.naturality f) Z
    μIso_hom_natural_right X f := (β.hom.app X).naturality f
    associativity := bifunctorμ_associativity E.functor β fun X Y Z => by
      have h := Functor.LaxMonoidal.associativity (F := G) X Y Z
      simp only [← μ_fac] at h
      exact h
    left_unitality := bifunctorμ_left_unitality E.functor β ε fun Y => by
      have h := Functor.LaxMonoidal.left_unitality (F := G) Y
      rwa [← μ_fac] at h
    right_unitality := bifunctorμ_right_unitality E.functor β ε fun Y => by
      have h := Functor.LaxMonoidal.right_unitality (F := G) Y
      rwa [← μ_fac] at h }
  let : E.functor.Monoidal := c.toMonoidal
  refine ⟨c.toMonoidal, ?_⟩
  refine { unit := ?_, tensor := ?_ }
  · change (ε.hom ≫ E.functor.map (𝟙 _)) ≫ E.iso.hom.app (𝟙_ P.FullSubcategory) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact he.unit
  · intro X Y
    change ((bifunctorμ β X.obj Y.obj).hom ≫ E.functor.map (𝟙 _)) ≫ E.iso.hom.app (X ⊗ Y) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, μ_fac]
    exact he.tensor X Y

end ModuleCat
