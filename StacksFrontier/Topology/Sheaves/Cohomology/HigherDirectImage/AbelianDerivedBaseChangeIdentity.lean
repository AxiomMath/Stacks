module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting

/-!
# The identity law for the derived base change map

`Stacks.Cohomology.BaseChange.derived` descends a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` of
underived composites to the bounded below right derived functors. For a commutative square

```
A --V--> A
|P        |P
v         v
B --U--> B
```

with `U` exact, whose horizontal legs are isomorphic to the identity, `cU : U ≅ 𝟭 ℬ` and
`cV : V ≅ 𝟭 𝒜`, and whose comparison `τ` is the one those isomorphisms force at each object of
`𝒜`, the derived comparison is the one `R(U) ≅ 𝟭` and `R(V) ≅ 𝟭` force.

## Main definitions

* `Stacks.Cohomology.BaseChange.derivedId`: the comparison the two derived identity
  isomorphisms force, as a transformation `RP ⋙ RU ⟶ RV ⋙ RP`.

## Main results

* `Stacks.Cohomology.BaseChange.mate_app`: the components of `Stacks.Cohomology.BaseChange.mate`.
* `Stacks.Cohomology.BaseChange.mate_id_app`: when the comparison of the composite right adjoints
  is the one two identity isomorphisms force, the mate is the one the corresponding isomorphisms
  of the left adjoints force.
* `Stacks.Cohomology.BaseChange.idLaw_mapHomologicalComplex_app`,
  `Stacks.Cohomology.BaseChange.idLaw_mapHomotopyCategory_app`,
  `Stacks.Cohomology.BaseChange.mapPlus_idLaw_app` and
  `Stacks.Cohomology.BaseChange.mapSquarePlus_idLaw_app`: the degreewise image of an identity
  law is the identity law of the degreewise images, on complexes, on the homotopy category, and
  on the bounded below homotopy category in the two forms `mapPlus` and `mapSquarePlus`.
* `Stacks.Cohomology.BaseChange.derived_id` and
  `Stacks.Cohomology.BaseChange.derived_id_app`: the identity law for the derived comparison, as
  an identity of natural transformations and evaluated at an object.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### The underived identity law for a mate -/

section MateId

variable {A B : Type*} [Category* A] [Category* B]

/-- The components of `Stacks.Cohomology.BaseChange.mate`: the unit of the second adjunction,
then the given comparison, then the counit of the first. -/
theorem mate_app {C D : Type*} [Category* C] [Category* D] {G : B ⥤ D} {P : D ⥤ B}
    (adj : G ⊣ P) {G' : A ⥤ C} {P' : C ⥤ A} (adj' : G' ⊣ P') (F : A ⥤ B) (F' : C ⥤ D)
    (e : P' ⋙ F ≅ F' ⋙ P) (X : A) :
    (mate adj adj' F F' e).app X =
      G.map (F.map (adj'.unit.app X)) ≫ G.map (e.hom.app (G'.obj X)) ≫
        adj.counit.app (F'.obj (G'.obj X)) := by
  simp [mate, Functor.associator, Functor.rightUnitor]

/-- **The underived identity law for a mate.** Let `U ⊣ U'` and `V ⊣ V'` be adjunctions of
endofunctors, let `P : 𝒜 ⥤ ℬ`, and let the comparison `κ : V' ⋙ P ≅ P ⋙ U'` of the two
composite right adjoints be the one that isomorphisms `cU : U' ≅ 𝟭 ℬ` and `cV : V' ≅ 𝟭 𝒜` force.
Then the mate `P ⋙ U ⟶ V ⋙ P` is the one the corresponding isomorphisms
`CategoryTheory.Adjunction.leftAdjointIdIso` of the left adjoints force. -/
theorem mate_id_app {U U' : B ⥤ B} (adjU : U ⊣ U') {V V' : A ⥤ A} (adjV : V ⊣ V')
    (P : A ⥤ B) (κ : V' ⋙ P ≅ P ⋙ U') (cU : U' ≅ 𝟭 B) (cV : V' ≅ 𝟭 A)
    (hκ : ∀ X, κ.hom.app X = P.map (cV.hom.app X) ≫ cU.inv.app (P.obj X)) (X : A) :
    (mate adjU adjV P P κ).app X =
      (adjU.leftAdjointIdIso cU).hom.app (P.obj X) ≫
        P.map ((adjV.leftAdjointIdIso cV).inv.app X) := by
  have hnat := (adjU.leftAdjointIdIso cU).hom.naturality
    (P.map (adjV.unit.app X ≫ cV.hom.app (V.obj X)))
  dsimp only [Functor.id_map, Functor.id_obj] at hnat
  rw [Adjunction.leftAdjointIdIso_inv_app, ← hnat, Adjunction.leftAdjointIdIso_hom_app,
    mate_app, hκ (V.obj X)]
  simp only [Functor.map_comp, Category.assoc]

end MateId

/-! ### The identity law, degreewise -/

section IdLawComplexes

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  {P : A ⥤ B} {U : B ⥤ B} {V : A ⥤ A} [P.Additive] [U.Additive] [V.Additive]
  (cU : U ≅ 𝟭 B) (cV : V ≅ 𝟭 A) (τ : P ⋙ U ⟶ V ⋙ P)

/-- **An identity law between squares of additive functors, applied degreewise to a complex.**
If the identity law holds at each object of the source category, the same identity holds for
the induced transformations on complexes. -/
theorem idLaw_mapHomologicalComplex_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (L : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex τ c).app L =
      (NatTrans.mapHomologicalComplex cU.hom c).app ((P.mapHomologicalComplex c).obj L) ≫
        (P.mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex cV.inv c).app L) := by
  ext i
  simpa using hτ (L.X i)

/-- **The identity law on the homotopy category.** The image of
`idLaw_mapHomologicalComplex_app` under the quotient by homotopy. -/
theorem idLaw_mapHomotopyCategory_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (M : HomotopyCategory A c) :
    (NatTrans.mapHomotopyCategory τ c).app M =
      (NatTrans.mapHomotopyCategory cU.hom c).app ((P.mapHomotopyCategory c).obj M) ≫
        (P.mapHomotopyCategory c).map
          ((NatTrans.mapHomotopyCategory cV.inv c).app M) := by
  obtain ⟨L⟩ := M
  exact (congrArg (HomotopyCategory.quotient B c).map
    (idLaw_mapHomologicalComplex_app cU cV τ c hτ L)).trans (Functor.map_comp _ _ _)

end IdLawComplexes

section IdLawPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (P : A ⥤ B) (U : B ⥤ B) (V : A ⥤ A) [P.Additive] [U.Additive] [V.Additive]
  (cU : U ≅ 𝟭 B) (cV : V ≅ 𝟭 A) (τ : P ⋙ U ⟶ V ⋙ P)

/-- **The degreewise image on `HomotopyCategory.Plus` of an identity law between squares of
additive functors is the identity law of the degreewise images**, with `cU` and `cV` replaced
by their degreewise images. -/
theorem mapPlus_idLaw_app
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (K : HomotopyCategory.Plus A) :
    (mapPlus τ).app K =
      (mapPlus cU.hom).app (P.mapHomotopyCategoryPlus.obj K) ≫
        P.mapHomotopyCategoryPlus.map ((mapPlus cV.inv).app K) := by
  ext
  exact idLaw_mapHomotopyCategory_app cU cV τ (ComplexShape.up ℤ) hτ K.obj

/-- **The identity law for `mapSquarePlus`**, written with the degreewise identity comparisons
`CategoryTheory.Functor.mapHomotopyCategoryPlusIdIsoOf` of the two horizontal legs. -/
theorem mapSquarePlus_idLaw_app
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (K : HomotopyCategory.Plus A) :
    (mapSquarePlus P P U V τ).app K =
      (Functor.mapHomotopyCategoryPlusIdIsoOf U cU).hom.app
          (P.mapHomotopyCategoryPlus.obj K) ≫
        P.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusIdIsoOf V cV).inv.app K) := by
  rw [Functor.mapHomotopyCategoryPlusIdIsoOf_hom_app,
    Functor.mapHomotopyCategoryPlusIdIsoOf_inv_app]
  exact (mapSquarePlus_app P P U V τ K).trans
    (mapPlus_idLaw_app P U V cU cV τ hτ K)

end IdLawPlus

/-! ### The identity law for the descent -/

section Identity

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [EnoughInjectives B]
  (P : A ⥤ B) (U : B ⥤ B) (V : A ⥤ A)
  [P.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (cU : U ≅ 𝟭 B) (cV : V ≅ 𝟭 A) (τ : P ⋙ U ⟶ V ⋙ P)

/-- **The comparison the derived identity isomorphisms force**: the comparison `RU ≅ 𝟭` on the
base, then the comparison `𝟭 ≅ RV` on the source, read through `RP`. -/
def derivedId :
    P.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus ⟶
      V.rightDerivedFunctorPlus ⋙ P.rightDerivedFunctorPlus :=
  Functor.whiskerLeft P.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom ≫
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusIdIsoOf V cV).inv
      P.rightDerivedFunctorPlus

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- The components of `Stacks.Cohomology.BaseChange.derivedId`. -/
theorem derivedId_app (M : DerivedCategory.Plus A) :
    (derivedId P U V cU cV).app M =
      (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom.app
          (P.rightDerivedFunctorPlus.obj M) ≫
        P.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusIdIsoOf V cV).inv.app M) :=
  rfl

/-- After the derived-functor unit of `RP`, the forced derived comparison is the `onHomotopy` of
the square. -/
theorem onHomotopy_eq_unit_comp_derivedId_app
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (K : HomotopyCategory.Plus A) :
    (onHomotopy P P U V τ (asIso U.rightDerivedFunctorPlusUnit)).app K =
      U.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlusUnit.app K) ≫
        (derivedId P U V cU cV).app (DerivedCategory.Plus.Qh.obj K) := by
  have hnat0 := (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom.naturality
    (P.rightDerivedFunctorPlusUnit.app K)
  have hfacU : (asIso U.rightDerivedFunctorPlusUnit).hom.app
        (P.mapHomotopyCategoryPlus.obj K) ≫
      (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom.app
        (DerivedCategory.Plus.Qh.obj (P.mapHomotopyCategoryPlus.obj K)) =
    DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusIdIsoOf U cU).hom.app
      (P.mapHomotopyCategoryPlus.obj K)) :=
    Functor.rightDerivedFunctorPlusIdIsoOf_fac U cU (P.mapHomotopyCategoryPlus.obj K)
  have hfacU' : (asIso U.rightDerivedFunctorPlusUnit).inv.app
        (P.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusIdIsoOf U cU).hom.app
        (P.mapHomotopyCategoryPlus.obj K)) =
    (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom.app
      (DerivedCategory.Plus.Qh.obj (P.mapHomotopyCategoryPlus.obj K)) := by
    rw [← hfacU, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hfacV := Functor.rightDerivedFunctorPlusIdIsoOf_inv_app V cV K
  have hnatP := P.rightDerivedFunctorPlusUnit.naturality
    ((Functor.mapHomotopyCategoryPlusIdIsoOf V cV).inv.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hnatP
  rw [onHomotopy_app_mapSquarePlus, mapSquarePlus_idLaw_app P U V cU cV τ hτ K, derivedId_app,
    reassoc_of% hnat0, ← hfacU', hfacV]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnatP]

/-- **The identity law for the derived base change comparison.** For a commutative square of
additive functors whose two horizontal legs are isomorphic to the identity, the descent of the
comparison those isomorphisms force is the comparison the derived identity isomorphisms force. -/
theorem derived_id
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X)) :
    derived P P U V τ (asIso U.rightDerivedFunctorPlusUnit) = derivedId P U V cU cV := by
  let _ : (P.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.whiskerRight P.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
      (fun K ↦ by dsimp; infer_instance)
  refine Functor.rightDerived_ext (P.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus)
    (Functor.whiskerRight P.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A) _ _ _ ?_
  rw [Category.assoc, derived_fac]
  refine NatTrans.ext (funext fun K => ?_)
  simpa [Functor.associator] using
    onHomotopy_eq_unit_comp_derivedId_app P U V cU cV τ hτ K

/-- **The identity law for the derived base change comparison, evaluated at an object.** -/
theorem derived_id_app
    (hτ : ∀ X, τ.app X = cU.hom.app (P.obj X) ≫ P.map (cV.inv.app X))
    (M : DerivedCategory.Plus A) :
    (derived P P U V τ (asIso U.rightDerivedFunctorPlusUnit)).app M =
      (Functor.rightDerivedFunctorPlusIdIsoOf U cU).hom.app
          (P.rightDerivedFunctorPlus.obj M) ≫
        P.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusIdIsoOf V cV).inv.app M) := by
  rw [derived_id P U V cU cV τ hτ, derivedId_app]

end Identity

end Stacks.Cohomology.BaseChange

end
