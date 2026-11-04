module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedTilde
import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness

/-!
# Derived global sections of complexes with quasi-coherent cohomology

Let `R` be a commutative ring. This file assembles the two functors between `D(R)` and
`D_QCoh(𝒪_{Spec R})` whose adjunction is the content of Stacks 06Z0: derived sheafification
`AlgebraicGeometry.derivedTilde`, which is already available, and the restriction of `A`-linear
unbounded derived global sections `RΓ(Spec R, -)` to the complexes with quasi-coherent
cohomology, which is defined here. The latter is exact, being the composition of the inclusion
of a triangulated subcategory with a right derived functor along the quasi-isomorphisms.

Also recorded here are the degreewise comparison maps that normalize the derived adjunction: the
canonical map from the complex of global sections of a complex of `𝒪_X`-modules to the derived
global sections of its image in `D(𝒪_X)`, and the degreewise sheafification–sections unit.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` — `RΓ(Spec R, -)` restricted to
  `D_QCoh(𝒪_{Spec R})`.
* `AlgebraicGeometry.globalSectionsComplexComparison` and
  `AlgebraicGeometry.globalSectionsComplexComparisonNatTrans` — the canonical comparison
  `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))`, objectwise and as a natural transformation.
* `AlgebraicGeometry.globalSectionsCyclesToHomology` — a global cycle of a complex gives a
  cohomology class of the complex of global sections.
* `AlgebraicGeometry.tildeGlobalSectionsComplexUnit` — the degreewise
  sheafification–sections unit.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOver_isTriangulated` — `RΓ(X, -)` is exact.
* `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent_isTriangulated` — **Stacks 06Z0**:
  derived global sections is exact on complexes with quasi-coherent cohomology.

## Implementation notes

The two derived categories are taken at free `[HasDerivedCategory.{w₁} (Spec R).Modules]` and
`[HasDerivedCategory.{w₂} (ModuleCat.{u} R)]` binders, with independent morphism universes, so
that a consumer may instantiate them at whichever model it must meet; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`. The default, supplied by
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`, is the
locally small one.

`AlgebraicGeometry.globalSectionsOver (𝟙 (Spec R))` and `AlgebraicGeometry.moduleSpecΓFunctor`
are not merely isomorphic but *equal*: the structure morphism of the identity of `Spec R`
restricts scalars along `(Scheme.ΓSpecIso R).inv` composed with an identity, which is the ring
map `moduleSpecΓFunctor` uses. So `moduleSpecΓIsoGlobalSectionsOver` is the identity
isomorphism, and the degreewise unit below is the degreewise
`AlgebraicGeometry.tilde.adjunction` unit.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace AlgebraicGeometry

/-! ### Exactness of unbounded derived global sections -/

section Triangulated

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- The canonical shift structure on `A`-linear unbounded derived global sections, the one
carried by every right derived functor along the quasi-isomorphisms. -/
instance derivedGlobalSectionsOver_commShift : (derivedGlobalSectionsOver f).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedGlobalSectionsOver f)
    (derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ

/-- `A`-linear unbounded derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` is an exact functor
of triangulated categories: it is a right derived functor along the quasi-isomorphisms out of a
category with enough K-injective complexes. -/
instance derivedGlobalSectionsOver_isTriangulated :
    (derivedGlobalSectionsOver f).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (Scheme.Modules.exists_quasiIso_isKInjective X) _ _ _

/-! ### The degreewise comparison maps -/

/-- The canonical comparison from the complex of `A`-linear global sections of a complex of
`𝒪_X`-modules to the derived global sections of the complex it represents in `D(𝒪_X)`. -/
def globalSectionsComplexComparison (K : CochainComplex X.Modules ℤ) :
    DerivedCategory.Q.obj
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (derivedGlobalSectionsOver f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app _ ≫
    DerivedCategory.Qh.map
      (((globalSectionsOver f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
    (derivedGlobalSectionsOverUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K) ≫
    (derivedGlobalSectionsOver f).map
      ((DerivedCategory.quotientCompQhIso X.Modules).hom.app K)

/-- `globalSectionsComplexComparison` as a natural transformation
`Γ(X, -) ⋙ Q ⟶ Q ⋙ RΓ(X, -)`. -/
def globalSectionsComplexComparisonNatTrans :
    (globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedGlobalSectionsOver f :=
  Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (((globalSectionsOver f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv)
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ))
      (derivedGlobalSectionsOverUnit f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso X.Modules).hom
      (derivedGlobalSectionsOver f)

/-- The component of `globalSectionsComplexComparisonNatTrans` at a complex `K` is
`globalSectionsComplexComparison f K`. -/
@[simp]
lemma globalSectionsComplexComparisonNatTrans_app (K : CochainComplex X.Modules ℤ) :
    (globalSectionsComplexComparisonNatTrans f).app K = globalSectionsComplexComparison f K := by
  simp [globalSectionsComplexComparisonNatTrans, globalSectionsComplexComparison]

/-- A global section of the sheaf of cycles of a complex of `𝒪_X`-modules gives a degree-`n`
cohomology class of the complex of `A`-linear global sections. -/
def globalSectionsCyclesToHomology (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (globalSectionsOver f).obj (K.cycles n) ⟶
      (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n := by
  let F := globalSectionsOver f
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  exact L.liftCycles (F.map (K.iCycles n)) (n + 1) (by simp)
    (by simp [L, ← F.map_comp]) ≫ L.homologyπ n

end Triangulated

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- Global sections of `𝒪_{Spec R}`-modules read as an `R`-module through the identity of
`Spec R` is global sections of `𝒪_{Spec R}`-modules: the two functors are equal. -/
def moduleSpecΓIsoGlobalSectionsOver :
    moduleSpecΓFunctor (R := R) ≅ globalSectionsOver (𝟙 (Spec R)) :=
  Iso.refl _

/-- The sheafification–sections unit of `AlgebraicGeometry.tilde.adjunction`, applied degreewise
to cochain complexes of `R`-modules. -/
def tildeGlobalSectionsComplexUnit :
    𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex
      ((tilde.adjunction (R := R)).unit ≫
        Functor.whiskerLeft (tilde.functor R) (moduleSpecΓIsoGlobalSectionsOver R).hom)
      (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor R ⋙ globalSectionsOver (𝟙 (Spec R)))) (ComplexShape.up ℤ)).inv

/-- The degreewise sheafification–sections unit is an isomorphism: `Γ(Spec R, M̃) = M` already
for a single module, and the statement is degreewise. -/
instance tildeGlobalSectionsComplexUnit_isIso : IsIso (tildeGlobalSectionsComplexUnit R) := by
  have h : IsIso ((tilde.adjunction (R := R)).unit ≫
      Functor.whiskerLeft (tilde.functor R) (moduleSpecΓIsoGlobalSectionsOver R).hom) :=
    inferInstance
  have h' : IsIso (NatTrans.mapHomologicalComplex ((tilde.adjunction (R := R)).unit ≫
      Functor.whiskerLeft (tilde.functor R) (moduleSpecΓIsoGlobalSectionsOver R).hom)
      (ComplexShape.up ℤ)) :=
    (NatIso.mapHomologicalComplex (asIso ((tilde.adjunction (R := R)).unit ≫
      Functor.whiskerLeft (tilde.functor R) (moduleSpecΓIsoGlobalSectionsOver R).hom))
      (ComplexShape.up ℤ)).isIso_hom
  dsimp only [tildeGlobalSectionsComplexUnit]
  infer_instance

/-- **Stacks 06Z0.** Derived global sections on an affine scheme, restricted to the complexes
with quasi-coherent cohomology: `D_QCoh(𝒪_{Spec R}) ⥤ D(R)`. -/
-- NO `@[stacks 06Z0]` ATTRIBUTE HERE, DELIBERATELY -- but not because the tag is open: it is
-- proved. That this functor is an equivalence, which is what the tag asserts, is
-- `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent_isEquivalence` of
-- `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`, and the full
-- covering set of the tag is listed in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/DerivedTilde.lean`. The functor itself is the OBJECT the tag
-- speaks about, not a clause of its statement, so an attribute here would report 06Z0 a second
-- time, on the strength of a definition.
def derivedGlobalSectionsQuasicoherent :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
      derivedGlobalSectionsOver (𝟙 (Spec R))

/-- **Stacks 06Z0.** Derived global sections commutes with the shift on complexes with
quasi-coherent cohomology, for the canonical shift structure on a right derived functor. -/
instance derivedGlobalSectionsQuasicoherent_commShift :
    (derivedGlobalSectionsQuasicoherent R).CommShift ℤ :=
  inferInstanceAs (((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
      derivedGlobalSectionsOver (𝟙 (Spec R))).CommShift ℤ)

/-- **Stacks 06Z0.** Derived global sections is exact on complexes with quasi-coherent
cohomology: it is the inclusion of a triangulated subcategory followed by the exact functor
`RΓ(Spec R, -)`. -/
instance derivedGlobalSectionsQuasicoherent_isTriangulated :
    (derivedGlobalSectionsQuasicoherent R).IsTriangulated :=
  inferInstanceAs (((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
      derivedGlobalSectionsOver (𝟙 (Spec R))).IsTriangulated)

end AlgebraicGeometry

end
