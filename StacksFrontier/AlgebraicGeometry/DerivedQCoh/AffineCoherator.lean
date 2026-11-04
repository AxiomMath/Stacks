module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPushforward

/-!
# The coherator on an affine scheme

Let `X = Spec A` be an affine scheme. The inclusion of the quasi-coherent `𝒪_X`-modules into all
`𝒪_X`-modules has a right adjoint `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)`, the coherator
([Stacks, Tag 077P]). On an affine scheme it is computed by global sections: `Q_X(F)` is the
quasi-coherent module `Γ(X, F)^~` attached to the `A`-module of global sections of `F`. Deriving
this identification gives the derived coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))`, which sends `E` to
the complex of quasi-coherent modules attached to `RΓ(X, E) ∈ D(A)`; and restricted to the
complexes with quasi-coherent cohomology it is a quasi-inverse to the comparison functor of
[Stacks, Tag 06VT]. These are the three assertions of [Stacks, Tag 08D9].

The proof of part (1) is the source's: `ι ⊣ Q_X` and `~ ⊣ Γ(X, -)` are adjunctions, the
associated-sheaf functor is an equivalence `Mod(A) ≌ QCoh(𝒪_X)` onto the quasi-coherent modules
([Stacks, Tag 01I7], Mathlib's `AlgebraicGeometry.tildeEquiv`), and composing the second adjunction
with that equivalence exhibits `Γ(X, -) ⋙ ~` as a right adjoint of `ι`; a right adjoint is unique
up to canonical isomorphism. Part (2) derives part (1): both sides are total right derived functors
of isomorphic functors, so the uniqueness of right derived functors applies, derived
sheafification being an equivalence of derived categories and hence a left adjoint. Part (3) is the
source's reduction to [Stacks, Tag 06Z0]: the derived Spec–Γ adjunction of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction`, transported along the equivalence
`Stacks.DerivedQCoh.derivedTildeEquiv` and along
`Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso`, becomes an adjunction between the
comparison functor and the restriction of `RQ_X`; since the comparison functor is an equivalence
(`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`), its right adjoint is a
quasi-inverse.

## Main definitions

* `Stacks.DerivedQCoh.derivedCoherator` — the derived coherator
  `RQ_X : D(𝒪_{Spec R}) ⥤ D(QCoh(𝒪_{Spec R}))`, the total right derived functor of the coherator.
* `Stacks.DerivedQCoh.derivedCoheratorQCoh` — its restriction to `D_QCoh(𝒪_{Spec R})`.
* `Stacks.DerivedQCoh.derivedCoheratorComparisonAdjunction` — the comparison functor of
  [Stacks, Tag 06VT] is left adjoint to that restriction.

## Main results

* `Stacks.DerivedQCoh.coheratorSpecIso` — **08D9 part (1)**: `Q_X ≅ Γ(X, -) ⋙ ~`.
* `Stacks.DerivedQCoh.derivedCoheratorIso` — **08D9 part (2)**: `RQ_X ≅ RΓ(X, -) ⋙ ~`.
* `Stacks.DerivedQCoh.derivedCoheratorEquivalence` — **08D9 part (3)**: the equivalence
  `D(QCoh(𝒪_{Spec R})) ≌ D_QCoh(𝒪_{Spec R})` whose functor is the comparison functor of
  [Stacks, Tag 06VT] and whose inverse is the restriction of `RQ_X`.

## Implementation notes

Parts (1) and (2) are stated at **free** `HasDerivedCategory` binders, with independent morphism
universes for `D(𝒪_{Spec R})`, `D(R)` and `D(QCoh(𝒪_{Spec R}))`, as in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/FlatPushforward.lean`: the standard model
puts the morphisms of `D(𝒪_X)` a universe above its objects, which makes the direct sums of
Stacks 09IS and 0A9A false rather than merely unavailable, so no declaration about `D(𝒪_X)` may
pin it. Part (3) is at the locally small models of
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, `ModuleCat.hasDerivedCategory` and
`Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent`, which instance search supplies: its input
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` is proved there and nowhere else.

The existence of `RQ_X` on the *whole* unbounded derived category needs no boundedness or
finiteness hypothesis: `𝒪_X`-modules are Grothendieck abelian, so every cochain complex has a
K-injective resolution and `AlgebraicGeometry.Scheme.Modules.hasRightDerivedFunctor` derives every
functor out of `K(𝒪_X)`.

The inclusion of the quasi-coherent modules is spelled `AlgebraicGeometry.quasicoherentModulesι`,
with codomain `AlgebraicGeometry.Scheme.Modules X` rather than `SheafOfModules X.ringCatSheaf`:
the two are definitionally equal but carry separately declared `Category` instances, and the
coherator is stated in the first spelling.

## References

* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe w₁ w₂ w₃ u

namespace Stacks.DerivedQCoh

variable (R : CommRingCat.{u})

/-! ### Part (1): the coherator of an affine scheme -/

/-- **[Stacks, Tag 08D9] part (1).** On the affine scheme `X = Spec R` the coherator
`Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` sends a module `F` to the quasi-coherent module `Γ(X, F)^~` attached
to the `R`-module of global sections of `F`.

Both `Q_X` and `Γ(X, -) ⋙ ~` are right adjoint to the inclusion of the quasi-coherent modules:
for the second, compose the sheafification–sections adjunction `~ ⊣ Γ(X, -)` with the equivalence
`Mod(R) ≌ QCoh(𝒪_X)` of `AlgebraicGeometry.tildeEquiv`. A right adjoint is unique up to a unique
natural isomorphism. -/
@[stacks 08D9 "part (1): the coherator on an affine scheme"]
def coheratorSpecIso :
    coherator (Spec R) ≅ moduleSpecΓFunctor (R := R) ⋙ (tildeEquiv (R := R)).functor := by
  have htilde : (tildeEquiv (R := R)).functor ⋙ quasicoherentModulesι (Spec R) ≅
      tilde.functor R :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have hleft : (tildeEquiv (R := R)).inverse ⋙
      ((tildeEquiv (R := R)).functor ⋙ quasicoherentModulesι (Spec R)) ≅
      quasicoherentModulesι (Spec R) :=
    (Functor.associator (tildeEquiv (R := R)).inverse (tildeEquiv (R := R)).functor
        (quasicoherentModulesι (Spec R))).symm ≪≫
      Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso
        (quasicoherentModulesι (Spec R)) ≪≫
      Functor.leftUnitor _
  exact (Adjunction.rightAdjointUniq
    ((((tildeEquiv (R := R)).symm.toAdjunction).comp
      ((tilde.adjunction (R := R)).ofNatIsoLeft htilde.symm)).ofNatIsoLeft hleft)
    (coheratorAdjunction (Spec R))).symm

/-! ### Part (2): the derived coherator -/

section Derived

variable [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w₃} (Scheme.QuasicoherentModules (Spec R))]

/-- The coherator of the affine scheme `Spec R` read on the homotopy category of cochain complexes
of `𝒪_{Spec R}`-modules, with values in `D(QCoh(𝒪_{Spec R}))`. This is the functor whose right
derived functor is `Stacks.DerivedQCoh.derivedCoherator`. -/
def homotopyCoherator : HomotopyCategory (Spec R).Modules (ComplexShape.up ℤ) ⥤
    DerivedCategory (Scheme.QuasicoherentModules (Spec R)) :=
  (coherator (Spec R)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The coherator of an affine scheme has an unbounded right derived functor: `𝒪_X`-modules are
Grothendieck abelian, so every cochain complex has a K-injective resolution. -/
instance homotopyCoherator_hasRightDerivedFunctor :
    (homotopyCoherator R).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor (Spec R) _

/-- **The derived coherator** `RQ_X : D(𝒪_{Spec R}) ⥤ D(QCoh(𝒪_{Spec R}))` of the affine scheme
`X = Spec R`: the total right derived functor of the coherator on the whole unbounded derived
category. -/
def derivedCoherator : DerivedCategory (Spec R).Modules ⥤
    DerivedCategory (Scheme.QuasicoherentModules (Spec R)) :=
  (homotopyCoherator R).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ))

/-- The canonical comparison from the termwise coherator to the derived coherator. -/
def derivedCoheratorUnit :
    homotopyCoherator R ⟶ DerivedCategory.Qh ⋙ derivedCoherator R :=
  (homotopyCoherator R).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ))

/-- The comparison exhibits `Stacks.DerivedQCoh.derivedCoherator` as the right derived functor of
the coherator, which is the universal property that characterizes it. -/
instance derivedCoherator_isRightDerivedFunctor :
    (derivedCoherator R).IsRightDerivedFunctor (derivedCoheratorUnit R)
      (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs (((homotopyCoherator R).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homotopyCoherator R).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ))) _)

/-- **[Stacks, Tag 08D9] part (2).** On the affine scheme `X = Spec R` the derived coherator
`RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` sends an object `E` to the complex of quasi-coherent modules
attached to the object `RΓ(X, E)` of `D(R)`.

Both sides are right derived functors of the two isomorphic functors of
`Stacks.DerivedQCoh.coheratorSpecIso`: the right-hand side because derived sheafification
`D(R) ≌ D(QCoh(𝒪_X))` is an equivalence, hence a left adjoint, and postcomposing a right derived
functor with a left adjoint again gives a right derived functor. A right derived functor is unique
up to a unique natural isomorphism. -/
@[stacks 08D9 "part (2): the derived coherator"]
def derivedCoheratorIso :
    derivedCoherator R ≅
      derivedGlobalSectionsOver (𝟙 (Spec R)) ⋙ (derivedTildeEquiv R).functor := by
  have e₀ : coherator (Spec R) ≅
      globalSectionsOver (𝟙 (Spec R)) ⋙ (tildeEquiv (R := R)).functor :=
    coheratorSpecIso R ≪≫
      Functor.isoWhiskerRight (moduleSpecΓIsoGlobalSectionsOver R)
        (tildeEquiv (R := R)).functor
  have eHC : (coherator (Spec R)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (globalSectionsOver (𝟙 (Spec R)) ⋙
        (tildeEquiv (R := R)).functor).mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e₀.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have eComp : (globalSectionsOver (𝟙 (Spec R))).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (tildeEquiv (R := R)).functor.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (globalSectionsOver (𝟙 (Spec R)) ⋙
        (tildeEquiv (R := R)).functor).mapHomotopyCategory (ComplexShape.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso
      (Iso.refl (globalSectionsOver (𝟙 (Spec R)) ⋙ (tildeEquiv (R := R)).functor))
      (ComplexShape.up ℤ)
  have eSrc : homotopyCoherator R ≅
      homotopyGlobalSectionsOver (𝟙 (Spec R)) ⋙ (derivedTildeEquiv R).functor :=
    Functor.isoWhiskerRight eHC DerivedCategory.Qh ≪≫
      Functor.isoWhiskerRight eComp.symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((globalSectionsOver (𝟙 (Spec R))).mapHomotopyCategory (ComplexShape.up ℤ))
        (tildeEquiv (R := R)).functor.mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.rightDerivedNatIso (derivedCoherator R)
    (derivedGlobalSectionsOver (𝟙 (Spec R)) ⋙ (derivedTildeEquiv R).functor)
    (derivedCoheratorUnit R)
    (Functor.whiskerRight (derivedGlobalSectionsOverUnit (𝟙 (Spec R)))
        (derivedTildeEquiv R).functor ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (Spec R).Modules (ComplexShape.up ℤ)) eSrc

/-- **The derived coherator restricted to `D_QCoh(𝒪_{Spec R})`**, the complexes of
`𝒪_{Spec R}`-modules all of whose cohomology sheaves are quasi-coherent. This is the functor
asserted to be a quasi-inverse to the comparison functor of [Stacks, Tag 06VT]. -/
def derivedCoheratorQCoh :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      DerivedCategory (Scheme.QuasicoherentModules (Spec R)) :=
  (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙ derivedCoherator R

end Derived

/-! ### Part (3): the derived coherator is a quasi-inverse to the comparison functor -/

/-- **The comparison functor of [Stacks, Tag 06VT] is left adjoint to the derived coherator on
`D_QCoh(𝒪_{Spec R})`.**

Compose the derived Spec–Γ adjunction `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction`,
whose left adjoint is derived sheafification `D(R) ⥤ D_QCoh(𝒪_{Spec R})`, with the equivalence
`Stacks.DerivedQCoh.derivedTildeEquiv : D(R) ≌ D(QCoh(𝒪_{Spec R}))`. The resulting left adjoint is
the comparison functor, by `Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso`, and the
resulting right adjoint is `RΓ(Spec R, -) ⋙ ~`, which is the restriction of `RQ_X` by
`Stacks.DerivedQCoh.derivedCoheratorIso`. -/
def derivedCoheratorComparisonAdjunction :
    derivedQuasicoherentComparison.{u} (Spec R) ⊣ derivedCoheratorQCoh R := by
  have iso₂ : (derivedTildeEquiv.{u, u} R).inverse ⋙ derivedTilde R ≅
      derivedQuasicoherentComparison.{u} (Spec R) :=
    Functor.isoWhiskerLeft (derivedTildeEquiv.{u, u} R).inverse
        (derivedTildeEquivCompComparisonIso R).symm ≪≫
      (Functor.associator (derivedTildeEquiv.{u, u} R).inverse
        (derivedTildeEquiv.{u, u} R).functor
        (derivedQuasicoherentComparison.{u} (Spec R))).symm ≪≫
      Functor.isoWhiskerRight (derivedTildeEquiv.{u, u} R).counitIso
        (derivedQuasicoherentComparison.{u} (Spec R)) ≪≫
      Functor.leftUnitor _
  have iso₃ : derivedGlobalSectionsQuasicoherent R ⋙ (derivedTildeEquiv.{u, u} R).functor ≅
      derivedCoheratorQCoh R :=
    Functor.associator
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι)
        (derivedGlobalSectionsOver (𝟙 (Spec R))) (derivedTildeEquiv.{u, u} R).functor ≪≫
      Functor.isoWhiskerLeft _ (derivedCoheratorIso R).symm
  exact ((((derivedTildeEquiv.{u, u} R).symm.toAdjunction).comp
    (derivedTildeQuasicoherentAdjunction R)).ofNatIsoLeft iso₂).ofNatIsoRight iso₃

/-- **[Stacks, Tag 08D9] part (3).** On the affine scheme `X = Spec R` the derived coherator,
restricted to the complexes with quasi-coherent cohomology, is a quasi-inverse to the comparison
functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT]: the two are the two halves of an
equivalence of categories.

The comparison functor is an equivalence by
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`, and
`Stacks.DerivedQCoh.derivedCoheratorComparisonAdjunction` exhibits the restricted derived coherator
as its right adjoint; a right adjoint of an equivalence is its quasi-inverse. -/
@[stacks 08D9 "part (3): quasi-inverse to the comparison functor"]
def derivedCoheratorEquivalence :
    DerivedCategory (Scheme.QuasicoherentModules (Spec R)) ≌
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory :=
  have := derivedQuasicoherentComparison_isEquivalence R
  (derivedQuasicoherentComparison.{u} (Spec R)).asEquivalence.changeInverse
    (Adjunction.rightAdjointUniq
      (derivedQuasicoherentComparison.{u} (Spec R)).asEquivalence.toAdjunction
      (derivedCoheratorComparisonAdjunction R))

/-- The functor of `Stacks.DerivedQCoh.derivedCoheratorEquivalence` is the comparison functor of
[Stacks, Tag 06VT]. -/
@[simp]
lemma derivedCoheratorEquivalence_functor :
    (derivedCoheratorEquivalence R).functor = derivedQuasicoherentComparison.{u} (Spec R) :=
  rfl

/-- The inverse of `Stacks.DerivedQCoh.derivedCoheratorEquivalence` is the derived coherator
restricted to the complexes with quasi-coherent cohomology. -/
@[simp]
lemma derivedCoheratorEquivalence_inverse :
    (derivedCoheratorEquivalence R).inverse = derivedCoheratorQCoh R :=
  rfl

/-- The derived coherator, restricted to the complexes with quasi-coherent cohomology, is an
equivalence of categories onto `D(QCoh(𝒪_{Spec R}))`. -/
instance derivedCoheratorQCoh_isEquivalence : (derivedCoheratorQCoh R).IsEquivalence :=
  (derivedCoheratorEquivalence R).isEquivalence_inverse

end Stacks.DerivedQCoh

end
