module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationFrobeniusExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical action of the geometric Frobenius on `RΓ_c(X_k̄, K)`

Let `k` be a finite field with `q = p ^ f` elements, `X` a scheme over `k`, `j : X ⟶ X̄` a
compactification of `X` over `k` and `k̄` an extension field of `k`.  Following the source,
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`, and the geometric Frobenius `π_X^*` acts on it
through the endomorphism `π̄ = π_{X̄} × id` of `X̄_k̄`.  The map needed is a morphism
`L|_{X̄_k̄} ⟶ Rπ̄_* (L|_{X̄_k̄})` for `L = j_! K`; this file constructs it canonically, as the base
change along `pr : X̄_k̄ ⟶ X̄` of the Frobenius descent isomorphism `L ≅ (π_{X̄})_* L` of
[Stacks, Tag 03SR].

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist` — for a commutative square
  `a ≫ g = g ≫ b` and a transformation `ψ : 𝟭 ⟶ b_*`, the transformation
  `g^{-1} ⟶ a_* ∘ g^{-1}`: the base change morphism `g^{-1} b_* ⟶ a_* g^{-1}` after `g^{-1} ψ`.
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist` — its value for `g = pr`, `a = π̄`,
  `b = π_{X̄}` and `ψ` the Frobenius descent isomorphism of Tag 03SR.
* `Stacks.EtaleCohomology.frobeniusRestrictionDerivedMap` — the induced morphism
  `C|_{X̄_k̄} ⟶ Rπ̄_*(C|_{X̄_k̄})` in the bounded below derived category, for a bounded below
  complex `C` on `X̄`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomology` — the complex
  `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` of the source.
* `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` — the endomorphism `π_X^*` of it.
* `Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusGroup` — the endomorphism `π_X^*` of
  `H^i_c(X_k̄, K)`.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber` — its trace
  `Tr(π_X^* | RΓ_c(X_k̄, K))`, given perfectness.

## Implementation notes

The construction uses no inverse image along `π̄` at all.  Under the adjunction
`pr^{-1} ⊣ pr_*` the wanted map `pr^{-1} L ⟶ π̄_* pr^{-1} L` corresponds to
`L ⟶ pr_* π̄_* pr^{-1} L = (π̄ ≫ pr)_* pr^{-1} L = (pr ≫ π_{X̄})_* pr^{-1} L
 = (π_{X̄})_* pr_* pr^{-1} L`, and that is the Frobenius descent isomorphism `L ⟶ (π_{X̄})_* L`
followed by `(π_{X̄})_*` of the unit.  This is the source's map: `π_X^*` on the cohomology of a
sheaf pulled back from `X̄` is induced by the canonical identification `π_{X̄}^{-1} L ≅ L`.

Unlike `Stacks.EtaleCohomology.compactSupportPullback`, which takes the map `𝟭 ⟶ Rπ̄_*` as an
argument, the endomorphism here is determined by `X`, `j`, `k̄` and the cardinality of `k`.
There is no canonical transformation `𝟭 ⟶ Rπ̄_*` on all of `D⁺(X̄_k̄)`, because `π̄` is not a
power of the absolute Frobenius of `X̄_k̄`; the canonical map exists on objects pulled back from
`X̄`, which are the only ones the source uses.

## References

* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The base change of a transformation `𝟭 ⟶ b_*` -/

section Twist

variable (Λ : Type r) [Ring Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y)
  (w : a ≫ g = g ≫ b)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)

/-- The transformation `L ⟶ g_* a_* g^{-1} L` adjoint to the base change twist: `ψ`, then
`b_*` of the unit of `g^{-1} ⊣ g_*`, then the identification
`b_* g_* = (g ≫ b)_* = (a ≫ g)_* = g_* a_*`. -/
public def etaleModuleBaseChangeTwistAdj :
    𝟭 (EtaleModules.{u, r} Λ Y) ⟶
      (etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleDirectImage.{u, r} Λ a) ⋙
        etaleModuleDirectImage.{u, r} Λ g :=
  ψ ≫ (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (etaleModuleInverseImageAdj.{u, r} Λ g).unit
      (etaleModuleDirectImage.{u, r} Λ b) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ g)
      ((etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom ≫
        (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv) ≫
    (Functor.associator _ _ _).inv

/-- **The base change twist.**  For a commutative square `a ≫ g = g ≫ b` and a transformation
`ψ : 𝟭 ⟶ b_*`, the transformation `g^{-1} ⟶ a_* ∘ g^{-1}`: the adjoint, under
`g^{-1} ⊣ g_*`, of `Stacks.EtaleCohomology.etaleModuleBaseChangeTwistAdj`.  It is the base
change morphism `g^{-1} b_* ⟶ a_* g^{-1}` precomposed with `g^{-1} ψ`. -/
public def etaleModuleBaseChangeTwist :
    etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleDirectImage.{u, r} Λ a :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (etaleModuleBaseChangeTwistAdj.{u, r} Λ g a b w ψ)
      (etaleModuleInverseImage.{u, r} Λ g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleDirectImage.{u, r} Λ a)
      (etaleModuleInverseImageAdj.{u, r} Λ g).counit ≫
    (Functor.rightUnitor _).hom

/-- The component of the base change twist at `L` is the adjoint of the component of
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwistAdj`. -/
public lemma etaleModuleBaseChangeTwist_app (L : EtaleModules.{u, r} Λ Y) :
    (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ).app L =
      ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).symm
        ((etaleModuleBaseChangeTwistAdj.{u, r} Λ g a b w ψ).app L) := by
  simp [etaleModuleBaseChangeTwist, Adjunction.homEquiv_counit]

end Twist

/-! ### The Frobenius base change twist -/

section Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The canonical map `L|_{Y_k̄} ⟶ π̄_*(L|_{Y_k̄})`** for a sheaf `L` of `Λ`-modules on
`Y_étale`, where `π̄ = π_Y × id` is the base change of the geometric Frobenius: the base change
along `Y_k̄ ⟶ Y` of the Frobenius descent isomorphism `L ≅ (π_Y)_* L` of [Stacks, Tag 03SR]. -/
public def frobeniusBaseChangeTwist :
    etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⟶
      etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  etaleModuleBaseChangeTwist.{u, r} Λ (fieldBaseChangeProj Y kbar)
    (geometricFrobeniusBaseChange Y kbar p q hcard) (geometricFrobenius Y p q hcard).left
    (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
    (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom

/-- The restriction `C|_{Y_k̄}` of a bounded below complex of sheaves of `Λ`-modules on `Y_étale`
to the base change `Y_k̄`, as an object of the bounded below derived category: the degreewise
inverse image along `Y_k̄ ⟶ Y`. -/
public abbrev fieldBaseChangeRestriction
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ (fieldBaseChange Y kbar)) :=
  DerivedCategory.Plus.Q.obj
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)

/-- **The canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})`** in the bounded below derived
category: the base change twist applied degreewise, followed by the comparison of the degreewise
direct image with the derived direct image. -/
public def frobeniusRestrictionDerivedMap
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    fieldBaseChangeRestriction.{u, r} Λ Y kbar C ⟶
      (etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) :=
  DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk (X := (etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
        (Y := (etaleModuleDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C))
        ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app C.obj)) ≫
    (Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))).app
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)

/-- **The canonical morphism is natural in the complex.** -/
public lemma frobeniusRestrictionDerivedMap_naturality
    {C C' : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)} (φ : C ⟶ C') :
    DerivedCategory.Plus.Q.map
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
          φ) ≫ frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C' =
      frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C ≫
        (etaleModuleDerivedDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ)) := by
  have hu := (Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, r} Λ
    (geometricFrobeniusBaseChange Y kbar p q hcard))).naturality
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
        φ)
  dsimp only [Functor.comp_map] at hu
  unfold frobeniusRestrictionDerivedMap
  rw [Category.assoc, ← hu, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  ext n : 2
  dsimp [Functor.mapCochainComplexPlus]
  exact (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).naturality (φ.hom.f n)

/-- `π̄ = π_Y × id` is a morphism over `Spec k̄`. -/
public lemma geometricFrobeniusBaseChange_comp_toBase :
    geometricFrobeniusBaseChange Y kbar p q hcard ≫ pullback.snd Y.hom (specAlgebraMap k kbar) =
      pullback.snd Y.hom (specAlgebraMap k kbar) :=
  geometricFrobeniusBaseChange_comp_snd Y kbar p q hcard

/-- **The canonical endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})`** induced by the geometric Frobenius,
for a bounded below complex `C` on `Y_étale`: `RΓ(Spec k̄, -)` applied to `Rf_*` of the
canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})`, followed by `Rπ̄_* ⋙ Rf_* ≅ Rf_*`, where
`f : Y_k̄ ⟶ Spec k̄` is the structure morphism. -/
public def frobeniusRestrictionCohomologyEndo
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)) ⟶
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map
    ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
        (frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C) ≫
      (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C))

end Frobenius

/-! ### Cohomology with compact support -/

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The complex `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`** of the source, for a bounded
below complex `K` of sheaves of `Λ`-modules on `X_étale` and a compactification `j : X ⟶ X̄`
over `k`: extension by zero to `X̄`, restriction to `X̄_k̄`, and derived global sections. -/
@[sga "4½ Rapport 3.6"]
public abbrev compactSupportFrobeniusCohomology
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
    ((etaleModuleDerivedDirectImage.{u, r} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).obj
      (fieldBaseChangeRestriction.{u, r} Λ (Over.mk j.toBase) kbar
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K)))

/-- **The canonical endomorphism `π_X^*` of `RΓ_c(X_k̄, K)`.**  It is the endomorphism induced
on `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` by `π̄ = π_{X̄} × id` together with the canonical morphism
`(j_! K)|_{X̄_k̄} ⟶ Rπ̄_*((j_! K)|_{X̄_k̄})`, the base change of the Frobenius descent
isomorphism of [Stacks, Tag 03SR].  Every ingredient is determined by `X`, `j`, `k̄` and the
cardinality of `k`. -/
public def canonicalCompactSupportFrobenius
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K ⟶
      compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K :=
  frobeniusRestrictionCohomologyEndo.{u, r} Λ (Over.mk j.toBase) kbar p q hcard
    ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K)

/-- The module `H^i_c(X_k̄, K)`, the `i`-th cohomology of `RΓ_c(X_k̄, K)`. -/
public abbrev compactSupportFrobeniusCohomologyGroup
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    ModuleCat.{max (u + 1) r} Λ :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).obj
    (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)

/-- **The canonical endomorphism `π_X^*` of `H^i_c(X_k̄, K)`**, induced on cohomology by
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`. -/
public def canonicalCompactSupportFrobeniusGroup
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar K i ⟶
      compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar K i :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
    (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)

/-- **The datum of [Stacks, Tag 03TX] for the canonical action.**  Given perfectness of
`RΓ_c(X_k̄, K)`, the perfect complex together with the canonical endomorphism `π_X^*`. -/
public def canonicalFrobeniusActionOnCompactSupport [Finite Λ]
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K))) :
    FrobeniusActionOnCohomology.{r, max (u + 1) r} Λ where
  cohomology := ⟨_, hperf⟩
  frobeniusAction :=
    DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)

/-- **`Tr(π_X^* | RΓ_c(X_k̄, K))` for the canonical action**, an element of `Λ^natural`. -/
public def canonicalCompactSupportLefschetzNumber [Finite Λ]
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K))) :
    CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient Λ :=
  globalLefschetzNumber.{r, max (u + 1) r} Λ
    (canonicalFrobeniusActionOnCompactSupport.{u, r} Λ f j kbar p q hcard K hperf)

end CompactSupport

end Stacks.EtaleCohomology

end
