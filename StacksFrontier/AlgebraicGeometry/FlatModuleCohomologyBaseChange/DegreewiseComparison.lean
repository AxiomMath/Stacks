module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.UnderivedComparison
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# The degreewise comparison map of flat base change

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `G` be a quasi-coherent `𝒪_{S'}`-module which is flat
over `S`. With the two coefficient functors

`Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G` and `Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G`

of `CoefficientFunctors.lean`, [Stacks, Tag 0GN5] asserts that for every `i` the canonical map

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

is an isomorphism. This file constructs that map in every degree.

The construction is the one the étale development of [Stacks, Tag 0F02] uses for abelian
sheaves: the underived comparison `Φ ∘ f_* ⟶ f'_* ∘ Ψ` of `UnderivedComparison.lean` descends to
a comparison `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` of functors on bounded below derived categories, because
`RΦ` applied to the image of a complex under `f_*` is `Φ` applied degreewise — and that is where
exactness of `Φ` is consumed. Taking degree-`i` cohomology recovers the degreewise map, once
both sides have been identified with cohomology of the derived composites; exactness of `Ψ` is
consumed in the second of those two identifications, which says that `RΨ` sends `F[0]` to
`(Ψ F)[0]`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison`: the descent
  `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` of the underived comparison to bounded below derived categories.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonSourceIso` and
  `comparisonTargetIso`: the identifications of `Φ ∘ R ⁱ f_*` and of `R ⁱ f'_* ∘ Ψ` with
  cohomology of the derived composites.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.degreewiseComparison`: **the degreewise comparison
  map** `Φ ∘ R ⁱ f_* ⟶ R ⁱ f'_* ∘ Ψ`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison_fac`: **the derived comparison is
  the canonical one.** Composed with the derived-functor unit of `Rf_*` it is the underived
  comparison applied degreewise; since `Rf_* ⋙ RΦ` is a right derived functor of `f_* ⋙ Φ` with
  that unit, this equation determines it.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.degreewiseComparison_eq` and
  `degreewiseComparison_app`: **the degreewise comparison is the degree-`i` cohomology of the
  derived comparison**, read through the two identifications. This pins the degreewise map to
  the derived one in every degree, not only in degree zero.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_iff`: the degreewise
  comparison is invertible exactly when the degree-`i` cohomology of the derived comparison is;
  the two identifications it is defined through are isomorphisms, so the assertion of
  [Stacks, Tag 0GN5] is not invertibility of something invertible by construction.

## Implementation notes

The generic machinery is `Stacks.Cohomology.BaseChange.derived` and
`Stacks.Cohomology.BaseChange.derived_fac`, which descend a transformation
`F ⋙ G ⟶ G' ⋙ F'` of underived composites to the bounded below right derived functors as soon
as the comparison between `RG` and degreewise `G` is invertible; `Stacks.Cohomology.BaseChange.
exactUnit_isIso` supplies that from exactness of `G`. The two identifications of the degreewise
sides use `Stacks.DerivedIndexing.rightDerivedIso`, which crosses between the
injective-resolution and bounded-below conventions for a right derived functor, and
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` and
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso`, which say that the right derived
functor of an exact functor commutes with cohomology and with the degree-zero embedding. All
four are used exactly as the étale development of [Stacks, Tag 0F02] uses them.

Exactness of the two coefficient functors is not a class, so it is threaded through as the
explicit hypotheses `hG` (flatness of `G` over `S`), `H` (the square is cartesian) and
`[G.IsQuasicoherent]`, and the corresponding `PreservesFiniteLimits` and
`PreservesFiniteColimits` instances are introduced by `letI` at each use. Consequently the
definitions below depend on those hypotheses as data, and two of them with different (but
propositionally equal) hypotheses are equal only after `Subsingleton.elim`; the hypotheses are
propositions, so nothing is lost.

Everything is written over `SheafOfModules (structureSheafRing _)` with the direct image
`RingedSpaceModuleAdjunction.modulePushforward`, for the reason explained in the implementation
notes of `CoefficientFunctors.lean`.

**What is not here.** The degree-zero component of the degreewise comparison is not identified
with the underived comparison of `UnderivedComparison.lean`. That identification is a statement
about `CategoryTheory.Functor.toRightDerivedZero` and
`Stacks.DerivedIndexing.rightDerivedIso`, whose compatibility the latter's own implementation
notes record as absent. What *is* available, and is recorded here, is
`derivedComparison_fac`: the derived comparison is pinned to the underived one through the
derived-functor unit, in all degrees at once.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {S S' X X' : Scheme.{u}}

/-! ### The derived comparison -/

section Derived

variable {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))

/-- The comparison between `RΦ` and `Φ` applied degreewise, an isomorphism because `Φ` is
exact. -/
def baseCoefficientsDerivedIso (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    (baseCoefficients g G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ (baseCoefficients g G).rightDerivedFunctorPlus :=
  letI := preservesFiniteLimits_baseCoefficients g G hG
  letI := preservesFiniteColimits_baseCoefficients g G hG
  letI : IsIso (baseCoefficients g G).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (baseCoefficients g G)
  asIso (baseCoefficients g G).rightDerivedFunctorPlusUnith

/-- **The derived comparison** `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` on bounded below derived categories:
the descent of the underived comparison along the derived-functor unit of `Rf_*`, which
determines it. -/
def derivedComparison (w : g' ≫ f = f' ≫ g)
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    (modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        (baseCoefficients g G).rightDerivedFunctorPlus ⟶
      (totalCoefficients g' f' G).rightDerivedFunctorPlus ⋙
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derived (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward f'.toLRSHom.toShHom) (baseCoefficients g G) (totalCoefficients g' f' G)
    (underivedComparison w G) (baseCoefficientsDerivedIso g G hG)

/-- The underived comparison applied degreewise on the bounded below homotopy category, followed
by the derived-functor units of `RΨ` and of `Rf'_*`. -/
def comparisonOnHomotopy (w : g' ≫ f = f' ≫ g)
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    ((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) ⋙ (baseCoefficients g G).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙ ((totalCoefficients g' f' G).rightDerivedFunctorPlus ⋙
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus) :=
  Stacks.Cohomology.BaseChange.onHomotopy (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward f'.toLRSHom.toShHom) (baseCoefficients g G) (totalCoefficients g' f' G)
    (underivedComparison w G) (baseCoefficientsDerivedIso g G hG)

/-- **The derived comparison is the canonical one.**  Composed with the derived-functor unit of
`Rf_*` it is the underived comparison applied degreewise; since `Rf_* ⋙ RΦ` is a right derived
functor of `f_* ⋙ Φ` with that unit, this equation determines the derived comparison. -/
theorem derivedComparison_fac (w : g' ≫ f = f' ≫ g)
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    Functor.whiskerRight
        (modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith
        (baseCoefficients g G).rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (derivedComparison G w hG) =
        comparisonOnHomotopy G w hG :=
  Stacks.Cohomology.BaseChange.derived_fac (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward f'.toLRSHom.toShHom) (baseCoefficients g G) (totalCoefficients g' f' G)
    (underivedComparison w G) (baseCoefficientsDerivedIso g G hG)

end Derived

/-! ### The two identifications of the degreewise sides -/

section Degreewise

variable {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))

/-- The identification of `Φ ∘ R ⁱ f_*` with the degree-`i` cohomology of the bounded below
derived source `RΦ ∘ Rf_*`: the comparison of the injective-resolution and bounded-below
conventions for the right derived functor of `f_*`, followed by the comparison of the exact
functor `Φ` with cohomology. -/
def comparisonSourceIso (f : X ⟶ S) (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    (modulePushforward f.toLRSHom.toShHom).rightDerived i ⋙ baseCoefficients g G ≅
      DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
        (modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        (baseCoefficients g G).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ) :=
  letI := preservesFiniteLimits_baseCoefficients g G hG
  letI := preservesFiniteColimits_baseCoefficients g G hG
  Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (modulePushforward f.toLRSHom.toShHom) i)
      (baseCoefficients g G) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
        (modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus)
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (baseCoefficients g G) (i : ℤ)).symm

/-- The identification of `R ⁱ f'_* ∘ Ψ` with the degree-`i` cohomology of the bounded below
derived target `Rf'_* ∘ RΨ`: the comparison of the injective-resolution and bounded-below
conventions for the right derived functor of `f'_*`, followed by the comparison of the exact
functor `Ψ` with the degree-zero embedding. -/
def comparisonTargetIso (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    totalCoefficients g' f' G ⋙ (modulePushforward f'.toLRSHom.toShHom).rightDerived i ≅
      DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
        (totalCoefficients g' f' G).rightDerivedFunctorPlus ⋙
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ) :=
  letI := preservesFiniteLimits_totalCoefficients H G hG
  letI := preservesFiniteColimits_totalCoefficients H G hG
  Functor.isoWhiskerLeft (totalCoefficients g' f' G)
      (Stacks.DerivedIndexing.rightDerivedIso (modulePushforward f'.toLRSHom.toShHom) i) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (totalCoefficients g' f' G) 0)
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ))

/-- **The degreewise comparison map of [Stacks, Tag 0GN5]**,
`Φ ∘ R ⁱ f_* ⟶ R ⁱ f'_* ∘ Ψ`. It is the degree-`i` cohomology of the derived comparison
`derivedComparison`, transported along the canonical identifications `comparisonSourceIso` and
`comparisonTargetIso` of the two sides with cohomology of the bounded below derived
composites. -/
def degreewiseComparison (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    (modulePushforward f.toLRSHom.toShHom).rightDerived i ⋙ baseCoefficients g G ⟶
      totalCoefficients g' f' G ⋙ (modulePushforward f'.toLRSHom.toShHom).rightDerived i :=
  (comparisonSourceIso f g G hG i).hom ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0)
      (Functor.whiskerRight (derivedComparison G H.w hG)
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ))) ≫
    (comparisonTargetIso H G hG i).inv

/-- The degreewise comparison is the degree-`i` cohomology of the derived comparison, read
through the two identifications. This is its definition, recorded as an equation. -/
theorem degreewiseComparison_eq (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    degreewiseComparison H G hG i =
      (comparisonSourceIso f g G hG i).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0)
          (Functor.whiskerRight (derivedComparison G H.w hG)
            (DerivedCategory.Plus.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ))) ≫
        (comparisonTargetIso H G hG i).inv :=
  rfl

/-- The component of the degreewise comparison, read as the composite of the two
identifications with the degree-`i` cohomology of the derived comparison. -/
theorem degreewiseComparison_app (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (degreewiseComparison H G hG i).app F =
      (comparisonSourceIso f g G hG i).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ)).map
          ((derivedComparison G H.w hG).app
            ((DerivedCategory.Plus.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) ≫
        (comparisonTargetIso H G hG i).inv.app F := by
  rw [degreewiseComparison_eq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- A morphism conjugated by two isomorphisms is invertible exactly when it is. -/
private theorem isIso_hom_comp_comp_inv_iff {C : Type*} [Category* C] {A B A' B' : C}
    (a : A ≅ B) (c : A' ≅ B') (m : B ⟶ B') :
    IsIso (a.hom ≫ m ≫ c.inv) ↔ IsIso m := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  rw [show m = a.inv ≫ (a.hom ≫ m ≫ c.inv) ≫ c.hom by simp]
  infer_instance

/-- **The degreewise comparison is invertible exactly when the derived comparison is.**  The two
identifications `comparisonSourceIso` and `comparisonTargetIso` through which
`degreewiseComparison` is defined are isomorphisms, so the degreewise assertion of
[Stacks, Tag 0GN5] and the degree-`i` cohomology of the derived comparison stand or fall
together. In particular that assertion is not invertibility of something invertible by
construction. -/
theorem isIso_degreewiseComparison_app_iff (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) (i : ℕ)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    IsIso ((degreewiseComparison H G hG i).app F) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (i : ℤ)).map
        ((derivedComparison G H.w hG).app
          ((DerivedCategory.Plus.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))) := by
  rw [degreewiseComparison_app H G hG i F]
  exact isIso_hom_comp_comp_inv_iff ((comparisonSourceIso f g G hG i).app F)
    ((comparisonTargetIso H G hG i).app F) _

end Degreewise

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
