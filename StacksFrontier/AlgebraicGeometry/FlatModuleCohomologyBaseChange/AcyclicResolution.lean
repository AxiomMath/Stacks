module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffineInvertibility

/-!
# The derived comparison read on a complex computing the direct image

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `G` be a quasi-coherent `𝒪_{S'}`-module flat over `S`.
The derived comparison `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ` of `DegreewiseComparison.lean` is pinned down by
`derivedComparison_fac`, which reads it through the derived-functor unit of `Rf_*`. This file
turns that equation into a usable criterion: the derived comparison is invertible at the image
of a bounded below complex `L` as soon as

* the unit of `Rf_*` is invertible at `L` — that is, `f_*L` already computes `Rf_*L`; and
* the comparison `comparisonOnHomotopy` is invertible at `L` — that is, the complex `Φ(f_*L)`
  computes `Rf'_*(ΨL)` through the canonical map.

Both hypotheses are statements about a *complex*, where the two sides are computed degreewise,
and neither mentions an injective resolution. This is what connects the derived comparison to a
complex built out of a covering: for the absolute Čech resolution of a quasi-coherent module by
a finite affine open covering the first hypothesis is Leray's acyclicity lemma
([Stacks, Tag 015E]), available in that spelling in
`StacksFrontier/AlgebraicGeometry/DerivedIso/Leray.lean`, and the second is a degreewise assertion
about the direct images of the restrictions of the module to affine opens.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_Qh`: **the criterion**
  — the derived comparison is invertible at `Qh L`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_resolution`:
  the same at `F[0]`, for a complex `L` whose image in `D⁺(X)` is `F[0]`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_resolution`:
  **[Stacks, Tag 0GN5] from a complex computing both sides** — the degreewise comparison
  `Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)` is invertible in every degree.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_comparisonOnHomotopy_app_iff`: the second
  hypothesis is exactly invertibility of the canonical map from `Φ(f_*L)` to `Rf'_*(ΨL)`: the
  two remaining factors of `comparisonOnHomotopy` are invertible for every `L`, one because `Φ`
  is exact and the other because `Ψ` is.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.complexComparison`: that canonical map.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_complexComparison`: it is invertible as soon
  as the underived comparison is invertible at every term of `L` and `Ψ` of every term of `L` is
  right acyclic for `f'_*`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app`: the underived
  comparison is invertible at a module where the base-change morphism of [Stacks, Tag 02KG] and
  the projection-formula morphism of [Stacks, Tag 0FZE] are.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_degreewise`:
  **[Stacks, Tag 0GN5] from a complex whose terms carry the comparison** — the whole reduction,
  with hypotheses only about the individual terms of `L` and about `L` computing `Rf_*F`.

## Implementation notes

`derivedComparison_fac` says that the derived comparison, precomposed with `RΦ` of the unit of
`Rf_*`, is `comparisonOnHomotopy`. Read at a single object `L` of the bounded below homotopy
category the associators are identities, so the equation becomes a factorisation of one morphism
as a composite of two; invertibility of the first factor and of the composite gives
invertibility of the second. Passing from `Qh L` to `F[0]` is naturality of the derived
comparison along an isomorphism of `D⁺(X)`, and the passage to every degree is
`isIso_degreewiseComparison_app_of_isIso`.

The decomposition `isIso_comparisonOnHomotopy_app_iff` unfolds `Stacks.Cohomology.BaseChange.
onHomotopy` at `L`. Of its four factors the first is a component of `baseCoefficientsDerivedIso`,
invertible because `Φ` is exact, and the last is `Rf'_*` applied to a component of the unit of
`RΨ`, invertible because `Ψ` is exact — the two exactness statements of
`CoefficientFunctors.lean`. What is left is the underived comparison applied degreewise to `L`,
followed by the unit of `Rf'_*` at `ΨL`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- If `a ≫ b = c` with `a` and `c` invertible, then `b` is invertible. -/
private theorem isIso_of_comp_eq_of_isIso {C : Type*} [Category* C] {X Y Z : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c) [IsIso a] [IsIso c] : IsIso b := by
  have : IsIso (a ≫ b) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left a b

/-- **The derived comparison is invertible at the image of a complex computing both sides.**
If the derived-functor unit of `Rf_*` is invertible at `L`, so that `f_*L` computes `Rf_*L`, and
the comparison on the bounded below homotopy category is invertible at `L`, so that `Φ(f_*L)`
computes `Rf'_*(ΨL)`, then the derived comparison of [Stacks, Tag 0GN5] is invertible at the
image of `L` in `D⁺(X)`.

This is `derivedComparison_fac` read at `L`: the derived comparison there is the second factor
of a composite whose first factor and whose value are both invertible. -/
theorem isIso_derivedComparison_app_Qh (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (hcmp : IsIso ((comparisonOnHomotopy G w hG).app L)) :
    IsIso ((derivedComparison G w hG).app (DerivedCategory.Plus.Qh.obj L)) := by
  have key := NatTrans.congr_app (derivedComparison_fac G w hG) L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at key
  exact isIso_of_comp_eq_of_isIso key

/-- **The derived comparison is invertible at `F[0]`** when some complex `L` whose image in
`D⁺(X)` is `F[0]` computes both sides.  Naturality of the derived comparison along the
isomorphism `Qh L ≅ F[0]` transports the conclusion of `isIso_derivedComparison_app_Qh`. -/
theorem isIso_derivedComparison_app_single_of_resolution (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj L ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (hcmp : IsIso ((comparisonOnHomotopy G w hG).app L)) :
    IsIso ((derivedComparison G w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) := by
  have := isIso_derivedComparison_app_Qh w G hG L hL hcmp
  exact isIso_of_comp_eq_of_isIso ((derivedComparison G w hG).naturality e.hom)

/-- **[Stacks, Tag 0GN5] from a complex computing both sides.**  Let the square be cartesian, let
`G` be a quasi-coherent `𝒪_{S'}`-module flat over `S`, and suppose given a bounded below complex
`L` of `𝒪_X`-modules whose image in `D⁺(X)` is `F[0]`, such that `f_*L` computes `Rf_*F` and
`Φ(f_*L)` computes `Rf'_*(ΨF)` through the canonical comparison.  Then the degreewise comparison

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

is invertible in every degree `i`. -/
theorem isIso_degreewiseComparison_app_of_resolution (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj L ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (hcmp : IsIso ((comparisonOnHomotopy G H.w hG).app L)) (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) :=
  isIso_degreewiseComparison_app_of_isIso H G hG F
    (isIso_derivedComparison_app_single_of_resolution H.w G hG F L e hL hcmp) i

/-! ### The comparison on the homotopy category is the canonical map out of `Φ(f_*L)` -/

/-- A composite of four morphisms whose first and last factors are invertible is invertible
exactly when the two middle ones compose to an invertible morphism. -/
private theorem isIso_comp_comp_comp_iff {C : Type*} [Category* C] {V W Y Z T : C}
    (a : V ⟶ W) [IsIso a] (b : W ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) [IsIso d] :
    IsIso (a ≫ b ≫ c ≫ d) ↔ IsIso (b ≫ c) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [show b ≫ c = inv a ≫ (a ≫ b ≫ c ≫ d) ≫ inv d by simp]
    infer_instance
  · rw [show a ≫ b ≫ c ≫ d = a ≫ (b ≫ c) ≫ d by simp]
    infer_instance

/-- **The canonical map from `Φ(f_*L)` to `Rf'_*(ΨL)`**: the underived comparison
`Φ ∘ f_* ⟶ f'_* ∘ Ψ` applied degreewise to `L`, followed by the derived-functor unit of
`Rf'_*` at `ΨL`. -/
def complexComparison (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    DerivedCategory.Plus.Qh.obj
        ((baseCoefficients g G).mapHomotopyCategoryPlus.obj
          ((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj L)) ⟶
      (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj
          ((totalCoefficients g' f' G).mapHomotopyCategoryPlus.obj L)) :=
  DerivedCategory.Plus.Qh.map
      ((Stacks.Cohomology.BaseChange.mapPlus (underivedComparison w G)).app L) ≫
    (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app
      ((totalCoefficients g' f' G).mapHomotopyCategoryPlus.obj L)

/-- **The hypothesis of `isIso_derivedComparison_app_Qh` is invertibility of the canonical map
out of `Φ(f_*L)`.**  Of the four factors of `comparisonOnHomotopy` at `L` the first is a
component of `baseCoefficientsDerivedIso`, invertible because `Φ` is exact, and the last is
`Rf'_*` applied to a component of the derived-functor unit of `RΨ`, invertible because `Ψ` is
exact.  So the condition on `L` is exactly that the complex `Φ(f_*L)` computes `Rf'_*(ΨL)`
through the canonical comparison. -/
theorem isIso_comparisonOnHomotopy_app_iff (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((comparisonOnHomotopy G H.w hG).app L) ↔ IsIso (complexComparison H.w G L) := by
  let := preservesFiniteLimits_totalCoefficients H G hG
  let := preservesFiniteColimits_totalCoefficients H G hG
  have : IsIso (totalCoefficients g' f' G).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (totalCoefficients g' f' G)
  have : IsIso ((totalCoefficients g' f' G).rightDerivedFunctorPlusUnith.app L) :=
    NatIso.isIso_app_of_isIso _ L
  have : IsIso ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.map
      ((totalCoefficients g' f' G).rightDerivedFunctorPlusUnith.app L)) :=
    Functor.map_isIso _ _
  have : IsIso ((baseCoefficientsDerivedIso g G hG).inv.app
      ((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj L)) :=
    NatIso.isIso_app_of_isIso _ _
  have happ : (comparisonOnHomotopy G H.w hG).app L =
      (baseCoefficientsDerivedIso g G hG).inv.app
          ((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj L) ≫
        DerivedCategory.Plus.Qh.map
          ((Stacks.Cohomology.BaseChange.mapPlus (underivedComparison H.w G)).app L) ≫
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app
          ((totalCoefficients g' f' G).mapHomotopyCategoryPlus.obj L) ≫
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.map
          ((totalCoefficients g' f' G).rightDerivedFunctorPlusUnith.app L) :=
    Stacks.Cohomology.BaseChange.onHomotopy_app
      (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
      (baseCoefficients g G) (totalCoefficients g' f' G)
      (underivedComparison H.w G) (baseCoefficientsDerivedIso g G hG) L
  rw [happ]
  exact isIso_comp_comp_comp_iff _ _ _ _

/-- **The underived comparison is invertible at a module where its two factors are.**  The
comparison `Φ(f_*N) ⟶ f'_*(ΨN)` is the base-change morphism of [Stacks, Tag 02KG] tensored with
`G`, followed by the projection-formula morphism of [Stacks, Tag 0FZE]; so it is invertible as
soon as those two are.  This is the form in which the degreewise hypothesis of
`isIso_complexComparison` is checked. -/
theorem isIso_underivedComparison_app (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hbc : IsIso ((baseChangeNatTrans w).app N))
    (hpf : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
      ((modulePullback g'.toLRSHom.toShHom).obj N) G)) :
    IsIso ((underivedComparison w G).app N) := by
  have h1 : IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf).flip.obj G).map ((baseChangeNatTrans w).app N)) :=
    @Functor.map_isIso _ _ _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S'.toRingedSpace.sheaf).flip.obj G) ((baseChangeNatTrans w).app N) hbc
  rw [underivedComparison_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 hpf

/-- **The canonical map out of `Φ(f_*L)` is invertible when it is so degreewise and `ΨL` is
`f'_*`-acyclic.**  The underived comparison applied degreewise to `L` is an isomorphism of
complexes as soon as it is an isomorphism at every term, and the derived-functor unit of `Rf'_*`
is invertible at `ΨL` as soon as every term of `ΨL` is right acyclic for `f'_*`, which is
Leray's acyclicity lemma ([Stacks, Tag 015E]).

The two hypotheses are assertions about the individual terms of `L`.  For the absolute Čech
resolution of a quasi-coherent module by a covering by affine opens they are assertions about
the direct image of its restriction to an affine open. -/
theorem isIso_complexComparison (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hiso : ∀ n : ℤ, IsIso ((underivedComparison w G).app (L.obj.as.X n)))
    (hac : ∀ n : ℤ, (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj (L.obj.as.X n))) :
    IsIso (complexComparison w G L) := by
  have hunit : IsIso ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app
      ((totalCoefficients g' f' G).mapHomotopyCategoryPlus.obj L)) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ hac
  have : ∀ n : ℤ, IsIso (((NatTrans.mapHomologicalComplex (underivedComparison w G)
      (ComplexShape.up ℤ)).app L.obj.as).f n) := hiso
  have hc : IsIso ((NatTrans.mapHomologicalComplex (underivedComparison w G)
      (ComplexShape.up ℤ)).app L.obj.as) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hc2 : IsIso ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (underivedComparison w G)
        (ComplexShape.up ℤ)).app L.obj.as)) :=
    Functor.map_isIso _ _
  have : IsIso ((HomotopyCategory.Plus.ι
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))).map
      ((Stacks.Cohomology.BaseChange.mapPlus (underivedComparison w G)).app L)) := hc2
  have : IsIso ((Stacks.Cohomology.BaseChange.mapPlus (underivedComparison w G)).app L) :=
    isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)))
  have hQh : IsIso (DerivedCategory.Plus.Qh.map
      ((Stacks.Cohomology.BaseChange.mapPlus (underivedComparison w G)).app L)) :=
    Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hQh hunit

/-- **[Stacks, Tag 0GN5] from a complex universally computing both sides, through the canonical
comparison.**  Let the square be cartesian, let `G` be a quasi-coherent `𝒪_{S'}`-module flat
over `S` and let `L` be a bounded below complex of `𝒪_X`-modules with

* `Qh L ≅ F[0]` in `D⁺(X)`, so `L` resolves `F`;
* the derived-functor unit of `Rf_*` invertible at `L`, so `f_*L` computes `Rf_*F`;  and
* the canonical map `Φ(f_*L) ⟶ Rf'_*(ΨL)` invertible, so `Φ(f_*L)` computes `Rf'_*(Ψ F)`.

Then the degreewise comparison `Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)` is invertible in every degree.
Nothing else is assumed: no hypothesis on `f`, on `g` or on the schemes. -/
theorem isIso_degreewiseComparison_app_of_complexComparison (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj L ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (hcmp : IsIso (complexComparison H.w G L)) (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) :=
  isIso_degreewiseComparison_app_of_resolution H G hG F L e hL
    ((isIso_comparisonOnHomotopy_app_iff H G hG L).2 hcmp) i

/-- **[Stacks, Tag 0GN5] from a complex whose terms carry the comparison.**  Let the square be
cartesian, let `G` be a quasi-coherent `𝒪_{S'}`-module flat over `S` and let `L` be a bounded
below complex of `𝒪_X`-modules such that

* `Qh L ≅ F[0]` in `D⁺(X)`, so `L` resolves `F`;
* the derived-functor unit of `Rf_*` is invertible at `L`, so `f_*L` computes `Rf_*F`;
* the underived comparison `Φ(f_*N) ⟶ f'_*(ΨN)` is invertible at every term `N` of `L`;  and
* `ΨN` is right acyclic for `f'_*` for every term `N` of `L`.

Then the degreewise comparison `Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)` is invertible in every degree.
The last two hypotheses are assertions about single modules, and the first two are the content of
[Stacks, Tag 01XN] for `L`; nothing else is assumed. -/
theorem isIso_degreewiseComparison_app_of_degreewise (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj L ≅
      (DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (hiso : ∀ n : ℤ, IsIso ((underivedComparison H.w G).app (L.obj.as.X n)))
    (hac : ∀ n : ℤ, (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj (L.obj.as.X n))) (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) :=
  isIso_degreewiseComparison_app_of_complexComparison H G hG F L e hL
    (isIso_complexComparison H.w G L hiso hac) i

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
