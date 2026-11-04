module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftExact
public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# The naive cotangent complex at a larger universe of module sections

`Stacks.SheafOfModules.naiveCotangentComplex.{v, u, w, z}` of Stacks 08TW has a free universe
parameter `z` for its module sections, which enter only through `max w u v z`.  This file shows
that raising `z` is the universe lift of sheaves of modules applied termwise:

`NL.{max z t}_{B/A} ≅ ulift.{t} NL.{z}_{B/A}`.

This is what lets a naive cotangent complex computed on a small site, such as `NL_{X₀/Y₀}` on the
Zariski site of a scheme (Stacks 0D0H), be compared with complexes whose module sections live in
a larger universe, such as `NL_{X/Y}` on the small étale site of an algebraic space (Stacks 0D0V),
whose sections are forced into `Type (u + 1)`; this is the comparison Stacks 0D0X needs.

The terms of the naive cotangent complex are sheafifications of universe lifts
(`Stacks.Sites.Conormal.liftModules`) of presheaves of modules with sections in the ring
universe.  Lifting first to `max z t` is lifting to `z` and then by `t`
(`Stacks.Sites.Conormal.liftModulesULiftNatIso`), and sheafification commutes with the universe
lift
(`PresheafOfModules.sheafifyULiftHom`, an isomorphism), naturally
(`PresheafOfModules.sheafificationULiftNatIso`).  Whiskering the conormal sequence with these
isomorphisms identifies the two conormal sequences
(`Stacks.Sites.Conormal.conormalSequenceULiftIso`), and the two two-term complexes follow
(`Stacks.SheafOfModules.naiveCotangentComplexULiftIso`).

## Main definitions

* `Stacks.Sites.Conormal.liftModulesULiftNatIso`: lifting module sections to `max z t` is lifting
  them to `z` and then by `t`.
* `PresheafOfModules.sheafificationULiftNatIso`: sheafification of presheaves of modules
  commutes with the universe lift, naturally.
* `Stacks.Sites.Conormal.conormalSequenceULiftIso`: the conormal sequence at `max z t` is the
  universe lift of the conormal sequence at `z`.
* `Stacks.SheafOfModules.naiveCotangentComplexULiftIso`: **the naive cotangent complex at
  `max z t` is the universe lift of the naive cotangent complex at `z`.**

## Main results

* `PresheafOfModules.sheafifyULiftHom_naturality`: the comparison of the sheafification of a
  universe lift with the universe lift of the sheafification is natural.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w z t

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C]

/-- Lifting the sections of a presheaf of modules to the universe `max z t` of
`Stacks.Sites.Conormal.liftModules` is lifting them to `z` and then by `t`; the comparison is
`ULift.up ∘ ULift.up ∘ ULift.down` on sections. -/
def liftModulesULiftNatIso (S : Cᵒᵖ ⥤ RingCat.{w}) :
    liftModules.{v, u, w, max z t} S ≅
      liftModules.{v, u, w, z} S ⋙ PresheafOfModules.uliftFunctor.{_, _, _, _, t} :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk
      (fun X ↦
        (ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv).symm).toModuleIso)
      (fun _ _ f ↦ by ext x; rfl))
    (fun f ↦ by ext X x; rfl)

end Stacks.Sites.Conormal

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z t}]
  [HasWeakSheafify J AddCommGrpCat.{max z t}]

/-- **The comparison of the sheafification of a universe lift with the universe lift of the
sheafification is natural** in the presheaf of modules.  Both composites are adjunct to the
universe lift of the sheafification unit followed by the universe lift of the map, by the
naturality of the unit. -/
theorem sheafifyULiftHom_naturality {M N : PresheafOfModules.{z} R₀} (g : M ⟶ N) :
    (sheafification.{max z t} α).map (uliftFunctor.{_, _, _, _, t}.map g) ≫
        sheafifyULiftHom.{_, _, _, _, t} α N =
      sheafifyULiftHom.{_, _, _, _, t} α M ≫
        SheafOfModules.uliftFunctor.{_, _, _, _, t}.map ((sheafification.{z} α).map g) := by
  have h₁ : (sheafification.{max z t} α).map (uliftFunctor.{_, _, _, _, t}.map g) ≫
      sheafifyULiftHom.{_, _, _, _, t} α N =
        ((sheafificationAdjunction.{max z t} α).homEquiv _ _).symm
          (uliftFunctor.{_, _, _, _, t}.map g ≫ uliftSheafifyUnit.{_, _, _, _, t} α N) :=
    ((sheafificationAdjunction.{max z t} α).homEquiv_naturality_left_symm _ _).symm
  have h₂ : sheafifyULiftHom.{_, _, _, _, t} α M ≫
      SheafOfModules.uliftFunctor.{_, _, _, _, t}.map ((sheafification.{z} α).map g) =
        ((sheafificationAdjunction.{max z t} α).homEquiv _ _).symm
          (uliftSheafifyUnit.{_, _, _, _, t} α M ≫
            (SheafOfModules.forget R ⋙ restrictScalars α).map
              (SheafOfModules.uliftFunctor.{_, _, _, _, t}.map ((sheafification.{z} α).map g))) :=
    ((sheafificationAdjunction.{max z t} α).homEquiv_naturality_right_symm _ _).symm
  rw [h₁, h₂]
  congr 1
  ext X x
  exact congrArg ULift.up (congrArg (fun φ ↦ Hom.app φ X x.down)
    ((sheafificationAdjunction.{z} α).unit.naturality g))

/-- **Sheafification of presheaves of modules commutes with the universe lift of the module
sections, naturally**: `PresheafOfModules.sheafifyULiftHom`, an isomorphism by
`PresheafOfModules.isIso_sheafifyULiftHom`, assembled into an isomorphism of functors. -/
def sheafificationULiftNatIso :
    uliftFunctor.{_, _, _, _, t} ⋙ sheafification.{max z t} α ≅
      sheafification.{z} α ⋙ SheafOfModules.uliftFunctor.{_, _, _, _, t} :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (sheafifyULiftHom.{_, _, _, _, t} α M)
      (isIso_sheafifyULiftHom.{_, _, _, _, t} α M))
    (fun g ↦ sheafifyULiftHom_naturality α g)

end PresheafOfModules

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sheafification instance `Stacks.Sites.Conormal.conormalSequence` is formed with. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- The local bijectivity instance `Stacks.Sites.Conormal.conormalSequence` is formed with. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]

/-- **The conormal sequence with module sections in `max z t` is the universe lift of the
conormal sequence with module sections in `z`.**  Its terms are the sheafifications of the
universe lifts of the objectwise conormal sequence, and both the lift and the sheafification
commute with the further lift by `t`. -/
def conormalSequenceULiftIso :
    conormalSequence.{v, u, w, max z t} J R A B a φ ≅
      (conormalSequence.{v, u, w, z} J R A B a φ).map
        (SheafOfModules.uliftFunctor.{v, u, w, max w u v z, t}) :=
  ShortComplex.mapNatIso (conormalPresheafComplex φ.hom a.hom)
    (Functor.isoWhiskerRight (liftModulesULiftNatIso.{v, u, w, z, t} _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (PresheafOfModules.sheafificationULiftNatIso.{v, u, w, max w u v z, t}
          (quotientToRingSheaf J A B φ)))

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **The naive cotangent complex of Stacks 08TW with module sections in `max z t` is the universe
lift of the one with module sections in `z`**: `NL.{max z t}_{B/A} ≅ ulift.{t} NL.{z}_{B/A}`. Both
are two-term complexes on the left-hand map of the conormal sequence of the canonical presentation,
and `Stacks.Sites.Conormal.conormalSequenceULiftIso` identifies those maps; the universe lift of a
two-term complex is the two-term complex of the lifted map
(`HomologicalComplex.doubleMapFunctorIso`). -/
def naiveCotangentComplexULiftIso :
    naiveCotangentComplex.{v, u, w, max z t} J A B a ≅
      ((_root_.SheafOfModules.uliftFunctor.{v, u, w, max w u v z, t}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v, u, w, z} J A B a) :=
  have : Presheaf.IsLocallySurjective J
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective J A B a)
  have : HasZeroObject (_root_.SheafOfModules.{max w u v z t}
      (Stacks.SheafOfModules.Tensor.ringSheaf B)) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (_root_.SheafOfModules.{max w u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf B)) := hasZeroObject_of_hasTerminal_object
  let e := Stacks.Sites.Conormal.conormalSequenceULiftIso.{v, u, w, z, t} J A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)) B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
  HomologicalComplex.doubleSquareIso _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)
      (by decide) _ (ShortComplex.π₁.mapIso e)
      (ShortComplex.π₂.mapIso e) e.hom.comm₁₂.symm ≪≫
    HomologicalComplex.doubleMapFunctorIso
      (_root_.SheafOfModules.uliftFunctor.{v, u, w, max w u v z, t})
      (canonicalConormalSequence.{v, u, w, z} J A B a).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)

end Stacks.SheafOfModules

end
