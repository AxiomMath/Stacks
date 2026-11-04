module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDesc
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring with a sheaf of modules with flat fibers is exact, on a site with enough points

Let `(C, J)` be a site with a conservative family of points `P` (relative to a universe `w`),
`Λ` a commutative ring and `G` a sheaf of `Λ`-modules (values in `ModuleCat.{w} Λ`, with the
tensor product of `CategoryTheory.Sheaf.monoidalCategory`). The fiber functors at the points are
monoidal (`CategoryTheory.GrothendieckTopology.Point.sheafFiber`, Mathlib) and jointly reflect
monomorphisms (Stacks 00YL). Hence if the fiber of `G` at every point of `P` is a flat
`Λ`-module, `- ⊗ G` preserves monomorphisms; it is right exact because the tensor product of
sheaves is closed, so it is exact.

This is the site-independent form of
`AlgebraicGeometry.preservesFiniteLimits_tensorRight_of_flat`, which is stated for the small étale
site of Stacks 021B with its geometric points. The form here applies to Mathlib's small étale site
`X.smallEtaleTopology`, whose conservative families of points are
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale_ulift`; that is the site on which the
compactly supported cohomology of the geometric fibre lives, and the exactness of `- ⊗ G` there
is what the cup product `Stacks.ExtCup.cup` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) needs.

## Main results

* `IsConservativeFamilyOfPoints.preservesMonomorphisms_tensorRight_of_flat`: if every fiber of
  `G` is flat, then `- ⊗ G` preserves monomorphisms.
* `IsConservativeFamilyOfPoints.preservesFiniteLimits_tensorRight_of_flat`: if every fiber of
  `G` is flat, then `- ⊗ G` is additive and preserves finite limits and finite colimits.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} (hP : P.IsConservativeFamilyOfPoints)
  (Λ : Type) [CommRing Λ]

/-- Tensoring on the left with a module preserves colimits, the large-universe tensor product of
modules being closed. -/
theorem moduleCat_preservesColimits_tensorLeft (M : ModuleCat.{w} Λ) :
    PreservesColimitsOfSize.{w, w} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- Tensoring on the right with a module preserves colimits, through the braiding. -/
theorem moduleCat_preservesColimits_tensorRight (M : ModuleCat.{w} Λ) :
    PreservesColimitsOfSize.{w, w} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

attribute [local instance] moduleCat_preservesColimits_tensorLeft
  moduleCat_preservesColimits_tensorRight

/-- On modules, the large-universe tensor product with a flat module preserves injectivity. -/
@[sga "3 I 5.3.1.1" "partial", sga "3 VIB 11.7" "special case"]
theorem moduleCat_mono_whiskerRight_of_flat {M N : ModuleCat.{w} Λ} (f : M ⟶ N) [Mono f]
    (Q : ModuleCat.{w} Λ) [Module.Flat Λ Q] : Mono (f ▷ Q) := by
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.rTensor_preserves_injective_linearMap f.hom
    ((ModuleCat.mono_iff_injective f).1 inferInstance)

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] [AB5OfSize.{w, w} (ModuleCat.{w} Λ)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} Λ))]

include hP in
/-- **Tensoring with a sheaf whose fibers are flat preserves monomorphisms**: at a point `Φ`,
`f ▷ G` becomes `f_Φ ▷ G_Φ`, injective by flatness, and the fiber functors of a conservative
family of points jointly reflect monomorphisms. -/
theorem preservesMonomorphisms_tensorRight_of_flat (G : Sheaf J (ModuleCat.{w} Λ))
    (hG : ∀ Φ : P.FullSubcategory,
      Module.Flat Λ ((Φ.obj.sheafFiber (A := ModuleCat.{w} Λ)).obj G)) :
    (tensorRight G).PreservesMonomorphisms := by
  refine ⟨fun {X Y} f _ => ?_⟩
  have : ∀ Φ : P.FullSubcategory,
      Mono ((Φ.obj.sheafFiber (A := ModuleCat.{w} Λ)).map (f ▷ G)) := by
    intro Φ
    let Ψ := Φ.obj.sheafFiber (A := ModuleCat.{w} Λ)
    have := hG Φ
    have := moduleCat_mono_whiskerRight_of_flat Λ (Ψ.map f) (Ψ.obj G)
    show Mono (Ψ.map (f ▷ G))
    rw [show Ψ.map (f ▷ G) = (Functor.Monoidal.μIso Ψ X G).inv ≫
        (Ψ.map f ▷ Ψ.obj G) ≫ (Functor.Monoidal.μIso Ψ Y G).hom from
      Functor.Monoidal.map_whiskerRight Ψ f G]
    infer_instance
  exact @JointlyReflectMonomorphisms.mono _ _ _ _ _ _
    (hP.jointlyReflectMonomorphisms (ModuleCat.{w} Λ)) _ _ (f ▷ G) this

include hP in
/-- **Tensoring with a sheaf whose fibers are flat is exact**: it is right exact, being a left
adjoint up to the braiding (`CategoryTheory.Sheaf.preservesColimitsOfSize_tensorRight_moduleCat`),
hence additive, and it preserves monomorphisms. -/
theorem preservesFiniteLimits_tensorRight_of_flat [UnivLE.{max u v, w}]
    [HasSheafify J (ModuleCat.{w} Λ)] (G : Sheaf J (ModuleCat.{w} Λ))
    (hG : ∀ Φ : P.FullSubcategory,
      Module.Flat Λ ((Φ.obj.sheafFiber (A := ModuleCat.{w} Λ)).obj G)) :
    (tensorRight G).Additive ∧ PreservesFiniteLimits (tensorRight G) ∧
      PreservesFiniteColimits (tensorRight G) := by
  have hc : PreservesColimitsOfSize.{v, u} (tensorRight G) :=
    Sheaf.preservesColimitsOfSize_tensorRight_moduleCat.{w} G
  have : PreservesFiniteColimits (tensorRight G) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight G) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have : PreservesBinaryBiproducts (tensorRight G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorRight G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have := preservesMonomorphisms_tensorRight_of_flat hP Λ G hG
  exact ⟨inferInstance,
    Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _,
    inferInstance⟩

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

end
