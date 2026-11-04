module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDesc
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring with an étale sheaf with flat stalks is exact

Let `B` be a big étale site containing a scheme `S` and `Λ` a commutative ring. For sheaves of
`Λ`-modules on the small étale site of `S` (with the large-universe tensor product of
`CategoryTheory.Sheaf.monoidalCategory`), the stalk functors at the geometric points are
monoidal (`CategoryTheory.GrothendieckTopology.Point.sheafFiber`, Mathlib) and jointly faithful
(Stacks 03PU, `AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber`, transported from abelian
sheaves). Hence if every stalk of `G` is a flat `Λ`-module, `- ⊗ G` preserves monomorphisms;
it is right exact because the tensor product of sheaves is closed, so it is exact. This is the
exactness needed to form the cup product `Stacks.ExtCup.cup` with coefficients in a finite
locally constant sheaf of free `ℤ/ℓ^kℤ`-modules, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber_moduleCat`: the stalk functors are
  jointly faithful on sheaves of modules.
* `AlgebraicGeometry.preservesMonomorphisms_tensorRight_of_flat`,
  `AlgebraicGeometry.preservesFiniteLimits_tensorRight_of_flat`: tensoring with a sheaf with
  flat stalks preserves monomorphisms and finite limits.
* `Stacks.EtaleCohomology.flat_sheafFiber_representationLevelSheaf`: the stalks of the level
  sheaves of `ℱ_ρ` are free, hence flat.
* `Stacks.EtaleCohomology.exact_tensorRight_representationLevelSheaf`: tensoring with a level
  sheaf of `ℱ_ρ` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type) [CommRing Λ]

/-- Forgetting the module structure preserves filtered colimits of size `u`. -/
private instance preservesFilteredColimits_forget₂_addCommGrp :
    PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- **Stacks 03PU for sheaves of modules**: the stalk functors at the geometric points are
jointly faithful, because they are so on the underlying abelian sheaves and forgetting the
module structure commutes with stalks and is faithful. -/
@[sga "4 VIII 3.7" "special case"]
theorem jointlyFaithful_etaleStalkSheafFiber_moduleCat :
    JointlyFaithful (fun s : GeometricPoint S =>
      (geometricPointSitePoint B S hS s).sheafFiber (A := ModuleCat.{u + 1} Λ)) := by
  refine ⟨fun {F G} {φ ψ} h => ?_⟩
  apply (sheafCompose (SmallEtale.topology B S hS)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map_injective
  apply (jointlyFaithful_etaleStalkSheafFiber.{u, u + 1} B S hS).map_injective
  intro s
  have e := (geometricPointSitePoint B S hS s).sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hφ := e.hom.naturality φ
  have hψ := e.hom.naturality ψ
  dsimp only [Functor.comp_map] at hφ hψ
  rw [← cancel_mono (e.hom.app G), hφ, hψ, h s]

section Tensor

attribute [local instance] Sheaf.monoidalCategory

/-- Tensoring on the left with a module preserves colimits, the large-universe tensor product
of modules being closed. -/
theorem moduleCat_preservesColimits_tensorLeft (M : ModuleCat.{u + 1} Λ) :
    PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- Tensoring on the right with a module preserves colimits, through the braiding. -/
theorem moduleCat_preservesColimits_tensorRight (M : ModuleCat.{u + 1} Λ) :
    PreservesColimitsOfSize.{u, u} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

attribute [local instance] moduleCat_preservesColimits_tensorLeft
  moduleCat_preservesColimits_tensorRight

/-- On modules, the large-universe tensor product with a flat module preserves injectivity. -/
theorem moduleCat_mono_whiskerRight_of_flat {M N : ModuleCat.{u + 1} Λ} (f : M ⟶ N) [Mono f]
    (P : ModuleCat.{u + 1} Λ) [Module.Flat Λ P] : Mono (f ▷ P) := by
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.rTensor_preserves_injective_linearMap f.hom
    ((ModuleCat.mono_iff_injective f).1 inferInstance)

variable [((SmallEtale.topology B S hS).W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
  [HasWeakSheafify (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)]

/-- The monoidal structure on sheaves of modules given by sheafifying the tensor product of
presheaves. -/
local instance : MonoidalCategory (Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) :=
  Sheaf.monoidalCategory _ _

/-- The category of `Λ`-modules in `Type (u + 1)` has all colimits of size `u`. -/
local instance : HasColimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u, u} Λ

/-- The category of `Λ`-modules in `Type (u + 1)` has all limits of size `u`. -/
local instance : HasLimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u, 0}

omit [((SmallEtale.topology B S hS).W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
  [HasWeakSheafify (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)] in
/-- Filtered colimits of size `u` of modules in `Type (u + 1)` are exact: they are computed on
the underlying abelian groups. -/
theorem moduleCat_AB5OfSize : AB5OfSize.{u, u} (ModuleCat.{u + 1, 0} Λ) where
  ofShape J _ _ := by
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

attribute [local instance] moduleCat_AB5OfSize

/-- **Tensoring with a sheaf whose stalks are flat preserves monomorphisms**: on the stalk at a
geometric point, `f ▷ G` becomes `f_s̄ ▷ G_s̄`, injective by flatness, and the stalk functors
jointly reflect monomorphisms. -/
theorem preservesMonomorphisms_tensorRight_of_flat
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ))
    (hG : ∀ s : GeometricPoint S, Module.Flat Λ
      ((geometricPointSitePoint B S hS s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj G)) :
    (tensorRight G).PreservesMonomorphisms := by
  refine ⟨fun {X Y} f _ => ?_⟩
  have key (s : GeometricPoint S) :
      Mono (((geometricPointSitePoint B S hS s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
        (f ▷ G)) := by
    let Ψ := (geometricPointSitePoint B S hS s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have := hG s
    have := moduleCat_mono_whiskerRight_of_flat Λ (Ψ.map f) (Ψ.obj G)
    show Mono (Ψ.map (f ▷ G))
    have e : Ψ.map (f ▷ G) = (Functor.Monoidal.μIso Ψ X G).inv ≫
        (Ψ.map f ▷ Ψ.obj G) ≫ (Functor.Monoidal.μIso Ψ Y G).hom :=
      Functor.Monoidal.map_whiskerRight Ψ f G
    rw [e]
    infer_instance
  exact @JointlyReflectMonomorphisms.mono _ _ _ _ _ _
    (jointlyFaithful_etaleStalkSheafFiber_moduleCat B S hS Λ).jointlyReflectMonomorphisms _ _
    (f ▷ G) key

/-- **Tensoring with a sheaf whose stalks are flat is exact**: it is right exact, being a left
adjoint up to the braiding (`CategoryTheory.Sheaf.preservesColimitsOfSize_tensorRight_moduleCat`),
hence additive, and it preserves monomorphisms. -/
theorem preservesFiniteLimits_tensorRight_of_flat
    [HasSheafify (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)]
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ))
    (hG : ∀ s : GeometricPoint S, Module.Flat Λ
      ((geometricPointSitePoint B S hS s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj G)) :
    (tensorRight G).Additive ∧ PreservesFiniteLimits (tensorRight G) ∧
      PreservesFiniteColimits (tensorRight G) := by
  have hc : PreservesColimitsOfSize.{u, u + 1} (tensorRight G) :=
    Sheaf.preservesColimitsOfSize_tensorRight_moduleCat.{u + 1} G
  have : PreservesFiniteColimits (tensorRight G) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight G) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have : PreservesBinaryBiproducts (tensorRight G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorRight G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have := preservesMonomorphisms_tensorRight_of_flat B S hS Λ G hG
  exact ⟨inferInstance,
    Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _,
    inferInstance⟩

end Tensor

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- **The stalks of the level sheaves of `ℱ_ρ` are free `ℤ/ℓ^kℤ`-modules**, hence flat: the stalk
at any geometric point is `(ℤ/ℓ^kℤ)^r` (`Stacks.EtaleCohomology.representationLevelStalkIso`,
for a path from the geometric point to `x̄`, which exists because `X` is connected). -/
theorem flat_sheafFiber_representationLevelSheaf
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) (k : ℕ)
    (s : GeometricPoint X.1) :
    Module.Flat (ZMod (ℓ ^ k))
      ((geometricPointSitePoint B X.1 X.2 s).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
        |>.obj (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  let e : ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) ≃+
      ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) :=
    (representationLevelStalkIso B X x ρ hρ t k).addCommGroupIsoToAddEquiv
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap (ℓ ^ k)) e.bijective)

attribute [local instance] Sheaf.monoidalCategory in
/-- **Tensoring with a level sheaf of `ℱ_ρ` is exact**, on sheaves of `ℤ/ℓ^kℤ`-modules on the
small étale site: its stalks are free. This is the hypothesis under which the cup product
`Stacks.ExtCup.cup` with coefficients in `ℱ_{ρ,k}` is defined. -/
theorem exact_tensorRight_representationLevelSheaf
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) (k : ℕ) :
    (MonoidalCategory.tensorRight (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) :=
  preservesFiniteLimits_tensorRight_of_flat B X.1 X.2 (ZMod (ℓ ^ k)) _
    (flat_sheafFiber_representationLevelSheaf B X x ρ hρ k)

end Stacks.EtaleCohomology
