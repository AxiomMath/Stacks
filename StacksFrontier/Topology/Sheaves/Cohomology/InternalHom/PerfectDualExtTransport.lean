module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PreimageSectionsForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceDegreeZeroTransport
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# `Ext` out of a perfect object as cohomology of a tensor product with its dual

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E` a perfect object of
`D(𝒪_X)` with dual `E^∨ = RSheafHom(E, 𝒪_X)`. For every object `N` of `D(𝒪_X)` and every `i`,

`H^i(X, E^∨ ⊗^L_{𝒪_X} N) ≅ Ext^i_{𝒪_X}(E, N) = Hom_{D(𝒪_X)}(E, N[i])`,

naturally in `N`, and these isomorphisms carry the connecting morphisms of an arbitrary triangle
`N₁ → N₂ → N₃ → N₁[1]` of `D(𝒪_X)` — the cohomology connecting morphism on the left, Yoneda
composition with `N₃ → N₁[1]` on the right — to one another. Cohomology on `X` is read as `H^i`
of `RΓ(f⁻¹ Y, -)`, a `Γ(Y, 𝒪_Y)`-module with its scalars forgotten.

In degree zero this is the fourth assertion of [Stacks, Tag 08DQ], `H⁰(X, M ⊗^L E^∨) = Hom(E, M)`,
read through the commutativity constraint of the derived tensor product ([Stacks, Tag 0FPT]).

## Main definitions

* `Stacks.Cohomology.PerfectDualExt.tensorSwapIso`: `E' ⊗^L - ≅ - ⊗^L E'` between the two
  canonical derived tensor products.
* `Stacks.Cohomology.PerfectDualExt.degreeZeroIso`: `H⁰(X, E^∨ ⊗^L M) ≅ Hom(E, M)`, naturally
  in `M`.
* `Stacks.Cohomology.PerfectDualExt.extIso`: `H^i(X, E^∨ ⊗^L N) ≅ Hom(E, N[i])`, naturally in
  `N`.

## Main results

* `Stacks.Cohomology.PerfectDualExt.extIso_hom_app_comp_homologySequenceδ`: compatibility with
  connecting morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Pretriangulated
open Stacks.Cohomology.ModuleSections StrictlyPerfect

universe u

namespace Stacks.Cohomology.PerfectDualExt

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing StrictlyPerfect.structureSheafOfRings
  CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The derived tensor product of [Stacks, Tag 06YU] at the structure sheaf of `X`. -/
abbrev tensor' := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf

/-- **`E' ⊗^L - ≅ - ⊗^L E'`**, from the derived tensor product of [Stacks, Tag 0A1F] with `E'`
on the left to the derived tensor product of [Stacks, Tag 08DQ] with `E'` on the right: the
commutativity constraint of [Stacks, Tag 0FPT] followed by the comparison of the two canonical
derived tensor bifunctors. -/
def tensorSwapIso (E' : DerivedCategory (OXMod.{u, u} X)) :
    (tensor' (X := X)).obj E' ≅
      (Stacks.SheafOfModules.derivedTensor X.sheaf).flip.obj E' :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (Stacks.SheafOfModules.ringedSite X.sheaf)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf)).app E' ≪≫
    NatIso.ofComponents
      (fun M => (((AlgebraicGeometry.RingedSite.derivedTensorFunctorIso
        (Stacks.SheafOfModules.ringedSite X.sheaf)).app M).app E').symm)
      (fun {M M'} m => by
        exact congrArg (fun τ => NatTrans.app τ E')
          ((AlgebraicGeometry.RingedSite.derivedTensorFunctorIso
            (Stacks.SheafOfModules.ringedSite X.sheaf)).inv.naturality m))

variable (E : DerivedCategory (OXMod.{u, u} X))
  (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) E)

/-- The dual `E^∨ = RSheafHom(E, 𝒪_X)` of [Stacks, Tag 08DQ]. -/
def dual : DerivedCategory (OXMod.{u, u} X) := Stacks.SheafOfModules.derivedDual X.sheaf E

/-- `dual E` is by definition the derived dual `Stacks.SheafOfModules.derivedDual X.sheaf E`. -/
theorem dual_eq : dual E = Stacks.SheafOfModules.derivedDual X.sheaf E :=
  rfl

/-- Forgetting the `Γ(Y, 𝒪_Y)`-module structure and lifting to the universe of the morphism
groups of `D(𝒪_X)`. -/
abbrev forgetLift :
    ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤)) ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `M ↦ RΓ(f⁻¹ ⊤, E^∨ ⊗^L M)`. -/
abbrev sections :
    DerivedCategory (OXMod.{u, u} X) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) :=
  (tensor' (X := X)).obj (dual E) ⋙
    Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤

/-- `M ↦ H⁰(X, E^∨ ⊗^L M)`, as abelian groups. -/
abbrev degreeZeroSide :
    DerivedCategory (OXMod.{u, u} X) ⥤ AddCommGrpCat.{u + 1} :=
  sections f E ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) 0 ⋙
    forgetLift (Y := Y)

include hE in
/-- **`H⁰(X, E^∨ ⊗^L M) ≅ Hom_{D(𝒪_X)}(E, M)`, naturally in `M`**: the fourth assertion of
[Stacks, Tag 08DQ], read through `E^∨ ⊗^L M ≅ M ⊗^L E^∨` and through the comparison of
`RΓ(f⁻¹ ⊤, -)` with the derived global sections of the ringed site of `X`. -/
def degreeZeroIso : degreeZeroSide f E ≅ preadditiveCoyoneda.obj (op E) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((tensor' (X := X)).obj (dual E))
        (Stacks.Cohomology.PreimageSectionsForget.homologyZeroForgetNatIso f) ≪≫
      Functor.isoWhiskerRight (tensorSwapIso (dual E))
        (derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0))
      AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
    NatIso.ofComponents
      (fun (M : DerivedCategory (OXMod.{u, u} X)) => (AddEquiv.ulift.trans
        (Stacks.SheafOfModules.derivedTensorDualGlobalSectionsAddEquivOfIsPerfectSpace
          X E M hE)).toAddCommGrpIso)
      (fun {M M' : DerivedCategory (OXMod.{u, u} X)} m => by
        ext ⟨z⟩
        exact Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_naturality X.sheaf E m z)

/-- `H⁰` on `D(Γ(Y, 𝒪_Y))`, with Mathlib's shift sequence `n ↦ H^n`. -/
abbrev H0 := DerivedCategory.homologyFunctor
  (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) 0

/-- The commutation of `RΓ(f⁻¹ ⊤, E^∨ ⊗^L -)` with the shift: that of the derived tensor
product in its second variable ([Stacks, Tag 06YU]) followed by that of derived sections. -/
instance sections_commShift : (sections f E).CommShift ℤ :=
  letI := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).commShift_right
    (dual E)
  Functor.CommShift.comp ((tensor' (X := X)).obj (dual E))
    (Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤)

/-- The shift sequence `n ↦ H^n(RΓ(f⁻¹ ⊤, E^∨ ⊗^L -))`. -/
@[implicit_reducible]
def sectionsShiftSequence : (sections f E ⋙ H0 (Y := Y)).ShiftSequence ℤ :=
  Functor.ShiftSequence.leftComp (Iso.refl _) ℤ

attribute [local instance] sectionsShiftSequence

/-- `M ↦ H⁰(X, E^∨ ⊗^L M)` as a composite to which shift sequences attach: the shift sequence of
`H⁰` along the commutation of `RΓ(f⁻¹ ⊤, E^∨ ⊗^L -)` with the shift, post-composed with
`forgetLift`. -/
abbrev cohomologySide :
    DerivedCategory (OXMod.{u, u} X) ⥤ AddCommGrpCat.{u + 1} :=
  (sections f E ⋙ H0 (Y := Y)) ⋙ forgetLift (Y := Y)

/-- The shift sequence `n ↦ H^n(X, E^∨ ⊗^L -)` of `cohomologySide`. -/
@[implicit_reducible]
def cohomologyShiftSequence : (cohomologySide f E).ShiftSequence ℤ :=
  Functor.ShiftSequence.rightComp (sections f E ⋙ H0 (Y := Y)) (forgetLift (Y := Y))

attribute [local instance] cohomologyShiftSequence

include hE in
/-- `degreeZeroIso` between the degree-zero functors of the two shift sequences. -/
def degreeZeroShiftIso :
    (cohomologySide f E).shift (0 : ℤ) ≅ (preadditiveCoyoneda.obj (op E)).shift (0 : ℤ) :=
  (cohomologySide f E).isoShiftZero ℤ ≪≫ degreeZeroIso f E hE ≪≫
    ((preadditiveCoyoneda.obj (op E)).isoShiftZero ℤ).symm

include hE in
/-- **`H^i(X, E^∨ ⊗^L N) ≅ Hom_{D(𝒪_X)}(E, N[i])`, naturally in `N`.** The left side is
`H^i(RΓ(f⁻¹ ⊤, E^∨ ⊗^L N))` with its scalars forgotten; the right side is
`(preadditiveCoyoneda.obj (op E)).shift i`, whose value at `N` is `E ⟶ N⟦i⟧`. -/
def extIso (i : ℤ) :
    (cohomologySide f E).shift i ≅ (preadditiveCoyoneda.obj (op E)).shift i :=
  Functor.shiftSequenceTransportIso _ _ (degreeZeroShiftIso f E hE) i

/-- The connecting morphisms of the left side are the images of those of `H⁰` at the image of
the triangle under `RΓ(f⁻¹ ⊤, E^∨ ⊗^L -)`. -/
theorem cohomologySide_homologySequenceδ (T : Triangle (DerivedCategory (OXMod.{u, u} X)))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (cohomologySide f E).homologySequenceδ T n₀ n₁ h =
      (forgetLift (Y := Y)).map ((sections f E ⋙ H0 (Y := Y)).homologySequenceδ T n₀ n₁ h) :=
  Functor.ShiftSequence.rightComp_homologySequenceδ _ _ T n₀ n₁ h

include hE in
/-- **The isomorphisms `H^i(X, E^∨ ⊗^L -) ≅ Hom(E, -[i])` carry connecting morphisms to Yoneda
composition with the third morphism**, for every triangle `T` of `D(𝒪_X)`: the square formed by
the connecting morphism `H^i(X, E^∨ ⊗^L T₃) ⟶ H^{i+1}(X, E^∨ ⊗^L T₁)`, the map
`x ↦ x ≫ T.mor₃⟦i⟧' ≫ (T₁⟦1⟧⟦i⟧ ≅ T₁⟦i + 1⟧)` and the two isomorphisms commutes. -/
theorem extIso_hom_app_comp_homologySequenceδ
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (extIso f E hE n₀).hom.app T.obj₃ ≫
        (preadditiveCoyoneda.obj (op E)).homologySequenceδ T n₀ n₁ h =
      (forgetLift (Y := Y)).map ((sections f E ⋙ H0 (Y := Y)).homologySequenceδ T n₀ n₁ h) ≫
        (extIso f E hE n₁).hom.app T.obj₁ := by
  rw [← cohomologySide_homologySequenceδ]
  exact Functor.shiftSequenceTransport_app_comp_homologySequenceδ _ _ _ T n₀ n₁ h

end Stacks.Cohomology.PerfectDualExt

end
