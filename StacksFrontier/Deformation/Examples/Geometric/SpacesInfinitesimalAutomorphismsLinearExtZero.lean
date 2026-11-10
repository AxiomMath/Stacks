module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearDerivations
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear

/-!
# `Ext⁰` out of the naive cotangent complex is `Hom(Ω, -)` linearly

Let `𝒜` be an abelian category, linear over a ring `R`.  For a map `f : X₀ ⟶ X₁` of `𝒜`, the
identification `Ext⁰_𝒜(double f, G) = Hom_𝒜(coker f, G)` of
`StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv`, which is taking `H⁰`, is `R`-linear, because
the homology functor on the derived category is.  Applied to the naive cotangent complex of a
morphism `f : X ⟶ Y` of algebraic spaces this makes the degree `0` identification of
Stacks 0D0Y, `Ext⁰_{𝒪_X}(NL_{X/Y}, F) = Hom_{𝒪_X}(Ω_{X/Y}, F)`, linear over any ring `R` mapping
to the global functions `Γ(X, 𝒪_X)`.

## Main results

* `StacksDraft.TwoTermExt.twoTermExtZeroHom_smul`: taking `H⁰` is `R`-linear on `Ext⁰`.
* `AlgebraicGeometry.Space.naiveCotangentExtZeroAddEquivDifferentialsHom_smul` and
  `AlgebraicGeometry.Space.naiveCotangentExtZeroLinearEquivDifferentialsHom`:
  `Ext⁰_{𝒪_X}(NL_{X/Y}, F) ≃ₗ[R] Hom_{𝒪_X}(Ω_{X/Y}, F)`.

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace StacksDraft.TwoTermExt

universe t v u

variable {R : Type*} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{t} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) (G : C)

/-- **Taking `H⁰` on `Ext⁰` out of a two-term complex is `R`-linear.** -/
theorem twoTermExtZeroHom_smul (r : R) (ξ : twoTermExt.{v, u, t} f G 0) :
    twoTermExtZeroHom.{v, u, t} f G (r • ξ) = r • twoTermExtZeroHom.{v, u, t} f G ξ := by
  rw [twoTermExtZeroHom_apply, twoTermExtZeroHom_apply]
  have h : (DerivedCategory.homologyFunctor C 0).shiftMap (r • ξ) 0 0 (by lia) =
      r • (DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by lia) := by
    simp only [Functor.shiftMap]
    have h0 : ((DerivedCategory.homologyFunctor C 0).shift (0 : ℤ)).map (r • ξ) =
        r • ((DerivedCategory.homologyFunctor C 0).shift (0 : ℤ)).map ξ :=
      (DerivedCategory.homologyFunctor C 0).map_smul r ξ
    rw [h0, Linear.smul_comp]
  rw [h]
  exact (congrArg ((homologyZeroTwoTermIso.{v, u, t} f).inv ≫ ·)
    (Linear.smul_comp _ _ _ r _ _)).trans (Linear.comp_smul _ _ _ _ r _)

end StacksDraft.TwoTermExt

namespace Stacks.SheafOfModules

universe t z w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  [HasDerivedCategory.{t}
    (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]
  {R : Type*} [Ring R]
  [Linear R (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- **`Ext⁰_B(NL_{B/A}, 𝒢) = Hom_B(Ω_{B/A}, 𝒢)` is `R`-linear**, for any `R`-linear structure on
the sheaves of `B`-modules. -/
theorem naiveCotangentExtZeroAddEquiv_smul (r : R)
    (ξ : naiveCotangentExt.{v, u, w, z, t} J A B a G 0) :
    naiveCotangentExtZeroAddEquiv.{v, u, w, z, t} J A B a G (r • ξ) =
      r • naiveCotangentExtZeroAddEquiv.{v, u, w, z, t} J A B a G ξ := by
  change (canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a).inv ≫
      StacksDraft.TwoTermExt.twoTermExtZeroHom _ G (r • ξ) =
    r • ((canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a).inv ≫
      StacksDraft.TwoTermExt.twoTermExtZeroHom _ G ξ)
  exact (congrArg ((canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a).inv ≫ ·)
    (StacksDraft.TwoTermExt.twoTermExtZeroHom_smul _ G r ξ)).trans (Linear.comp_smul _ _ _ _ r _)

end Stacks.SheafOfModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- The sections of the structure sheaf of the small étale ringed topos commute, in the shape
the global-section constructions of `Stacks.Cohomology.SiteModules` take as a hypothesis. -/
instance smallEtaleRingedTopos_isMulCommutative (X : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    IsMulCommutative
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj U) :=
  structureRingSheaf_isMulCommutative B S hS X U

variable [HasDerivedCategory.{w} (NaiveCotangentModules B S hS X)]
  {R : Type*} [CommRing R] (ψ : R →+* GlobalSectionRing (structureRingSheaf B S hS X))

/-- The `R`-linear structure on the `𝒪_X`-modules in which `NL_{X/Y}` lives, induced by
`ψ : R →+* Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def naiveCotangentModulesLinear : Linear R (NaiveCotangentModules B S hS X) :=
  letI := linearSheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
  Linear.ofRingHom (D := NaiveCotangentModules B S hS X)
    (S := GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) ψ

omit [HasDerivedCategory.{w} (NaiveCotangentModules B S hS X)] in
/-- Reading a map out of the module of differentials of Stacks 04BN at the universe of `NL_{X/Y}`
as a derivation into `F` is linear over the global functions. -/
theorem derivationULiftAddEquiv_siteDifferentialsHomAddEquiv_smul (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (r : R)
    (g : AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1, u, u}
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
        (structureSharpInverseImage B S hS f) ⟶ naiveCotangentCoefficient B S hS F) :
    letI := naiveCotangentModulesLinear B S hS ψ
    derivationULiftAddEquiv B S hS f F (siteDifferentialsHomAddEquiv B S hS f _ (r • g)) =
      ψ r • derivationULiftAddEquiv B S hS f F (siteDifferentialsHomAddEquiv B S hS f _ g) := by
  let := naiveCotangentModulesLinear B S hS ψ
  ext U x
  let dX := (AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1, u, u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)).d x
  let c : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj U :=
    (ψ r).1 U
  exact (congrArg ULift.down ((g.val.app U).hom.map_smul c dX) :)

/-- **The degree `0` identification of Stacks 0D0Y is `R`-linear**, for a ring `R` acting on
`𝒪_X`-modules through `ψ : R →+* Γ(X, 𝒪_X)`. -/
theorem naiveCotangentExtZeroAddEquivDifferentialsHom_smul (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (r : R)
    (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (naiveCotangentCoefficient B S hS F)) 0) :
    letI := naiveCotangentModulesLinear B S hS ψ
    letI := modulesLinearOfRingHom B S hS ψ
    naiveCotangentExtZeroAddEquivDifferentialsHom B S hS f F (r • ξ) =
      r • naiveCotangentExtZeroAddEquivDifferentialsHom B S hS f F ξ := by
  let := naiveCotangentModulesLinear B S hS ψ
  let := modulesLinearOfRingHom B S hS ψ
  have key : naiveCotangentExtZeroAddEquivDerivations B S hS f F (r • ξ) =
      ψ r • naiveCotangentExtZeroAddEquivDerivations B S hS f F ξ := by
    let E := Stacks.SheafOfModules.naiveCotangentExtZeroAddEquiv.{u, u + 1, u, u, w}
      (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
      (naiveCotangentCoefficient B S hS F)
    have h : E (r • ξ) = r • E ξ :=
      Stacks.SheafOfModules.naiveCotangentExtZeroAddEquiv_smul.{w, u, u, u, u + 1}
        (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
        (naiveCotangentCoefficient B S hS F) r ξ
    exact ((congrArg (fun g => derivationULiftAddEquiv B S hS f F
      (siteDifferentialsHomAddEquiv B S hS f _ g)) h).trans
        (derivationULiftAddEquiv_siteDifferentialsHomAddEquiv_smul B S hS ψ f F r (E ξ)) :)
  apply (differentialsHomAddEquiv B S hS f F).injective
  refine Eq.trans ?_ ((differentialsHomGlobalSectionLinearEquiv B S hS f F).map_smul (ψ r) _).symm
  simp only [naiveCotangentExtZeroAddEquivDifferentialsHom, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  exact key.trans (congrArg (ψ r • ·)
    (AddEquiv.apply_symm_apply (differentialsHomAddEquiv B S hS f F) _).symm)

/-- **`Ext⁰_{𝒪_X}(NL_{X/Y}, F) = Hom_{𝒪_X}(Ω_{X/Y}, F)` as `R`-modules**, for a ring `R` acting on
`𝒪_X`-modules through `ψ : R →+* Γ(X, 𝒪_X)`: the degree `0` identification of Stacks 0D0Y. -/
def naiveCotangentExtZeroLinearEquivDifferentialsHom (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    letI := naiveCotangentModulesLinear B S hS ψ
    letI := modulesLinearOfRingHom B S hS ψ
    DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (naiveCotangentCoefficient B S hS F)) 0 ≃ₗ[R]
      (sheafOfDifferentials B S hS f ⟶ F) :=
  letI := naiveCotangentModulesLinear B S hS ψ
  letI := modulesLinearOfRingHom B S hS ψ
  { naiveCotangentExtZeroAddEquivDifferentialsHom B S hS f F with
    map_smul' := naiveCotangentExtZeroAddEquivDifferentialsHom_smul B S hS ψ f F }

/-- The `R`-linear identification of Stacks 0D0Y has the underlying map
`AlgebraicGeometry.Space.naiveCotangentExtZeroAddEquivDifferentialsHom`. -/
theorem naiveCotangentExtZeroLinearEquivDifferentialsHom_apply (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (naiveCotangentCoefficient B S hS F)) 0) :
    naiveCotangentExtZeroLinearEquivDifferentialsHom B S hS ψ f F ξ =
      naiveCotangentExtZeroAddEquivDifferentialsHom B S hS f F ξ :=
  rfl

end AlgebraicGeometry.Space
