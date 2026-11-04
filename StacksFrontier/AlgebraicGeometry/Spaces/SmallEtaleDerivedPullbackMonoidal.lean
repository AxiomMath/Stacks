module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.CategoryTheory.Monoidal.OplaxOfAssociativity

/-!
# Derived pullback as a monoidal functor on `D(𝒪)`

For a morphism `g : X' ⟶ X` of algebraic spaces, derived pullback `Lg^* : D(𝒪_X) ⥤ D(𝒪_{X'})`
with the isomorphisms `Lg^*(K ⊗^L L) ≅ Lg^*K ⊗^L Lg^*L` of Stacks 07A4 as structure maps is a
strong monoidal functor for the monoidal structures of Stacks 0FPT: Stacks 07A4 is compatible
with the associators, and `Lg^*𝒪_X ≅ 𝒪_{X'}`, so the tensor structure determines a unit
satisfying both unit laws (`CategoryTheory.OplaxOfAssoc`).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackMonoidal`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackMonoidal_δ`: its tensor structure map is
  Stacks 07A4.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- Naturality of Stacks 07A4 in the first variable. -/
theorem smallEtaleDerivedPullbackTensorIso_naturality_left (g : X' ⟶ X)
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (f : K ⟶ K')
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L) ≫
        ((smallEtaleDerivedTensor B S hS X').map
            ((smallEtaleDerivedModulePullback B S hS g).map f)).app
          ((smallEtaleDerivedModulePullback B S hS g).obj L) =
      (smallEtaleDerivedModulePullback B S hS g).map
          (((smallEtaleDerivedTensor B S hS X).map f).app L) ≫
        (smallEtaleDerivedPullbackTensorIso g).hom.app (K', L) := by
  simpa using ((smallEtaleDerivedPullbackTensorIso g).hom.naturality
    ((f, 𝟙 L) : ((K, L) : _ × _) ⟶ (K', L))).symm

/-- Naturality of Stacks 07A4 in the second variable. -/
theorem smallEtaleDerivedPullbackTensorIso_naturality_right (g : X' ⟶ X)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {L L' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (f : L ⟶ L') :
    (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g).obj K)).map
          ((smallEtaleDerivedModulePullback B S hS g).map f) =
      (smallEtaleDerivedModulePullback B S hS g).map
          (((smallEtaleDerivedTensor B S hS X).obj K).map f) ≫
        (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L') := by
  simpa using ((smallEtaleDerivedPullbackTensorIso g).hom.naturality
    ((𝟙 K, f) : ((K, L) : _ × _) ⟶ (K, L'))).symm

/-- The oplax monoidal structure of derived pullback on `D(𝒪)`, with cotensorator Stacks 07A4 and
the counit that the cotensorator determines. -/
@[instance_reducible]
def smallEtaleDerivedPullbackOplaxMonoidal (g : X' ⟶ X) :
    @Functor.OplaxMonoidal
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) _
      (smallEtaleDerivedMonoidal X) (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X'))) _ (smallEtaleDerivedMonoidal X')
      (smallEtaleDerivedModulePullback B S hS g) :=
  letI : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X))) := smallEtaleDerivedMonoidal X
  letI : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X'))) := smallEtaleDerivedMonoidal X'
  OplaxOfAssoc.oplaxMonoidal (smallEtaleDerivedModulePullback B S hS g)
    (fun K L => (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L))
    (fun f L => smallEtaleDerivedPullbackTensorIso_naturality_left g f L)
    (fun K f => smallEtaleDerivedPullbackTensorIso_naturality_right g K f)
    (fun A A' A'' => (smallEtaleDerivedPullbackTensorIso_associativity g A A' A'').symm)
    (smallEtaleDerivedModulePullbackUnitIso g)

/-- The counit of `smallEtaleDerivedPullbackOplaxMonoidal` is invertible. -/
theorem isIso_smallEtaleDerivedPullbackOplaxMonoidal_η (g : X' ⟶ X) :
    @IsIso _ _ _ _ (@Functor.OplaxMonoidal.η
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) _
      (smallEtaleDerivedMonoidal X) (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X'))) _ (smallEtaleDerivedMonoidal X') _
      (smallEtaleDerivedPullbackOplaxMonoidal g)) :=
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X))) := smallEtaleDerivedMonoidal X
  let : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X'))) := smallEtaleDerivedMonoidal X'
  OplaxOfAssoc.isIso_counit (smallEtaleDerivedModulePullback B S hS g)
    (fun K L => (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L))
    (fun f L => smallEtaleDerivedPullbackTensorIso_naturality_left g f L)
    (fun K f => smallEtaleDerivedPullbackTensorIso_naturality_right g K f)
    (fun A A' A'' => (smallEtaleDerivedPullbackTensorIso_associativity g A A' A'').symm)
    (smallEtaleDerivedModulePullbackUnitIso g)

/-- **Derived pullback is a monoidal functor on `D(𝒪)`**, with the isomorphisms of Stacks 07A4 as
its tensor structure, for the monoidal structures of Stacks 0FPT on `D(𝒪_X)` and `D(𝒪_{X'})`. -/
@[instance_reducible]
def smallEtaleDerivedPullbackMonoidal (g : X' ⟶ X) :
    @Functor.Monoidal
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) _
      (smallEtaleDerivedMonoidal X) (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X'))) _ (smallEtaleDerivedMonoidal X')
      (smallEtaleDerivedModulePullback B S hS g) :=
  @Functor.Monoidal.ofOplaxMonoidal _ _ (smallEtaleDerivedMonoidal X) _ _
    (smallEtaleDerivedMonoidal X') (smallEtaleDerivedModulePullback B S hS g)
    (smallEtaleDerivedPullbackOplaxMonoidal g) (isIso_smallEtaleDerivedPullbackOplaxMonoidal_η g)
    (fun K L => inferInstanceAs (IsIso ((smallEtaleDerivedPullbackTensorIso g).hom.app (K, L))))

/-- The tensor structure map of `smallEtaleDerivedPullbackMonoidal` is Stacks 07A4. -/
theorem smallEtaleDerivedPullbackMonoidal_δ (g : X' ⟶ X)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    @Functor.OplaxMonoidal.δ
        (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) _
        (smallEtaleDerivedMonoidal X) (DerivedCategory (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS X'))) _ (smallEtaleDerivedMonoidal X') _
        (smallEtaleDerivedPullbackMonoidal g).toOplaxMonoidal K L =
      (smallEtaleDerivedPullbackTensorIso g).hom.app (K, L) :=
  rfl

end AlgebraicGeometry.Space

end
