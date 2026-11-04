module

public import StacksFrontier.AlgebraicGeometry.Quot.LimitDerivedHomUnitColimUnitCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.UnitEndomorphismValues
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingSquares

/-!
# The cocycle of `Lf^*𝒪_Y ≅ 𝒪_X`

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the identification
`AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` of `Lf^*𝒪_Y` with `𝒪_X` is
compatible with the composition comparison `L(f ≫ g)^* ≅ Lf^* ∘ Lg^*` of Stacks 0D6D. This is
deduced from the same compatibility of the underived identification `f^*𝒪_Y ≅ 𝒪_X` of
Stacks 03LU, by placing it in degree zero and passing to homotopy categories and left derived
functors (Stacks 06YY).

## Main results

* `CategoryTheory.PullbackData.leftDerived_transport_unit_comp`: for a transported pullback datum,
  the cocycle of an identification of inverse images of a distinguished object gives the cocycle
  of the induced identification of derived inverse images of that object in degree zero.
* `AlgebraicGeometry.Space.modulePullbackUnitIsoS_comp`: Stacks 03LU at the structure sheaf, in
  the spelling of `AlgebraicGeometry.Space.modulePullbackUnitIsoS`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso_comp`: the cocycle of
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso` at the single complex
  `𝒪[0]`.
* `AlgebraicGeometry.Space.derivedPullbackCoherence_unitPullIso_comp`: the cocycle of
  `AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` for
  `AlgebraicGeometry.Space.derivedPullbackCoherence`.

## Implementation notes

The structure sheaf has two spellings, through `AlgebraicGeometry.Space.smallEtaleRingedSite` and
through `AlgebraicGeometry.Space.smallEtaleRingedTopos`. The first is a plain `def` and the second
an `abbrev`, so the two are definitionally equal only at default transparency, and a unifier pass
at reducible transparency falls back to weak-head normalising the inverse image of modules, a
sheafification of a tensor product.

* Both sides are written with `AlgebraicGeometry.Space.modulePullbackUnitIsoS`, whose declared
  type ascribes the identification of Stacks 03LU to the modules of the small étale ringed topos,
  so the implicit site, topology and category arguments inside `SheafOfModules.unit` agree
  syntactically. With `AlgebraicGeometry.Space.modulePullbackUnitIso`, whose type is indexed
  through the ringed site, they disagree and unification does not finish.
* The three generic steps (transport along isomorphisms of the inverse images, passage to the
  homotopy categories, passage to the left derived functors) are composed into the single
  statement `CategoryTheory.PullbackData.leftDerived_transport_unit_comp` before being
  instantiated, so that no intermediate statement mentions the transported datum's inverse image
  at the concrete datum.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Preadditive (M a)] [∀ a, HasZeroObject (M a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)]

/-- **The cocycle of an identification of derived inverse images of a distinguished object, for a
transported datum.** An identification `f^*O_b ≅ O_a` of the inverse images of `P'` satisfying the
cocycle for `P'` gives, placed in degree zero and read through the comparison of Stacks 06YY, an
identification of the derived inverse images satisfying the cocycle for the left derived datum of
`CategoryTheory.PullbackData.transport`. -/
theorem leftDerived_transport_unit_comp (P' : PullbackData A M)
    (pull' : ∀ {a b : A}, (a ⟶ b) → (M b ⥤ M a))
    (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P'.pull f)
    [∀ {a b : A} (f : a ⟶ b), ((transport P' pull' ε).pull f).Additive]
    (Q : ∀ a, HomotopyCategory (M a) (ComplexShape.up ℤ) ⥤ D a)
    (W : ∀ a, MorphismProperty (HomotopyCategory (M a) (ComplexShape.up ℤ)))
    [∀ a, (Q a).IsLocalization (W a)]
    (L : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (c : ∀ {a b : A} (f : a ⟶ b), Q b ⋙ L f ⟶ ((transport P' pull' ε).toHomotopy).pull f ⋙ Q a)
    [hL : ∀ {a b : A} (f : a ⟶ b), (L f).IsLeftDerivedFunctor (c f) (W b)]
    [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d),
      IsIso (derivedComp Q W ((transport P' pull' ε).toHomotopy) L c f g)]
    [hid : ∀ a : A, IsIso (derivedIdLift Q W ((transport P' pull' ε).toHomotopy) L c a)]
    {a b d : A} (f : a ⟶ b) (g : b ⟶ d) {Oa : M a} {Ob : M b} {Od : M d}
    (mf : (P'.pull f).obj Ob ≅ Oa) (mg : (P'.pull g).obj Od ≅ Ob)
    (mk : (P'.pull (f ≫ g)).obj Od ≅ Oa)
    (h : (P'.compIso f g).hom.app Od ≫ (P'.pull f).map mg.hom ≫ mf.hom = mk.hom) :
    ((leftDerived Q W ((transport P' pull' ε).toHomotopy) L c).compIso f g).hom.app
          ((Q d).obj ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od))) ≫
        (L f).map ((c g).app ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) ≫
            (Q b).map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
              (singleUnitIso (transport P' pull' ε) g ((ε g).app Od ≪≫ mg)).hom)) ≫
          (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj Ob)) ≫
            (Q a).map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
              (singleUnitIso (transport P' pull' ε) f ((ε f).app Ob ≪≫ mf)).hom) =
      (c (f ≫ g)).app ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) ≫
        (Q a).map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
          (singleUnitIso (transport P' pull' ε) (f ≫ g) ((ε (f ≫ g)).app Od ≪≫ mk)).hom) :=
  leftDerived_unit_comp Q W ((transport P' pull' ε).toHomotopy) L c f g _ _ _
    (toHomotopy_unit_comp (transport P' pull' ε) f g
      ((ε f).app Ob ≪≫ mf) ((ε g).app Od ≪≫ mg) ((ε (f ≫ g)).app Od ≪≫ mk)
      (transport_unit_comp P' pull' ε f g mf mg mk h))

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03LU at the structure sheaf, along a composite**, in the spelling of
`AlgebraicGeometry.Space.modulePullbackUnitIsoS`: the comparison of the inverse images along
`f ≫ g` followed by the identifications `f^*g^*𝒪 ≅ f^*𝒪 ≅ 𝒪` is the identification for `f ≫ g`,
with the composition comparison read off `AlgebraicGeometry.Space.toposModulePullbackData`. -/
theorem modulePullbackUnitIsoS_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((toposModulePullbackData B S hS).compIso f g).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS Z)) ≫
        ((toposModulePullbackData B S hS).pull f).map (modulePullbackUnitIsoS g).hom ≫
        (modulePullbackUnitIsoS f).hom =
      (modulePullbackUnitIsoS (f ≫ g)).hom :=
  modulePullbackCompIso_inv_app_unit_comp f g

/-- **The cocycle of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso`.**
For `f : X ⟶ Y` and `g : Y ⟶ Z` the two ways of identifying `L(f ≫ g)^*𝒪_Z[0]` with `𝒪_X[0]`
agree: the identification for the composite is the composition comparison of Stacks 0D6D, followed
by the identification for `g` pushed forward by `Lf^*`, followed by the identification for `f`. -/
theorem smallEtaleDerivedPullbackUnitComplexIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((derivedPullbackCoherence B S hS).compIso f g).hom.app
          ((toposQh Z).obj (unitComplex Z)) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          (smallEtaleDerivedPullbackUnitComplexIso g).hom ≫
        (smallEtaleDerivedPullbackUnitComplexIso f).hom =
      (smallEtaleDerivedPullbackUnitComplexIso (f ≫ g)).hom := by
  rw [smallEtaleDerivedPullbackUnitComplexIso_hom f, smallEtaleDerivedPullbackUnitComplexIso_hom g,
    smallEtaleDerivedPullbackUnitComplexIso_hom (f ≫ g)]
  exact PullbackData.leftDerived_transport_unit_comp (toposModulePullbackData B S hS)
    (fun f => (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules)
    (fun f => toposPullbackModulesIso f)
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
    (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
    (hid := fun X => isIso_smallEtaleDerivedIdLift X) f g
    (modulePullbackUnitIsoS f) (modulePullbackUnitIsoS g) (modulePullbackUnitIsoS (f ≫ g))
    (modulePullbackUnitIsoS_comp f g)

/-- **The cocycle of `AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` for
`AlgebraicGeometry.Space.derivedPullbackCoherence`**: the identification `Lf^*𝒪_Y ≅ 𝒪_X` is
compatible with the composition comparison of Stacks 0D6D. -/
theorem derivedPullbackCoherence_unitPullIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((derivedPullbackCoherence B S hS).compIso f g).hom.app (structureObject B S hS Z) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          ((derivedPullbackCoherence B S hS).unitPullIso g).hom ≫
        ((derivedPullbackCoherence B S hS).unitPullIso f).hom =
      ((derivedPullbackCoherence B S hS).unitPullIso (f ≫ g)).hom :=
  unitPullIso_comp smallEtaleDerivedPullbackUnitComplexIso_comp f g

end AlgebraicGeometry.Space

end
