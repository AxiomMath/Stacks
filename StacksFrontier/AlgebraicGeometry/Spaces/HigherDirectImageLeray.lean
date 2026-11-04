module

public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget

/-!
# Cohomology along a composite whose first factor has no higher direct images

Let `a : X₁ ⟶ X₂` and `b : X₂ ⟶ Y` be morphisms of algebraic spaces over a scheme `S` contained
in a big fppf site `B`, and let `𝓝` be an `𝒪_{X₁}`-module whose higher direct images along `a`
vanish.  The cohomology of `𝓝` along the composite, read as the right derived functors of
`Γ(Y, (a ≫ b)_* −)`, is the cohomology of `a_*𝓝` along `b`:

`R^p Γ(Y, (a ≫ b)_* −)(𝓝) = R^p Γ(Y, b_* −)(a_*𝓝)`,

as modules over `Γ(Y, 𝒪_Y)`, in every degree.  This is the degeneration of the Leray spectral
sequence of the pair `(a, b)` ([Stacks, Tag 0733]), proved without spectral sequences.

## Main results

* `AlgebraicGeometry.Space.acyclic_pushforwardGlobalSections_modulePushforward_of_injective`:
  the direct image along `a` of an injective module is acyclic for `Γ(Y, b_* −)`.
* `AlgebraicGeometry.Space.pushforwardGlobalSectionsRightDerivedCompIso`: the identification
  above.

## Implementation notes

The identification is `Stacks.RightDerivedComp.objIsoOfAcyclicImage` for the factorization
`(a ≫ b)_* ≅ a_* ⋙ b_*` of Stacks 03LU.  Its acyclicity input is read in abelian groups, where
`Γ(Y, b_* −)` is `Γ(X₂, −)` (`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`) and the
direct image of an injective module is acyclic for global sections by Stacks 072Z and part (3)
of Stacks 0731
(`AlgebraicGeometry.Space.acyclic_globalSectionsFunctor_modulePushforward_of_injective`);
forgetting the module structure is exact, so it commutes with the right derived functors.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₁ X₂ Y : AlgebraicSpaces B S hS}

/-- If `T ⋙ G ≅ T' ⋙ G'`, then `G` of the `n`-th right derived functor of `T` vanishes at `K` as
soon as `G'` of that of `T'` does. -/
private theorem isZero_obj_rightDerived_of_iso {A D D' C : Type*} [Category A] [Category D]
    [Category D'] [Category C] [Abelian A] [Abelian D] [Abelian D'] [Abelian C]
    [HasInjectiveResolutions A] (T : A ⥤ D) (T' : A ⥤ D') (G : D ⥤ C) (G' : D' ⥤ C)
    [T.Additive] [T'.Additive] [G.Additive] [G'.Additive] [G.PreservesHomology]
    [G'.PreservesHomology] (e : T ⋙ G ≅ T' ⋙ G') (n : ℕ) (K : A)
    (h : IsZero (G'.obj ((T'.rightDerived n).obj K))) : IsZero (G.obj ((T.rightDerived n).obj K)) :=
  h.of_iso (((Functor.rightDerivedCompIso T G n).app K).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso e n).app K ≪≫ (Functor.rightDerivedCompIso T' G' n).app K)

/-- A module vanishes if its underlying `ULift`ed abelian group does. -/
private theorem isZero_of_isZero_obj_uliftForget {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact @Equiv.subsingleton _ _ (Equiv.ulift.{u + 1, u}).symm
    (AddCommGrpCat.isZero_iff_subsingleton.1 h)

/-- **The direct image of an injective module is acyclic for the cohomology along a further
morphism.**  For `a : X₁ ⟶ X₂`, `b : X₂ ⟶ Y` and an injective `𝒪_{X₁}`-module `𝓘`, the higher
right derived functors of `Γ(Y, b_* −)` vanish at `a_*𝓘`.

In abelian groups `Γ(Y, b_* −)` is `Γ(X₂, −)`, and `a_*𝓘` is acyclic for global sections on `X₂`
by Stacks 072Z and Stacks 0731 (3). -/
theorem acyclic_pushforwardGlobalSections_modulePushforward_of_injective (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ Y) (Z : Modules.{u, u} B S hS X₁.1 X₁.2) [Injective Z] :
    have := enoughInjectives_modules B S hS X₂.1 X₂.2
    Stacks.RightDerivedComp.acyclic (modulePushforward B S hS b ⋙
      globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((modulePushforward B S hS a).obj Z) := by
  intro _ n hn
  have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
  have := modulePushforward_additive B S hS b
  let T := modulePushforward B S hS b ⋙ globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
  let Γ₂ := globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O))
  have h₀ : IsZero ((forget₂ _ AddCommGrpCat.{u + 1}).obj
      ((Γ₂.rightDerived n).obj ((modulePushforward B S hS a).obj Z))) :=
    Functor.map_isZero _
      (acyclic_globalSectionsFunctor_modulePushforward_of_injective B S hS a Z n hn)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (isZero_obj_rightDerived_of_iso T Γ₂
    (forget₂ _ AddCommGrpCat.{u + 1}) (forget₂ _ AddCommGrpCat.{u + 1})
    (globalSectionsModulePushforwardIso B S hS b) n _ h₀)

/-- **Cohomology along a composite whose first factor has no higher direct images.**  For
`a : X₁ ⟶ X₂`, `b : X₂ ⟶ Y` and an `𝒪_{X₁}`-module `𝓝` with `R^q a_*𝓝 = 0` for every `q > 0`,

`R^p Γ(Y, (a ≫ b)_* −)(𝓝) ≅ R^p Γ(Y, b_* −)(a_*𝓝)`

as `Γ(Y, 𝒪_Y)`-modules, in every degree. -/
def pushforwardGlobalSectionsRightDerivedCompIso (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (N : Modules.{u, u} B S hS X₁.1 X₁.2)
    (hN : ∀ q, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
      IsZero (((modulePushforward B S hS a).rightDerived q).obj N)) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
    have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
    ((modulePushforward B S hS (a ≫ b) ⋙ globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived p).obj N ≅
      ((modulePushforward B S hS b ⋙ globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived p).obj
        ((modulePushforward B S hS a).obj N) :=
  have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
  have := enoughInjectives_modules B S hS X₂.1 X₂.2
  have := modulePushforward_additive B S hS a
  have := modulePushforward_additive B S hS b
  have := modulePushforward_additive B S hS (a ≫ b)
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  (Functor.rightDerivedIsoOfNatIso
      (Functor.isoWhiskerRight (modulePushforwardCompIso B S hS a b).symm _ ≪≫
        Functor.associator _ _ _) p).app N ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (modulePushforward B S hS a)
      (modulePushforward B S hS b ⋙ globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) hN
      (fun Z _ => acyclic_pushforwardGlobalSections_modulePushforward_of_injective B S hS a b Z) p

/-! ### Cohomology read as sections over a terminal chart

When the target `Y` has a terminal étale chart `W` — for instance when `Y` is represented by a
scheme, whose identity chart is terminal — global sections on `Y` are sections over `W`, and the
cohomology along a morphism to `Y` can be read through the functor `b_* ⋙ Γ(W, −)`, whose values
are modules over the ring `𝒪_Y(W)` of functions on the chart.  The two statements above hold
verbatim in that reading. -/

section TerminalChart

variable {W : SmallEtale B S hS Y.1} (hW : IsTerminal W)

include hW in
/-- **The direct image of an injective module is acyclic for sections over a terminal chart of
the target of a further morphism.**  This is
`AlgebraicGeometry.Space.acyclic_pushforwardGlobalSections_modulePushforward_of_injective` read
through the identification of global sections on `Y` with sections over the terminal chart `W`,
`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`, on underlying abelian
groups. -/
theorem acyclic_pushforwardEvaluation_modulePushforward_of_injective (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ Y) (Z : Modules.{u, u} B S hS X₁.1 X₁.2) [Injective Z] :
    have := enoughInjectives_modules B S hS X₂.1 X₂.2
    Stacks.RightDerivedComp.acyclic (modulePushforward B S hS b ⋙
      SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W))
      ((modulePushforward B S hS a).obj Z) := by
  intro _ n hn
  have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
  have := modulePushforward_additive B S hS b
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  have : (SheafOfModules.evaluation O (Opposite.op W)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  let T := modulePushforward B S hS b ⋙ SheafOfModules.evaluation O (Opposite.op W)
  let T' := modulePushforward B S hS b ⋙ globalSectionsFunctor.{u + 1, u, u, u} O
  let G := forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op W))) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e : T' ⋙ forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1} ≅
      T ⋙ G :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (modulePushforward B S hS b)
      (globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O (Opposite.op W) hW.op) ≪≫
      (Functor.associator _ _ _).symm
  have h₀ := acyclic_pushforwardGlobalSections_modulePushforward_of_injective B S hS a b Z n hn
  exact isZero_of_isZero_obj_uliftForget (isZero_obj_rightDerived_of_iso T T' G
    (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) e.symm n _
    (Functor.map_isZero _ h₀))

include hW in
/-- **Higher cohomology over a terminal chart vanishes with higher global cohomology.**  If
`R^n Γ(Y, −)` vanishes at an `𝒪_Y`-module `𝓚`, so does the `n`-th right derived functor of
sections over a terminal chart `W` of `Y`: on underlying abelian groups the two functors agree
(`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`), and forgetting is
exact. -/
theorem isZero_rightDerived_evaluation_of_isZero_rightDerived_globalSectionsFunctor
    (K : Modules.{u, u} B S hS Y.1 Y.2) (n : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived n).obj K)) :
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W)).rightDerived
        n).obj K) := by
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  have : (SheafOfModules.evaluation O (Opposite.op W)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  let G := forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op W))) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  exact isZero_of_isZero_obj_uliftForget (isZero_obj_rightDerived_of_iso
    (SheafOfModules.evaluation O (Opposite.op W)) (globalSectionsFunctor.{u + 1, u, u, u} O) G
    (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1})
    (globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O (Opposite.op W) hW.op).symm n K
    (Functor.map_isZero _ h))

include hW in
/-- **Cohomology along a composite whose first factor has no higher direct images, read over a
terminal chart of the target.**  For `a : X₁ ⟶ X₂`, `b : X₂ ⟶ Y`, a terminal chart `W` of `Y` and
an `𝒪_{X₁}`-module `𝓝` with `R^q a_*𝓝 = 0` for every `q > 0`,

`R^p Γ(W, (a ≫ b)_* −)(𝓝) ≅ R^p Γ(W, b_* −)(a_*𝓝)`

as `𝒪_Y(W)`-modules, in every degree. -/
def pushforwardEvaluationRightDerivedCompIso (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (N : Modules.{u, u} B S hS X₁.1 X₁.2)
    (hN : ∀ q, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
      IsZero (((modulePushforward B S hS a).rightDerived q).obj N)) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
    have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
    ((modulePushforward B S hS (a ≫ b) ⋙ SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (Opposite.op W)).rightDerived
        p).obj N ≅
      ((modulePushforward B S hS b ⋙ SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (Opposite.op W)).rightDerived
        p).obj ((modulePushforward B S hS a).obj N) :=
  have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
  have := enoughInjectives_modules B S hS X₂.1 X₂.2
  have := modulePushforward_additive B S hS a
  have := modulePushforward_additive B S hS b
  have := modulePushforward_additive B S hS (a ≫ b)
  have : (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (Opposite.op W)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  (Functor.rightDerivedIsoOfNatIso
      (Functor.isoWhiskerRight (modulePushforwardCompIso B S hS a b).symm _ ≪≫
        Functor.associator _ _ _) p).app N ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (modulePushforward B S hS a)
      (modulePushforward B S hS b ⋙ SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W)) hN
      (fun Z _ => acyclic_pushforwardEvaluation_modulePushforward_of_injective B S hS hW a b Z) p

include hW in
/-- **The degeneration of the Leray spectral sequence of `f` over a terminal chart of the
target.**  If every higher direct image `R^q f_*𝓕` is acyclic for sections over a terminal chart
`W` of `Y`, then

`R^n Γ(W, f_* −)(𝓕) ≅ Γ(W, R^n f_*𝓕)`

as `𝒪_Y(W)`-modules.  Applying `f_*` to an injective resolution of `𝓕` gives a complex whose
cohomology is `R^• f_*𝓕` and whose terms are acyclic for `Γ(W, −)`, by Stacks 072Z, and a left
exact functor commutes with the cohomology of such a complex. -/
def evaluationRightDerivedIso (f : X₁ ⟶ Y) (F : Modules.{u, u} B S hS X₁.1 X₁.2)
    (hR : ∀ q : ℕ,
      have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
      have := enoughInjectives_modules B S hS Y.1 Y.2
      Stacks.RightDerivedComp.acyclic (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (Opposite.op W))
        (((modulePushforward B S hS f).rightDerived q).obj F)) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ SheafOfModules.evaluation
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
            (Opposite.op W)).rightDerived
          n).obj F ≅
      (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (Opposite.op W)).obj (((modulePushforward B S hS f).rightDerived n).obj F) :=
  have := enoughInjectives_modules B S hS X₁.1 X₁.2
  have := hasInjectiveResolutions_modules B S hS X₁.1 X₁.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (Opposite.op W)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  (injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f ⋙
      SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W)) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic
      (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W))
      (Stacks.RightDerivedComp.mapCocomplex (modulePushforward B S hS f)
        (injectiveResolution F))
      (fun q m hm =>
        have := (injectiveResolution F).injective q
        isZero_rightDerived_evaluation_of_isZero_rightDerived_globalSectionsFunctor
          B S hS hW _ m
          (acyclic_globalSectionsFunctor_modulePushforward_of_injective B S hS f _ m hm))
      (fun q => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
        ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) q) (hR q)) n ≪≫
    (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W)).mapIso
      ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) n).symm

include hW in
/-- **Cohomology over terminal charts is unchanged by a direct image, as far as vanishing goes.**
For `b : X₂ ⟶ Y`, terminal charts `W` of `Y` and `W₂` of `X₂`, and an `𝒪_{X₂}`-module `𝓚`: if the
`n`-th right derived functor of sections over `W₂` vanishes at `𝓚`, so does the `n`-th right
derived functor of `Γ(W, b_* −)`.  On underlying abelian groups both functors are global
sections on `X₂` (`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso` and
`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`), and forgetting is
exact. -/
theorem isZero_rightDerived_pushforwardEvaluation_of_isZero_rightDerived_evaluation
    (b : X₂ ⟶ Y) {W₂ : SmallEtale B S hS X₂.1} (hW₂ : IsTerminal W₂)
    (K : Modules.{u, u} B S hS X₂.1 X₂.2) (n : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
      IsZero (((SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O))
          (Opposite.op W₂)).rightDerived
          n).obj K)) :
    have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
    IsZero (((modulePushforward B S hS b ⋙ SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (Opposite.op W)).rightDerived
        n).obj K) := by
  have := hasInjectiveResolutions_modules B S hS X₂.1 X₂.2
  have := modulePushforward_additive B S hS b
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let O₂ := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O)
  have : (SheafOfModules.evaluation O (Opposite.op W)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : (SheafOfModules.evaluation O₂ (Opposite.op W₂)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  let T := modulePushforward B S hS b ⋙ SheafOfModules.evaluation O (Opposite.op W)
  let G := forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op W))) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let G₂ := forget₂ (ModuleCat.{u} (O₂.obj.obj (Opposite.op W₂))) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e : T ⋙ G ≅ SheafOfModules.evaluation O₂ (Opposite.op W₂) ⋙ G₂ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (modulePushforward B S hS b)
      (globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O (Opposite.op W) hW.op).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ globalSectionsModulePushforwardIso B S hS b ≪≫
      globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O₂ (Opposite.op W₂) hW₂.op
  exact isZero_of_isZero_obj_uliftForget
    (isZero_obj_rightDerived_of_iso T (SheafOfModules.evaluation O₂ (Opposite.op W₂)) G G₂ e n K
      (Functor.map_isZero G₂ h))

end TerminalChart

end AlgebraicGeometry.Space

end
