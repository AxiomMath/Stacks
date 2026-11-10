module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Functor

/-!
# Twisting modules on `ℙⁿ_T` over an arbitrary base

For a scheme `T`, an integer `d` and a module `ℱ` on `ℙⁿ_T`, the twist `ℱ(d) = ℱ ⊗ 𝒪(d)` is formed
with the pullback `𝒪(d)` of the twisting sheaf of the integral model `ℙⁿ_ℤ`
(`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver`). Over `T = Spec R` it is
`AlgebraicGeometry.projectiveTwist` on the nose. The proof of Stacks 0DPA twists a flat family of
quotients `𝒪^{⊕ r} ⟶ 𝒬` on `ℙⁿ_T` by the integer `m` of Stacks 08AG; this file records what that
needs: the twist of a module of finite presentation flat over `T` is again such a module, and
twisting commutes with base change `ℙⁿ_{T'} ⟶ ℙⁿ_T`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.twist d ℱ`: the twist `ℱ(d)` on `ℙⁿ_T`.
* `AlgebraicGeometry.ProjectiveQuot.twistPullbackIso g d ℱ`: `(g^* ℱ)(d) ≅ g^*(ℱ(d))` for the
  base change `ℙⁿ_{T'} ⟶ ℙⁿ_T` of `g : T' ⟶ T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.twist_spec`: over `Spec R` the twist is `projectiveTwist`.
* `AlgebraicGeometry.ProjectiveQuot.isFinitePresentation_twist` and
  `AlgebraicGeometry.ProjectiveQuot.isFlatOver_twist`: twisting preserves finite presentation and
  flatness over any morphism, since `𝒪(d)` is invertible and its stalks are free of rank one.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n : ℕ}

variable (n) in
/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_T`, pulled back from the integral model. -/
abbrev twistingSheaf (T : Scheme.{u}) (d : ℤ) : (projectiveSpaceOver n T).Modules :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n T d

/-- **The twist `ℱ(d) = ℱ ⊗ 𝒪(d)` of a module on `ℙⁿ_T`.** -/
abbrev twist {T : Scheme.{u}} (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    (projectiveSpaceOver n T).Modules :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
      (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩)).obj (F, twistingSheaf n T d)

/-- Over `Spec R`, the twist is `AlgebraicGeometry.projectiveTwist`. -/
theorem twist_spec (R : Type u) [CommRing R] (d : ℤ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) :
    twist d F = projectiveTwist n F d :=
  rfl

/-- The twist is the tensor product `AlgebraicGeometry.Scheme.Modules.tensorObj` with `𝒪(d)`. -/
theorem twist_eq_tensorObj {T : Scheme.{u}} (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    twist d F = Scheme.Modules.tensorObj F (twistingSheaf n T d) :=
  rfl

/-- **Twisting preserves finite presentation.** -/
theorem isFinitePresentation_twist {T : Scheme.{u}} (d : ℤ) (F : (projectiveSpaceOver n T).Modules)
    (hF : F.IsFinitePresentation) : (twist d F).IsFinitePresentation :=
  Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_tensorSheaf _ F _ hF
    (Stacks.ModuleDescent.isFinitePresentation_of_isInvertible _ _
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n T
        d).toAlgebraicGeometry)

/-- **Twisting preserves flatness over any morphism**: the stalk of `ℱ(d)` at a point is linearly
isomorphic to that of `ℱ`, the stalks of `𝒪(d)` being free of rank one. -/
theorem isFlatOver_twist {S T : Scheme.{u}} (f : projectiveSpaceOver n T ⟶ S) (d : ℤ)
    (F : (projectiveSpaceOver n T).Modules) (hF : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver f.toLRSHom.toShHom (twist d F) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveSpaceOver n T).sheaf.obj
      (projectiveSpaceOver n T).ringCatSheaf.property (twistingSheaf n T d) :=
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n T
      d).toAlgebraicGeometry
  intro x
  have hx := hF x
  let e := Stacks.Divisors.tensorInvertibleStalkEquiv F (twistingSheaf n T d) x
  let : Module (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    Module.compHom _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
  let : Module (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (twist d F).val.presheaf x) :=
    Module.compHom _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
  have : Module.Flat (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := hx
  let e' : TopCat.Presheaf.stalk (C := Ab.{u}) (twist d F).val.presheaf x
      ≃ₗ[S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x)]
      TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x :=
    { e.toAddEquiv with map_smul' := fun a m => e.map_smul _ m }
  change Module.Flat (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
    (TopCat.Presheaf.stalk (C := Ab.{u}) (twist d F).val.presheaf x)
  exact Module.Flat.of_linearEquiv e'

/-! ### Base change -/

variable (n) in
/-- The pullback of `𝒪(d)` along `ℙⁿ_{T'} ⟶ ℙⁿ_T` is `𝒪(d)`: both are pulled back from the integral
model, and `ℙⁿ_{T'} ⟶ ℙⁿ_T` lies over the identity of the integral model. -/
def twistingSheafPullbackIso {T' T : Scheme.{u}} (g : T' ⟶ T) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistingSheaf n T d) ≅
      twistingSheaf n T' d :=
  (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
      (projectiveSpaceOver.toIntegralAtUniverse n T)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd n g)).app _

/-- **Twisting commutes with base change**: `(g^* ℱ)(d) ≅ g^*(ℱ(d))` for the base change
`ℙⁿ_{T'} ⟶ ℙⁿ_T` of `g : T' ⟶ T` (Stacks 01CD for the tensor product). The pair at which the
comparison is read is written out. -/
def twistPullbackIso {T' T : Scheme.{u}} (g : T' ⟶ T) (d : ℤ)
    (F : (projectiveSpaceOver n T).Modules) :
    twist d ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twist d F) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n T').toSheafedSpace.presheaf,
        (projectiveSpaceOver n T').toSheafedSpace.IsSheaf⟩)).mapIso
      (Iso.prod (Iso.refl ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F))
        (twistingSheafPullbackIso n g d).symm) ≪≫
    ((Stacks.RingedSpace.comparisonBifunctorIso
        (projectiveSpaceOverMap n g).toLRSHom.toShHom).app
      (F, twistingSheaf n T d)).symm

/-- The twist `φ(d) : ℱ(d) ⟶ 𝒢(d)` of a morphism of modules on `ℙⁿ_T`. -/
abbrev twistMap {T : Scheme.{u}} (d : ℤ) {F G : (projectiveSpaceOver n T).Modules} (φ : F ⟶ G) :
    twist d F ⟶ twist d G :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
      (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩)).map
    ((φ, 𝟙 (twistingSheaf n T d)) : (F, twistingSheaf n T d) ⟶ (G, twistingSheaf n T d))

/-- In a bifunctor, a morphism in the first variable commutes with one in the second. -/
private theorem bifunctor_map_comm {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (H : C × D ⥤ E) {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    H.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ H.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
      H.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ H.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) := by
  rw [← H.map_comp, ← H.map_comp]
  congr 1
  exact Prod.ext (by simp) (by simp)

/-- **`AlgebraicGeometry.ProjectiveQuot.twistPullbackIso` is natural in the module.** -/
theorem twistPullbackIso_hom_naturality {T' T : Scheme.{u}} (g : T' ⟶ T) (d : ℤ)
    {F G : (projectiveSpaceOver n T).Modules} (φ : F ⟶ G) :
    twistMap d ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map φ) ≫
        (twistPullbackIso g d G).hom =
      (twistPullbackIso g d F).hom ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistMap d φ) := by
  have nat := ((Stacks.RingedSpace.comparisonBifunctorIso
    (projectiveSpaceOverMap n g).toLRSHom.toShHom).inv.naturality
      ((φ, 𝟙 (twistingSheaf n T d)) : (F, twistingSheaf n T d) ⟶ (G, twistingSheaf n T d)))
  have nat' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n T').toSheafedSpace.presheaf,
        (projectiveSpaceOver n T').toSheafedSpace.IsSheaf⟩)).map
        (((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map φ,
          𝟙 ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistingSheaf n T d))) :
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F,
            (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistingSheaf n T d)) ⟶
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G,
            (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistingSheaf n T d))) ≫
        (Stacks.RingedSpace.comparisonBifunctorIso
          (projectiveSpaceOverMap n g).toLRSHom.toShHom).inv.app (G, twistingSheaf n T d) =
      (Stacks.RingedSpace.comparisonBifunctorIso
          (projectiveSpaceOverMap n g).toLRSHom.toShHom).inv.app (F, twistingSheaf n T d) ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistMap d φ) := by
    rw [← CategoryTheory.Functor.map_id (Scheme.Modules.pullback (projectiveSpaceOverMap n g))]
    exact nat
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (bifunctor_map_comm (Functor.uncurry.obj _) _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) nat').trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.ProjectiveQuot

end
