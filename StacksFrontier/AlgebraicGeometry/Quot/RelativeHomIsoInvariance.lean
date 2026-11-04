module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeKernelFunctor

/-!
# The relative Hom functor only depends on the situation up to isomorphism

In Situation 08JT let `e : X ≅ X'` be an isomorphism of algebraic spaces over the base, and let
the two modules `F`, `G` on `X` be identified with the pullbacks along `e` of two modules `F'`,
`G'` on `X'`.  Then the relative Hom functors of `(X, F, G)` and of `(X', F', G')` are
isomorphic.

## Main definitions

* `AlgebraicGeometry.Space.moduleHomOverCongrSource`: an isomorphism of the source module
  induces an isomorphism of relative Hom functors over the algebraic spaces over `X`.
* `AlgebraicGeometry.Space.baseChangeOverIsoOfIso`: base change along an isomorphism of the
  source, as an isomorphism of functors to the algebraic spaces over the new source.
* `AlgebraicGeometry.Space.HomSituation.homFunctorIsoOfIso`: **the invariance.**

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS}

/-- Precomposing with the image of an isomorphism and then with the image of its inverse
changes nothing. -/
theorem map_hom_map_inv_comp {C : Type*} {D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {F F₂ : C} (a : F ≅ F₂) {A : D} (α : P.obj F ⟶ A) :
    P.map a.hom ≫ P.map a.inv ≫ α = α := by
  rw [← Category.assoc, ← P.map_comp, a.hom_inv_id, P.map_id, Category.id_comp]

/-- Precomposing with the image of the inverse of an isomorphism and then with the image of the
isomorphism changes nothing. -/
theorem map_inv_map_hom_comp {C : Type*} {D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {F F₂ : C} (a : F ≅ F₂) {A : D} (α : P.obj F₂ ⟶ A) :
    P.map a.inv ≫ P.map a.hom ≫ α = α := by
  exact map_hom_map_inv_comp P a.symm α

/-- Precomposition with the inverse image of an isomorphism of the source module, as an
isomorphism of the two Hom sets over an algebraic space over `X`. -/
def moduleHomOverSourceIso {F F₂ : Modules.{u, u} B S hS X.1 X.2} (a : F ≅ F₂)
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : Over X) :
    moduleHomOverObj F G Z ≅ moduleHomOverObj F₂ G Z where
  hom := ↾fun α : (modulePullback B S hS Z.hom).obj F ⟶ (modulePullback B S hS Z.hom).obj G ↦
    (modulePullback B S hS Z.hom).map a.inv ≫ α
  inv := ↾fun α : (modulePullback B S hS Z.hom).obj F₂ ⟶ (modulePullback B S hS Z.hom).obj G ↦
    (modulePullback B S hS Z.hom).map a.hom ≫ α
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun α ↦
    map_hom_map_inv_comp (modulePullback B S hS Z.hom) a α
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun α ↦
    map_inv_map_hom_comp (modulePullback B S hS Z.hom) a α

/-- **An isomorphism of the source module induces an isomorphism of relative Hom functors over
the algebraic spaces over `X`.**  Its naturality is the naturality of the comparison of iterated
inverse images in the module. -/
def moduleHomOverCongrSource (hc : ModulePushforwardCoherence B S hS)
    {F F₂ : Modules.{u, u} B S hS X.1 X.2} (a : F ≅ F₂) (G : Modules.{u, u} B S hS X.1 X.2) :
    moduleHomOver hc F G ≅ moduleHomOver hc F₂ G :=
  NatIso.ofComponents (fun Z ↦ moduleHomOverSourceIso a G Z.unop)
    (fun {Z Z'} m ↦ ofHom_comp_eq_comp
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      (fun α ↦ (modulePullback B S hS (Opposite.unop Z').hom).map a.inv ≫ α)
      (fun α ↦ (modulePullback B S hS (Opposite.unop Z).hom).map a.inv ≫ α)
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      fun α ↦ (CategoryTheory.Functor.conjHom_map_comp
        (modulePullbackTriangle B S hS (Over.w m.unop)) a.inv α).symm)

/-- **Base change along an isomorphism of the source.**  For `e : X ≅ X'` and `f' : X' ⟶ Y`, the
base change of `e.hom ≫ f'` along the test schemes over `Y`, read over `X'` through `e`, is the
base change of `f'`: the comparison `X_T ⟶ X'_T` is a base change of the isomorphism `e`. -/
def baseChangeOverIsoOfIso (e : X ≅ X') (f' : X' ⟶ Y) :
    baseChangeOver (e.hom ≫ f') ⋙ Over.map e.hom ≅ baseChangeOver f' :=
  have : ∀ T, IsIso (baseChangeSourceMap f' e.hom T) := fun T =>
    have : IsIso e.hom := inferInstance
    (isPullback_baseChangeSourceMap f' e.hom T).isIso_fst_of_isIso
  have : ∀ T, IsIso ((baseChangeSourceOver f' e.hom).app T) := fun T =>
    have : IsIso ((Over.forget X').map ((baseChangeSourceOver f' e.hom).app T)) := this T
    isIso_of_reflects_iso _ (Over.forget X')
  have := NatIso.isIso_of_isIso_app (baseChangeSourceOver f' e.hom)
  asIso (baseChangeSourceOver f' e.hom)

namespace HomSituation

/-- **The relative Hom functor only depends on the situation up to isomorphism.**  If
`e : X ≅ X'` lies over the base and the two modules are pullbacks along `e` of `F'` and `G'` on
`X'`, then `Hom(F, G)` is the relative Hom functor of `(X' ⟶ base, F', G')`. -/
def homFunctorIsoOfIso (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)
    (e : s.X ≅ X') (f' : X' ⟶ s.base) (hf : e.hom ≫ f' = s.f)
    (F' G' : Modules.{u, u} B S hS X'.1 X'.2)
    (α : s.F ≅ (modulePullback B S hS e.hom).obj F')
    (β : s.G ≅ (modulePullback B S hS e.hom).obj G') :
    s.homFunctor hc ≅ (baseChangeOver f').op ⋙ moduleHomOver hc F' G' :=
  Functor.isoWhiskerLeft (baseChangeOver s.f).op
      (moduleHomOverCongrSource hc α s.G ≪≫ moduleHomOverCongrTarget hc _ β ≪≫
        moduleHomOverPullback hc e.hom F' G') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (Functor.isoWhiskerRight (eqToIso (congrArg baseChangeOver hf).symm)
          (Over.map e.hom) ≪≫ baseChangeOverIsoOfIso e f')).symm
      (moduleHomOver hc F' G')

end HomSituation

end AlgebraicGeometry.Space

end
