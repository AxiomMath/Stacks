module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleSheafDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleToposCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceInverseImage

/-!
# Sheaves on the small étale site are descent data along a presentation

Let `X` be an algebraic space over a scheme `S`, let `φ : U ⟶ X` be a surjective étale
morphism presenting `X` as `U/R`, and let `(U, R, s, t, c, e, i)` be the resulting groupoid, so
that `R = U ×_X U` with `t` and `s` the two projections and `c` the composition law on
`R₂ = R ×_{s, U, t} R`. Stacks 05YY says that the functor

`ℱ ↦ (𝒢, α)`, `𝒢 = φ⁻¹ℱ`, `α : t⁻¹𝒢 ⟶ s⁻¹𝒢`

is an equivalence from sheaves on the small étale site of `X` to the pairs `(𝒢, α)` with `𝒢` a
sheaf on the small étale site of `U` and `α` an isomorphism whose pentagon over `R₂` commutes.
The isomorphism `α` attached to a sheaf and its cocycle condition are
`AlgebraicGeometry.Space.presentationPullbackIsoApp` and
`AlgebraicGeometry.Space.presentationPullbackIsoApp_cocycle`; the remaining assertion is that
the functor is an equivalence of categories.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.presentationChosenPullback`: `R` as a chosen pullback
  of the structure morphism of `U` with itself, in the spaces-étale site of `X`;
* `AlgebraicGeometry.Space.SpacesEtale.presentationChosenPullback₃`: `R₂` as a chosen
  threefold wide pullback of that structure morphism with itself, the lift to `R` of its outer
  pair of projections being the composition law `c` of the groupoid;
* `AlgebraicGeometry.Space.SpacesEtale.toPresentationDescentData`: the functor `ℱ ↦ (𝒢, α)`;
* `CategoryTheory.Pseudofunctor.DescentData'.mk'`: a descent datum built from transition
  *isomorphisms* satisfying the cocycle condition.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toPresentationDescentData`:
  **Stacks 05YY**, the functor `ℱ ↦ (𝒢, α)` is an equivalence of categories.
* `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_self_of_isIso` and
  `CategoryTheory.Pseudofunctor.DescentData'.mk'_self`: a descent datum is the same as a family
  of transition isomorphisms satisfying the cocycle condition.
* `AlgebraicGeometry.Space.SpacesEtale.smallEtaleSheafSystem_map_iso`: the pullback functors of
  the pseudofunctor the descent data are taken in are the small étale inverse images of
  Stacks 03G2, part (3).

## References

* [Stacks Project, Tag 05YY](https://stacks.math.columbia.edu/tag/05YY)
* [Stacks Project, Tag 0GFS](https://stacks.math.columbia.edu/tag/0GFS)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

/-! ### Descent data whose transition morphism is given as an isomorphism -/

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

universe w₃ w₄ w₁ w₂

variable {C : Type w₂} [Category.{w₁} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₃, w₄}}

/-- The pullback of an isomorphism is an isomorphism. -/
instance isIso_pullHom {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    [IsIso φ] {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) :=
  ⟨pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁,
    by simp [pullHom, ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app],
    by simp [pullHom, ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]⟩

namespace DescentData'

universe w₅

variable {ι : Type w₅} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
  {obj : ∀ i, F.obj (.mk (op (X i)))}
  (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

/-- A family of transition isomorphisms pulls back to isomorphisms. -/
theorem isIso_pullHom' (hiso : ∀ i j, IsIso (hom i j)) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    IsIso (pullHom' hom q f₁ f₂ hf₁ hf₂) :=
  have := hiso i₁ i₂
  isIso_pullHom (hom i₁ i₂) _ _ _ _ _

/-- The normalisation along the diagonal is automatic: a family of transition *isomorphisms*
satisfying the cocycle condition restricts to the identity on the diagonal. -/
theorem pullHom'_hom_self_of_isIso (hiso : ∀ i j, IsIso (hom i j))
    (hom_comp : ∀ i₁ i₂ i₃ : ι,
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    (i : ι) : pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := by
  have := isIso_pullHom' hom hiso (f i) (𝟙 (X i)) (𝟙 (X i))
  have h := comp_pullHom'' hom hom_comp (f i) (𝟙 (X i)) (𝟙 (X i)) (𝟙 (X i))
    (by simp) (by simp) (by simp)
  rw [← cancel_mono (pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i))), h]
  exact (Category.id_comp _).symm

/-- **Descent data in the shape the Stacks Project uses**: a family of objects together with
transition *isomorphisms* satisfying the cocycle condition. The normalisation along the
diagonal that `CategoryTheory.Pseudofunctor.DescentData'` asks for in addition is automatic. -/
noncomputable def mk' (hiso : ∀ i j, IsIso (hom i j))
    (hom_comp : ∀ i₁ i₂ i₃ : ι,
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃) :
    F.DescentData' sq sq₃ where
  obj := obj
  hom := hom
  pullHom'_hom_self := pullHom'_hom_self_of_isIso hom hiso hom_comp
  pullHom'_hom_comp := hom_comp

/-- The objects of `mk' hom hiso hom_comp` are `obj`. -/
@[simp]
theorem mk'_obj (hiso : ∀ i j, IsIso (hom i j)) (hom_comp) :
    (mk' hom hiso hom_comp (sq₃ := sq₃)).obj = obj := rfl

/-- The transition morphisms of `mk' hom hiso hom_comp` are `hom`. -/
@[simp]
theorem mk'_hom (hiso : ∀ i j, IsIso (hom i j)) (hom_comp) :
    (mk' hom hiso hom_comp (sq₃ := sq₃)).hom = hom := rfl

/-- Every descent datum is `mk'` of its own transition morphisms, which are isomorphisms, and its
cocycle condition. -/
theorem mk'_self (D : F.DescentData' sq sq₃) :
    mk' D.hom (fun _ _ => inferInstance) D.pullHom'_hom_comp = D := rfl

end DescentData'

end CategoryTheory.Pseudofunctor

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-- **The pullback of the sheaf system is the small étale inverse image.** The one-morphism
part of `AlgebraicGeometry.Space.SpacesEtale.smallEtaleSheafSystem` at a morphism `φ : V ⟶ U`
of the spaces-étale site of `X` agrees with the inverse image of Stacks 03G2, part (3), along
the morphism of algebraic spaces underlying `φ`. -/
noncomputable def smallEtaleSheafSystem_map_iso
    [∀ (U : SpacesEtale B S hS X) (Z : _),
      HasLimitsOfShape
        (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))]
    {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    ((smallEtaleSheafSystem B S hS (X := X)).map φ.op.toLoc).toFunctor ≅
      smallEtaleSheafInverseImage B S hS ((toSpaces B S hS X).map φ) :=
  Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS U.obj.left).inverse
    (Functor.isoWhiskerRight (sheafOverEquivSmall_overMapPullback_iso B S hS φ)
      (smallEtaleToposEquiv B S hS V.obj.left).functor)

section

variable {Uo Ro R₂o : SpacesEtale B S hS X}

/-- `R = U ×_X U`, as a chosen pullback of the structure morphism of `U` with itself in the
spaces-étale site of `X`. -/
noncomputable def presentationChosenPullback (t s : Ro ⟶ Uo)
    (hR : IsPullback t.hom.left s.hom.left Uo.obj.hom Uo.obj.hom) :
    ChosenPullback (toFinal B S hS Uo) (toFinal B S hS Uo) where
  pullback := Ro
  p₁ := t
  p₂ := s
  condition := (isPullback_of_toSpaces B S hS hR).w
  isLimit := (isPullback_of_toSpaces B S hS hR).isLimit

/-- `R ×_{s, U, t} R`, as a chosen threefold wide pullback. -/
noncomputable def presentationChosenPullback₃ (t s : Ro ⟶ Uo)
    (hR : IsPullback t.hom.left s.hom.left Uo.obj.hom Uo.obj.hom)
    (pr₀ pr₁ c : R₂o ⟶ Ro)
    (hR₂ : IsPullback pr₀.hom.left pr₁.hom.left s.hom.left t.hom.left)
    (hct : pr₀ ≫ t = c ≫ t) (hcs : pr₁ ≫ s = c ≫ s) :
    ChosenPullback₃ (presentationChosenPullback B S hS t s hR)
      (presentationChosenPullback B S hS t s hR)
      (presentationChosenPullback B S hS t s hR) where
  chosenPullback :=
    { pullback := R₂o
      p₁ := pr₀
      p₂ := pr₁
      condition := (isPullback_of_toSpaces B S hS hR₂).w
      isLimit := (isPullback_of_toSpaces B S hS hR₂).isLimit }
  l :=
    { f := c
      f_p₁ := hct.symm
      f_p₂ := hcs.symm
      f_p := (final_isTerminal B S hS X).hom_ext _ _ }

variable
  [∀ (U : SpacesEtale B S hS X) (Z : _),
    HasLimitsOfShape
      (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))]
  (t s : Ro ⟶ Uo)
  (hR : IsPullback t.hom.left s.hom.left Uo.obj.hom Uo.obj.hom)
  (pr₀ pr₁ c : R₂o ⟶ Ro)
  (hR₂ : IsPullback pr₀.hom.left pr₁.hom.left s.hom.left t.hom.left)
  (hct : pr₀ ≫ t = c ≫ t) (hcs : pr₁ ≫ s = c ≫ s)

/-- **Stacks 05YY**, the functor. Let `φ : U ⟶ X` be a morphism of the spaces-étale site of
`X` to the final object, let `R = U ×_X U` with projections `t` and `s`, let
`R₂ = R ×_{s, U, t} R` with projections `pr₀` and `pr₁`, and let `c : R₂ ⟶ R` be the
composition law of the resulting groupoid. This is the functor taking a sheaf `ℱ` on the small
étale site of `X` to the pair `(𝒢, α)` consisting of `𝒢 = φ⁻¹ℱ`, a sheaf on the small étale
site of `U`, and the canonical isomorphism `α : t⁻¹𝒢 ⟶ s⁻¹𝒢`, whose pentagon over `R₂`
commutes. -/
noncomputable def toPresentationDescentData :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⥤
      (smallEtaleSheafSystem B S hS (X := X)).DescentData'
        (fun _ _ : Unit => presentationChosenPullback B S hS t s hR)
        (fun _ _ _ : Unit =>
          presentationChosenPullback₃ B S hS t s hR pr₀ pr₁ c hR₂ hct hcs) :=
  (smallEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun _ : Unit => toFinal B S hS Uo) ⋙
    Pseudofunctor.DescentData'.fromDescentDataFunctor _ _ _

/-- Let `X` be an algebraic space over a scheme `S`, let `φ : U ⟶ X` be a
surjective étale morphism and let `(U, R, s, t, c, e, i)` be the groupoid of the presentation
`X = U/R`, so that `R = U ×_X U` with `t` and `s` the two projections and `c` the composition
law on `R₂ = R ×_{s, U, t} R`. Then the functor taking a sheaf `ℱ` on the small étale site of
`X` to the pair `(𝒢, α)`, where `𝒢 = φ⁻¹ℱ` is a sheaf on the small étale site of `U` and
`α : t⁻¹𝒢 ⟶ s⁻¹𝒢` is the canonical isomorphism, is an equivalence of categories onto the
category of such pairs: pairs of a sheaf on the small étale site of `U` and an isomorphism
`t⁻¹𝒢 ⟶ s⁻¹𝒢` whose pentagon over `R₂` commutes, with morphisms the maps of sheaves commuting
with those isomorphisms. -/
@[stacks 05YY "the equivalence of categories"]
theorem isEquivalence_toPresentationDescentData
    (hsurj : IsSurjective B S hS Uo.obj.hom.hom) :
    (toPresentationDescentData B S hS t s hR pr₀ pr₁ c hR₂ hct hcs).IsEquivalence := by
  have h₁ : ((smallEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun _ : Unit => toFinal B S hS Uo)).IsEquivalence :=
    isEquivalence_toDescentData_smallEtaleSheafSystem_of_jointlySurjective B S hS
      (fun _ : Unit => Uo) ((isJointlySurjective_const_iff B S hS _).2 hsurj)
  have h₂ : (Pseudofunctor.DescentData'.fromDescentDataFunctor
      (smallEtaleSheafSystem B S hS (X := X))
      (fun _ _ : Unit => presentationChosenPullback B S hS t s hR)
      (fun _ _ _ : Unit =>
        presentationChosenPullback₃ B S hS t s hR pr₀ pr₁ c hR₂ hct hcs)).IsEquivalence :=
    (Pseudofunctor.DescentData'.descentDataEquivalence
      (smallEtaleSheafSystem B S hS (X := X))
      (fun _ _ : Unit => presentationChosenPullback B S hS t s hR)
      (fun _ _ _ : Unit =>
        presentationChosenPullback₃ B S hS t s hR pr₀ pr₁ c hR₂ hct hcs)).isEquivalence_inverse
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h₁ h₂

end

end AlgebraicGeometry.Space.SpacesEtale

end
