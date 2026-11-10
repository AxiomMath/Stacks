module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineUnitTensorPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.GeometricFactorUnitExplicit
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# The Eilenberg-Watts unit of (b) over `V` is the pullback map on cohomology

`GeometricFactorUnitExplicit.lean` writes the functor `Φ` of [Stacks, Tag 0EX3] (b) and the unit
of its geometric factor out at a *variable* scheme over a *variable* affine base, and
`AffineUnitTensorPullback.lean` computes the degree-`d` cohomology of that unit, over a compatible
pair of affine opens, as `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` followed by the
right-hand end of the computation. This file joins the two: it instantiates the generic statements
at the situation restricted to an affine open `V` of the base and composes them with the
identification `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs`.

The result is the Eilenberg-Watts half of conclusion (c) as a single morphism identity: **the
Eilenberg-Watts module of `Φ`, followed by `Φ` of the ring unit and by the identification of
`Φ(Γ(Y'', W))` with the cohomology upstairs, is the pullback map on cohomology** — with no
Eilenberg-Watts machinery left in it.

## Main results

* `…TopDegreeBaseChange.restrictBase_geometricFactorFormulaObjSelfIso_inv_eq`,
  `…TopDegreeBaseChange.restrictBase_topDegreeFunctorObjSelfIso_inv_eq` and
  `…TopDegreeBaseChange.restrictBase_topDegreeFunctor_map_eq`: the three generic statements of
  `GeometricFactorUnitExplicit.lean`, instantiated at the restricted situation.
* `…TopDegreeBaseChange.topDegreeFunctorObjSelfIso_inv_comp_map_comp_cohomologyUpstairs`: **the
  identity.** Neither base carries a hypothesis; only the two opens are affine, and the map out of
  the functions on `V` is a variable with the one property of it that is used.

## Implementation notes

*Why the instantiation is three separate statements.* The generic statements are phrased at a
variable `Z : Over (Spec (CommRingCat.of R))`, where every conversion between the named factors
and the explicit spelling is `rfl`; the explicit statements below are phrased at
`(S.f' ⁻¹ᵁ V : Scheme)` and `(S.f' ∣_ V) ≫ V.isoSpec.hom`, which is the spelling the geometric
side of the computation produces. Reconciling the two costs one definitional step per statement,
and the elaborator affords one such step per declaration but not four: performing them all inside
the composite identity exhausts the budget at `whnf`. So each is performed once, in a statement
small enough that it is the only thing happening.

*The implicit open is passed explicitly at each use.* `restrictBase_…` applied inside a term whose
expected type is still a metavariable leaves the affine open `V` undetermined, and the unifier then
compares two spellings of the functor of conclusion (b) with a metavariable inside one of them;
that is the same timeout one level down. Writing `(V := V)` at each application costs nothing and
removes it.

*Two cheap steps where one is not affordable.* The identification of `Φ(Γ(Y'', W))` with the
cohomology upstairs is, by definition, an `eqToHom` of
`…TopDegreeBaseChange.topDegreeFunctor_obj_eq` followed by the cohomological tail; the `eqToHom`
is the identity because that equality is between definitionally equal objects. Unfolding the chain
and collapsing the `eqToHom` in one `rfl` exceeds the recursion limit, and the two steps
separately are both cheap.

*The map is a variable.* As in
`…TopDegreeBaseChange.rightDerived_tensorSheafUnitRightIso_inv_comp_pullbackTildeUnit`, the ring
unit `r ↦ r • 1` enters as a variable `ψ` with the hypothesis that it is the canonical map of
structure sheaves on global sections. Written out, the restriction of scalars has to be rebuilt at
a second spelling of the functions on `V`, where the module instance is not found.

*No `@[stacks 0EX3]` attribute is placed.* This is one step of the computation of conclusion (c).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Rewriting all three factors of a three-fold composite at once.** Stated at variables of an
abstract category, where the three substitutions are free; at the concrete spelling the goal is
large enough that a rewrite on it does not finish. -/
theorem comp₃_congr {C : Type*} [Category C] {A B D E : C} {x x' : A ⟶ B} {y y' : B ⟶ D}
    {z z' : D ⟶ E} (hx : x = x') (hy : y = y') (hz : z = z') {w : A ⟶ E}
    (hw : x' ≫ y' ≫ z' = w) : x ≫ y ≫ z = w := by
  rw [hx, hy, hz, hw]

/-- **A three-fold composite of images, from a five-fold identity about the functor.** For
functors `G` and `K`, a morphism `a` presented as a three-fold composite `a₁ ≫ a₂ ≫ a₃`, two
further morphisms `b` and `c`, and an isomorphism `i` through which `K` of the five-fold composite
factors as `s ≫ i.hom`, the composite `G(K a) ≫ G(K b) ≫ G(K c ≫ i.inv ≫ q)` is `G (s ≫ q)`.

Stated at variables of abstract categories: the reassociations and the cancellation of `i` are
free there, and the unifier meets the concrete spelling only at the application. -/
theorem map_comp₃_of_map_comp₅_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (K : E ⥤ C) {A₁ A₂ A₃ A₄ A₅ A₆ : E}
    {a : A₁ ⟶ A₄} {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {a₃ : A₃ ⟶ A₄}
    (ha : a = a₁ ≫ a₂ ≫ a₃) (b : A₄ ⟶ A₅) (c : A₅ ⟶ A₆)
    {B Z : C} {s : K.obj A₁ ⟶ B} (i : B ≅ K.obj A₆) (q : B ⟶ Z)
    (hK : K.map (a₁ ≫ a₂ ≫ a₃ ≫ b ≫ c) = s ≫ i.hom) :
    G.map (K.map a) ≫ G.map (K.map b) ≫ G.map (K.map c ≫ i.inv ≫ q) = G.map (s ≫ q) := by
  have h1 : K.map a ≫ K.map b ≫ K.map c ≫ i.inv ≫ q = s ≫ q := by
    have h0 : K.map a ≫ K.map b ≫ K.map c ≫ i.inv ≫ q =
        K.map (a₁ ≫ a₂ ≫ a₃ ≫ b ≫ c) ≫ i.inv ≫ q := by
      rw [ha]
      simp only [K.map_comp, Category.assoc]
    rw [h0, hK, Category.assoc, i.hom_inv_id_assoc]
  rw [← G.map_comp, ← G.map_comp, h1]

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

omit [F'.IsQuasicoherent] in
/-- **The unit of the geometric factor of [Stacks, Tag 0EX3] (b) over an affine open `V` of the
base, inverted and written out.** This is
`…TopDegreeBaseChange.geometricFactorFormulaObjSelfIso_inv_eq'` at the situation restricted to
`V`, whose structure morphism over `Spec Γ(V, ⊤)` is `(f' ∣_ V) ≫ V.isoSpec.hom`. -/
theorem restrictBase_geometricFactorFormulaObjSelfIso_inv_eq :
    (geometricFactorFormulaObjSelfIso Γ((V : Scheme), ⊤) ((S.restrictBase V).affineBaseOver)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv =
      (tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullbackUnitIso
              ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).inv) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
              (AlgebraicGeometry.tildeSelf
                (R := CommRingCat.of Γ((V : Scheme), ⊤))).inv) :=
  geometricFactorFormulaObjSelfIso_inv_eq' Γ((V : Scheme), ⊤)
    ((S.restrictBase V).affineBaseOver)
    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')

/-- **The Eilenberg-Watts module of the functor of [Stacks, Tag 0EX3] (b) over an affine open `V`
of the base, with its identification with `H^d(f'⁻¹(V), F'|)` inverted and written out.** This is
`…TopDegreeBaseChange.affineTopDegreeFunctorObjSelfIso_inv_eq` at the situation restricted to
`V`. -/
theorem restrictBase_topDegreeFunctorObjSelfIso_inv_eq :
    ((S.restrictBase V).topDegreeFunctorObjSelfIso
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).inv =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
          (geometricFactorFormulaObjSelfIso Γ((V : Scheme), ⊤)
            ((S.restrictBase V).affineBaseOver)
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv) :=
  affineTopDegreeFunctorObjSelfIso_inv_eq Γ((V : Scheme), ⊤)
    ((S.restrictBase V).affineBaseOver) S.d
    ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
      (inferInstance :
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩

/-- **The functor of [Stacks, Tag 0EX3] (b) over an affine open `V` of the base, on morphisms,
written out.** This is `…TopDegreeBaseChange.affineTopDegreeFunctor_map_eq` at the situation
restricted to `V`: a map of `Γ(V, ⊤)`-modules goes to the degree-`d` cohomology of `𝟙_{F'|}`
tensored with the pullback along `(f' ∣_ V) ≫ V.isoSpec.hom` of its tilde. -/
theorem restrictBase_topDegreeFunctor_map_eq {M N : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (g : M ⟶ N) :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
              F').IsQuasicoherent)⟩).map g =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
            (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
              (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
                ((AlgebraicGeometry.tilde.functor
                  (CommRingCat.of Γ((V : Scheme), ⊤))).map g)))) :=
  affineTopDegreeFunctor_map_eq Γ((V : Scheme), ⊤) ((S.restrictBase V).affineBaseOver) S.d
    ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
      (inferInstance :
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩ g

/-- **The Eilenberg-Watts side of [Stacks, Tag 0EX3] (c) over a compatible pair of affine opens.**
For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, a quasi-coherent `F'`
and any map `ψ` out of the functions on `V` which is the canonical map of structure sheaves on
global sections: the identification of the Eilenberg-Watts module of the functor `Φ` of conclusion
(b) over `V` with `H^d(f'⁻¹(V), F'|)`, inverted, followed by `Φ(ψ)` and by the identification
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` of `Φ(Γ(Y'', W))` with the
degree-`d` cohomology of `((h')^* F')|` over `f''⁻¹(W)`, **is the pullback map on cohomology** —
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`, followed by the comparison of the two
spellings of that cohomology.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem topDegreeFunctorObjSelfIso_inv_comp_map_comp_cohomologyUpstairs
    (ψ : ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤) ⟶
      (ModuleCat.restrictScalars
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
          (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))
    (hψ : ψ ≫ (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) :
    ((S.restrictBase V).topDegreeFunctorObjSelfIso
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                F').IsQuasicoherent)⟩).inv ≫
        ((S.restrictBase V).topDegreeFunctor
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map ψ ≫
        (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
        (affineOpenCohomologyPullbackMap hsq hWV (preimage_le_preimage_of_isPullback hsq hWV) F'
            inferInstance S.d ≫
          (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
            (restrictPullbackRightDerivedPlusIso h'
              (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) := by
  have hcoh := rightDerived_tensorSheafUnitRightIso_inv_comp_pullbackTildeUnit S F' h' f'' h
    hsq hWV ψ hψ
  have hwritten : (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom =
      eqToHom (topDegreeFunctor_obj_eq S F'
          ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom)).obj
              (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))) ≫
        (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
            Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
          (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                    (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
                (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                  (pullbackTildeSectionsIso S h hWV).hom)) ≫
            (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV
              (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d).inv ≫
            (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
              (restrictPullbackRightDerivedPlusIso h'
                (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) := rfl
  refine comp₃_congr (restrictBase_topDegreeFunctorObjSelfIso_inv_eq S F' (V := V))
    (restrictBase_topDegreeFunctor_map_eq S F' (V := V) ψ)
    (hwritten.trans (eqToHom_comp_of_refl _ _)) ?_
  exact map_comp₃_of_map_comp₅_eq
    (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
      Γ((((S.restrictBase V).affineBaseOver)).left, ⊤)))
    ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d)
    (restrictBase_geometricFactorFormulaObjSelfIso_inv_eq S F' (V := V)) _ _ _ _ hcoh

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
