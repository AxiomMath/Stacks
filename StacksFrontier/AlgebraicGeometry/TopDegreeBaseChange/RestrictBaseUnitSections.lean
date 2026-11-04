module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RestrictBaseUnitPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SourceSectionsNormalisation

/-!
# The linear map `ψ` extends is the pullback map on cohomology

`RestrictBaseUnitPullback.lean` identifies the Eilenberg-Watts unit of [Stacks, Tag 0EX3] (b) over
an affine open `V` of the base, in degree-`d` cohomology, with
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`. This file carries that identity along the
two ends of the computation and reads it on the pure tensors, which is the form conclusion (c)
consumes: the map

> `ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `…TopDegreeBaseChange.baseChangeSectionsMap` is the extension of scalars of the
`Γ(Y', V)`-linear map which **reads a section of `R^d f'_* F'` over `V` as a cohomology class
over `f'⁻¹(V)` ([Stacks, Tag 01XK]), applies the pullback map on cohomology, and reads the result
as a section over `W`.** Not one Eilenberg-Watts object occurs in that description; what is left
for the remaining half of conclusion (c) is to say the same of `Γ(W, γ⁺)` on the pullback of a
section.

## Main results

* `…TopDegreeBaseChange.topDegreeFunctorObjSelfIso_inv_comp_map_comp_targetSections`: the identity
  of `RestrictBaseUnitPullback.lean`, carried to the sections of the right-hand end.
* `…TopDegreeBaseChange.topDegreeFunctorObjSelfIsoSourceSections_inv_eq`: the identification of
  the sections of `R^d f'_* F'` over `V` with the Eilenberg-Watts module of `Φ`, inverted and
  split into its outer part and its Eilenberg-Watts part.
* `…TopDegreeBaseChange.sourceSections_inv_comp_map_comp_targetSections`: **the `Γ(Y', V)`-linear
  map that `ψ` is the extension of, with the geometry on the right.** Neither base carries a
  hypothesis; only the two opens are affine.
* `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul_of_eq`: the same, with the map, the ring
  unit and the composite taken as variables carrying their defining equations.
* `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul`: **`ψ` on the pure tensors**, which is the
  form conclusion (c) consumes.

## Implementation notes

*Everything about the geometry is done at the level of morphisms.* The two rearrangements are
hoisted to variables of abstract categories, and apart from the last statement — which is the
pure-tensor reading itself, and so cannot avoid it — no statement below about the situation
mentions an element. That is not cosmetic: a `CategoryTheory.comp_apply` or a
`ModuleCat.restrictScalars.map_apply` performed against the concrete spelling costs a definitional
reconciliation of a restriction of scalars in the presence of a concrete element, which is the wall
`…TopDegreeBaseChange.sourceSectionsIsoTensor_inv_eq` records; each of four such steps here
alone exhausts the elaborator, whether by heartbeats or by recursion depth. The pure
tensor is therefore handled by `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul`, which is
stated at variables — where the reconciliation is free — and keeps the composite intact instead of
splitting it into a nest of applications.

*Why the last statement needs every ingredient to be a variable.* The composite that
`…TopDegreeBaseChange.fromExtendScalarsComp` applies to a pure tensor and the composite the chain
above is stated at are, at the concrete spelling, the same term printed the same way; they differ
only in instance arguments that do not print. Reconciling those **inside an application to an
element** exhausts the elaborator's recursion budget, and no amount of rearranging the equality
chain avoids it, because both of its sides are closed terms. Compared on their own, as morphisms,
each reconciliation is immediate. That is what
`…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul_of_eq` is for: it takes the map, the ring
unit and the composite as variables carrying their defining equations, so each is discharged
separately and at morphism level, and the one equation left against the goal is matched rather
than compared.

*Where the restriction-of-scalars transport comes from.*
`…TopDegreeBaseChange.baseChangeSectionsMap` is `…TopDegreeBaseChange.fromExtendScalarsComp`, whose
defining `Γ(Y', V)`-linear map ends with the transport `ModuleCat.restrictScalarsCongr` along
`…TopDegreeBaseChange.appLE_eq_comp_topIso`.
Its underlying map is the identity, but it is part of the term, so it occurs below.

*The map out of the functions on `V` is a variable.* As in
`…TopDegreeBaseChange.rightDerived_tensorSheafUnitRightIso_inv_comp_pullbackTildeUnit`, the ring
unit `r ↦ r • 1` is taken as a variable with the hypothesis that it is the canonical map of
structure sheaves on global sections;
`…TopDegreeBaseChange.toSpanSingleton_comp_sectionsIsoPushforwardUnitSections` discharges it at the
one place where the ring unit is needed.

*No `@[stacks 0EX3]` attribute is placed.* This is one half of the pure-tensor identity of
conclusion (c), not a conclusion of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **An isomorphism in the third place of a three-fold composite is moved to the right.** From
`x ≫ y ≫ i.hom = w` one gets the value of `x ≫ y ≫ t` for any `t` out of the source of `i.hom`.
Stated at variables of an abstract category, where the cancellation is free. -/
theorem comp₂_comp_eq_of_comp₃_eq {C : Type*} [Category C] {A B D E T : C}
    (x : A ⟶ B) (y : B ⟶ D) (i : D ≅ E) (t : D ⟶ T) {w : A ⟶ E}
    (hw : x ≫ y ≫ i.hom = w) : x ≫ y ≫ t = w ≫ i.inv ≫ t := by
  rw [← hw]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **A composite whose first factor factors through a functor, rewritten.** If `j = o ≫ G.map s`
and `s ≫ m = g`, then `j ≫ G.map m ≫ t = o ≫ G.map g ≫ t`. Stated at variables of abstract
categories: the reassociation and the functoriality are free there, and the unifier meets the
concrete spelling only at the application. -/
theorem comp_map_comp_congr {C D : Type*} [Category C] [Category D] (G : D ⥤ C)
    {A A' : C} {B₁ B₂ B₃ : D} {j : A ⟶ G.obj B₁} {o : A ⟶ G.obj B₂} {s : B₂ ⟶ B₁}
    (hj : j = o ≫ G.map s) (m : B₁ ⟶ B₃) {g : B₂ ⟶ B₃} (hg : s ≫ m = g)
    (t : G.obj B₃ ⟶ A') : j ≫ G.map m ≫ t = o ≫ G.map g ≫ t := by
  rw [hj, ← hg, G.map_comp]
  simp only [Category.assoc]

/-- **The value on a pure tensor of a map presented by the Eilenberg-Watts construction, with
each ingredient a variable carrying its defining equation.** If `P` is the map
`…TopDegreeBaseChange.fromExtendScalarsComp` produces out of `A ⊗_{R₀} M₀`, if `U` is the ring
unit `r ↦ r • 1` of `A`, and if `m` is the composite that construction applies to a pure tensor,
then `P (1 ⊗ x) = m x`.

*Why the three facts are hypotheses rather than definitional steps.* At the concrete spelling
each of them holds, and holds on the nose; but the two sides differ in instance arguments that do
not print, and reconciling them **inside an application to an element** exhausts the elaborator's
recursion budget — the same wall `…TopDegreeBaseChange.sourceSectionsIsoTensor_inv_eq` records.
Compared on their own, as morphisms, each reconciliation is immediate. Taking them as hypotheses
is what lets a consumer discharge them one at a time, at morphism level, in the order it chooses:
`m` and `U` are fixed by the equations it supplies, and `P` is then matched against a goal whose
left-hand side is already determined. Stated at variables, where every conversion is plain `rfl`,
the proof is `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul` after three substitutions. -/
theorem fromExtendScalarsComp_one_tmul_of_eq {R₀ R A : Type u} [CommRing R₀] [CommRing R]
    [CommRing A] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) (σ : R₀ ≃+* R) (φ : R →+* A)
    (ρ : R₀ →+* A) (hρ : ρ = (φ : R →+* A).comp (σ : R₀ →+* R)) {M₀ : ModuleCat.{u} R₀}
    (j : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj (F.obj (ModuleCat.of R R)) ≅ M₀)
    {N : ModuleCat.{u} A}
    (Xi : F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) ⟶
      (ModuleCat.restrictScalars φ).obj N)
    {P : (ModuleCat.extendScalars ρ).obj M₀ ⟶ N}
    (hP : P = fromExtendScalarsComp F σ φ ρ hρ j Xi)
    {U : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)}
    (hU : U = ModuleCat.ofHom (LinearMap.toSpanSingleton R
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A)))
    {m : M₀ ⟶ (ModuleCat.restrictScalars ρ).obj N}
    (hm : m = j.inv ≫ (ModuleCat.restrictScalars (σ : R₀ →+* R)).map (F.map U ≫ Xi) ≫
      (ModuleCat.restrictScalarsCongr hρ.symm).hom.app N) (x : M₀) :
    P ((1 : A) ⊗ₜ[R₀,ρ] x) = m x := by
  subst hP
  subst hU
  subst hm
  exact fromExtendScalarsComp_one_tmul F σ φ ρ hρ j Xi x

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The Eilenberg-Watts side of [Stacks, Tag 0EX3] (c), carried to the sections of the right-hand
end.** This is
`…TopDegreeBaseChange.topDegreeFunctorObjSelfIso_inv_comp_map_comp_cohomologyUpstairs` with the
identification of `Φ(Γ(Y'', W))` with the cohomology upstairs replaced by the identification
`…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` of it with `Γ(R^d f''_* (h')^* F', W)`;
the former is moved to the right-hand side, inverted. -/
theorem topDegreeFunctorObjSelfIso_inv_comp_map_comp_targetSections
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
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
            Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
          (affineOpenCohomologyPullbackMap hsq hWV (preimage_le_preimage_of_isPullback hsq hWV) F'
              inferInstance S.d ≫
            (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
              (restrictPullbackRightDerivedPlusIso (h := h) h'
                (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
        (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
          (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom :=
  comp₂_comp_eq_of_comp₃_eq _ _ _ _
    (topDegreeFunctorObjSelfIso_inv_comp_map_comp_cohomologyUpstairs S F' h' f'' h hsq
      (V := V) hWV ψ hψ)

/-- **The sections of `R^d f'_* F'` over `V` as the Eilenberg-Watts module of `Φ`, inverted and
split.** `…TopDegreeBaseChange.topDegreeFunctorObjSelfIsoSourceSections` is a three-fold
composite; inverted, it is [Stacks, Tag 01XK] over `V` and the comparison of the two readings of
the scalars, followed by the restriction of scalars applied to the Eilenberg-Watts identification
itself. The equality holds by definition, `Iso.trans`, `Iso.symm` and `Functor.mapIso` all
computing their `inv` field on the nose. -/
theorem topDegreeFunctorObjSelfIsoSourceSections_inv_eq :
    (topDegreeFunctorObjSelfIsoSourceSections S F' (V := V)).inv =
      ((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
            (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
          (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
        (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
            Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).map
          ((S.restrictBase V).topDegreeFunctorObjSelfIso
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).inv := rfl

/-- **The `Γ(Y', V)`-linear map that `ψ` is the extension of, with the geometry on the right.**
The defining map of `…TopDegreeBaseChange.baseChangeSectionsMap` — the identification of the
sections of `R^d f'_* F'` over `V` with the Eilenberg-Watts module of `Φ`, inverted, followed by
`Φ` of the ring unit, by the identification of the right-hand end, and by the transport of
`ModuleCat.restrictScalarsCongr` — is [Stacks, Tag 01XK] over `V` followed by the pullback map on
cohomology and by the identification of the right-hand end.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem sourceSections_inv_comp_map_comp_targetSections
    (ψ : ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤) ⟶
      (ModuleCat.restrictScalars
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
          (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))
    (hψ : ψ ≫ (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) :
    (topDegreeFunctorObjSelfIsoSourceSections S F' (V := V)).inv ≫
        (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
            Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).map
          (((S.restrictBase V).topDegreeFunctor
              ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
                (inferInstance :
                  ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                    F').IsQuasicoherent)⟩).map ψ ≫
            (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
        (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
          (ModuleCat.of Γ(Y'', W)
            Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F'), W)) =
      ((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
            (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
          (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
        (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
            Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).map
          ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
              (affineOpenCohomologyPullbackMap hsq hWV
                  (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                    (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                  (restrictPullbackRightDerivedPlusIso (h := h) h'
                    (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
            (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
              (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
        (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
          (ModuleCat.of Γ(Y'', W)
            Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F'), W)) :=
  comp_map_comp_congr _ (topDegreeFunctorObjSelfIsoSourceSections_inv_eq S F' (V := V)) _
    (topDegreeFunctorObjSelfIso_inv_comp_map_comp_targetSections S F' h' f'' h hsq
      (V := V) hWV ψ hψ) _

/-- **`ψ` on the pure tensors is the pullback map on cohomology.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, the `Γ(Y'', W)`-linear map

`ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `…TopDegreeBaseChange.baseChangeSectionsMap` sends the pure tensor `1 ⊗ a` to the value at `a`
of: [Stacks, Tag 01XK] over `V`, then `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`, then
the identification of the right-hand end with the sections over `W`. Not one Eilenberg-Watts
object occurs on the right.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem baseChangeSectionsMap_one_tmul
    (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)) :
    baseChangeSectionsMap S F' h' f'' h hsq hWV
        ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
      (((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
              (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
            (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
          (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
              Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
                (affineOpenCohomologyPullbackMap hsq hWV
                    (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso (h := h) h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
              (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
          (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
            (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W))) a := by
  refine fromExtendScalarsComp_one_tmul_of_eq (R := Γ((V : Scheme), ⊤))
    ((S.restrictBase V).topDegreeFunctor
      ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
        (inferInstance :
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩)
    ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv)
    ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)
    (h.appLE V W hWV).hom (appLE_eq_comp_topIso S h hWV)
    (topDegreeFunctorObjSelfIsoSourceSections S F')
    (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom ?_ rfl
    (sourceSections_inv_comp_map_comp_targetSections S F' h' f'' h hsq (V := V) hWV _
      (toSpanSingleton_comp_sectionsIsoPushforwardUnitSections S h hWV)).symm a
  exact baseChangeSectionsMap_eq S F' h' f'' h hsq hWV

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
