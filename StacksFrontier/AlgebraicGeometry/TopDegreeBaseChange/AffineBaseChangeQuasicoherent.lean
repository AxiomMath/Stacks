module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor

/-!
# Top-degree cohomology under an affine base change, for an arbitrary quasi-coherent module

Let `p : X ⟶ Spec A` be quasi-compact and quasi-separated, let `d` be a degree above which the
cohomology of every quasi-coherent module on `X` vanishes, let `F` be a quasi-coherent
`𝒪_X`-module and consider a cartesian square

```
X_B --q--> X
|          |p
Spec B --Spec φ--> Spec A
```

over the spectrum of a ring map `φ : A ⟶ B`. Then

`Hᵈ(X_B, q^* F) = Hᵈ(X, F) ⊗_A B`.

This is conclusion (c) of [Stacks, Tag 0EX3] in the case where the base and the base change are
both affine, and — unlike (c) in general — it costs no derived-category machinery and no
comparison map: the source's own reduction of (c) to (b) is available verbatim, because over an
affine base (b) is the Eilenberg-Watts identity of `EilenbergWattsUnitor.lean`, and an affine
base change lets the two cohomologies be compared by [Stacks, Tag 089W] rather than by a
base-change morphism whose invertibility would have to be proved.

## The three steps

* **Eilenberg-Watts.** `EilenbergWattsUnitor.lean`'s `affineTopDegreeTensorCohomologyIso` says
  that `M ↦ Hᵈ(X, F ⊗ p^* M~)` is tensoring with `Hᵈ(X, F)`. It already holds at an arbitrary
  quasi-coherent `F`, so nothing has to be generalized here.
* **The geometric step, which is the content of this file.**
  `geometricFactorFormulaObjBaseRingIso` identifies `F ⊗ p^* B~` with `q_*(q^* F)`. The sheaf
  `B~` on `Spec A` is `(Spec φ)_* 𝒪_{Spec B}` by [Stacks, Tag 01I9], pulling that back along `p`
  is taking the direct image along `q` of the pullback of `𝒪_{Spec B}` by [Stacks, Tag 02KG] —
  the lower horizontal morphism being affine — and `F ⊗ q_* 𝒪_{X_B} ≅ q_*(q^* F)` is the
  **projection formula for an affine morphism**, [Stacks, Tag 0FZE], in the form
  `…DerivedAffinePushforward.pushforwardStructureSheafTensorIso`. At `F = 𝒪_X` the projection
  formula degenerates to a unitor; for a general `F` it is irreducible, and it is the only thing
  that separates the statement below from its structure-sheaf case.
* **The cohomology of a direct image along an affine morphism.** `q` is affine, being a base
  change of `Spec φ`, so `Hᵈ(X, q_* q^* F)` is `Hᵈ(X_B, q^* F)` by [Stacks, Tag 089W].

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaObjBaseRingIso`:
  `F ⊗ p^* B~ ≅ q_*(q^* F)`, the projection-formula step. No vanishing hypothesis and no bound
  on the degree: this is a statement about sheaves.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeFunctorObjBaseRingIso`: its
  cohomological consequence, `Hᵈ(X, F ⊗ p^* B~) ≅ Hᵈ(X_B, q^* F)` with the scalars of the
  right-hand side restricted to `A`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeTensorBaseChangeIso`:
  **conclusion (c) of [Stacks, Tag 0EX3] for an affine base change over an affine base, at an
  arbitrary quasi-coherent module** — `Hᵈ(X, F) ⊗_A B ≅ Hᵈ(X_B, q^* F)`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_pullback_baseChange`: the
  vanishing form, `Hᵈ(X, F) = 0 ⟹ Hᵈ(X_B, q^* F) = 0`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_isZero_pullback_baseChange`:
  its converse for a faithfully flat base change.

## Implementation notes

**The target of the comparison carries `A`-scalars through two restrictions and not one.** The
Eilenberg-Watts package reads cohomology on `X` as an `A`-module by restricting scalars along
`A ⟶ Γ(X, ⊤)`, and [Stacks, Tag 089W] compares `Hᵈ(X_B, −)` with `Hᵈ(X, q_* −)` after
restricting along `q^♯ : Γ(X, ⊤) ⟶ Γ(X_B, ⊤)`. So the `A`-module on the right-hand side below is
`Hᵈ(X_B, q^* F)` restricted twice, in that order, and no composite ring map is formed: forming
one would need an `Algebra A Γ(X_B, ⊤)` instance that instance search cannot recover from the
`CategoryTheory.Over` presentation the geometric factor is written against.

**The `B`-module structure is not claimed.** `Hᵈ(X_B, q^* F)` is a module over `Γ(X_B, ⊤)` and
hence over `B`, and the left-hand side is a `B`-module through its right tensor factor; the
comparison below is proved `A`-linear only. That is what its three steps give, and it is enough
for the vanishing form.

**`HasDerivedCategory.standard` is given a raised priority.** The import closure contains a
global `CategoryTheory.HasDerivedCategory` instance which instance search prefers, and under it
the `rightDerivedPlus` of the vanishing hypothesis lands in a different derived-category universe
from the one `TopDegreeBaseChange/` is written at, so the statements stop composing.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-- **The geometric factor of the Eilenberg-Watts functor, at the base ring of an affine base
change**: `F ⊗ p^* B~ ≅ q_*(q^* F)`.

[Stacks, Tag 01I9] identifies `B~` on `Spec R` with `(Spec φ)_* 𝒪_{Spec B}`, where
`AlgebraicGeometry.tildeSelf` reads `B~` on `Spec B` as the structure sheaf; [Stacks, Tag 02KG]
carries the pullback of that direct image to the direct image along `q` of the pullback of
`𝒪_{Spec B}`, which `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` identifies with
`𝒪_{X_B}`; and the **projection formula for an affine morphism** ([Stacks, Tag 0FZE], at the
structure sheaf) turns `F ⊗ q_* 𝒪_{X_B}` into `q_*(q^* F)`. The symmetry of the sheafified
tensor product moves the direct image into the left factor, which is the slot the projection
formula puts it in. -/
def geometricFactorFormulaObjBaseRingIso
    (F : _root_.SheafOfModules.{u} W.left.ringCatSheaf)
    (hF : (show W.left.Modules from F).IsQuasicoherent)
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) {ZB : Scheme.{u}}
    (q : ZB ⟶ W.left) (pB : ZB ⟶ Spec B)
    (sq : IsPullback pB q (Spec.map φ) W.hom) :
    (geometricFactorFormula R W F).obj
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      (Scheme.Modules.pushforward q).obj
        ((Scheme.Modules.pullback q).obj (show W.left.Modules from F)) :=
  haveI : IsAffineHom q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  (tensorFactor R W F).mapIso
      ((Scheme.Modules.pullback W.hom).mapIso
          ((AlgebraicGeometry.pushforwardTildeIso (CommRingCat.of R) B φ).app
            (ModuleCat.of B B)).symm ≪≫
        @asIso _ _ _ _ _
          (Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
            sq (Scheme.unitModule (Spec B))) ≪≫
        (Scheme.Modules.pushforward q).mapIso (Scheme.Modules.pullbackUnitIso pB)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap W.left.presheaf (ringSheafCond W.left)
      ((Scheme.Modules.pushforward q).obj
        (_root_.SheafOfModules.unit ZB.ringCatSheaf)) F ≪≫
    Stacks.AlgebraicGeometry.DerivedAffinePushforward.pushforwardStructureSheafTensorIso q
      (show W.left.Modules from F) hF

section Cohomology

variable (d : ℕ)

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **The Eilenberg-Watts functor at the base ring of an affine base change is the top-degree
cohomology of the base-changed module**: `Hᵈ(X, F ⊗ p^* B~) ≅ Hᵈ(X_B, q^* F)`, the right-hand
side read as an `R`-module by restricting its scalars along `q^♯` and then along
`R ⟶ Γ(X, ⊤)`.

This is `geometricFactorFormulaObjBaseRingIso` carried through the cohomological tail of
`affineTopDegreeFunctor`, followed by [Stacks, Tag 089W] for the affine morphism `q`. No
vanishing hypothesis is used. -/
def affineTopDegreeFunctorObjBaseRingIso
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) {ZB : Scheme.{u}}
    (q : ZB ⟶ W.left) (pB : ZB ⟶ Spec B)
    (sq : IsPullback pB q (Spec.map φ) W.hom) :
    (affineTopDegreeFunctor R W d (geometricFactor R W F)).obj
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((ModuleCat.restrictScalars q.appTop.hom).obj
          (((moduleGlobalSections ZB).rightDerived d).obj
            ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj)))) :=
  haveI : IsAffineHom q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  haveI : (show W.left.Modules from F.obj).IsQuasicoherent := F.property
  haveI : ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback q (show W.left.Modules from F.obj) F.property
  (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).mapIso
    (((moduleGlobalSections W.left).rightDerived d).mapIso
        ((geometricFactorCompιIso R W F).app
            ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≪≫
          geometricFactorFormulaObjBaseRingIso R W F.obj F.property φ q pB sq) ≪≫
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward q
        ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj)) d).symm)

variable [QuasiCompact W.hom] [QuasiSeparated W.hom]

/-- **Conclusion (c) of [Stacks, Tag 0EX3] for an affine base change over an affine base, at an
arbitrary quasi-coherent module**: `Hᵈ(X, F) ⊗_R B ≅ Hᵈ(X_B, q^* F)`.

Over an affine base the source obtains (c) from (b), and over an affine base (b) is the
Eilenberg-Watts identity `affineTopDegreeTensorCohomologyIso`: `M ↦ Hᵈ(X, F ⊗ p^* M~)` is
tensoring with `Hᵈ(X, F)`. Reading it at `M = B` and composing with
`affineTopDegreeFunctorObjBaseRingIso` gives the displayed identification, with no base-change
morphism constructed and no invertibility to prove. -/
@[stacks 0EX3 "(c) for an affine base change over an affine base, at an arbitrary quasi-coherent \
module; the comparison is proved linear over the base ring and not over the base-changed ring, \
and no canonical base-change map is constructed"]
def affineTopDegreeTensorBaseChangeIso
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G))
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) {ZB : Scheme.{u}}
    (q : ZB ⟶ W.left) (pB : ZB ⟶ Spec B)
    (sq : IsPullback pB q (Spec.map φ) W.hom) :
    (MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
          ((qcohCohomology W.left d).obj F))).obj
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((ModuleCat.restrictScalars q.appTop.hom).obj
          (((moduleGlobalSections ZB).rightDerived d).obj
            ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj)))) :=
  (affineTopDegreeTensorCohomologyIso R W d F hvan).app
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≪≫
    affineTopDegreeFunctorObjBaseRingIso R W d F φ q pB sq

/-- Restricting scalars along a ring map preserves and reflects zero modules. -/
private theorem isZero_restrictScalars_iff {S T : Type u} [Ring S] [Ring T] (f : S →+* T)
    (M : ModuleCat.{u} T) : IsZero ((ModuleCat.restrictScalars f).obj M) ↔ IsZero M := by
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **The vanishing form of conclusion (c) over an affine base, for an arbitrary quasi-coherent
module.** If `Hᵈ(X, F) = 0` then `Hᵈ(X_B, q^* F) = 0`, for every cartesian square over the
spectrum of a ring map out of the base ring.

All three steps of `affineTopDegreeTensorBaseChangeIso` are isomorphisms, and tensoring with a
zero module is a zero module; the two transfers of vanishing through
`ModuleCat.isZero_iff_subsingleton` cross between modules with the same carrier but different
scalars, which is all that separates `Hᵈ(X, F)` read over `R` from `Hᵈ(X, F)` read over
`Γ(X, ⊤)`. -/
theorem isZero_rightDerived_pullback_baseChange
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G))
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) {ZB : Scheme.{u}}
    (q : ZB ⟶ W.left) (pB : ZB ⟶ Spec B)
    (sq : IsPullback pB q (Spec.map φ) W.hom)
    (h : IsZero (((moduleGlobalSections W.left).rightDerived d).obj
      (show W.left.Modules from F.obj))) :
    IsZero (((moduleGlobalSections ZB).rightDerived d).obj
      ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj))) := by
  have hR := (isZero_restrictScalars_iff (algebraMap R Γ(W.left, ⊤))
    ((qcohCohomology W.left d).obj F)).mpr h
  have htens : IsZero ((MonoidalCategory.tensorLeft
      ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((qcohCohomology W.left d).obj F))).obj
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B))) :=
    Functor.map_isZero (MonoidalCategory.tensorRight
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B))) hR
  have hfin := IsZero.of_iso htens
    (affineTopDegreeTensorBaseChangeIso R W d F hvan φ q pB sq).symm
  rwa [isZero_restrictScalars_iff, isZero_restrictScalars_iff] at hfin

/-- **The converse of `isZero_rightDerived_pullback_baseChange` for a faithfully flat base
change.** If `φ : R ⟶ B` is faithfully flat, then `Hᵈ(X_B, q^* F) = 0` forces `Hᵈ(X, F) = 0`.

The comparison `affineTopDegreeTensorBaseChangeIso` reads backwards unchanged; what replaces the
step "tensoring with a zero module is zero" is that `Hᵈ(X, F) ⊗_R B` is a subsingleton only if
`Hᵈ(X, F)` is, which is `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left`. -/
theorem isZero_rightDerived_of_isZero_pullback_baseChange
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G))
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) (hφ : φ.hom.FaithfullyFlat)
    {ZB : Scheme.{u}} (q : ZB ⟶ W.left) (pB : ZB ⟶ Spec B)
    (sq : IsPullback pB q (Spec.map φ) W.hom)
    (h : IsZero (((moduleGlobalSections ZB).rightDerived d).obj
      ((Scheme.Modules.pullback q).obj (show W.left.Modules from F.obj)))) :
    IsZero (((moduleGlobalSections W.left).rightDerived d).obj
      (show W.left.Modules from F.obj)) := by
  let : Algebra R B := φ.hom.toAlgebra
  have : Module.FaithfullyFlat R B := hφ
  have : Module.FaithfullyFlat R
      (↥((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) : Type u) := hφ
  have hfin := (isZero_restrictScalars_iff (algebraMap R Γ(W.left, ⊤)) _).mpr
    ((isZero_restrictScalars_iff q.appTop.hom _).mpr h)
  have htens : IsZero ((MonoidalCategory.tensorLeft
      ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((qcohCohomology W.left d).obj F))).obj
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B))) :=
    IsZero.of_iso hfin (affineTopDegreeTensorBaseChangeIso R W d F hvan φ q pB sq)
  have htsub : Subsingleton (TensorProduct R
      (↥((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((qcohCohomology W.left d).obj F)) : Type u)
      (↥((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) : Type u)) :=
    ModuleCat.isZero_iff_subsingleton.mp htens
  have hM : Subsingleton (↥((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
      ((qcohCohomology W.left d).obj F)) : Type u) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left R _
      (N := (↥((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) : Type u))).mp htsub
  exact (isZero_restrictScalars_iff _ _).mp (ModuleCat.isZero_iff_subsingleton.mpr hM)

end Cohomology

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
