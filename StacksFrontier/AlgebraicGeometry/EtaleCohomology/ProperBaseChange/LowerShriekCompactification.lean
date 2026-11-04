module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunctionUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived lower shriek through a compactification: the comparisons of Tags 0F7B, 0F7G, 0F7I

Let `f : X ⟶ Y` be a separated morphism of finite type and `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y` a
compactification of `X` over `Y`. The derived lower shriek of [Stacks, Tag 0F7H] is
`Rf_! = Rf̄_* ∘ Rj_!`, which is `Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on the
unbounded derived categories `D(-_étale, Λ)` of sheaves of `Λ`-modules. This file constructs the
comparison maps of [Stacks, Tag 0F7B] for a cartesian square whose horizontal arrows are open
immersions, the map of [Stacks, Tag 0F7G] for a morphism of compactifications, and the
comparison of [Stacks, Tag 0F7I] along a cartesian morphism of compactifications, and proves them
invertible on bounded below objects with torsion cohomology granted the proper base change
theorem.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedIdIso` — `R(id_X)_* ≅ 𝟭`.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedDerivedCompIso` —
  `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` on `D(-_étale, Λ)`, for arbitrary `f` and `g`.
* `Stacks.EtaleCohomology.extensionByZeroDerivedDirectImageMap` — the map
  `Rj_! Rh'_* ⟶ Rh_* Rj'_!` of [Stacks, Tag 0F7B] for a cartesian square
  ```
  X' --j'--> X̄'
  |h'        |h
  v          v
  X  --j-->  X̄
  ```
  with `j` an open immersion: the mate, along the two adjunctions `Rj_! ⊣ j^{-1}` and
  `Rj'_! ⊣ j'^{-1}`, of the inverse of the open base change isomorphism
  `j^{-1} Rh_* ≅ Rh'_* j'^{-1}`.
* `Stacks.EtaleCohomology.compactificationHomExtensionByZeroMap` — the map of Tag 0F7G.
* `Stacks.EtaleCohomology.derivedLowerShriekCompactificationHom` — the comparison of Tag 0F7I.

## Main results

* `isIso_etaleModuleDerivedInverseImage_map_extensionByZeroDerivedDirectImageMap`
  — restricted to the open `X`, the map of Tag 0F7B is an isomorphism, with no hypothesis.
* `isIso_extensionByZeroDerivedDirectImageMap_app_of_cohomologyCommutesWithBaseChange`
  — Tag 0F7B (a) for such squares, granted that cohomology commutes with base change for `h`.
* `isIso_derivedLowerShriekCompactificationHom_app_of_cohomologyCommutesWithBaseChange`
  — Tag 0F7I along a cartesian morphism of compactifications, granted Tag 095T.

## Implementation notes

Torsion is a condition on the underlying complex of abelian sheaves
(`Stacks.EtaleCohomology.etaleModuleForgetDerived`): the proper base change theorem is formulated
for abelian sheaves (`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange`), and it reaches
`D(-_étale, Λ)` through
`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange`.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective)

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

/-! ### Extension by zero along an open immersion preserves torsion -/

section ExtensionByZero

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Extension by zero along an open immersion preserves torsion sheaves.** For an open
immersion `j : U ⟶ X` and a torsion abelian sheaf `F` on `U_étale`, `j_! F` is torsion. -/
public theorem torsionSheafProperty_extensionByZero
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
    (hF : Stacks.Torsion.torsionSheafProperty U.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((extensionByZero.{u, r} j).obj F) := by
  classical
  rw [extensionByZero_obj_eq_sheafify]
  refine Stacks.Torsion.torsionSheafProperty_sheafify.{max (u + 1) r} X.smallEtaleTopology _ ?_
  intro V x
  let P := extensionByZeroPresheaf j F.obj
  let fam : (V ⟶ Scheme.Etale.smallEtaleSource j) → AddCommGrpCat.{max (u + 1) r} :=
    fun φ ↦ F.obj.obj (Opposite.op (Scheme.Etale.sourceDescend j φ))
  let σ := extensionByZeroPresheafSectionIso j F.obj V
  have h2 : x = σ.hom (σ.inv x) := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
    rfl
  have hsub : Subsingleton (V ⟶ Scheme.Etale.smallEtaleSource j) := ⟨fun φ ψ ↦
    MorphismProperty.Over.Hom.ext ((cancel_mono j).1
      ((MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm))⟩
  by_cases hφ : Nonempty (V ⟶ Scheme.Etale.smallEtaleSource j)
  · obtain ⟨φ⟩ := hφ
    let : Unique (V ⟶ Scheme.Etale.smallEtaleSource j) :=
      { default := φ, uniq := fun _ ↦ Subsingleton.elim _ _ }
    let y : fam φ := (coproductUniqueIso fam).hom (σ.inv x)
    have hx : x = extensionByZeroSummandInclusion j F.obj φ y := by
      have h1 : σ.inv x = Sigma.ι fam φ y := by
        show σ.inv x = Sigma.ι fam default ((coproductUniqueIso fam).hom (σ.inv x))
        rw [← coproductUniqueIso_inv, ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
        rfl
      rw [h2, h1, ← ConcreteCategory.comp_apply]
      show (Sigma.ι fam φ ≫ Sigma.desc _) y = _
      rw [Sigma.ι_desc]
    obtain ⟨R, hR, hkill⟩ := hF (Scheme.Etale.sourceDescend j φ) y
    let e := Scheme.Etale.sourceDescendIso j φ
    refine ⟨(Sieve.functorPushforward (Scheme.Etale.smallEtaleCompose j) R).pullback e.inv,
      X.smallEtaleTopology.pullback_stable e.inv
        ((Scheme.Etale.smallEtaleCompose_coverPreserving j).cover_preserve hR), ?_⟩
    rintro W f ⟨Z, g, k, hg, hfk⟩
    obtain ⟨n, hn, hn0⟩ := hkill Z g hg
    refine ⟨n, hn, ?_⟩
    let η := (Scheme.Etale.smallEtaleCompose j).op.lanUnit.app F.obj
    have hres : P.map f.op x = P.map k.op (η.app (Opposite.op Z) (F.obj.map g.op y)) := by
      rw [hx, extensionByZeroSummandInclusion, ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply (P.map _), ← P.map_comp, ← op_comp, hfk, op_comp,
        P.map_comp, ConcreteCategory.comp_apply]
      congr 1
      exact (NatTrans.naturality_apply η g.op y).symm
    rw [hres, ← _root_.map_nsmul, ← _root_.map_nsmul, hn0, map_zero, map_zero]
  · have : IsEmpty (V ⟶ Scheme.Etale.smallEtaleSource j) := not_nonempty_iff.1 hφ
    have hid : 𝟙 (∐ fam) = 0 := Sigma.hom_ext _ _ (fun b ↦ isEmptyElim b)
    have hx : x = 0 := by
      rw [h2, ← ConcreteCategory.id_apply (σ.inv x), hid]
      simp
    refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W f _ ↦ ⟨1, one_pos, ?_⟩⟩
    rw [hx, map_zero, smul_zero]

/-- **Extension by zero preserves torsion cohomology.** For an open immersion `j` and an object `K`
of `D(U_étale)` with torsion cohomology sheaves, `j_! K` has torsion cohomology sheaves: `j_!` is
exact, so `Hⁱ(j_! K) ≅ j_! Hⁱ(K)`. -/
public theorem torsionCohomologyProperty_extensionByZero_mapDerivedCategory
    (K : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} U.smallEtaleTopology K) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((extensionByZero.{u, r} j).mapDerivedCategory.obj K) := fun q ↦
  Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
    (((extensionByZero.{u, r} j).mapDerivedCategoryHomologyIso q).app K).symm
    (torsionSheafProperty_extensionByZero.{u, r} j _ (hK q))

/-- **`Rj_!` preserves torsion cohomology, on `D(-_étale, Λ)`.** For an open immersion `j` and an
object `K` of `D(U_étale, Λ)` whose underlying complex of abelian sheaves has torsion cohomology
sheaves, so does `Rj_! K`: forgetting the module structure commutes with `Rj_!`, and the abelian
extension by zero preserves torsion cohomology. -/
public theorem torsionCohomologyProperty_etaleModuleForgetDerived_extensionByZero
    (K : DerivedCategory (EtaleModules.{u, r} Λ U))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} U.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ U).obj K)) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj K)) := fun q ↦
  Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedForgetIso.{u, r} Λ j).app K).symm)
    (torsionCohomologyProperty_extensionByZero_mapDerivedCategory.{u, r} j _ hK q)

end ExtensionByZero

/-- **Inverse image preserves torsion cohomology, on `D(-_étale, Λ)`.** For a morphism of schemes
`g : Y ⟶ X` and an object `K` of `D(X_étale, Λ)` whose underlying complex of abelian sheaves has
torsion cohomology sheaves, so does `g⁻¹ K`: forgetting the module structure commutes with `g⁻¹`
(`Stacks.EtaleCohomology.etaleModuleDerivedInverseImageForgetIso`), and the abelian inverse
image preserves torsion cohomology. -/
@[sga "4 IX 1.2" "(iv)"]
public theorem torsionCohomologyProperty_etaleModuleForgetDerived_inverseImage (Λ : Type r)
    [Ring Λ] {X Y : Scheme.{u}} (g : Y ⟶ X) (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} Y.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ Y).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).obj K)) := fun q ↦
  Stacks.Torsion.torsionSheafProperty_of_iso Y.smallEtaleTopology
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((etaleModuleDerivedInverseImageForgetIso.{u, r} Λ g).app K).symm)
    (torsionCohomologyProperty_etaleAbelianDerivedInverseImage.{u, r} g _ hK q)

/-! ### Direct image along the identity and along a composite -/

section DirectImage

variable (Λ : Type r) [Ring Λ]

/-- Direct image of sheaves of `Λ`-modules along the identity of `X` is the identity functor:
it is restriction along base change by the identity, which is isomorphic to the identity of the
small étale site. -/
public def etaleModuleDirectImageIdIso (X : Scheme.{u}) :
    etaleModuleDirectImage.{u, r} Λ (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _

/-- The degreewise identity `Q ⋙ 𝟭 ≅ (id_X)_* ⋙ Q`, exhibiting `𝟭` as a derived direct image
along the identity. -/
public def etaleModuleDerivedDirectImageUnboundedIdFac (X : Scheme.{u}) :
    DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (EtaleModules.{u, r} Λ X)) ≅
      (etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).symm ≪≫
        (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, r} Λ X)
          (ComplexShape.up ℤ)).symm) DerivedCategory.Q

/-- **Derived direct image along the identity is the identity**: `R(id_X)_* ≅ 𝟭` on
`D(X_étale, Λ)`. The identity functor is a right derived functor of `(id_X)_* ≅ 𝟭`, which is
exact, so the two right derived functors agree. -/
public def etaleModuleDerivedDirectImageUnboundedIdIso (X : Scheme.{u}) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (𝟙 X) ≅ 𝟭 _ :=
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))
    (𝟭 _) (etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X)
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 X))
    (etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X).inv
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)

/-- The comparison `(fg)_* ⋙ Q ⟶ Q ⋙ Rf_* ⋙ Rg_*` making `Rf_* ⋙ Rg_*` a derived direct image
along `fg = f ≫ g`: the composite of the derivation units of `Rg_*` (at `f_* K`) and of `Rf_*`. -/
public def etaleModuleDerivedDirectImageUnboundedDerivedCompUnit :
    (etaleModuleDirectImage.{u, r} Λ fg).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) :=
  Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f) _ ≫
    (Functor.associator _ _ _).hom

/-- `Rf_* ⋙ Rg_*` is a right derived functor of the direct image along `fg = f ≫ g`: on a
K-injective complex `I` both units are invertible, `f_* I` being K-injective because `f_*` has
the exact left adjoint `f^{-1}`. -/
public instance etaleModuleDerivedDirectImageUnboundedDerivedComp_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageUnboundedDerivedCompUnit.{u, r} Λ f g fg hfg)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q _)]
  intro I hI
  have : CochainComplex.IsKInjective
      (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (etaleModuleInverseImageAdj.{u, r} Λ f) I
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ g _ this
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f I hI
  simp only [etaleModuleDerivedDirectImageUnboundedDerivedCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **`R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` on `D(-_étale, Λ)`**, for arbitrary morphisms of schemes; the
composite is a separate argument `fg` with `fg = f ≫ g`. -/
public def etaleModuleDerivedDirectImageUnboundedDerivedCompIso :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ fg ≅
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg)
    (etaleModuleDerivedDirectImageUnboundedDerivedCompUnit.{u, r} Λ f g fg hfg)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

end DirectImage

/-! ### The comparison map of Tag 0F7B for a cartesian square with open horizontal arrows -/

section Square

variable (Λ : Type r) [Ring Λ]
  {X X' Xbar Xbar' : Scheme.{u}} (j : X ⟶ Xbar) (h : Xbar' ⟶ Xbar) (j' : X' ⟶ Xbar')
  (h' : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback j' h' h j)

/-- **The map of [Stacks, Tag 0F7B]** for a cartesian square
```
X' --j'--> X̄'
|h'        |h
v          v
X  --j-->  X̄
```
with `j` (hence `j'`) an open immersion: the natural map `Rj_! Rh'_* K ⟶ Rh_* Rj'_! K` on
`D(-_étale, Λ)`. It is the mate, along the adjunctions `Rj'_! ⊣ j'^{-1}` and `Rj_! ⊣ j^{-1}`, of
the inverse of the base change map `j^{-1} Rh_* ⟶ Rh'_* j'^{-1}` of Tag 0A2A, which is invertible
because `j` is an open immersion. -/
public def extensionByZeroDerivedDirectImageMap :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h' ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⟶
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j' ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h :=
  have := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion_unconditional.{u, r} Λ h j j' h' sq
  ((mateEquiv (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j')
    (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j)).symm
    (TwoSquare.mk _ _ _ _
      (inv (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h j j' h' sq.w)))).natTrans

/-- **Over the open `X`, the map of Tag 0F7B is an isomorphism.** For the cartesian square of
`extensionByZeroDerivedDirectImageMap`, the restriction `j^{-1}(Rj_! Rh'_* K ⟶ Rh_* Rj'_! K)` of
the comparison map to `X` is an isomorphism, for every `K`. By the unit identity of mates it is
identified, through the invertible units of `Rj_! ⊣ j^{-1}` and `Rj'_! ⊣ j'^{-1}`, with the
inverse of the open base change isomorphism. -/
public theorem isIso_etaleModuleDerivedInverseImage_map_extensionByZeroDerivedDirectImageMap
    (K : DerivedCategory (EtaleModules.{u, r} Λ X')) :
    IsIso ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ j).map
      ((extensionByZeroDerivedDirectImageMap.{u, r} Λ j h j' h' sq).app K)) := by
  have := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion_unconditional.{u, r} Λ h j j' h' sq
  have key := unit_mateEquiv_symm (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j')
    (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j)
    (TwoSquare.mk _ _ _ _ (inv (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h j j' h' sq.w))) K
  have hl : IsIso ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h').map
      ((etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j').unit.app K) ≫
      (TwoSquare.mk _ _ _ _
        (inv (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h j j' h' sq.w))).app _) := by
    show IsIso (_ ≫ (inv (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h j j' h' sq.w)).app _)
    infer_instance
  rw [key, isIso_comp_left_iff] at hl
  exact hl

/-- **The map of [Stacks, Tag 0F7B] is invertible at `K` as soon as the base change maps of `h`
are invertible at `Rj'_! K`.** For the cartesian square of `extensionByZeroDerivedDirectImageMap`
and an object `K` of `D(X'_étale, Λ)`, suppose that for every `i : Z ⟶ X̄` the base change map
`i^{-1} Rh_* ⟶ Rh_{Z,*} (i')^{-1}` of the pullback square of `h` along `i` is invertible at
`Rj'_! K`. Then `Rj_! Rh'_* K ⟶ Rh_* Rj'_! K` is an isomorphism.

The map is checked after restriction to the open `X` and to its closed complement `Z`, which
jointly reflect isomorphisms. Over `X` it is an isomorphism with no hypothesis. Over `Z` both
sides vanish: `i^{-1} Rj_! = 0`, and `i^{-1} Rh_* (Rj'_! K) ≅ Rh_{Z,*}((i')^{-1} Rj'_! K) = 0` by
the hypothesis, the inverse image of `Z` in `X̄'` being the complement of `X'` because the square
is cartesian. -/
public theorem isIso_extensionByZeroDerivedDirectImageMap_app_of_isIso_baseChange
    (K : DerivedCategory (EtaleModules.{u, r} Λ X'))
    (hbc : ∀ {Z : Scheme.{u}} (i : Z ⟶ Xbar),
      IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h i (pullback.fst h i) (pullback.snd h i)
        pullback.condition).app ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j').obj K))) :
    IsIso ((extensionByZeroDerivedDirectImageMap.{u, r} Λ j h j' h' sq).app K) := by
  -- the closed complement of the open `X` in `X̄`
  let C : TopologicalSpace.Closeds Xbar :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by
    simp [i, C, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  -- its inverse image in `X̄'` is the complement of `X'`
  have hrange : ∀ {P A B S : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S},
      IsPullback fst snd f g → Set.range fst.base = f.base ⁻¹' Set.range g.base := by
    intro P A B S fst snd f g H
    have hsurj : Function.Surjective H.isoPullback.hom.base := fun z ↦
      ⟨H.isoPullback.inv.base z, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
  have sqi := IsPullback.of_hasPullback h i
  have hij' : Set.range j'.base = (Set.range (pullback.fst h i).base)ᶜ := by
    rw [hrange sq, hrange sqi, hij, Set.preimage_compl]
  refine isIso_of_isIso_etaleModuleDerivedInverseImage_of_range_eq_compl Λ i j hij _ ?_
    (isIso_etaleModuleDerivedInverseImage_map_extensionByZeroDerivedDirectImageMap.{u, r}
      Λ j h j' h' sq K)
  refine IsZero.isIso
    (isZero_etaleModuleDerivedInverseImage_extensionByZero_general.{u, r} Λ i j hij _) ?_ _
  -- `i^{-1} Rh_* (Rj'_! K) ≅ Rh_{Z,*}((i')^{-1} Rj'_! K)`, and `(i')^{-1} Rj'_! K = 0`
  have hbci := hbc i
  refine IsZero.of_iso ?_ (asIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ h i
    (pullback.fst h i) (pullback.snd h i) sqi.w).app
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j').obj K)))
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ (pullback.snd h i)
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ (pullback.snd h i)
  exact Functor.map_isZero (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (pullback.snd h i))
    (isZero_etaleModuleDerivedInverseImage_extensionByZero_general.{u, r} Λ (pullback.fst h i) j'
      hij' K)

/-- **[Stacks, Tag 0F7B], case (a), for a cartesian square with open horizontal arrows, granted
the proper base change theorem for `h`.** Suppose that cohomology commutes with base change for
`h` (for `h` proper this is the proper base change theorem, [Stacks, Tag 095T]). Then for every
object `K` of `D(X'_étale, Λ)` which is bounded below and whose underlying complex of abelian
sheaves has torsion cohomology sheaves, the map `Rj_! Rh'_* K ⟶ Rh_* Rj'_! K` of
`extensionByZeroDerivedDirectImageMap` is an isomorphism.

The source proves this through the stalks of the higher direct images; here it is
`isIso_extensionByZeroDerivedDirectImageMap_app_of_isIso_baseChange`, the base change maps of `h`
being invertible at the bounded below complex `Rj'_! K`, which has torsion cohomology, by the
passage of [Stacks, Tag 0DDE]. -/
public theorem isIso_extensionByZeroDerivedDirectImageMap_app_of_cohomologyCommutesWithBaseChange
    (hh : CohomologyCommutesWithBaseChange.{u, r} h)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X')) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X'.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X').obj K)) :
    IsIso ((extensionByZeroDerivedDirectImageMap.{u, r} Λ j h j' h' sq).app K) := by
  have hGE : ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j').obj K).IsGE n := by
    have := Functor.isGE_obj_mapDerivedCategory (etaleModuleExtensionByZero.{u, r} Λ j') K n
      inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j').app K).symm n
  refine isIso_extensionByZeroDerivedDirectImageMap_app_of_isIso_baseChange Λ j h j' h' sq K
    fun i ↦ ?_
  exact isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, r} Λ hh
    (IsPullback.of_hasPullback h i) ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j').obj K)
    n (torsionCohomologyProperty_etaleModuleForgetDerived_extensionByZero.{u, r} Λ j' K hK)

end Square

/-! ### The comparison of Tag 0F7I along a cartesian morphism of compactifications -/

section Compactification

variable (Λ : Type r) [Ring Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {j₁ j₂ : CompactificationOf (Over.mk f)} (φ : j₁ ⟶ j₂)
  (hφ : IsPullback j₁.immersion (𝟙 X) (CompactificationOf.Hom.map φ) j₂.immersion)

/-- **The map of [Stacks, Tag 0F7G] for a morphism of compactifications.** For a morphism
`h : X̄₁ ⟶ X̄₂` of compactifications `j₁ : X ⟶ X̄₁`, `j₂ : X ⟶ X̄₂` of `X` over `Y` along which `X`
is cartesian (`h⁻¹(X) = X`), the map `Rj₂,! ⟶ Rh_* ∘ Rj₁,!`: the map of Tag 0F7B for the square
with left edge the identity of `X`, preceded by `R(id_X)_* ≅ 𝟭`. -/
public def compactificationHomExtensionByZeroMap :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j₂.immersion ⟶
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j₁.immersion ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map φ) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedIdIso.{u, r} Λ X).inv _ ≫
    extensionByZeroDerivedDirectImageMap.{u, r} Λ j₂.immersion (CompactificationOf.Hom.map φ)
      j₁.immersion (𝟙 X) hφ

/-- The structure morphisms of two compactifications are related by a morphism between them:
`f̄₁ = h ≫ f̄₂`. -/
public theorem CompactificationOf.toBase_eq_map_comp :
    j₁.toBase = CompactificationOf.Hom.map φ ≫ j₂.toBase :=
  (Over.w φ.hom.right).symm

/-- **The comparison of [Stacks, Tag 0F7I] along a cartesian morphism of compactifications.** For
a morphism `h : X̄₁ ⟶ X̄₂` of compactifications of `X` over `Y` with `h⁻¹(X) = X`, the natural map
`Rf_!^{(2)} = Rf̄₂_* ∘ Rj₂,! ⟶ Rf̄₂_* ∘ Rh_* ∘ Rj₁,! ≅ Rf̄₁_* ∘ Rj₁,! = Rf_!^{(1)}` on
`D(-_étale, Λ)`, built from the map of Tag 0F7G and `R(h ≫ f̄₂)_* ≅ Rh_* ⋙ Rf̄₂_*`. It is an
isomorphism on bounded below objects with torsion cohomology, granted the proper base change
theorem
(`isIso_derivedLowerShriekCompactificationHom_app_of_cohomologyCommutesWithBaseChange`). -/
public def derivedLowerShriekCompactificationHom :
    derivedLowerShriekUnbounded.{u, r} f j₂ Λ ⟶ derivedLowerShriekUnbounded.{u, r} f j₁ Λ :=
  Functor.whiskerRight (compactificationHomExtensionByZeroMap.{u, r} Λ φ hφ)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j₂.toBase) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ
      (CompactificationOf.Hom.map φ) j₂.toBase j₁.toBase
      (CompactificationOf.toBase_eq_map_comp φ)).inv

/-- **[Stacks, Tag 0F7I] along a cartesian morphism of compactifications, granted the proper base
change theorem.** Suppose that cohomology commutes with base change for every proper morphism of
schemes ([Stacks, Tag 095T]). For a morphism `h : X̄₁ ⟶ X̄₂` of compactifications of `X` over `Y`
with `h⁻¹(X) = X`, the comparison `Rf_!^{(2)} K ⟶ Rf_!^{(1)} K` is an isomorphism for every `K` in
`D(X_étale, Λ)` bounded below whose underlying complex of abelian sheaves has torsion cohomology
sheaves.

The morphism `h` is proper, `f̄₁ = h ≫ f̄₂` being proper and `f̄₂` separated, so this is
`isIso_extensionByZeroDerivedDirectImageMap_app_of_cohomologyCommutesWithBaseChange` for the
square with left edge the identity of `X`. -/
public theorem
    isIso_derivedLowerShriekCompactificationHom_app_of_cohomologyCommutesWithBaseChange
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    IsIso ((derivedLowerShriekCompactificationHom.{u, r} Λ φ hφ).app K) := by
  have : IsProper (CompactificationOf.Hom.map φ ≫ j₂.toBase) := by
    rw [← CompactificationOf.toBase_eq_map_comp φ]
    infer_instance
  have : IsProper (CompactificationOf.Hom.map φ) := IsProper.of_comp _ j₂.toBase
  have hγ :=
    isIso_extensionByZeroDerivedDirectImageMap_app_of_cohomologyCommutesWithBaseChange.{u, r}
      Λ j₂.immersion (CompactificationOf.Hom.map φ) j₁.immersion (𝟙 X) hφ
      (h095T (CompactificationOf.Hom.map φ)) K n hK
  dsimp only [derivedLowerShriekCompactificationHom,
    compactificationHomExtensionByZeroMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end Compactification

end Stacks.EtaleCohomology

end
