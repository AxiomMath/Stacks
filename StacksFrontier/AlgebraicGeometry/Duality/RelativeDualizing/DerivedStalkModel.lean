module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DimensionFunctionScheme
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat

/-!
# The derived stalk of a dualizing complex, and the dimension function it determines

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X`. [Stacks, Tag 0AWF]
says that `X` is universally catenary and that the function `x ↦ δ(x)`, where
`ω^•_{X,x}⟦-δ(x)⟧` is a normalized dualizing complex over `𝒪_{X,x}`, is a dimension function.
Here `ω^•_{X,x}` is the derived stalk of `K` at `x`. The source proves this as "immediate from
the affine case and the definitions": over an affine open `U ∋ x` the complex `K` is the sheaf
associated to a dualizing complex `ω` over `Γ(X, U)`, so `ω^•_{X,x}` is the localization of `ω`
at the prime of `x`, and the affine case is [Stacks, Tag 0A7Z]. This file makes the first step
precise and deduces the lemma.

## Main results

* `Stacks.Duality.restrictStalkModuleNatIso` — the stalk at `x` of the restriction of a sheaf of
  modules along an open immersion `j` is the stalk at `j x`, as modules over `𝒪_{Y, j x}`.
* `Stacks.Duality.tildeSchemeStalkIso` — the stalk at `y` of the sheaf on `Spec R` associated to
  an `R`-module `M` is `𝒪_{Spec R, y} ⊗_R M`, naturally in `M`.
* `Stacks.Duality.affineStalkNatIso` — the same for an affine open `U` of `X`, read over
  `𝒪_{X,x}` through `Stacks.Duality.affineGermRingHom`, which presents `𝒪_{X,x}` as the
  localization of `Γ(X, U)` at the prime of `x`
  (`Stacks.Duality.isLocalization_affineGermRingHom`).
* `Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars` — **the derived stalk of `K`
  at `x` is the localization of any dualizing model of `K` over an affine open neighbourhood**.
* `Stacks.Duality.associatedShiftFunction_eq_dualizingDimension` — the shift function of `K` is
  the dimension function ([Stacks, Tag 0A7W]) of any such model.
* `Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction` —
  **[Stacks, Tag 0AWF]**.

## Implementation notes

*The comparison of stalks.* The stalk functor of `Stacks.Duality.schemeStalkModuleFunctor` is
exact, so it descends to the derived categories, and the derived stalk of a complex is computed
degreewise. The comparison with a model `ω` over `Γ(X, U)` is therefore a chain of isomorphisms
of exact functors, each descended along
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`: restriction to `U` does not
change stalks (`Stacks.Duality.restrictStalkModuleNatIso`, applied to `U.ι` and to
`U ≅ Spec Γ(X, U)`), and the stalk of an associated sheaf is a base change
(`Stacks.TildeStalk.tildeStalkFunctorIso`). The base change is along a flat map, a localization,
so it is exact as well and the composite is the extension of scalars of `ω` read in the derived
category, which is the functor of
`Dualizing.isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension`.

*The ring map.* The local ring is reached from `Γ(X, U)` through the stalk of `Spec Γ(X, U)` and
the isomorphisms of stalks along `U.ι` and `U ≅ Spec Γ(X, U)`; the resulting ring map
`Stacks.Duality.affineGermRingHom` is used as it comes, and that `𝒪_{X,x}` is a localization
through it is transported from the stalk of `Spec Γ(X, U)`, so no identification of it with the
germ map is needed.

*Derived categories.* `D(𝒪_X)` is an instance argument, as in `Stacks.Duality.IsDualizingComplex`.
The derived categories of modules over rings and of `𝒪_U`-modules are at
`CategoryTheory.HasDerivedCategory.standard`; this is forced for modules over rings by
`Dualizing.IsNormalizedDualizingComplex`.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Duality

/-! ### Exactness of the stalk module functor -/

/-- The stalk module functor preserves finite limits: the stalk functor does, and restriction of
scalars along the comparison of the two stalk rings is the functor of an equivalence. -/
instance schemeStalkModuleFunctor_preservesFiniteLimits {Z : Scheme.{u}} (z : Z) :
    PreservesFiniteLimits (schemeStalkModuleFunctor z) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf z)
    (ModuleCat.restrictScalars.{u} (SemilinearStalk.commStalkIso Z.presheaf z).inv.hom)
    (AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits Z.ringCatSheaf z)
    (@PreservesLimits.preservesFiniteLimits _ _ _ _ _
      (Adjunction.rightAdjoint_preservesLimits (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (SemilinearStalk.commStalkRingEquiv Z.presheaf z).symm).symm.toAdjunction))

/-- The stalk module functor preserves finite colimits. -/
instance schemeStalkModuleFunctor_preservesFiniteColimits {Z : Scheme.{u}} (z : Z) :
    PreservesFiniteColimits (schemeStalkModuleFunctor z) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf z)
    (ModuleCat.restrictScalars.{u} (SemilinearStalk.commStalkIso Z.presheaf z).inv.hom)
    (AlgebraicGeometry.SheafOfModules.instPreservesFiniteColimitsStalkFunctor Z.ringCatSheaf z)
    (@PreservesColimits.preservesFiniteColimits _ _ _ _ _
      (Adjunction.leftAdjoint_preservesColimits (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (SemilinearStalk.commStalkRingEquiv Z.presheaf z).symm).toAdjunction))

/-- `Stacks.Duality.schemeStalkModuleFunctor` with its source written as `X.Modules`, the category
the restriction functors and the derived categories of this file are stated for. -/
def modulesStalkFunctor {Z : Scheme.{u}} (z : Z) :
    Z.Modules ⥤ ModuleCat.{u} (Z.presheaf.stalk z) :=
  schemeStalkModuleFunctor z

/-- The stalk module functor on `X.Modules` is additive. -/
instance modulesStalkFunctor_additive {Z : Scheme.{u}} (z : Z) :
    (modulesStalkFunctor z).Additive :=
  inferInstanceAs (schemeStalkModuleFunctor z).Additive

/-- The stalk module functor on `X.Modules` preserves finite limits. -/
instance modulesStalkFunctor_preservesFiniteLimits {Z : Scheme.{u}} (z : Z) :
    PreservesFiniteLimits (modulesStalkFunctor z) :=
  inferInstanceAs (PreservesFiniteLimits (schemeStalkModuleFunctor z))

/-- The stalk module functor on `X.Modules` preserves finite colimits. -/
instance modulesStalkFunctor_preservesFiniteColimits {Z : Scheme.{u}} (z : Z) :
    PreservesFiniteColimits (modulesStalkFunctor z) :=
  inferInstanceAs (PreservesFiniteColimits (schemeStalkModuleFunctor z))

section OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)

/-- The germ of a section `b` over `W` is the image under the stalk map of the germ of the
corresponding section of `Y` over `j ''ᵁ W`. -/
theorem stalkMap_germ_appIso_inv (W : X.Opens) (hx : x ∈ W) (b : Γ(X, W)) :
    j.stalkMap x (Y.presheaf.germ (j ''ᵁ W) (j x) (by simpa using hx) ((j.appIso W).inv b)) =
      X.presheaf.germ W x hx b := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact X.presheaf.germ_res_apply _ _ _ _

/-- On germs, the action of `𝒪_{Z,z}` on the stalk module of `schemeStalkModuleFunctor` is the
action of sections. -/
theorem schemeStalkModuleFunctor_germ_smul {Z : Scheme.{u}} (z : Z) (M : Z.Modules)
    (V : Z.Opens) (hz : z ∈ V) (a : Γ(Z, V)) (n : Γ(M, V)) :
    (show (schemeStalkModuleFunctor z).obj M from
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf V z hz).hom (a • n)) =
      Z.presheaf.germ V z hz a •
        (show (schemeStalkModuleFunctor z).obj M from
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf V z hz).hom n) := by
  have h : (SemilinearStalk.commStalkIso Z.presheaf z).inv.hom (Z.presheaf.germ V z hz a) =
      TopCat.Presheaf.germ (C := RingCat.{u}) Z.ringCatSheaf.obj V z hz a := by
    rw [← SemilinearStalk.commStalkRingEquiv_germ Z.presheaf z V hz a]
    change ((SemilinearStalk.commStalkIso Z.presheaf z).hom ≫
      (SemilinearStalk.commStalkIso Z.presheaf z).inv).hom _ = _
    rw [Iso.hom_inv_id]
    rfl
  refine (PresheafOfModules.germ_ringCat_smul M.val z V hz a n).trans ?_
  rw [← h]
  rfl

/-- The comparison `restrictStalkNatIso` of stalks of abelian groups along an open immersion, as
an additive bijection. -/
def restrictStalkAddEquiv (G : Y.Modules) :
    (schemeStalkModuleFunctor x).obj ((Scheme.Modules.restrictFunctor j).obj G) ≃+
      (schemeStalkModuleFunctor (j x)).obj G :=
  ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv

/-- `Stacks.Duality.restrictStalkAddEquiv` sends the germ at `x` of a section `t` of `G|_X` over
`W` to the germ at `j x` of `t`, viewed as a section of `G` over `j ''ᵁ W`. -/
theorem restrictStalkAddEquiv_germ (G : Y.Modules) (W : X.Opens) (hx : x ∈ W)
    (t : Γ((Scheme.Modules.restrictFunctor j).obj G, W)) :
    restrictStalkAddEquiv j x G
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((Scheme.Modules.restrictFunctor j).obj G).val.presheaf W x hx).hom t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf (j ''ᵁ W) (j x)
        (by simpa using hx)).hom t :=
  ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x G hx) t

/-- **The stalk of a restriction along an open immersion.** The stalk at `x` of `G|_X`, as a
module over `𝒪_{Y, j x}` through the stalk map, is the stalk of `G` at `j x`. -/
def restrictStalkModuleIso (G : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((schemeStalkModuleFunctor x).obj ((Scheme.Modules.restrictFunctor j).obj G)) ≅
      (schemeStalkModuleFunctor (j x)).obj G :=
  LinearEquiv.toModuleIso (show
    ((ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((schemeStalkModuleFunctor x).obj ((Scheme.Modules.restrictFunctor j).obj G))) ≃ₗ[
        Y.presheaf.stalk (j x)] ((schemeStalkModuleFunctor (j x)).obj G) from
    { toAddEquiv := restrictStalkAddEquiv j x G
      map_smul' := by
        intro s m
        obtain ⟨W₁, hx₁, b, hb⟩ := X.presheaf.exists_germ_eq (j.stalkMap x s)
        obtain ⟨W₂, hx₂, t, ht⟩ := TopCat.Presheaf.exists_germ_eq
          ((Scheme.Modules.restrictFunctor j).obj G).val.presheaf m
        let W := W₁ ⊓ W₂
        have hx : x ∈ W := ⟨hx₁, hx₂⟩
        let b' : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left : W ⟶ W₁).op b
        let t' : Γ((Scheme.Modules.restrictFunctor j).obj G, W) :=
          ((Scheme.Modules.restrictFunctor j).obj G).val.presheaf.map
            (homOfLE inf_le_right : W ⟶ W₂).op t
        have hb' : X.presheaf.germ W x hx b' = j.stalkMap x s := by
          rw [← hb]
          exact X.presheaf.germ_res_apply _ _ _ _
        have ht' : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            ((Scheme.Modules.restrictFunctor j).obj G).val.presheaf W x hx).hom t' = m := by
          rw [← ht]
          exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
        have hs : Y.presheaf.germ (j ''ᵁ W) (j x) (by simpa using hx)
            ((j.appIso W).inv b') = s := by
          apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
          rw [stalkMap_germ_appIso_inv j x W hx b', hb']
        change restrictStalkAddEquiv j x G (j.stalkMap x s • m) =
          s • restrictStalkAddEquiv j x G m
        rw [← hb', ← ht']
        refine (congrArg (restrictStalkAddEquiv j x G)
          (schemeStalkModuleFunctor_germ_smul x _ W hx b' t').symm).trans ?_
        refine (restrictStalkAddEquiv_germ j x G W hx _).trans ?_
        refine Eq.trans ?_ (congrArg (fun r => r • restrictStalkAddEquiv j x G _) hs)
        refine Eq.trans ?_
          (congrArg (fun n => _ • n) (restrictStalkAddEquiv_germ j x G W hx t').symm)
        exact schemeStalkModuleFunctor_germ_smul (j x) G (j ''ᵁ W) _ ((j.appIso W).inv b') t' })

/-- **The stalk of a restriction along an open immersion, as an isomorphism of functors.** -/
def restrictStalkModuleNatIso :
    Scheme.Modules.restrictFunctor j ⋙ modulesStalkFunctor x ⋙
        ModuleCat.restrictScalars (j.stalkMap x).hom ≅
      modulesStalkFunctor (j x) :=
  NatIso.ofComponents (restrictStalkModuleIso j x) fun {G G'} f => by
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality f) m

end OpenImmersion

/-! ### Extension of scalars followed by restriction along a ring isomorphism -/

section RingEquiv

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Extension of scalars along `e.symm : T ≃+* S` is restriction of scalars along `e`: both are
left adjoint to restriction of scalars along `e.symm`. -/
def extendScalarsSymmIsoRestrictScalars (e : S ≃+* T) :
    ModuleCat.extendScalars.{u, u, u} e.symm.toRingHom ≅
      ModuleCat.restrictScalars.{u} e.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj e.symm.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction

/-- **Extension of scalars followed by restriction along a ring isomorphism** is extension of
scalars along the composite with the inverse isomorphism. -/
def extendScalarsCompRestrictScalarsIso (g : R →+* T) (e : S ≃+* T) :
    ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars.{u} e.toRingHom ≅
      ModuleCat.extendScalars.{u, u, u} (e.symm.toRingHom.comp g) :=
  Functor.isoWhiskerLeft _ (extendScalarsSymmIsoRestrictScalars e).symm ≪≫
    (ModuleCat.extendScalarsComp g e.symm.toRingHom).symm

end RingEquiv

/-! ### The stalk of an associated sheaf on an affine scheme -/

section TildeStalk

variable (R : CommRingCat.{u}) (y : Spec R)

/-- The germ map `R ⟶ 𝒪_{Spec R, y}` into the `CommRingCat`-valued stalk. -/
def specGermRingHom : R →+* (Spec R).presheaf.stalk y :=
  letI := Stacks.RingedSpace.structureStalkCommRing (Spec R).toRingedSpace y
  (SemilinearStalk.commStalkRingEquiv (Spec R).presheaf y).toRingHom.comp
    (Stacks.TildeStalk.specStalkRingHom R y)

/-- **The stalk of `M~` at `y` is `𝒪_{Spec R, y} ⊗_R M`**, naturally in `M`, for the stalk module
of `Stacks.Duality.schemeStalkModuleFunctor`. -/
def tildeSchemeStalkIso :
    tilde.functor R ⋙ modulesStalkFunctor y ≅
      ModuleCat.extendScalars.{u, u, u} (specGermRingHom R y) :=
  letI := Stacks.RingedSpace.structureStalkCommRing (Spec R).toRingedSpace y
  Functor.isoWhiskerRight (Stacks.TildeStalk.tildeStalkFunctorIso R y)
      (ModuleCat.restrictScalars.{u}
        (SemilinearStalk.commStalkRingEquiv (Spec R).presheaf y).symm.toRingHom) ≪≫
    extendScalarsCompRestrictScalarsIso (Stacks.TildeStalk.specStalkRingHom R y)
      (SemilinearStalk.commStalkRingEquiv (Spec R).presheaf y).symm

/-- `Stacks.Duality.specGermRingHom` is the algebra map `R → 𝒪_{Spec R, y}`. -/
theorem specGermRingHom_eq :
    letI : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
    specGermRingHom R y = algebraMap R ((Spec R).presheaf.stalk y) := by
  ext r
  exact SemilinearStalk.commStalkRingEquiv_germ (Spec R).presheaf y ⊤ trivial _

end TildeStalk

/-! ### The stalk of the sheaf associated to a module over an affine open -/

section AffineOpen

/-- The stalk maps of an open immersion are isomorphisms; stated with the point a variable so that
it applies where instance search does not see through an anonymous constructor. -/
theorem isIso_stalkMap_of_isOpenImmersion {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (y : Y) : IsIso (f.stalkMap y) :=
  inferInstance

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)

/-- The stalk map of `U.ι` at `x`, with its source written as `𝒪_{X,x}`. -/
def affineStalkMap : X.presheaf.stalk x ⟶ U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme) :=
  U.ι.stalkMap (⟨x, hx⟩ : U.toScheme)

/-- The stalk of a restriction to `U`, read over `𝒪_{X,x}`, is the stalk at `x`. -/
def affineRestrictStalkNatIso :
    Scheme.Modules.restrictFunctor U.ι ⋙ modulesStalkFunctor (⟨x, hx⟩ : U.toScheme) ⋙
        ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom ≅
      modulesStalkFunctor x :=
  restrictStalkModuleNatIso U.ι (⟨x, hx⟩ : U.toScheme)

/-- The two descriptions of the local ring at `x ∈ U`: as the stalk of `X` and as the stalk of
`Spec Γ(X, U)` at the prime of `x`, compared through the stalk of `U`. -/
def affineStalkRingEquiv :
    X.presheaf.stalk x ≃+* (Spec Γ(X, U)).presheaf.stalk (hU.primeIdealOf (⟨x, hx⟩ : U)) :=
  (@asIso _ _ _ _ (U.ι.stalkMap (⟨x, hx⟩ : U)) (isIso_stalkMap_of_isOpenImmersion _ _) ≪≫
    (@asIso _ _ _ _ (hU.isoSpec.hom.stalkMap (⟨x, hx⟩ : U))
      (isIso_stalkMap_of_isOpenImmersion _ _)).symm).commRingCatIsoToRingEquiv

/-- The stalk map of `U.ι` at `x` is the composite of `Stacks.Duality.affineStalkRingEquiv` with
the stalk map of `U ≅ Spec Γ(X, U)`. -/
theorem stalkMap_isoSpec_comp_affineStalkRingEquiv :
    (U.ι.stalkMap (⟨x, hx⟩ : U)).hom =
      (hU.isoSpec.hom.stalkMap (⟨x, hx⟩ : U)).hom.comp
        (affineStalkRingEquiv hU x hx).toRingHom := by
  ext b
  exact (ConcreteCategory.congr_hom
    (@asIso _ _ _ _ (hU.isoSpec.hom.stalkMap (⟨x, hx⟩ : U))
      (isIso_stalkMap_of_isOpenImmersion _ _)).inv_hom_id (U.ι.stalkMap (⟨x, hx⟩ : U) b)).symm

/-- The ring map `Γ(X, U) → 𝒪_{X,x}` through which the stalk of an associated sheaf is computed:
the germ map of `Spec Γ(X, U)` at the prime of `x`, read in `𝒪_{X,x}`. -/
def affineGermRingHom : Γ(X, U) →+* X.presheaf.stalk x :=
  (affineStalkRingEquiv hU x hx).symm.toRingHom.comp
    (specGermRingHom Γ(X, U) (hU.primeIdealOf (⟨x, hx⟩ : U)))

/-- `𝒪_{X,x}` is the localization of `Γ(X, U)` at the prime of `x`, through
`Stacks.Duality.affineGermRingHom`. -/
theorem isLocalization_affineGermRingHom :
    letI := (affineGermRingHom hU x hx).toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf (⟨x, hx⟩ : U)).asIdeal := by
  let := (affineGermRingHom hU x hx).toAlgebra
  let y := hU.primeIdealOf (⟨x, hx⟩ : U)
  let : Algebra Γ(X, U) ((Spec Γ(X, U)).presheaf.stalk y) := StructureSheaf.stalkAlgebra _ y
  have : IsLocalization.AtPrime ((Spec Γ(X, U)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let e : (Spec Γ(X, U)).presheaf.stalk y ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
    { (affineStalkRingEquiv hU x hx).symm with
      commutes' := fun a => by
        change (affineStalkRingEquiv hU x hx).symm (algebraMap _ _ a) =
          (affineStalkRingEquiv hU x hx).symm (specGermRingHom Γ(X, U) y a)
        exact congrArg _ (DFunLike.congr_fun (specGermRingHom_eq Γ(X, U) y) a).symm }
  exact IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl e

/-- **The stalk at `x` of the sheaf on `U` associated to a `Γ(X, U)`-module `M` is
`𝒪_{X,x} ⊗ M`**, naturally in `M`, the sheaf being transported to `U` along `U ≅ Spec Γ(X, U)`
and its stalk read as a module over `𝒪_{X,x}`. -/
def affineStalkNatIso :
    tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
        modulesStalkFunctor (⟨x, hx⟩ : U.toScheme) ⋙
          ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom ≅
      ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx) := by
  let xU : U.toScheme := ⟨x, hx⟩
  let θ := affineStalkRingEquiv hU x hx
  change (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
      modulesStalkFunctor xU) ⋙ ModuleCat.restrictScalars.{u} (U.ι.stalkMap xU).hom ≅ _
  refine Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' θ.toRingHom
    (hU.isoSpec.hom.stalkMap xU).hom (U.ι.stalkMap xU).hom
    (stalkMap_isoSpec_comp_affineStalkRingEquiv hU x hx)) ≪≫ ?_
  change (tilde.functor Γ(X, U) ⋙ (Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
      modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u}
        (hU.isoSpec.hom.stalkMap xU).hom)) ⋙ ModuleCat.restrictScalars.{u} θ.toRingHom ≅ _
  refine Functor.isoWhiskerRight (Functor.isoWhiskerLeft (tilde.functor Γ(X, U))
    (restrictStalkModuleNatIso hU.isoSpec.hom xU)) _ ≪≫ ?_
  refine Functor.isoWhiskerRight (tildeSchemeStalkIso Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)) _ ≪≫ ?_
  exact extendScalarsCompRestrictScalarsIso (specGermRingHom Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)) θ

/-- Extension of scalars along `Stacks.Duality.affineGermRingHom` preserves finite limits, being
the base change along a localization. -/
private theorem preservesFiniteLimits_extendScalars_affineGermRingHom {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI := (affineGermRingHom hU x hx).toAlgebra
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)) := by
  let := (affineGermRingHom hU x hx).toAlgebra
  have := isLocalization_affineGermRingHom hU x hx
  exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))

end AffineOpen


/-! ### The derived stalk of a dualizing complex is the localization of a dualizing model -/

section DerivedStalk

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

open Stacks.DerivedCategoryComparisons in
/-- **The derived stalk of `K` at `x` is the extension to `𝒪_{X,x}` of any model of `K` over an
affine open neighbourhood of `x`.** Let `E` represent `K` and let `ω` over `Γ(X, U)` satisfy
`K|_U ≅ ω~` in `D(𝒪_U)`. Then the degreewise stalk of `E` at `x` is isomorphic, in
`D(𝒪_{X,x})`, to the degreewise extension of scalars of `ω` along
`Stacks.Duality.affineGermRingHom`, which presents `𝒪_{X,x}` as the localization of `Γ(X, U)`
at the prime of `x`. -/
theorem nonempty_derivedStalkOfComplex_iso_extendScalars {K : DerivedCategory X.Modules}
    (E : CochainComplex X.Modules ℤ) (hE : Nonempty (DerivedCategory.Q.obj E ≅ K))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hω : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) :
    letI := (affineGermRingHom hU x hx).toAlgebra
    letI : PreservesFiniteLimits
        (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)) :=
      haveI := isLocalization_affineGermRingHom hU x hx
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))
    Nonempty (derivedStalkOfComplex x E ≅
      (ModuleCat.extendScalars.{u, u, u}
        (affineGermRingHom hU x hx)).mapDerivedCategory.obj ω) := by
  let := (affineGermRingHom hU x hx).toAlgebra
  have := preservesFiniteLimits_extendScalars_affineGermRingHom hU x hx
  let xU : U.toScheme := ⟨x, hx⟩
  have hG := mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor U.ι)
    (modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom)
  have hT := mapDerivedCategoryCompIso
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)
    (modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom)
  have hN := mapDerivedCategoryIsoOfNatIso
    ((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
      (modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom))
    (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx))
    (affineStalkNatIso hU x hx)
  have hS := mapDerivedCategoryIsoOfNatIso
    (Scheme.Modules.restrictFunctor U.ι ⋙
      (modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom))
    (modulesStalkFunctor x) (affineRestrictStalkNatIso x hx)
  have e0 : derivedStalkOfComplex x E ≅
      (modulesStalkFunctor x).mapDerivedCategory.obj (DerivedCategory.Q.obj E) :=
    ((modulesStalkFunctor x).mapDerivedCategoryFactors.app E).symm
  exact ⟨e0 ≪≫ (modulesStalkFunctor x).mapDerivedCategory.mapIso hE.some ≪≫
    hS.symm.app K ≪≫ hG.app K ≪≫
    (modulesStalkFunctor xU ⋙
      ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom).mapDerivedCategory.mapIso hω.some ≪≫
    (hT.app ω).symm ≪≫ hN.app ω⟩

/-- **The normalizing shift of a derived stalk is the dimension function of a model.** Let `ω`
be a dualizing model of `K` over an affine open `U ∋ x` and let `E` represent `K`. Then
`ω^•_{X,x}⟦-n⟧`, the shifted derived stalk of `E` at `x`, is a normalized dualizing complex over
`𝒪_{X,x}` exactly when `n` is the value at the prime of `x` of the dimension function of `ω`
([Stacks, Tag 0A7W]). -/
theorem isNormalizedDualizingComplex_derivedStalkOfComplex_shift_iff [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules}
    (E : CochainComplex X.Modules ℤ) (hE : Nonempty (DerivedCategory.Q.obj E ≅ K))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω) (n : ℤ) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    Dualizing.IsNormalizedDualizingComplex.{u, u} (A := X.presheaf.stalk x)
        ((derivedStalkOfComplex x E)⟦-n⟧) ↔
      n = Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨x, hx⟩) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := (affineGermRingHom hU x hx).toAlgebra
  have := isLocalization_affineGermRingHom hU x hx
  have := preservesFiniteLimits_extendScalars_affineGermRingHom hU x hx
  obtain ⟨e⟩ := nonempty_derivedStalkOfComplex_iso_extendScalars E hE hU x hx ω hω.2
  rw [Dualizing.isNormalizedDualizingComplex_congr.{u, u}
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))) (-n)).mapIso e)]
  exact Dualizing.isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension ω hω.1
    (hU.primeIdealOf ⟨x, hx⟩) (X.presheaf.stalk x) n

/-- **The shift function of a dualizing complex is read off any dualizing model.** At a point `x`
of an affine open `U` carrying a dualizing model `ω` of `K`, the value of
`Stacks.Duality.associatedShiftFunction` is the value at the prime of `x` of the dimension function
of `ω`. -/
theorem associatedShiftFunction_eq_dualizingDimension [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω)
    (x : X) (hx : x ∈ U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    associatedShiftFunction K x =
      Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨x, hx⟩) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hset : {n : ℤ | ∃ E : CochainComplex X.Modules ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
        Dualizing.IsNormalizedDualizingComplex (A := X.presheaf.stalk x)
          ((derivedStalkOfComplex x E)⟦-n⟧)} =
      {Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨x, hx⟩)} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨E, hE, hn⟩ =>
      (isNormalizedDualizingComplex_derivedStalkOfComplex_shift_iff E hE hU x hx ω hω n).mp hn,
      fun hn => ⟨DerivedCategory.Q.objPreimage K, ⟨DerivedCategory.Q.objObjPreimageIso K⟩,
        (isNormalizedDualizingComplex_derivedStalkOfComplex_shift_iff _
          ⟨DerivedCategory.Q.objObjPreimageIso K⟩ hU x hx ω hω n).mpr hn⟩⟩
  change sInf _ = _
  rw [hset, csInf_singleton]

/-- Every point of a locally Noetherian scheme with a dualizing complex `K` lies in an affine open
carrying a dualizing model of `K`. -/
private theorem exists_isDualizingModelOn_of_mem [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) (x : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), IsDualizingModelOn K hU ω := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, he⟩ := hK U hU
  exact ⟨U, hU, hxU, ω, hω, he⟩

/-- **The shift function of a dualizing complex satisfies the characterising condition of the
dimension function.** -/
theorem isDualizingDimensionFunction_associatedShiftFunction [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    IsDualizingDimensionFunction K (associatedShiftFunction K) := by
  intro x
  obtain ⟨U, hU, hxU, ω, hω⟩ := exists_isDualizingModelOn_of_mem hK x
  exact ⟨U, hU, hxU, ω, hω, fun y => associatedShiftFunction_eq_dualizingDimension hU ω hω y.1 y.2⟩

/-- Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X`. Then `X` is
universally catenary, and the function `δ : X → ℤ` defined by `x ↦ δ(x)` such that
`ω^•_{X,x}⟦-δ(x)⟧` is a normalized dualizing complex over `𝒪_{X,x}` is a dimension function.

Here `δ` is `Stacks.Duality.associatedShiftFunction K`, and `ω^•_{X,x}` is the derived stalk of
`K` at `x`, computed degreewise on any complex `E` representing `K`
(`Stacks.Duality.derivedStalkOfComplex`). The second conjunct says that `δ(x)` is *the* integer
of the source: for every representative `E`, `ω^•_{X,x}⟦-n⟧` is a normalized dualizing complex
exactly when `n = δ(x)`. The third says that `δ` is a dimension function. -/
@[stacks 0AWF]
theorem isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction
    [IsLocallyNoetherian X] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    AlgebraicGeometry.Scheme.IsUniversallyCatenary X ∧
      (∀ (x : X) (E : CochainComplex X.Modules ℤ), Nonempty (DerivedCategory.Q.obj E ≅ K) →
        ∀ n : ℤ, Dualizing.IsNormalizedDualizingComplex.{u, u} (A := X.presheaf.stalk x)
            ((derivedStalkOfComplex x E)⟦-n⟧) ↔ n = associatedShiftFunction K x) ∧
      ∃ d : TopologicalSpace.DimensionFunction X, ∀ x : X, d x = associatedShiftFunction K x := by
  refine ⟨isUniversallyCatenary_of_isDualizingComplex hK, fun x E hE n => ?_,
    exists_dimensionFunction_of_isDualizingDimensionFunction K _
      (isDualizingDimensionFunction_associatedShiftFunction hK)⟩
  obtain ⟨U, hU, hxU, ω, hω⟩ := exists_isDualizingModelOn_of_mem hK x
  rw [associatedShiftFunction_eq_dualizingDimension hU ω hω x hxU]
  exact isNormalizedDualizingComplex_derivedStalkOfComplex_shift_iff E hE hU x hxU ω hω n

end DerivedStalk

end Stacks.Duality
