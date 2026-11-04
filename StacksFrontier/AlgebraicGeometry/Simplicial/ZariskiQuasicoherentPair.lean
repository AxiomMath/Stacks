module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianPair

/-!
# Quasi-coherent modules on the total Zariski site are pairs with quasi-coherent module

Let `X` be a simplicial scheme. By Stacks 0D7M a sheaf of `𝒪_X`-modules on the total Zariski site
is quasi-coherent exactly when it is cartesian and its components are quasi-coherent; for a
cartesian module the components are the pullbacks of the component in degree zero, so it is
enough that the component in degree zero be quasi-coherent. Combined with Stacks 07TH for the
total Zariski site (`AlgebraicGeometry.SimplicialScheme.zariskiPairFunctor_isEquivalence`) this
identifies the quasi-coherent modules on `X_Zar` with the pairs `(ℱ, α)` whose module `ℱ` is a
quasi-coherent `𝒪_{X_0}`-module.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.QuasicoherentZariskiPair`: the pairs with quasi-coherent
  module.
* `AlgebraicGeometry.SimplicialScheme.quasicoherentEquivQuasicoherentPair`: the equivalence.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_iff_isCartesianModule_and_zero`: a
  module on the total Zariski site is quasi-coherent if and only if it is cartesian and its
  component in degree zero is quasi-coherent.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X : SimplicialObject Scheme.{u}}

/-- **Quasi-coherence on the total Zariski site through degree zero.** A sheaf of `𝒪_X`-modules
on the total Zariski site of a simplicial scheme is quasi-coherent if and only if it is cartesian
and its component in degree zero is a quasi-coherent `𝒪_{X_0}`-module. -/
theorem isQuasicoherentOnSite_iff_isCartesianModule_and_zero (M : Modules X) :
    M.IsQuasicoherentOnSite ↔
      IsCartesianModule X M ∧ ((componentModule X (op ⦋0⦌)).obj M).IsQuasicoherent := by
  rw [isQuasicoherentOnSite_iff_isCartesianModule_and_components]
  refine ⟨fun h => ⟨h.1, (SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite
    ((componentModule X (op ⦋0⦌)).obj M)).2 (h.2 (op ⦋0⦌))⟩, fun h => ⟨h.1, fun k => ?_⟩⟩
  have h0 := h.2
  have hk : ((Scheme.Modules.pullback (X.map (SimplexCategory.const ⦋0⦌ k.unop 0).op)).obj
      ((componentModule X (op ⦋0⦌)).obj M)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  exact (SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite
    ((componentModule X k).obj M)).1 <| (SheafOfModules.isQuasicoherent _).prop_of_iso
      (@asIso _ _ _ _ (componentModuleTransition X (SimplexCategory.const ⦋0⦌ k.unop 0).op M)
        (h.1 _)) hk

/-- The pairs of the family of modules on the degrees of `X` whose module is quasi-coherent. -/
abbrev QuasicoherentZariskiPair (X : SimplicialObject Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun A : (zariskiModuleFamily X).Pair =>
      (show (X.obj (op ⦋0⦌)).Modules from A.obj).IsQuasicoherent)

/-- The quasi-coherent sheaves of `𝒪_X`-modules on the total Zariski site. -/
abbrev QuasicoherentZariskiModule (X : SimplicialObject Scheme.{u}) :=
  (SheafOfModules.isQuasicoherentOnSite
    (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)).FullSubcategory

variable (X) in
/-- A quasi-coherent module on the total Zariski site is cartesian. -/
noncomputable def quasicoherentToCartesianZariski :
    QuasicoherentZariskiModule X ⥤ CartesianZariskiModule X :=
  ObjectProperty.lift (IsCartesianModule X) (ObjectProperty.ι _)
    (fun M => ((isQuasicoherentOnSite_iff_isCartesianModule_and_zero M.obj).1 M.property).1)

/-- The functor `quasicoherentToCartesianZariski X` is faithful. -/
instance : (quasicoherentToCartesianZariski X).Faithful :=
  have : (quasicoherentToCartesianZariski X ⋙ ObjectProperty.ι (IsCartesianModule X)).Faithful :=
    (inferInstance : (ObjectProperty.ι _).Faithful)
  Functor.Faithful.of_comp _ (ObjectProperty.ι (IsCartesianModule X))

/-- The functor `quasicoherentToCartesianZariski X` is full. -/
instance : (quasicoherentToCartesianZariski X).Full :=
  have : (quasicoherentToCartesianZariski X ⋙ ObjectProperty.ι (IsCartesianModule X)).Full :=
    (inferInstance : (ObjectProperty.ι _).Full)
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι (IsCartesianModule X))

variable (X) in
/-- The functor from quasi-coherent modules on the total Zariski site to pairs with
quasi-coherent module. -/
noncomputable def quasicoherentToPair : QuasicoherentZariskiModule X ⥤ QuasicoherentZariskiPair X :=
  ObjectProperty.lift _ (quasicoherentToCartesianZariski X ⋙ zariskiPairFunctor X)
    (fun M => ((isQuasicoherentOnSite_iff_isCartesianModule_and_zero M.obj).1 M.property).2)

/-- The functor `quasicoherentToPair X` is faithful. -/
instance : (quasicoherentToPair X).Faithful :=
  have : (quasicoherentToPair X ⋙ ObjectProperty.ι _).Faithful :=
    (inferInstance : (quasicoherentToCartesianZariski X ⋙ zariskiPairFunctor X).Faithful)
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- The functor `quasicoherentToPair X` is full. -/
instance : (quasicoherentToPair X).Full :=
  have : (quasicoherentToPair X ⋙ ObjectProperty.ι _).Full :=
    (inferInstance : (quasicoherentToCartesianZariski X ⋙ zariskiPairFunctor X).Full)
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

/-- Every pair with quasi-coherent module is isomorphic to the image under
`quasicoherentToPair X` of a quasi-coherent module on the total Zariski site. -/
instance : (quasicoherentToPair X).EssSurj where
  mem_essImage A := by
    let M := (zariskiPairFunctor X).objPreimage A.obj
    let e : (zariskiPairFunctor X).obj M ≅ A.obj := (zariskiPairFunctor X).objObjPreimageIso A.obj
    have h0 : ((componentModule X (op ⦋0⦌)).obj M.obj).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent _).prop_of_iso
        (SimplicialPseudoFamily.Pair.objIso e.symm) A.property
    exact ⟨⟨M.obj, (isQuasicoherentOnSite_iff_isCartesianModule_and_zero M.obj).2
      ⟨M.property, h0⟩⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

variable (X) in
/-- **The quasi-coherent modules on the total Zariski site of a simplicial scheme are the pairs
`(ℱ, α)` with `ℱ` quasi-coherent** (Stacks 07TH and Stacks 0D7M). -/
noncomputable def quasicoherentEquivQuasicoherentPair :
    QuasicoherentZariskiModule X ≌ QuasicoherentZariskiPair X :=
  have : (quasicoherentToPair X).IsEquivalence := { }
  (quasicoherentToPair X).asEquivalence

end AlgebraicGeometry.SimplicialScheme

end
