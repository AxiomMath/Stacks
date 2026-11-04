module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase

/-!
# The Zariski reading inverts Stacks 03DX (2) on a represented algebraic space

For an object `T` of the big fppf site, Stacks 03DX (2) at `τ = étale` identifies quasi-coherent
modules on the scheme of `T` with quasi-coherent `𝒪`-modules on the small étale site of the
representable algebraic space `yoneda.obj T`
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`).  The Zariski reading
`AlgebraicGeometry.Space.zariskiReading` — the direct image along the inclusion of the Zariski
opens of the scheme of `T` among the étale charts of `yoneda.obj T` — is right adjoint to its
functor (`AlgebraicGeometry.Space.zariskiReadingAdjunction`), and the counit is invertible on
quasi-coherent `𝒪`-modules. Hence **a quasi-coherent `𝒪`-module on `yoneda.obj T` is the module
attached by Stacks 03DX (2) to its Zariski reading**, naturally.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingQcoh`: the Zariski reading of a quasi-coherent
  `𝒪`-module on `yoneda.obj T`, as a quasi-coherent module on the scheme of `T`.
* `AlgebraicGeometry.Space.zariskiReadingQcohMap`: the Zariski reading of a morphism.
* `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`: **`N ≅ (N_Zar)^a`**, the inverse of
  the counit of the Zariski reading adjunction.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso_hom_naturality`: the identification is
  natural in `N`.
* `AlgebraicGeometry.Space.representedZariski_map_zariskiReadingQuasicoherentIso_hom`: its reading
  on the scheme, through the base identification of Stacks 03DX (2), is the identification of the
  two Zariski readings.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The Zariski reading of a quasi-coherent `𝒪`-module on a represented algebraic space**, as a
quasi-coherent module on the scheme of the representing object: the direct image along the
inclusion of the Zariski opens among the étale charts. -/
abbrev zariskiReadingQcoh (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory :=
  ⟨(SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N,
    isQuasicoherent_zariskiReading_piece T N hN⟩

/-- The Zariski reading of a morphism of quasi-coherent `𝒪`-modules on a represented algebraic
space, as a morphism of quasi-coherent modules on the scheme. -/
abbrev zariskiReadingQcohMap (T : BigFppfOver B S hS)
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite) (g : N ⟶ N') :
    zariskiReadingQcoh T N hN ⟶ zariskiReadingQcoh T N' hN' :=
  ObjectProperty.homMk ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map g)

/-- **A quasi-coherent `𝒪`-module on a represented algebraic space is the module attached by
Stacks 03DX (2) to its Zariski reading.**  For an object `T` of the site and a quasi-coherent
`𝒪`-module `N` on the small étale site of `yoneda.obj T`, `N ≅ (N_Zar)^a`, where `N_Zar` is the
Zariski reading (`AlgebraicGeometry.Space.zariskiReadingQcoh`) and `(-)^a` is the functor of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`: the inverse of the counit of
the Zariski reading adjunction, invertible on quasi-coherent modules. -/
def zariskiReadingQuasicoherentIso (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    N ≅ ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
      (zariskiReadingQcoh T N hN)).obj :=
  haveI := isIso_zariskiReadingAdjunction_counit_app T N hN
  (asIso ((zariskiReadingAdjunction T).counit.app N)).symm

/-- The inverse of the identification is the counit of the Zariski reading adjunction. -/
theorem zariskiReadingQuasicoherentIso_inv (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (zariskiReadingQuasicoherentIso T N hN).inv = (zariskiReadingAdjunction T).counit.app N :=
  rfl

/-- **The identification `N ≅ (N_Zar)^a` is natural in `N`.** -/
theorem zariskiReadingQuasicoherentIso_hom_naturality (T : BigFppfOver B S hS)
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite) (g : N ⟶ N') :
    (zariskiReadingQuasicoherentIso T N hN).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (zariskiReadingQcohMap T hN hN' g)).hom =
      g ≫ (zariskiReadingQuasicoherentIso T N' hN').hom :=
  (Iso.eq_inv_comp (zariskiReadingQuasicoherentIso T N hN)).1
    (((Iso.comp_inv_eq (zariskiReadingQuasicoherentIso T N' hN')).1
      ((zariskiReadingAdjunction T).counit.naturality g)).trans (Category.assoc _ _ _))

/-- The abstract shape of
`AlgebraicGeometry.Space.representedZariski_map_zariskiReadingQuasicoherentIso_hom`: the right
triangle identity of an adjunction transported along an isomorphism `ι` of right adjoints. -/
private theorem comp_eq_hom_of_triangle {C : Type*} [Category C] {a b c d : C} (ι : a ≅ b)
    (ηc : b ⟶ c) (r : c ⟶ b) (hr : r ≫ ηc = 𝟙 c) (Fε : c ⟶ a) (ιd : c ⟶ d) (ηz : b ⟶ d)
    (hη : ηz = ηc ≫ ιd) (Rε : d ⟶ b) (tri : ηz ≫ Rε = 𝟙 b) (nat : ιd ≫ Rε = Fε ≫ ι.hom)
    (Fβ : a ⟶ c) (hβ : Fβ ≫ Fε = 𝟙 a) : Fβ ≫ r = ι.hom := by
  have h1 : ηc ≫ Fε = ι.inv :=
    (Iso.comp_hom_eq_id ι).1 (by rw [Category.assoc, ← nat, ← Category.assoc, ← hη]; exact tri)
  have h2 : Fε = r ≫ ι.inv := by
    rw [← h1, ← Category.assoc, hr, Category.id_comp]
  exact (Iso.comp_inv_eq_id ι).1 (by rw [Category.assoc, ← h2]; exact hβ)

/-- The unit of the Zariski reading adjunction is the unit of the composite of the adjunction of
Stacks 03DU with the equivalence of the small étale sites, followed by the identification of the
two Zariski readings. -/
theorem zariskiReadingAdjunction_unit_app (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (zariskiReadingAdjunction T).unit.app
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) =
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp
        (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction).unit.app
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) ≫
        (zariskiReadingIso T).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
              ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N))) := by
  simp only [zariskiReadingAdjunction, Adjunction.ofNatIsoRight]
  rfl

/-- The base identification of Stacks 03DX (2) at the Zariski reading is inverse to the unit of the
composite adjunction. -/
private theorem representedZariskiModuleQuasicoherentSchemeIso_hom_comp_unit
    (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (representedZariskiModuleQuasicoherentSchemeIso B S hS T (zariskiReadingQcoh T N hN)).hom ≫
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp
        (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction).unit.app
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) = 𝟙 _ :=
  (representedZariskiModuleQuasicoherentSchemeIso B S hS T (zariskiReadingQcoh T N hN)).hom_inv_id

/-- **The reading on the scheme of the identification `N ≅ (N_Zar)^a` is the identification of the
two Zariski readings.**  Read on the scheme of `T` through
`AlgebraicGeometry.Space.representedZariskiModule` (the equivalence of the small étale sites
followed by restriction to the Zariski site), the identification
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`, followed by the base identification
`AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso` of Stacks 03DX (2), is the
identification `AlgebraicGeometry.Space.zariskiReadingIso` (componentwise
`AlgebraicGeometry.Space.selfOpensPushforwardIso`) of the restriction with the direct image along
the Zariski opens.  It is the triangle identity of the Zariski reading adjunction. -/
theorem representedZariski_map_zariskiReadingQuasicoherentIso_hom (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map
          (zariskiReadingQuasicoherentIso T N hN).hom) ≫
      (representedZariskiModuleQuasicoherentSchemeIso B S hS T
        (zariskiReadingQcoh T N hN)).hom =
    ((zariskiReadingIso T).app N).hom := by
  let E := representedSmallEtaleModuleEquivalence B S hS T
  let rM := _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let aM := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let R := SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)
  let ε := (zariskiReadingAdjunction T).counit.app N
  have nat : (zariskiReadingIso T).hom.app (E.functor.obj (aM.obj (R.obj N))) ≫ R.map ε =
      rM.map (E.inverse.map ε) ≫ ((zariskiReadingIso T).app N).hom :=
    ((zariskiReadingIso T).hom.naturality ε).symm
  have hβ : rM.map (E.inverse.map (zariskiReadingQuasicoherentIso T N hN).hom) ≫
      rM.map (E.inverse.map ε) = 𝟙 _ :=
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans (congrArg (E.inverse ⋙ rM).map
      (zariskiReadingQuasicoherentIso T N hN).hom_inv_id)).trans
        (CategoryTheory.Functor.map_id _ _)
  exact comp_eq_hom_of_triangle (a := rM.obj (E.inverse.obj N)) (b := R.obj N)
    (c := rM.obj (E.inverse.obj (E.functor.obj (aM.obj (R.obj N)))))
    (d := R.obj (E.functor.obj (aM.obj (R.obj N))))
    ((zariskiReadingIso T).app N)
    (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp E.toAdjunction).unit.app
        (R.obj N))
    _ (representedZariskiModuleQuasicoherentSchemeIso_hom_comp_unit T N hN)
    (rM.map (E.inverse.map ε))
    ((zariskiReadingIso T).hom.app (E.functor.obj (aM.obj (R.obj N))))
    ((zariskiReadingAdjunction T).unit.app (R.obj N))
    (zariskiReadingAdjunction_unit_app T N) (R.map ε)
    ((zariskiReadingAdjunction T).right_triangle_components N) nat _ hβ

end AlgebraicGeometry.Space

end
