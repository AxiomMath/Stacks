module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedSquare
public import StacksFrontier.CategoryTheory.Adjunction.TransportedAdjunction

/-!
# The étale base change map of sheaves of modules, read on the étale ringed topoi

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `Λ` a commutative ring. The étale base
change map `g^{-1} f_* ⟶ f'_* g'^{-1}` of sheaves of `Λ`-modules,
`Stacks.EtaleCohomology.etaleModuleBaseChange`, is the mate of the comparison of the two composite
inverse images around the square. On the étale ringed topoi `(X_étale, Λ̲)` the square commutes up
to the 2-isomorphism `Stacks.EtaleCohomology.etaleRingedToposHomSquareTwoIso`, whose base change
map of sheaves of modules is the mate of
`AlgebraicGeometry.RingedToposHom.TwoIso.squarePullbackIso`. This file compares the two through the
identifications `(etaleModulesEquivalence Λ X).inverse` of sheaves of `Λ̲`-modules with sheaves of
`Λ`-modules.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDirectImageCompIso`: `a_* ⋙ b_* ≅ (a ≫ b)_*`.
* `Stacks.EtaleCohomology.etaleRingedPushforwardComparison`: `f_* ⋙ Ψ_Y ≅ Ψ_X ⋙ f_*`, the identity
  on sections, for `Ψ = (etaleModulesEquivalence Λ _).inverse`.
* `Stacks.EtaleCohomology.etaleRingedPullbackComparison`: `Ψ_Y ⋙ f^{-1} ≅ f^* ⋙ Ψ_X`, the
  comparison of left adjoints it induces.

## Main results

* `Stacks.EtaleCohomology.unit_etaleModuleSquareInverseImageIso`: the comparison of inverse images
  of the étale base change map, characterized by the units.
* `Stacks.EtaleCohomology.unit_etaleRingedPullbackComparison` and
  `Stacks.EtaleCohomology.etaleRingedPullbackComparison_counit`: the compatibility of the pullback
  comparison with units and counits.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

section Composite

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **Direct image along a composite is the composite of the direct images**, for sheaves of
`Λ`-modules on small étale sites. -/
noncomputable def etaleModuleDirectImageCompIso :
    etaleModuleDirectImage.{u, r} Λ a ⋙ etaleModuleDirectImage.{u, r} Λ b ≅
      etaleModuleDirectImage.{u, r} Λ (a ≫ b) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp a b).symm
    (ModuleCat.{max (u + 1) r} Λ) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The composition isomorphism of inverse images is characterized by the units, through the
comparison `(a ≫ b)_* ≅ a_* ⋙ b_*` of direct images. -/
theorem unit_etaleModuleInverseImageCompIso (K : EtaleModules.{u, r} Λ Z) :
    (etaleModuleInverseImageAdj.{u, r} Λ (a ≫ b)).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ (a ≫ b)).map
          ((etaleModuleInverseImageCompIso.{u, r} Λ a b).hom.app K) =
      (etaleModuleInverseImageAdj.{u, r} Λ b).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ b).map
          ((etaleModuleInverseImageAdj.{u, r} Λ a).unit.app
            ((etaleModuleInverseImage.{u, r} Λ b).obj K)) ≫
        (etaleModuleDirectImageCompIso.{u, r} Λ a b).hom.app _ := by
  exact Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, r} Λ (a ≫ b))
    (((etaleModuleInverseImageAdj.{u, r} Λ b).comp
      (etaleModuleInverseImageAdj.{u, r} Λ a)).ofNatIsoRight
      (etaleModuleDirectImageCompIso.{u, r} Λ a b)) K

end Composite

/-- The unit along a morphism equal to another one, read through the identifications of inverse
and direct images that the equality induces. -/
theorem unit_eqToIso_etaleModuleInverseImage {X Y : Scheme.{u}} {c c' : X ⟶ Y} (h : c = c')
    (K : EtaleModules.{u, r} Λ Y) {T : EtaleModules.{u, r} Λ X}
    (x : (etaleModuleInverseImage.{u, r} Λ c).obj K ⟶ T) :
    (etaleModuleInverseImageAdj.{u, r} Λ c').unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ c').map
          ((eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) h)).inv.app K ≫ x) =
      (etaleModuleInverseImageAdj.{u, r} Λ c).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ c).map x ≫
        (eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) h)).app T := by
  subst h
  simp

section Square

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The square comparison of inverse images, characterized by the units**, for named
composites `c` and `c'` and isomorphisms `cL`, `cR` of their inverse images with the iterated
ones characterized by the units against `ζL`, `ζR`. -/
theorem unit_etaleModuleSquareInverseImageIso_aux {c c' : X' ⟶ Y} (h : c = c')
    (cL : etaleModuleInverseImage.{u, r} Λ c' ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleInverseImage.{u, r} Λ f')
    (cR : etaleModuleInverseImage.{u, r} Λ c ≅
      etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g')
    (ζL : etaleModuleDirectImage.{u, r} Λ f' ⋙ etaleModuleDirectImage.{u, r} Λ g ≅
      etaleModuleDirectImage.{u, r} Λ c')
    (ζR : etaleModuleDirectImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f ≅
      etaleModuleDirectImage.{u, r} Λ c)
    (hL : ∀ K, (etaleModuleInverseImageAdj.{u, r} Λ c').unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ c').map (cL.hom.app K) =
      (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleInverseImageAdj.{u, r} Λ f').unit.app
            ((etaleModuleInverseImage.{u, r} Λ g).obj K)) ≫
        ζL.hom.app _)
    (hR : ∀ K, (etaleModuleInverseImageAdj.{u, r} Λ c).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ c).map (cR.hom.app K) =
      (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ f).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app
            ((etaleModuleInverseImage.{u, r} Λ f).obj K)) ≫
        ζR.hom.app _)
    (K : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleInverseImageAdj.{u, r} Λ f').unit.app
            ((etaleModuleInverseImage.{u, r} Λ g).obj K)) ≫
        (etaleModuleDirectImage.{u, r} Λ g).map ((etaleModuleDirectImage.{u, r} Λ f').map
          ((cL.symm ≪≫ (cR.symm ≪≫
            eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) h)).symm).hom.app K)) =
      (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ f).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app
            ((etaleModuleInverseImage.{u, r} Λ f).obj K)) ≫
        ((ζR.hom ≫ eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) h) ≫ ζL.inv).app
          ((etaleModuleInverseImage.{u, r} Λ g').obj
            ((etaleModuleInverseImage.{u, r} Λ f).obj K))) := by
  subst h
  have h1 : (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app K ≫
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleInverseImageAdj.{u, r} Λ f').unit.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj K)) =
      (etaleModuleInverseImageAdj.{u, r} Λ c).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ c).map (cL.hom.app K) ≫ ζL.inv.app _ := by
    rw [reassoc_of% (hL K)]
    simp
  have h2 := ζL.inv.naturality
    ((cL.symm ≪≫ (cR.symm ≪≫ eqToIso (congrArg (fun m ↦ etaleModuleInverseImage.{u, r} Λ m)
      (rfl : c = c))).symm).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h2
  rw [reassoc_of% h1, ← h2, ← Functor.map_comp_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_symm, Iso.symm_symm_eq, eqToIso_refl,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc, eqToHom_refl, Category.id_comp, Iso.refl_inv]
  rw [reassoc_of% (hR K)]

variable (w : g' ≫ f = f' ≫ g)

/-- **The square comparison of inverse images, characterized by the units**: for a commutative
square `g' ≫ f = f' ≫ g`, the comparison `g^{-1} ⋙ f'^{-1} ≅ f^{-1} ⋙ g'^{-1}` of the étale base
change map `Stacks.EtaleCohomology.etaleModuleBaseChange` is the conjugate of the comparison of
direct images `g'_* ⋙ f_* ≅ (g' ≫ f)_* = (f' ≫ g)_* ≅ f'_* ⋙ g_*`. -/
theorem unit_etaleModuleSquareInverseImageIso (K : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleInverseImageAdj.{u, r} Λ f').unit.app
            ((etaleModuleInverseImage.{u, r} Λ g).obj K)) ≫
        (etaleModuleDirectImage.{u, r} Λ g).map ((etaleModuleDirectImage.{u, r} Λ f').map
          (((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
    ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
      eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm).hom.app K)) =
      (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app K ≫
        (etaleModuleDirectImage.{u, r} Λ f).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app
            ((etaleModuleInverseImage.{u, r} Λ f).obj K)) ≫
        (((etaleModuleDirectImageCompIso.{u, r} Λ g' f).hom ≫
          eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) w) ≫
          (etaleModuleDirectImageCompIso.{u, r} Λ f' g).inv).app
          ((etaleModuleInverseImage.{u, r} Λ g').obj
            ((etaleModuleInverseImage.{u, r} Λ f).obj K))) :=
  unit_etaleModuleSquareInverseImageIso_aux Λ f g f' g' w
    (etaleModuleInverseImageCompIso.{u, r} Λ f' g)
    (etaleModuleInverseImageCompIso.{u, r} Λ g' f) (etaleModuleDirectImageCompIso.{u, r} Λ f' g)
    (etaleModuleDirectImageCompIso.{u, r} Λ g' f) (unit_etaleModuleInverseImageCompIso Λ f' g)
    (unit_etaleModuleInverseImageCompIso Λ g' f) K

end Square


section Comparisons

/-- The sheaf of modules over the constant ring sheaf of the étale ringed topos `(X_étale, Λ̲)`,
read as a sheaf of `Λ`-modules: `(etaleModulesEquivalence Λ X).inverse`, with the category of
sheaves of modules of the ringed topos as its source. -/
abbrev etaleRingedForget (X : Scheme.{u}) :
    SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O) ⥤ EtaleModules.{u, r} Λ X :=
  (etaleModulesEquivalence.{u, r} Λ X).inverse

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The direct image of sheaves of `Λ̲`-modules is the étale direct image**, read through the
identifications `Ψ = (etaleModulesEquivalence Λ _).inverse`: `f_* ⋙ Ψ_Y ≅ Ψ_X ⋙ f_*`. It is the
identity on sections. -/
def etaleRingedPushforwardComparison :
    (etaleRingedToposHom.{u, r} Λ f).pushforwardModules ⋙
        etaleRingedForget.{u, r} Λ Y ≅
      etaleRingedForget.{u, r} Λ X ⋙ etaleModuleDirectImage.{u, r} Λ f :=
  Functor.isoWhiskerRight (etaleRingedSiteHom.{u, r} Λ f).pushforwardToposIso _ ≪≫
    etaleRingedPushforwardIso.{u, r} Λ f

/-- **The comparison of pullbacks**, `Ψ_Y ⋙ f^{-1} ≅ f^* ⋙ Ψ_X`: the uniqueness of the left
adjoint of the étale direct image, applied to the étale inverse image and to the pullback of
sheaves of `Λ̲`-modules transported along `Ψ`. -/
def etaleRingedPullbackComparison :
    etaleRingedForget.{u, r} Λ Y ⋙ etaleModuleInverseImage.{u, r} Λ f ≅
      (etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules ⋙
        etaleRingedForget.{u, r} Λ X :=
  Stacks.CategoryTheory.TransportedAdjunction.leftComparison
    (etaleModulesEquivalence.{u, r} Λ Y).symm (etaleModulesEquivalence.{u, r} Λ X).symm
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
    (etaleModuleInverseImageAdj.{u, r} Λ f)
    (Stacks.CategoryTheory.TransportedAdjunction.piOfRightComparison _ _
      (etaleRingedPushforwardComparison.{u, r} Λ f))

/-- The pullback comparison is compatible with the units. -/
theorem unit_etaleRingedPullbackComparison
    (K : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)).O)) :
    (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app ((etaleRingedForget.{u, r} Λ Y).obj K) ≫
        (etaleModuleDirectImage.{u, r} Λ f).map
          ((etaleRingedPullbackComparison.{u, r} Λ f).hom.app K) =
      (etaleRingedForget.{u, r} Λ Y).map
          ((RingedToposHom.pullbackAdjPushforwardModules
            (etaleRingedToposHom.{u, r} Λ f)).unit.app K) ≫
        (etaleRingedPushforwardComparison.{u, r} Λ f).hom.app
          ((etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules.obj K) := by
  have h := Stacks.CategoryTheory.TransportedAdjunction.unit_leftComparison
    (etaleModulesEquivalence.{u, r} Λ Y).symm (etaleModulesEquivalence.{u, r} Λ X).symm
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
    (etaleModuleInverseImageAdj.{u, r} Λ f)
    (Stacks.CategoryTheory.TransportedAdjunction.piOfRightComparison _ _
      (etaleRingedPushforwardComparison.{u, r} Λ f)) K
  rwa [Stacks.CategoryTheory.TransportedAdjunction.rightComparison_piOfRightComparison] at h

/-- The pullback comparison is compatible with the counits. -/
theorem etaleRingedPullbackComparison_counit
    (K : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O)) :
    (etaleModuleInverseImage.{u, r} Λ f).map
      ((etaleRingedPushforwardComparison.{u, r} Λ f).hom.app K) ≫
        (etaleModuleInverseImageAdj.{u, r} Λ f).counit.app ((etaleRingedForget.{u, r} Λ X).obj K) =
      (etaleRingedPullbackComparison.{u, r} Λ f).hom.app
          ((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.obj K) ≫
        (etaleRingedForget.{u, r} Λ X).map
          ((RingedToposHom.pullbackAdjPushforwardModules
            (etaleRingedToposHom.{u, r} Λ f)).counit.app K) := by
  have h := Stacks.CategoryTheory.TransportedAdjunction.leftComparison_counit
    (etaleModulesEquivalence.{u, r} Λ Y).symm (etaleModulesEquivalence.{u, r} Λ X).symm
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
    (etaleModuleInverseImageAdj.{u, r} Λ f)
    (Stacks.CategoryTheory.TransportedAdjunction.piOfRightComparison _ _
      (etaleRingedPushforwardComparison.{u, r} Λ f)) K
  rwa [Stacks.CategoryTheory.TransportedAdjunction.rightComparison_piOfRightComparison] at h

end Comparisons

/-- The identification of the direct images along two equal morphisms is the action of the
identification of the base change functors. -/
theorem eqToHom_etaleModuleDirectImage {X Y : Scheme.{u}} {c c' : X ⟶ Y} (h : c = c') :
    eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) h) =
      (Functor.sheafPushforwardContinuousIso
        (eqToIso (congrArg (fun m => smallEtaleBaseChange m) h))
        (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology).hom := by
  subst h
  ext N V x
  simp [Functor.sheafPushforwardContinuousNatTrans]
  rfl

/-- The identification of the base change functors along two equal morphisms, on the small models,
is the one on the small étale sites. -/
theorem eqToHom_etaleSmallModelBaseChange_app {X Y : Scheme.{u}} {c c' : X ⟶ Y} (h : c = c')
    (V : AsSmall.{max (u + 1) r} Y.Etale) :
    (eqToHom (congrArg (fun m => etaleSmallModelBaseChange.{u, r} m) h)).app V =
      AsSmall.up.map
        ((eqToHom (congrArg (fun m => smallEtaleBaseChange m) h)).app (AsSmall.down.obj V)) := by
  subst h
  simp
  rfl

/-- A form of `eqToHom_etaleSmallModelBaseChange_app` for the identification in the other
direction, at an object of the small étale site. -/
theorem eqToIso_etaleSmallModelBaseChange_symm_hom_app {X Y : Scheme.{u}} {c c' : X ⟶ Y}
    (h : c = c')
    (V : Y.Etale) :
    (eqToIso (congrArg (fun m => etaleSmallModelBaseChange.{u, r} m) h.symm)).hom.app
        ((AsSmall.up : Y.Etale ⥤ AsSmall.{max (u + 1) r} Y.Etale).obj V) =
      AsSmall.up.map ((eqToIso (congrArg (fun m => smallEtaleBaseChange m) h)).inv.app V) := by
  subst h
  simp
  rfl


section RingedSquare

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **The two comparisons of composite direct images around the square agree**, through the
pushforward comparisons: for any comparison `ρ` of the composite direct images of sheaves of
`Λ̲`-modules which is the inverse of the 2-isomorphism of the square on underlying sheaves of sets,
`Ψ` carries `ρ` to the comparison of composite étale direct images. -/
theorem etaleRingedPushforwardSquare_comparison
    (ρ : (etaleRingedToposHom.{u, r} Λ g').pushforwardModules ⋙
        (etaleRingedToposHom.{u, r} Λ f).pushforwardModules ⟶
      (etaleRingedToposHom.{u, r} Λ f').pushforwardModules ⋙
        (etaleRingedToposHom.{u, r} Λ g).pushforwardModules)
    (hρ : ∀ (M : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')).O)),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y)).O)).map
          (ρ.app M) =
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w).e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X')).O)).obj M))
    (M : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')).O)) :
    (etaleRingedPushforwardComparison.{u, r} Λ f).hom.app
        ((etaleRingedToposHom.{u, r} Λ g').pushforwardModules.obj M) ≫
      (etaleModuleDirectImage.{u, r} Λ f).map
        ((etaleRingedPushforwardComparison.{u, r} Λ g').hom.app M) ≫
      ((etaleModuleDirectImageCompIso.{u, r} Λ g' f).hom ≫
          eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) w) ≫
          (etaleModuleDirectImageCompIso.{u, r} Λ f' g).inv).app
        ((etaleRingedForget.{u, r} Λ X').obj M) =
    (etaleRingedForget.{u, r} Λ Y).map (ρ.app M) ≫
      (etaleRingedPushforwardComparison.{u, r} Λ g).hom.app
        ((etaleRingedToposHom.{u, r} Λ f').pushforwardModules.obj M) ≫
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleRingedPushforwardComparison.{u, r} Λ f').hom.app M) := by
  rw [eqToHom_etaleModuleDirectImage Λ w]
  apply Sheaf.hom_ext
  ext V x
  have h1 := congrArg
    (fun φ ↦ φ.hom.app
      (Opposite.op ((AsSmall.up : Y.Etale ⥤ AsSmall.{max (u + 1) r} Y.Etale).obj V.unop)) x)
    (hρ M)
  dsimp only at h1
  refine Eq.trans ?_ h1.symm
  change (((etaleRingedForget.{u, r} Λ X').obj M).obj.map
      ((smallEtaleBaseChangeComp f' g).inv.app V.unop).op).hom
    ((((etaleRingedForget.{u, r} Λ X').obj M).obj.map
      ((eqToIso (congrArg (fun m => smallEtaleBaseChange m) w)).inv.app V.unop).op).hom
      ((((etaleRingedForget.{u, r} Λ X').obj M).obj.map
        ((smallEtaleBaseChangeComp g' f).hom.app V.unop).op).hom x)) =
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X')).O)).obj M).obj.map
        ((etaleSmallModelBaseChangeCompIso.{u, r} f' g).hom.app
          ((AsSmall.up : Y.Etale ⥤ AsSmall.{max (u + 1) r} Y.Etale).obj V.unop)).op
      (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X')).O)).obj M).obj.map
        ((eqToIso (congrArg (fun m => etaleSmallModelBaseChange.{u, r} m) w.symm)).hom.app
          ((AsSmall.up : Y.Etale ⥤ AsSmall.{max (u + 1) r} Y.Etale).obj V.unop)).op
        (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X')).O)).obj M).obj.map
          ((etaleSmallModelBaseChangeCompIso.{u, r} g' f).inv.app
            ((AsSmall.up : Y.Etale ⥤ AsSmall.{max (u + 1) r} Y.Etale).obj V.unop)).op x))
  rw [eqToIso_etaleSmallModelBaseChange_symm_hom_app.{u, r} w V.unop]
  rfl


/-- **The two square comparisons of pullbacks agree**, through the pullback comparisons: `Ψ`
carries a comparison `SR` of the two composite pullbacks of sheaves of `Λ̲`-modules around the
2-commutative square of étale ringed topoi to the comparison of composite étale inverse images of
`Stacks.EtaleCohomology.etaleModuleBaseChange`, as soon as `SR` is characterized through the units
by a comparison `ρ` of composite direct images (`hunit`) which is the inverse of the 2-isomorphism
of the square on sections (`hρ`). -/
theorem etaleRingedSquarePullbackIso_comparison
    (SR : (etaleRingedToposHom.{u, r} Λ g).toModulesHom.pullbackModules ⋙
        (etaleRingedToposHom.{u, r} Λ f').toModulesHom.pullbackModules ≅
      (etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules ⋙
        (etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules)
    (ρ : (etaleRingedToposHom.{u, r} Λ g').pushforwardModules ⋙
        (etaleRingedToposHom.{u, r} Λ f).pushforwardModules ⟶
      (etaleRingedToposHom.{u, r} Λ f').pushforwardModules ⋙
        (etaleRingedToposHom.{u, r} Λ g).pushforwardModules)
    (hunit : ∀ K, (RingedToposHom.pullbackAdjPushforwardModules
          (etaleRingedToposHom.{u, r} Λ g)).unit.app K ≫
        (etaleRingedToposHom.{u, r} Λ g).pushforwardModules.map
          ((RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f')).unit.app
            ((etaleRingedToposHom.{u, r} Λ g).toModulesHom.pullbackModules.obj K)) ≫
        (etaleRingedToposHom.{u, r} Λ g).pushforwardModules.map
          ((etaleRingedToposHom.{u, r} Λ f').pushforwardModules.map
            (SR.hom.app K)) =
      (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f)).unit.app K ≫
        (etaleRingedToposHom.{u, r} Λ f).pushforwardModules.map
          ((RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ g')).unit.app
            ((etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules.obj K)) ≫
        ρ.app ((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.obj
          ((etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules.obj K)))
    (hρ : ∀ (M : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X')).O)),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y)).O)).map (ρ.app M) =
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w).e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X')).O)).obj M))
    (K : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)).O)) :
    ((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm).hom.app
        ((etaleRingedForget.{u, r} Λ Y).obj K) ≫
      (etaleModuleInverseImage.{u, r} Λ g').map
        ((etaleRingedPullbackComparison.{u, r} Λ f).hom.app K) ≫
      (etaleRingedPullbackComparison.{u, r} Λ g').hom.app
        ((etaleRingedToposHom.{u, r} Λ f).toModulesHom.pullbackModules.obj K) =
    (etaleModuleInverseImage.{u, r} Λ f').map
        ((etaleRingedPullbackComparison.{u, r} Λ g).hom.app K) ≫
      (etaleRingedPullbackComparison.{u, r} Λ f').hom.app
        ((etaleRingedToposHom.{u, r} Λ g).toModulesHom.pullbackModules.obj K) ≫
      (etaleRingedForget.{u, r} Λ X').map
        (SR.hom.app K) := by
  exact Stacks.CategoryTheory.TransportedAdjunction.square_transport
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ g))
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ g'))
    (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleModuleInverseImageAdj.{u, r} Λ f') (etaleModuleInverseImageAdj.{u, r} Λ g')
    (etaleRingedPushforwardComparison.{u, r} Λ f).hom
    (etaleRingedPushforwardComparison.{u, r} Λ g).hom
    (etaleRingedPushforwardComparison.{u, r} Λ f').hom
    (etaleRingedPushforwardComparison.{u, r} Λ g').hom
    (etaleRingedPullbackComparison.{u, r} Λ f).hom (etaleRingedPullbackComparison.{u, r} Λ g).hom
    (etaleRingedPullbackComparison.{u, r} Λ f').hom (etaleRingedPullbackComparison.{u, r} Λ g').hom
    SR ρ
    ((etaleModuleInverseImageCompIso.{u, r} Λ f' g).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ g' f).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w)).symm)
    ((etaleModuleDirectImageCompIso.{u, r} Λ g' f).hom ≫
      eqToHom (congrArg (fun m => etaleModuleDirectImage.{u, r} Λ m) w) ≫
      (etaleModuleDirectImageCompIso.{u, r} Λ f' g).inv)
    (unit_etaleRingedPullbackComparison.{u, r} Λ f) (unit_etaleRingedPullbackComparison.{u, r} Λ g)
    (unit_etaleRingedPullbackComparison.{u, r} Λ f')
    (unit_etaleRingedPullbackComparison.{u, r} Λ g')
    (fun K ↦ by exact hunit K)
    (fun K ↦ by exact unit_etaleModuleSquareInverseImageIso.{u, r} Λ f g f' g' w K)
    (fun M ↦ by exact etaleRingedPushforwardSquare_comparison.{u, r} Λ f g f' g' w ρ hρ M) K

end RingedSquare

end Stacks.EtaleCohomology
