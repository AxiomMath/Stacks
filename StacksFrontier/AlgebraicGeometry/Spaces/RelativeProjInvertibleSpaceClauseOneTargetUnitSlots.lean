module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetUnit

/-!
# The slots `hcomp` and `hsite` of the target square of clause (1) of Stacks 0D2Z at `r = 𝟙`

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) meets the section `c` of the
fibre `q : W ×_Y P ⟶ W`, with `c ≫ q = 𝟙`.  At `r = 𝟙` its hypotheses `hcomp` and `hsite` are
the identification `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) along a section
(`modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp_canHom`) and the unit law
of Stacks 03LU carried along an isomorphism.  Both are stated here at variables, in the shape of
the hypotheses, with `Φ = modulePullback` and `κ = modulePullbackCompIso`, the unit law `ρ_r` the
component of `AlgebraicGeometry.Space.modulePullbackIdIso` and `Fc = 𝟙`.

## Main results

* `AlgebraicGeometry.Space.compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom`:
  the hypothesis `hcomp` at `r = 𝟙`.
* `AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id`: the hypothesis
  `hsite` at `r = 𝟙`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The hypothesis `hcomp` of the target square at `r = 𝟙`**: for a section `c` of `q`
(`c ≫ q = 𝟙`) and a quasi-coherent module `Z` on the scheme of `W`, the comparison
`c^*q^*Z^a ≅ (c ≫ q)^*Z^a` of Stacks 03LU, the transport along `c ≫ q = 𝟙` and the unit law
`(𝟙)^* ≅ 𝟭` are the inverse image along `c` of the identification of Stacks 03DX (2) along `q`,
the identification along `c`, and the module attached to the canonical identification
`c^*q^*Z ≅ (c ≫ q)^*Z = (𝟙)^*Z ≅ Z`:
`modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp_canHom` read from right to
left, with the unit law the underlying morphism of a component. -/
theorem compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom
    {W F : BigFppfOver B S hS} (c : W ⟶ F) (q : F ⟶ W) (hcq : c ≫ q = 𝟙 W)
    (hcq' : (BigFppfOver.toScheme B S hS).map c ≫ (BigFppfOver.toScheme B S hS).map q =
      𝟙 ((BigFppfOver.toScheme B S hS).obj W))
    (hs : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS c)
      (representedSpaceMap B S hS q) =
        𝟙 (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
    (Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS c)
        (representedSpaceMap B S hS q)).hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj ≫
      pullbackTransport _ hs ≫
      ((modulePullbackIdIso B S hS
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)).app
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj).hom =
    (modulePullback B S hS (representedSpaceMap B S hS c)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS q Z).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c
        (quasicoherentPullbackObj B S hS q Z)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
        (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
            ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map q)
            (𝟙 _) hcq' Z.obj ≫ (Scheme.Modules.pullbackId _).hom.app Z.obj) :
          quasicoherentPullbackObj B S hS c (quasicoherentPullbackObj B S hS q Z) ⟶ Z)).hom :=
  (congrArg (fun t => (modulePullbackCompIso B S hS (representedSpaceMap B S hS c)
        (representedSpaceMap B S hS q)).hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj ≫
      pullbackTransport _ hs ≫ t) (Iso.app_hom _ _)).trans
    (modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp_canHom c q hcq hcq' hs
      Z).symm

/-- **The hypothesis `hsite` of the target square at `r = 𝟙`**: the inverse image along `𝟙` of an
isomorphism `ζ : v^*M ≅ Z`, followed by the unit law `(𝟙)^*Z ≅ Z` and `Fc = 𝟙`, is the comparison
`(𝟙)^*v^*M ≅ (𝟙 ≫ v)^*M` of Stacks 03LU, the transport along `𝟙 ≫ v = v`, and `ζ`. -/
theorem modulePullback_map_comp_idIso_app_hom_comp_id {T Y : AlgebraicSpaces B S hS}
    (v : T ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) {Z : Modules.{u, u} B S hS T.1 T.2}
    (ζ : (modulePullback B S hS v).obj M ≅ Z) :
    (modulePullback B S hS (𝟙 T)).map ζ.hom ≫ ((modulePullbackIdIso B S hS T).app Z).hom ≫
        𝟙 Z =
      ((modulePullbackCompIso B S hS (𝟙 T) v).hom.app M ≫
        pullbackTransport M (Category.id_comp v)) ≫ ζ.hom := by
  have hU := modulePullbackCompIso_hom_app_comp_pullbackTransport_of_eq_id (rfl : 𝟙 T = 𝟙 T) v
    (Category.id_comp v) M
  have h1 : pullbackTransport ((modulePullback B S hS v).obj M) (rfl : 𝟙 T = 𝟙 T) = 𝟙 _ := rfl
  have hU' := hU.trans ((congrArg (· ≫ _) h1).trans (Category.id_comp _))
  have h2 := (modulePullbackIdIso B S hS T).hom.naturality ζ.hom
  exact ((congrArg (_ ≫ ·) (Category.comp_id _)).trans h2).trans
    (congrArg (· ≫ ζ.hom) hU'.symm)

/-- `AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id` with the transport
along `𝟙 ≫ v = v` written as `eqToHom`, the spelling of the hypothesis `hτv`. -/
theorem modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom {T Y : AlgebraicSpaces B S hS}
    (v : T ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) {Z : Modules.{u, u} B S hS T.1 T.2}
    (ζ : (modulePullback B S hS v).obj M ≅ Z) :
    (modulePullback B S hS (𝟙 T)).map ζ.hom ≫ ((modulePullbackIdIso B S hS T).app Z).hom ≫
        𝟙 Z =
      ((modulePullbackCompIso B S hS (𝟙 T) v).hom.app M ≫
        eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M) (Category.id_comp v))) ≫
        ζ.hom :=
  modulePullback_map_comp_idIso_app_hom_comp_id v M ζ

end AlgebraicGeometry.Space

end
