module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The canonical map of differentials along an étale square is an isomorphism

Let `a ≫ f = ψ ≫ b` be a commutative square of algebraic spaces over `S` with `a : U ⟶ X` and
`b : V ⟶ Y` étale.  The canonical map `c_a : a^*Ω_{X/Y} ⟶ Ω_{U/V}` of
[Stacks Project, Tag 04CX] is the identification of [Stacks Project, Tag 04CU]
(`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`), hence an isomorphism
(`AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isEtale`).

## Main results

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`: the étale-source
  comparison `a^*Ω_{X/Y} ⟶ Ω_{U/Y}` is the canonical map of the square with bottom edge `𝟙 Y`.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_of_universalDerivationHom`: the
  characterizing property of the canonical map survives postcomposition with a map of
  differentials carrying one universal derivation to the other.
* `AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isEtale`: the canonical map of an
  étale square is an isomorphism.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (derivationSheafHom derivationSheafHom_postcomp)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section EtaleSource

variable {U X Y : AlgebraicSpaces B S hS}

/-- The structure map `a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` of the clause `a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV, on
underlying sheaves of sets, in the two spellings of the forgetful functor. -/
theorem commRingSetHom_etaleInverseImageStructureSheafIso_hom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) :
    Stacks.Sheaves.RingedToposModules.commRingSetHom
        (etaleInverseImageStructureSheafIso B S hS a ha).hom =
      structureSharpInverseImageSet B S hS a :=
  CategoryTheory.Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The universal derivation of `𝒪_U` as a derivation of the étale ringed topos, pushed forward
along `a`, is the direct image of `d_{U/Y}`. -/
theorem pushforward_map_derivationSheafHom_universalDerivation (a : U ⟶ X) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.map
        (derivationSheafHom (structureSharpInverseImage B S hS (a ≫ f))
          (sheafOfDifferentials B S hS (a ≫ f)) (universalDerivation B S hS (a ≫ f))) =
      (smallEtaleDirectImage B S hS a).map (universalDerivationHom B S hS (a ≫ f)) :=
  rfl

/-- The universal derivation of `𝒪_U` read back along the ring data of the étale-source
comparison is, on underlying sheaves of sets, `a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` followed by `d_{U/Y}`. -/
theorem derivationSheafHom_etaleSourceRingDataEquiv_symm (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom
        ((smallEtaleRingedToposHom B S hS a).toToposHom.inverseImageRing.map
          (structureSharpInverseImage B S hS f))
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        ((etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
          (universalDerivation B S hS (a ≫ f))) =
      Stacks.Sheaves.RingedToposModules.commRingSetHom
            (etaleInverseImageStructureSheafIso B S hS a ha).hom ≫
          derivationSheafHom (structureSharpInverseImage B S hS (a ≫ f))
            (sheafOfDifferentials B S hS (a ≫ f)) (universalDerivation B S hS (a ≫ f)) :=
  CategoryTheory.Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The transpose of `a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` followed by `d_{U/Y}` is `a♯ : 𝒪_X ⟶ a_*𝒪_U`
followed by the direct image of `d_{U/Y}`. -/
theorem homEquiv_commRingSetHom_comp_derivationSheafHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (Stacks.Sheaves.RingedToposModules.commRingSetHom
            (etaleInverseImageStructureSheafIso B S hS a ha).hom ≫
          derivationSheafHom (structureSharpInverseImage B S hS (a ≫ f))
            (sheafOfDifferentials B S hS (a ≫ f)) (universalDerivation B S hS (a ≫ f))) =
      structureSharpSet B S hS a ≫
        (smallEtaleDirectImage B S hS a).map (universalDerivationHom B S hS (a ≫ f)) :=
  ((smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv_naturality_right _ _).trans
    (congrArg₂ (· ≫ ·)
      ((congrArg ((smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _)
        (commRingSetHom_etaleInverseImageStructureSheafIso_hom B S hS a ha)).trans
        (homEquiv_structureSharpInverseImageSet B S hS a))
      (pushforward_map_derivationSheafHom_universalDerivation B S hS a f))

/-- The transpose of the universal derivation of `𝒪_U` read back along the ring data of the
étale-source comparison is `a♯ : 𝒪_X ⟶ a_*𝒪_U` followed by the direct image of `d_{U/Y}`. -/
theorem homEquiv_derivationSheafHom_etaleSourceRingDataEquiv_symm (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (derivationSheafHom
        ((smallEtaleRingedToposHom B S hS a).toToposHom.inverseImageRing.map
          (structureSharpInverseImage B S hS f))
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        ((etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
          (universalDerivation B S hS (a ≫ f)))) =
      structureSharpSet B S hS a ≫
        (smallEtaleDirectImage B S hS a).map (universalDerivationHom B S hS (a ≫ f)) :=
  (congrArg ((smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _)
    (derivationSheafHom_etaleSourceRingDataEquiv_symm B S hS a ha f)).trans
    (homEquiv_commRingSetHom_comp_derivationSheafHom B S hS a ha f)

/-- The derivation of `𝒪_X` with values in `a_*Ω_{U/Y}` attached to the étale-source comparison
is the transpose, along the morphism of small étale topoi of `a`, of the universal derivation
`d_{U/Y}` read back along the ring data. -/
theorem etaleSourceAdjEquiv_derivation_eq (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    differentialsHomEquiv B S hS f
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
          (etaleSourceLocalizationHom B S hS a ha f)) =
      Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv
        (smallEtaleRingedToposHom B S hS a).toToposHom (structureSharpInverseImage B S hS f)
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        ((etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
          (universalDerivation B S hS (a ≫ f))) :=
  (Equiv.symm_apply_eq _).1 ((Equiv.eq_symm_apply _).2
    (derivationEtalePullbackEquiv_etaleSourceLocalizationHom B S hS a ha f))

/-- The derivation attached to the étale-source comparison is the transpose of the universal
derivation `d_{U/Y}` read back along the ring data. -/
theorem derivationSheafHom_etaleSourceAdjEquiv_eq_homEquiv (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom (structureSharpInverseImage B S hS f)
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (differentialsHomEquiv B S hS f
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
            (etaleSourceLocalizationHom B S hS a ha f))) =
      (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (derivationSheafHom
          ((smallEtaleRingedToposHom B S hS a).toToposHom.inverseImageRing.map
            (structureSharpInverseImage B S hS f))
          ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          ((etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
            (universalDerivation B S hS (a ≫ f)))) :=
  congrArg (derivationSheafHom (structureSharpInverseImage B S hS f)
      ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f))))
    (etaleSourceAdjEquiv_derivation_eq B S hS a ha f)

/-- **The étale-source comparison of [Stacks Project, Tag 04CU] is the canonical map of
[Stacks Project, Tag 04CX]** of the square with top edge `a` and bottom edge `𝟙 Y`: its adjoint
transpose carries `d_{X/Y}(t)` to `d_{U/Y}(a♯ t)`. -/
theorem isSheafOfDifferentialsMap_etaleSourceLocalizationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    IsSheafOfDifferentialsMap B S hS a f (a ≫ f) (etaleSourceLocalizationHom B S hS a ha f) := by
  intro V t
  have hA : (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS f)
      (sheafOfDifferentials B S hS (a ≫ f)) (etaleSourceLocalizationHom B S hS a ha f) =
      etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
          (etaleSourceLocalizationHom B S hS a ha f) ≫
        (modulePushforwardIso B S hS a).hom.app (sheafOfDifferentials B S hS (a ≫ f)) :=
    Adjunction.homEquiv_ofNatIsoRight_apply _ _ _
  have h1 := congrArg (fun m ↦ (m.val.app V).hom ((universalDerivation B S hS f).d t)) hA
  have h2 := modulePushforwardIso_hom_app_val_app B S hS a (sheafOfDifferentials B S hS (a ≫ f)) V
    ((etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
      (etaleSourceLocalizationHom B S hS a ha f)).val.app V ((universalDerivation B S hS f).d t))
  have h4 := congrArg (fun m ↦ m.hom.app V t)
    (derivationSheafHom_etaleSourceAdjEquiv_eq_homEquiv B S hS a ha f)
  have h5 := congrArg (fun m ↦ m.hom.app V t)
    (homEquiv_derivationSheafHom_etaleSourceRingDataEquiv_symm B S hS a ha f)
  exact h1.trans (h2.trans (h4.trans h5))

end EtaleSource

section Postcomposition

variable {X Y X' Y' Y'' : AlgebraicSpaces B S hS}

/-- **The characterizing property of [Stacks Project, Tag 04CX] under postcomposition.**  If
`c : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` has the characterizing property and `g : Ω_{X'/Y'} ⟶ Ω_{X'/Y''}`
carries the universal derivation `d_{X'/Y'}` to `d_{X'/Y''}`, then `c ≫ g` has the
characterizing property for `X' ⟶ Y''`. -/
theorem isSheafOfDifferentialsMap_comp_of_universalDerivationHom (f : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X' ⟶ Y'')
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS f p p' c)
    (g : sheafOfDifferentials B S hS p' ⟶ sheafOfDifferentials B S hS p'')
    (hg : universalDerivationHom B S hS p' ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map g =
      universalDerivationHom B S hS p'') :
    IsSheafOfDifferentialsMap B S hS f p p'' (c ≫ g) := by
  have key : universalDerivationHom B S hS p ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p'') (c ≫ g)) =
      structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p'') := by
    refine (congrArg (fun m ↦ universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map m)
      (Adjunction.homEquiv_naturality_right _ c g)).trans ?_
    refine (congrArg (fun m ↦ universalDerivationHom B S hS p ≫ m)
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m ↦ m ≫ (smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map g))
      (universalDerivationHom_comp_homEquiv B S hS f p p' hc)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun m ↦ structureSharpSet B S hS f ≫ m) ?_
    exact ((smallEtaleDirectImage B S hS f).map_comp _ _).symm.trans
      (congrArg (smallEtaleDirectImage B S hS f).map hg)
  exact fun V t ↦ Sheaf.sections_congr key V t

/-- The backward comparison of the étale-base step of [Stacks Project, Tag 04CU] carries the
universal derivation `d_{X/Z}` to `d_{X/Y}`, on underlying sheaves of sets. -/
theorem universalDerivationHom_comp_sharpIsoInv (p : X ⟶ Y) (q : X ⟶ Y')
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p = structureSharpInverseImage B S hS q) :
    universalDerivationHom B S hS q ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (sharpIsoInv B S hS p q e he) =
      universalDerivationHom B S hS p :=
  CategoryTheory.Sheaf.hom_ext_sections fun _ x ↦
    PresheafOfModules.Derivation.congr_d (postcomp_sharpIsoInv B S hS p q e he) x

end Postcomposition

section EtaleSquare

variable {U V X Y : AlgebraicSpaces B S hS}

/-- **The étale-base step of [Stacks Project, Tag 04CU], at any spelling of the composite.**  For
an étale `b : V ⟶ Y` and any `g : U ⟶ Y` equal to `ψ ≫ b`, there is an isomorphism
`Ω_{U/Y} ⟶ Ω_{U/V}` (along `g`) carrying the universal derivation `d_{U/Y}` to `d_{U/V}`. -/
theorem exists_isIso_universalDerivationHom_comp_eq (ψ : U ⟶ V) (b : V ⟶ Y)
    (hb : IsEtale B S hS b.hom) (g : U ⟶ Y) (hg : g = ψ ≫ b) :
    ∃ k : sheafOfDifferentials B S hS g ⟶ sheafOfDifferentials B S hS ψ, IsIso k ∧
      universalDerivationHom B S hS g ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map k =
        universalDerivationHom B S hS ψ := by
  subst hg
  exact ⟨_, (sheafOfDifferentialsIsoOfSharpIso B S hS ψ (ψ ≫ b)
      (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb)
      (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS ψ b
        hb)).isIso_inv,
    universalDerivationHom_comp_sharpIsoInv B S hS ψ (ψ ≫ b)
      (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb)
      (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS ψ b hb)⟩

/-- **The canonical map `a^*Ω_{X/Y} ⟶ Ω_{U/V}` of [Stacks Project, Tag 04CX] is an isomorphism
when `a` and `b` are étale.** -/
theorem isIso_sheafOfDifferentialsMap_of_isEtale (f : X ⟶ Y) (a : U ⟶ X) (ψ : U ⟶ V)
    (b : V ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = ψ ≫ b) :
    IsIso (sheafOfDifferentialsMap B S hS a f ψ b hcomm) := by
  obtain ⟨k, hk, hkd⟩ := exists_isIso_universalDerivationHom_comp_eq B S hS ψ b hb (a ≫ f) hcomm
  have : IsIso (etaleSourceLocalizationHom B S hS a ha f) :=
    (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).isIso_hom
  have heq : sheafOfDifferentialsMap B S hS a f ψ b hcomm =
      etaleSourceLocalizationHom B S hS a ha f ≫ k :=
    eq_of_isSheafOfDifferentialsMap B S hS a f ψ
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a f ψ b hcomm)
      (isSheafOfDifferentialsMap_comp_of_universalDerivationHom B S hS a f (a ≫ f) ψ
        (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS a ha f) k hkd)
  rw [heq]
  infer_instance

end EtaleSquare

end AlgebraicGeometry.Space

end
