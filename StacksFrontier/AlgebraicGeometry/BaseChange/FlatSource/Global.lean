module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.AffineSingle
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.CechResolution
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting

/-!
# Base change of the direct image of a module flat over the base and over the source

Base change for the derived direct image of a quasi-coherent module flat over the base and
over the source, along a quasi-compact separated morphism and an arbitrary base change, also at
every shift. The question is local on the base, and over an affine open it is the affine
case.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Modules (toShHom_comm)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard

section General

variable {X' X S' S : RingedSpace.{u, u}}

/-- The derived base change map is invertible at an object as soon as it is at an isomorphic
one: it is natural in the object. -/
theorem isIso_derivedBaseChangeMap_of_iso (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
    (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (e : K ≅ L)
    (h : IsIso (derivedBaseChangeMap g' f' f g sq K)) :
    IsIso (derivedBaseChangeMap g' f' f g sq L) := by
  have : IsIso ((derivedPullback g).map ((derivedPushforward f).map e.hom) ≫
      derivedBaseChangeMap g' f' f g sq L) := by
    rw [derivedBaseChangeMap_naturality g' f' f g sq e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedPullback g).map ((derivedPushforward f).map e.hom)) _

/-- The derived base change map only depends on the horizontal arrows of the square, so it may
be transported along equalities of them. -/
theorem isIso_derivedBaseChangeMap_congr {g₁ g₂ : X' ⟶ X} (f' : X' ⟶ S') (f : X ⟶ S)
    {h₁ h₂ : S' ⟶ S} (eg : g₁ = g₂) (eh : h₁ = h₂) (sq₁ : g₁ ≫ f = f' ≫ h₁)
    (sq₂ : g₂ ≫ f = f' ≫ h₂) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (h : IsIso (derivedBaseChangeMap g₁ f' f h₁ sq₁ K)) :
    IsIso (derivedBaseChangeMap g₂ f' f h₂ sq₂ K) := by
  subst eg eh
  exact h

/-- **Two-out-of-three for horizontally pasted squares.** If the base change map of the left
square is invertible at the derived pullback of `K`, then the base change map of the outer
rectangle is invertible at `K` exactly when the derived pullback of the base change map of the
right square is. -/
theorem isIso_derivedPullback_map_derivedBaseChangeMap_iff {X'' S'' : RingedSpace.{u, u}}
    (g : X' ⟶ X) (g' : X'' ⟶ X') (f'' : X'' ⟶ S'') (f' : X' ⟶ S') (f : X ⟶ S)
    (h' : S'' ⟶ S') (h : S' ⟶ S) (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (h₂ : IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K)) ↔
      IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
        (hcomp_square g' g f'' f' f h' h sq₁ sq₂) K) := by
  rw [← derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂ K]
  refine ⟨fun _ => inferInstance, fun hc => ?_⟩
  have h₃ : IsIso ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K) ≫
      derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K) ≫
      (derivedPushforward f'').map
        ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' g).hom.app K)) :=
    IsIso.of_isIso_comp_left
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical h' h).inv.app
        ((derivedPushforward f).obj K)) _
  rw [← Category.assoc] at h₃
  have h₄ := IsIso.of_isIso_comp_right
    ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K) ≫
      derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K))
    ((derivedPushforward f'').map
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' g).hom.app K))
  exact IsIso.of_isIso_comp_right _
    (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K))

end General

section Scheme

variable {X' X S' S : Scheme.{u}}

/-- The restriction of a quasi-coherent module to an open subscheme, as a quasi-coherent
module. -/
abbrev restrictQcoh {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent U.ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback j).obj F.obj, AffineBaseChange.isQuasicoherent_pullback j F.obj⟩

/-- Flatness over `f` restricts along an open immersion `j` to flatness over any `d` with
`d ≫ ι = j ≫ f`, for an open immersion `ι`. -/
private theorem isFlatOver_restrictQcoh {U V : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (ι : V ⟶ S) [IsOpenImmersion ι] (d : U ⟶ V) (hd : d ≫ ι = j ≫ f)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) :
    IsFlatOver d.toLRSHom.toShHom (restrictQcoh j F).obj := by
  have : ((restrictQcoh j F).obj).IsQuasicoherent := (restrictQcoh j F).property
  refine (isFlatOver_comp_iff_of_etale d ι _).1 ?_
  rw [hd]
  intro x
  exact (isFlatOverAt_pullback_iff_of_isFlatAt j f F.obj x (Flat.stalkMap j x)).1 (hF _)

/-- A module flat over `O_X` restricts to a module flat over `O_U` on an open subscheme. -/
theorem isFlat_pullback_of_isOpenImmersion {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hFX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := U.sheaf)
      (restrictQcoh j F).obj := by
  exact (isFlatOver_id_iff_isFlat _).1 (isFlatOver_restrictQcoh (𝟙 X) j j (𝟙 U) (by simp) F
    ((isFlatOver_id_iff_isFlat _).2 hFX))

variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (hsq : IsPullback g' f' f g)

include hsq in
/-- **The local step of `isIso_derivedBaseChangeMap_of_affine_local`.** Suppose that over an
open immersion `j : W ⟶ S'` the base-changed square is pasted from a cartesian square `C` and a
cartesian square `D` over an open immersion `ι : V ⟶ S`. If the derived base change map of `C`
is invertible at the derived pullback of `K`, the derived pullback along `j` of the derived base
change map at `K` is invertible. -/
theorem isIso_derivedPullback_map_derivedBaseChangeMap_of_paste
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {W V P Q : Scheme.{u}} (j : W ⟶ S') [IsOpenImmersion j] (ι : V ⟶ S)
    [IsOpenImmersion ι] (a : P ⟶ X') (b : P ⟶ W) (hA : IsPullback a b f' j)
    (c : Q ⟶ X) (d : Q ⟶ V) (hD : IsPullback c d f ι) (e : P ⟶ Q) (gV : W ⟶ V)
    (hC : IsPullback e b d gV) (hec : e ≫ c = a ≫ g') (hgV : gV ≫ ι = j ≫ g)
    (hCK : IsIso (derivedBaseChangeMap e.toLRSHom.toShHom b.toLRSHom.toShHom d.toLRSHom.toShHom
        gV.toLRSHom.toShHom (toShHom_comm hC.w)
        ((derivedPullback c.toLRSHom.toShHom).obj K))) :
    IsIso ((derivedPullback j.toLRSHom.toShHom).map
      (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w) K)) := by
  have hDK : IsIso ((derivedPullback gV.toLRSHom.toShHom).map
      (derivedBaseChangeMap c.toLRSHom.toShHom d.toLRSHom.toShHom f.toLRSHom.toShHom
        ι.toLRSHom.toShHom (toShHom_comm hD.w) K)) := by
    have := isIso_derivedBaseChangeMap_of_isOpenImmersion c d f ι hD K
    infer_instance
  have hCD := (isIso_derivedPullback_map_derivedBaseChangeMap_iff c.toLRSHom.toShHom
    e.toLRSHom.toShHom b.toLRSHom.toShHom d.toLRSHom.toShHom f.toLRSHom.toShHom
    gV.toLRSHom.toShHom ι.toLRSHom.toShHom (toShHom_comm hD.w) (toShHom_comm hC.w) K
    hCK).1 hDK
  have hAB := isIso_derivedBaseChangeMap_congr b.toLRSHom.toShHom f.toLRSHom.toShHom
    (toShHom_comm hec) (toShHom_comm hgV) _
    (hcomp_square a.toLRSHom.toShHom g'.toLRSHom.toShHom b.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom
      (toShHom_comm hsq.w) (toShHom_comm hA.w)) K hCD
  have hA' := isIso_derivedBaseChangeMap_of_isOpenImmersion a b f' j hA
    ((derivedPullback g'.toLRSHom.toShHom).obj K)
  exact (isIso_derivedPullback_map_derivedBaseChangeMap_iff g'.toLRSHom.toShHom
    a.toLRSHom.toShHom b.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
    j.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hsq.w) (toShHom_comm hA.w) K
    hA').2 hAB

/-- **Base change is local on the base, for an object of `D(𝒪_X)`.** Let `f : X ⟶ S` be
quasi-compact and separated and `K` an object of `D(𝒪_X)`. Suppose that for every open immersion
`ι : V ⟶ S` from an affine scheme, with `X_V = X ×_S V ⟶ X` written `c`, and every cartesian
square over `V`, the derived base change map at `L c^* K` is invertible. Then the derived base
change map at `K` is invertible for every cartesian square over `S`.

The question is local on `S'`; over the preimage of an affine open `V ⊆ S` the square is pasted
from an open immersion square, a square over the affine base `V`, and another open immersion
square, and the derived base change maps of open immersion squares are invertible. -/
theorem isIso_derivedBaseChangeMap_of_affine_local
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ {V Q P W : Scheme.{u}} [IsAffine V] (ι : V ⟶ S) [IsOpenImmersion ι] (c : Q ⟶ X)
      (d : Q ⟶ V) (_ : IsPullback c d f ι) (e : P ⟶ Q) (b : P ⟶ W) (gV : W ⟶ V)
      (hC : IsPullback e b d gV),
      IsIso (derivedBaseChangeMap e.toLRSHom.toShHom b.toLRSHom.toShHom d.toLRSHom.toShHom
        gV.toLRSHom.toShHom (toShHom_comm hC.w)
        ((derivedPullback c.toLRSHom.toShHom).obj K))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w) K) := by
  refine Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
    (structureSheafRing S'.toRingedSpace)
    (fun V : S.affineOpens => g ⁻¹ᵁ (V.1 : S.Opens))
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)) _ fun V => ?_
  refine (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
      S'.toRingedSpace (g ⁻¹ᵁ (V.1 : S.Opens))) _).mp ?_
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  have hgV : g ∣_ (V.1 : S.Opens) ≫ (V.1 : S.Opens).ι = (g ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ g :=
    morphismRestrict_ι g _
  have hA := IsPullback.of_hasPullback f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι
  have hD := IsPullback.of_hasPullback f (V.1 : S.Opens).ι
  have hw : (pullback.fst f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ g') ≫ f =
      (pullback.snd f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ g ∣_ (V.1 : S.Opens)) ≫
        (V.1 : S.Opens).ι := by
    rw [Category.assoc, Category.assoc, hgV, hsq.w, ← Category.assoc, hA.w, Category.assoc]
  have hec := pullback.lift_fst _ _ hw
  have hout := hA.paste_horiz hsq
  rw [← hec, ← hgV] at hout
  have hC := IsPullback.of_right hout (pullback.lift_snd _ _ hw) hD
  exact isIso_derivedPullback_map_derivedBaseChangeMap_of_paste hsq K
    (g ⁻¹ᵁ (V.1 : S.Opens)).ι (V.1 : S.Opens).ι (pullback.fst f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι)
    (pullback.snd f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι) hA (pullback.fst f (V.1 : S.Opens).ι)
    (pullback.snd f (V.1 : S.Opens).ι) hD
    (pullback.lift (pullback.fst f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ g')
      (pullback.snd f' (g ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ g ∣_ (V.1 : S.Opens)) hw)
    (g ∣_ (V.1 : S.Opens)) hC hec hgV (hK (V.1 : S.Opens).ι _ _ hD _ _ _ hC)

/-- **Derived pullback along an open immersion of a shift of a module placed in degree zero** is
the shift of the pullback of the module placed in degree zero. -/
def derivedPullbackSingleShiftIsoOfIsOpenImmersion {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) (n : ℤ) :
    (derivedPullback j.toLRSHom.toShHom).obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) 0).obj F)⟦n⟧))) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing U.toRingedSpace))
          (ComplexShape.up ℤ) 0).obj ((Scheme.Modules.pullback j).obj F))⟦n⟧)) :=
  haveI := isIso_derivedPullbackComparison_of_isOpenImmersion j.toLRSHom.toShHom
  asIso ((derivedPullbackComparison j.toLRSHom.toShHom).app _) ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).app _ ≪≫
        (shiftFunctor _ n).mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback j.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app F)))

include hsq in
/-- **Base change for the direct image of a shift of a module flat over the base and over the
source.** Let `f : X ⟶ S` be quasi-compact and separated and let `F` be a quasi-coherent
`𝒪_X`-module which is flat over `S` and flat as an `𝒪_X`-module. For every cartesian square
with base change `g : S' ⟶ S` the derived base change map of Stacks 08HY at `F[-n]` is an
isomorphism. -/
theorem isIso_derivedBaseChangeMap_single_shift [QuasiCompact f] [IsSeparated f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj)
    (hFX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj) (n : ℤ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) 0).obj F.obj)⟦n⟧)))) := by
  refine isIso_derivedBaseChangeMap_of_affine_local hsq _ ?_
  intro V Q P W _ ι _ c d hD e b gV hC
  have : IsOpenImmersion c :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hD.flip inferInstance
  have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact) hD inferInstance
  have : IsSeparated d := MorphismProperty.of_isPullback (P := @IsSeparated) hD inferInstance
  have : CompactSpace Q := (quasiCompact_iff_compactSpace d).mp inferInstance
  have : IsSeparated (terminal.from Q) := by
    simpa using (inferInstance : IsSeparated (d ≫ terminal.from V))
  have hFV := isFlatOver_restrictQcoh f c ι d hD.w.symm F hF
  have hC' := isIso_derivedBaseChangeMap_single_shift_of_cover hC
    (ModuleBaseChange.finiteAffineOpenCover Q) (restrictQcoh c F) hFV
    (isFlat_pullback_of_isOpenImmersion c F hFX) n
  exact isIso_derivedBaseChangeMap_of_iso _ _ _ _ (toShHom_comm hC.w)
    (derivedPullbackSingleShiftIsoOfIsOpenImmersion c F.obj n).symm hC'

include hsq in
/-- **Base change for the direct image of a module flat over the base and over the source.**
Let `f : X ⟶ S` be quasi-compact and separated and let `F` be a quasi-coherent `𝒪_X`-module which
is flat over `S` and flat as an `𝒪_X`-module. For every cartesian square with base change
`g : S' ⟶ S` the derived base change map `Lg^*Rf_*F ⟶ Rf'_*L(g')^*F` of Stacks 08HY is an
isomorphism. -/
theorem isIso_derivedBaseChangeMap_single [QuasiCompact f] [IsSeparated f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj)
    (hFX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) 0).obj F.obj)))) :=
  isIso_derivedBaseChangeMap_of_iso _ _ _ _ (toShHom_comm hsq.w)
    (DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((shiftFunctorZero _ ℤ).app _)))
    (isIso_derivedBaseChangeMap_single_shift hsq F hF hFX 0)

end Scheme

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
