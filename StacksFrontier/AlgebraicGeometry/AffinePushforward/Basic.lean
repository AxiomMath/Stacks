module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the direct image along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a quasi-coherent
`𝒪_X`-module.  This file proves that `f_* F` is a quasi-coherent `𝒪_S`-module, which is the
first assertion of Stacks Tag 02KG.

## Main results

* `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`
  is the statement of the tag: the direct image of a quasi-coherent module along an affine
  morphism is quasi-coherent.
* `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` is the base-change
  isomorphism for the square obtained by restricting `f` over an open of `S`: restriction to
  `V` of the direct image along `f` agrees with the direct image along `f ∣_ V` of the
  restriction to `f ⁻¹ᵁ V`.
* `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine`
  is the affine case, and
  `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations` is the
  local-to-global step.

## Implementation notes

Mathlib has the affine case over `Spec` already: `isIso_fromTildeΓ_pushforward` says that the
direct image along `Spec.map φ` of a module whose comparison map `fromTildeΓ` is invertible
again has invertible comparison map, and `isQuasicoherent_iff_isIso_fromTildeΓ` identifies
invertibility of that map with quasi-coherence.  What is missing, and what this file supplies,
is everything needed to pass from that statement to a statement about an arbitrary affine
morphism of schemes:

* `isQuasicoherent_pushforward_of_isIso`: the direct image along an isomorphism of schemes
  preserves quasi-coherence.  It is deduced from Mathlib's
  `Scheme.Modules.isQuasicoherent_restrictFunctor` by exhibiting `(pushforward e.hom).obj N`
  as `(restrictFunctor e.inv).obj N`, using that restriction is a retraction of the direct
  image along an open immersion (`restrictFunctorAdjCounitIso`).
* `isQuasicoherent_pushforward_of_isAffine`: for a morphism of affine schemes, conjugating by
  the canonical isomorphisms `Scheme.isoSpec` reduces to the `Spec` case.
* `restrictPushforwardIso`: both `pushforward f ⋙ restrictFunctor V.ι` and
  `restrictFunctor (f ⁻¹ᵁ V).ι ⋙ pushforward (f ∣_ V)` are, by definition, direct images of
  sheaves of modules along the two site functors `W ↦ f ⁻¹ᵁ (V.ι ''ᵁ W)` and
  `W ↦ (f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ W)` on opens of `V`.  These two functors agree by
  `image_morphismRestrict_preimage`, and the two morphisms of sheaves of rings agree by
  `morphismRestrict_app`, so the comparison is assembled from
  `SheafOfModules.pushforwardNatIso` and `SheafOfModules.pushforwardCongr`.
* `isQuasicoherent_of_presentations`: quasi-coherence is local.  Mathlib's
  `SheafOfModules.QuasicoherentData` asks for a presentation of `M.over V` for `V` in a
  covering family, whereas the geometric input is a presentation of `M.restrict V.ι`;
  `presentationOver` transports one to the other along `Scheme.Modules.overEquiv`.
* `nonempty_presentation_of_isoSpec`: on a scheme isomorphic to a spectrum, a quasi-coherent
  module has a global presentation, obtained from `presentationTilde` after transporting along
  the isomorphism with `Scheme.Modules.presentationRestrict`.

In `presentationOver` the instance `PreservesColimitsOfSize` required by
`SheafOfModules.Presentation.map` is passed as an explicit argument.  It cannot be found by
instance search, because the category structure on `AlgebraicGeometry.Scheme.Modules` is a
separate instance from the one on `SheafOfModules` and the two are only equal after unfolding
a non-reducible definition; supplying the argument positionally makes the comparison happen at
the default transparency of term elaboration instead.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforward

/-! ### Restriction of the direct image to an open of the target -/

section Restrict

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- The two site functors on opens of `V` computing the restriction to `V` of a direct image
along `f` agree: `(f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ W) = f ⁻¹ᵁ (V.ι ''ᵁ W)`. -/
noncomputable def opensFunctorRestrictIso :
    (Opens.map (f ∣_ V).base ⋙ (f ⁻¹ᵁ V).ι.opensFunctor) ≅
      (V.ι.opensFunctor ⋙ Opens.map f.base) :=
  NatIso.ofComponents (fun W ↦ eqToIso (image_morphismRestrict_preimage f V W))

/-- Restriction to an open `V` of the target commutes with the direct image: the restriction
to `V` of `f_* M` is the direct image along `f ∣_ V` of the restriction of `M` to `f ⁻¹ᵁ V`. -/
noncomputable def restrictPushforwardIso :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _ (opensFunctorRestrictIso f V) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext W x
      have h := morphismRestrict_app f V (unop W)
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, opensFunctorRestrictIso]
      exact congr($h.symm x)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

end Restrict

/-! ### The direct image along an isomorphism, and the affine case -/

/-- Quasi-coherence of modules on a scheme is invariant under isomorphism. -/
private theorem isQuasicoherent_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    [M.IsQuasicoherent] : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e inferInstance

/-- The direct image of a quasi-coherent module along an isomorphism of schemes is
quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_isIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (N : Y.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pushforward e.hom).obj N).IsQuasicoherent := by
  have i₁ : (Scheme.Modules.pushforward e.inv).obj
      ((Scheme.Modules.pushforward e.hom).obj N) ≅ N :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app N ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app N ≪≫
      (Scheme.Modules.pushforwardId Y).app N
  have iso : (Scheme.Modules.restrictFunctor e.inv).obj N ≅
      (Scheme.Modules.pushforward e.hom).obj N :=
    ((Scheme.Modules.restrictFunctor e.inv).mapIso i₁).symm ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app _
  exact isQuasicoherent_of_iso iso

/-- The direct image of a quasi-coherent module along a morphism of spectra is
quasi-coherent. -/
theorem isQuasicoherent_pushforward_specMap {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (N : (Spec T).Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsQuasicoherent := by
  have : IsIso N.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (isIso_fromTildeΓ_pushforward φ N)

/-- The direct image of a quasi-coherent module along a morphism of affine schemes is
quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_isAffine {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (h : Y ⟶ Z) (N : Y.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pushforward h).obj N).IsQuasicoherent := by
  have key : h = Y.isoSpec.hom ≫ (Spec.map h.appTop ≫ Z.isoSpec.inv) := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have h₁ := isQuasicoherent_pushforward_of_isIso Y.isoSpec N
  have h₂ := isQuasicoherent_pushforward_specMap h.appTop
    ((Scheme.Modules.pushforward Y.isoSpec.hom).obj N)
  have h₃ := isQuasicoherent_pushforward_of_isIso Z.isoSpec.symm
    ((Scheme.Modules.pushforward (Spec.map h.appTop)).obj
      ((Scheme.Modules.pushforward Y.isoSpec.hom).obj N))
  have iso : (Scheme.Modules.pushforward Z.isoSpec.symm.hom).obj
      ((Scheme.Modules.pushforward (Spec.map h.appTop)).obj
        ((Scheme.Modules.pushforward Y.isoSpec.hom).obj N)) ≅
      (Scheme.Modules.pushforward h).obj N :=
    (Scheme.Modules.pushforwardComp (Spec.map h.appTop) Z.isoSpec.inv).app _ ≪≫
      (Scheme.Modules.pushforwardComp Y.isoSpec.hom
        (Spec.map h.appTop ≫ Z.isoSpec.inv)).app N ≪≫
      (Scheme.Modules.pushforwardCongr key.symm).app N
  exact isQuasicoherent_of_iso iso

/-! ### Quasi-coherence is local on the scheme -/

section Local

variable {X : Scheme.{u}}

/-- The isomorphism between `M.over V` and the image of the restriction `M.restrict V.ι` under
the inverse of the equivalence `Scheme.Modules.overEquiv V`, used to transport a presentation
of `M.restrict V.ι` into a presentation of `M.over V`. -/
noncomputable def overInverseIso (V : X.Opens) (M : X.Modules) :
    M.over V ≅ (Scheme.Modules.overEquiv V).inverse.obj (M.restrict V.ι) :=
  ((Scheme.Modules.overEquiv V).unitIso.app (M.over V)) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso ((Scheme.Modules.overFunctorEquiv V).app M)

/-- The equivalence `Scheme.Modules.overEquiv` carries the structure sheaf to the structure
sheaf. -/
noncomputable def overInverseUnitIso (V : X.Opens) :
    SheafOfModules.unit.{u} (Sheaf.over X.ringCatSheaf V) ≅
      (Scheme.Modules.overEquiv V).inverse.obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf) :=
  overInverseIso V (SheafOfModules.unit.{u} X.ringCatSheaf) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso (Scheme.Modules.restrictUnitIso V.ι)

/-- The inverse of the equivalence `Scheme.Modules.overEquiv V` is a left adjoint. -/
noncomputable instance isLeftAdjointOverEquivInverse (V : X.Opens) :
    Functor.IsLeftAdjoint (Scheme.Modules.overEquiv V).inverse :=
  (Scheme.Modules.overEquiv V).symm.toAdjunction.isLeftAdjoint

/-- A presentation of the restriction of `M` to an open `V` gives a presentation of
`M.over V`. -/
noncomputable def presentationOver (V : X.Opens) (M : X.Modules)
    (P : (M.restrict V.ι).Presentation) : (M.over V).Presentation :=
  SheafOfModules.Presentation.ofIsIso (overInverseIso V M).inv
    (@SheafOfModules.Presentation.map.{u, u, u, u, u} _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (Scheme.Modules.overEquiv V).inverse
      (inferInstance : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv V).inverse)
      (overInverseUnitIso V))

/-- Quasi-coherent data for `M` obtained from presentations of the restrictions of `M` to the
members of an open covering. -/
noncomputable def quasicoherentDataOfPresentations (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.QuasicoherentData where
  I := I
  X := U
  coversTop := (Opens.coversTop_iff _ U).mpr hU
  presentation i := presentationOver (U i) M (P i)

/-- Quasi-coherence is local: a module whose restriction to each member of an open covering
has a presentation is quasi-coherent. -/
theorem isQuasicoherent_of_presentations (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U) (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent :=
  (quasicoherentDataOfPresentations M U hU P).isQuasicoherent

end Local

/-- Transport of a presentation along an isomorphism.  This repackages
`SheafOfModules.Presentation.ofIsIso` so that the isomorphism is supplied as an
`CategoryTheory.Iso`, which avoids an instance search for `IsIso` that the two category
structures on sheaves of modules over a scheme would defeat. -/
noncomputable def presentationOfIso {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation :=
  SheafOfModules.Presentation.ofIsIso e.hom P

/-- On a scheme isomorphic to a spectrum, a quasi-coherent module has a global
presentation. -/
theorem nonempty_presentation_of_isoSpec {Y : Scheme.{u}} {R : CommRingCat.{u}} (e : Y ≅ Spec R)
    (N : Y.Modules) [N.IsQuasicoherent] : Nonempty N.Presentation := by
  have hqc : (N.restrict e.inv).IsQuasicoherent := inferInstance
  have hiso : IsIso (N.restrict e.inv).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (N.restrict e.inv)).mp hqc
  have e₀ := asIso (N.restrict e.inv).fromTildeΓ
  have P₀ : (N.restrict e.inv).Presentation :=
    presentationOfIso e₀ (presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
  have P₁ : ((N.restrict e.inv).restrict e.hom).Presentation :=
    Scheme.Modules.presentationRestrict e.hom P₀
  have iso : (N.restrict e.inv).restrict e.hom ≅ N :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app N ≪≫
      Scheme.Modules.restrictFunctorId.app N
  exact ⟨presentationOfIso iso P₁⟩

/-! ### The theorem -/

/-- **Stacks Project, Tag 02KG.** The direct image of a quasi-coherent module along an affine
morphism is quasi-coherent. -/
@[stacks 02KG "quasi-coherence of the direct image"]
instance pushforward_isQuasicoherent_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [IsAffineHom f] [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_presentations _ (fun V : S.affineOpens ↦ (V : S.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top S)) (fun V ↦ ?_)
  obtain ⟨V, hV⟩ := V
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hW
  have : IsAffine V.toScheme := hV
  have hqc : ((Scheme.Modules.pushforward (f ∣_ V)).obj (F.restrict (f ⁻¹ᵁ V).ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffine (f ∣_ V) _
  have hqc' : (((Scheme.Modules.pushforward f).obj F).restrict V.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      ((restrictPushforwardIso f V).app F).symm hqc
  exact (nonempty_presentation_of_isoSpec hV.isoSpec _).some

end Stacks.AlgebraicGeometry.AffinePushforward

end
