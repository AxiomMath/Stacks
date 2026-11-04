module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# The module attached to a quasi-coherent sheaf is cartesian on an affine site

Let `S` be a scheme and `𝒢` a quasi-coherent `𝒪_S`-module. Descent, Section 35.8 attaches to
`𝒢` the presheaf of modules `𝒢ᵃ : U/S ↦ Γ(U, f^*𝒢)` on a category of schemes over `S`; this is
`Stacks.Sites.associatedModulePresheaf`. On a category whose objects have *affine* total space
all of its base-change comparisons

`𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)`

are isomorphisms. This is the implication **condition (8) ⇒ condition (1)** of Stacks 0GZV, the
one the source gets from Schemes, Lemma 26.7.3; the topology plays no part in it, so it is
proved once for an arbitrary site of affine schemes over `S` and instantiated at the five big
affine sites `(Aff/S)_τ` of Stacks 0GZV.

## Main definitions

* `Stacks.Sites.commStructurePresheaf`: the presheaf of commutative rings of global functions of
  a site of schemes over `S`, the `CommRingCat`-valued reading of
  `Stacks.Sites.structurePresheaf`.
* `Stacks.Sites.affineAssociatedBaseChangeIsoOfEq`: the affine base-change comparison of
  `Stacks.Sites.affineAssociatedBaseChangeIso`, stated for any ring map *equal* to
  `g.left.appLE ⊤ ⊤`.
* `AlgebraicGeometry.bigAffineZariskiToOver` and its étale, smooth, syntomic and fppf
  counterparts: the presenting functors `(Aff/S)_τ ⥤ Over S` of the five big affine sites.

## Main results

* `Stacks.SheafOfModules.canonicalMap_eq_restrictionBaseChange`: the base-change map of a ringed
  site is the base-change comparison of the underlying presheaf of modules.
* `Stacks.Sites.restrictionBaseChange_associatedModulePresheaf_eq`: the base-change comparison of
  `𝒢ᵃ` between affine objects is the affine base-change isomorphism of Stacks 02KH.
* `Stacks.Sites.isIso_restrictionBaseChange_associatedModulePresheaf`: **`𝒢ᵃ` is cartesian on a
  site of affine schemes over `S`.**
* `AlgebraicGeometry.bigAffineZariski_isIso_restrictionBaseChange_associatedModule` and its four
  counterparts: Stacks 0GZV, condition (8) implies condition (1).

## Implementation notes

`Stacks.Sites.affineAssociatedBaseChangeIso` extends scalars along `g.left.appLE ⊤ ⊤`, while the
base-change comparison of a presheaf of modules extends scalars along the restriction map
`Scheme.Γ.map` of the structure presheaf. The two ring maps agree by
`Stacks.Sites.gammaMap_eq_appLE_top_top`, but only propositionally, so the comparison is restated
with the ring map as a parameter — the same device as
`Stacks.Sites.affineBaseChangeIsoOfEq`, of which this is the `𝒢ᵃ`-level form.

The identification of the two comparisons is made through the adjunction
`CategoryTheory.ModuleCat.extendRestrictScalarsAdj` rather than by an induction over the tensor
product: the base-change comparison is by definition the adjoint transpose of the restriction
map, so the identity on the generators `1 ⊗ m` that
`Stacks.Sites.affineAssociatedBaseChangeIsoOfEq_one_tmul` records *is* the statement that the two
transposes agree.

The structure presheaves of the five big affine ringed sites of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines` are the
`Stacks.Sites.commStructurePresheaf` of their presenting functors on the nose, as recorded by
`AlgebraicGeometry.bigAffineZariskiRingedSite_O_obj` and its counterparts, so the five statements
are about the structure presheaf those ringed sites carry and not a second copy of it.

## Coverage limits

Only the implication (8) ⇒ (1) is proved. The converse (1) ⇒ (8), which is where the uniqueness
of `𝒢` in condition (8) lives, rests on essential surjectivity in Descent, Proposition 03DX,
which this development does not have; see
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor`. Conditions (7) and (8) are
therefore the two of the eight that are not yet tied to the rest: conditions (1) and (2)–(6) are
equivalent, by this file's neighbours
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf`,
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines` and
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteQuasicoherentCartesian`.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.SheafOfModules

/-- The base-change map of a ringed site is the base-change comparison of the underlying
presheaf of modules, taken at the opposite morphism. -/
public theorem canonicalMap_eq_restrictionBaseChange
    (X : AlgebraicGeometry.RingedSite.{u + 1, u, u})
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C}
      (f : U ⟶ V) :
    canonicalMap X F f =
      Stacks.PresheafOfModules.restrictionBaseChange (R := X.O.obj) F.val f.op := rfl

end Stacks.SheafOfModules

namespace Stacks.Sites

open AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **The affine base-change comparison of `𝒢ᵃ`, with the extended ring map named.**
`Stacks.Sites.affineAssociatedBaseChangeIso` stated for any ring map *equal* to
`g.left.appLE ⊤ ⊤`, so that it can be compared with the base-change comparison of a presheaf of
modules over `Stacks.Sites.commStructurePresheaf`, whose base acts through `Scheme.Γ.map`. -/
public noncomputable def affineAssociatedBaseChangeIsoOfEq (F : S.Modules) [F.IsQuasicoherent]
    {X Y : Over S} [IsAffine X.left] [IsAffine Y.left] (g : X ⟶ Y)
    (φ : Γ(Y.left, ⊤) →+* Γ(X.left, ⊤))
    (hφ : φ = (g.left.appLE ⊤ ⊤ (top_le_preimage_top g.left)).hom) :
    (ModuleCat.extendScalars φ).obj
        (ModuleCat.of Γ(Y.left, ⊤) Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) ≅
      ModuleCat.of Γ(X.left, ⊤) Γ((Scheme.Modules.pullback X.hom).obj F, ⊤) :=
  affineBaseChangeIsoOfEq ((Scheme.Modules.pullback Y.hom).obj F) g.left φ hφ ≪≫
    (sectionsLinearEquivOfIso (pullbackSectionsComparison F g) ⊤).toModuleIso

/-- **The normalisation.** `Stacks.Sites.affineAssociatedBaseChangeIsoOfEq` sends the generator
`1 ⊗ m` to the restriction map of `𝒢ᵃ` applied to `m`; together with linearity this pins it down
as the canonical comparison. -/
public theorem affineAssociatedBaseChangeIsoOfEq_one_tmul (F : S.Modules) [F.IsQuasicoherent]
    {X Y : Over S} [IsAffine X.left] [IsAffine Y.left] (g : X ⟶ Y)
    (φ : Γ(Y.left, ⊤) →+* Γ(X.left, ⊤))
    (hφ : φ = (g.left.appLE ⊤ ⊤ (top_le_preimage_top g.left)).hom)
    (m : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    (affineAssociatedBaseChangeIsoOfEq F g φ hφ).hom
        ((1 : Γ(X.left, ⊤)) ⊗ₜ[Γ(Y.left, ⊤), φ] m) =
      AlgebraicGeometry.pullbackSectionsMap F g m := by
  refine (CategoryTheory.comp_apply _ _ _).trans ?_
  rw [affineBaseChangeIsoOfEq_one_tmul]
  exact pullbackSectionsComparison_pullbackSection F g (top_le_preimage_top g.left) m

/-- The presheaf of commutative rings of global functions of a site of schemes over `S`: the
`CommRingCat`-valued reading of `Stacks.Sites.structurePresheaf`. -/
public noncomputable abbrev commStructurePresheaf (S : Scheme.{u}) {C : Type (u + 1)}
    [Category.{u} C] (toOver : C ⥤ Over S) : Cᵒᵖ ⥤ CommRingCat.{u} :=
  (toOver ⋙ Over.forget S).op ⋙ Scheme.Γ

variable (F : S.Modules) [F.IsQuasicoherent]
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **The base-change comparison of `𝒢ᵃ` between affine objects is the affine base-change
isomorphism.** Both are the adjoint transpose of the restriction map of `𝒢ᵃ`, so they agree. -/
public theorem restrictionBaseChange_associatedModulePresheaf_eq
    [∀ X : C, IsAffine (toOver.obj X).left] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf S toOver) (associatedModulePresheaf S F toOver) f =
      (affineAssociatedBaseChangeIsoOfEq F (toOver.map f.unop)
        ((commStructurePresheaf S toOver).map f).hom
        (gammaMap_eq_appLE_top_top (toOver.map f.unop).left)).hom := by
  set φ := ((commStructurePresheaf S toOver).map f).hom with hφdef
  set e := affineAssociatedBaseChangeIsoOfEq F (toOver.map f.unop) φ
    (gammaMap_eq_appLE_top_top (toOver.map f.unop).left) with hedef
  have key : (ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ e.hom =
      (associatedModulePresheaf S F toOver).map f := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun m => ?_
    exact affineAssociatedBaseChangeIsoOfEq_one_tmul F (toOver.map f.unop) φ _ m
  exact (Equiv.symm_apply_eq _).mpr key.symm

/-- **The module attached to a quasi-coherent sheaf is cartesian on a site of affine schemes.**
For every morphism `U ⟶ U'` of a category of schemes over `S` whose objects have affine total
space, the base-change comparison `𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)` is an isomorphism. -/
public theorem isIso_restrictionBaseChange_associatedModulePresheaf
    [∀ X : C, IsAffine (toOver.obj X).left] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := commStructurePresheaf S toOver) (associatedModulePresheaf S F toOver) f) := by
  rw [restrictionBaseChange_associatedModulePresheaf_eq]
  exact Iso.isIso_hom _

end Stacks.Sites

namespace AlgebraicGeometry

open Stacks.Sites

/-! ### The five big affine sites of Stacks 0GZV -/

/-- The presenting functor of the big affine Zariski site of `S`. -/
public noncomputable abbrev bigAffineZariskiToOver (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigAffineZariski B S hS ⥤ Over S :=
  BigAffineZariski.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.bigAffineZariskiRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem bigAffineZariskiRingedSite_O_obj (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (bigAffineZariskiRingedSite B S hS).O.obj =
      commStructurePresheaf S (bigAffineZariskiToOver B S hS) := rfl

/-- Every object of the big affine Zariski site of `S` is sent by its presenting functor to an
affine scheme over `S`. -/
public instance isAffine_bigAffineZariskiToOver (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineZariski B S hS) :
    IsAffine ((bigAffineZariskiToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZV, condition (8) implies condition (1), on `(Aff/S)_Zar`.** -/
@[stacks 0GZV "(8) ⇒ (1) on the big affine Zariski category"]
public theorem bigAffineZariski_isIso_restrictionBaseChange_associatedModule
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (BigAffineZariski B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (bigAffineZariskiRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (bigAffineZariskiToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

/-- The presenting functor of the big affine étale site of `S`. -/
public noncomputable abbrev bigAffineEtaleToOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigAffineEtale B S hS ⥤ Over S :=
  BigAffineEtale.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.bigAffineEtaleRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem bigAffineEtaleRingedSite_O_obj (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (bigAffineEtaleRingedSite B S hS).O.obj =
      commStructurePresheaf S (bigAffineEtaleToOver B S hS) := rfl

/-- Every object of the big affine étale site of `S` is sent by its presenting functor to an
affine scheme over `S`. -/
public instance isAffine_bigAffineEtaleToOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineEtale B S hS) :
    IsAffine ((bigAffineEtaleToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZV, condition (8) implies condition (1), on `(Aff/S)_étale`.** -/
@[stacks 0GZV "(8) ⇒ (1) on the big affine étale category"]
public theorem bigAffineEtale_isIso_restrictionBaseChange_associatedModule
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (BigAffineEtale B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (bigAffineEtaleRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (bigAffineEtaleToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

/-- The presenting functor of the big affine smooth site of `S`. -/
public noncomputable abbrev bigAffineSmoothToOver (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) : BigAffineSmooth B S hS ⥤ Over S :=
  BigAffineSmooth.inclusion B S hS ⋙ Over.post (ObjectProperty.ι _)

/-- The structure presheaf of `AlgebraicGeometry.bigAffineSmoothRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem bigAffineSmoothRingedSite_O_obj (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    (bigAffineSmoothRingedSite B S hS).O.obj =
      commStructurePresheaf S (bigAffineSmoothToOver B S hS) := rfl

/-- Every object of the big affine smooth site of `S` is sent by its presenting functor to an
affine scheme over `S`. -/
public instance isAffine_bigAffineSmoothToOver (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) (X : BigAffineSmooth B S hS) :
    IsAffine ((bigAffineSmoothToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZV, condition (8) implies condition (1), on `(Aff/S)_smooth`.** -/
@[stacks 0GZV "(8) ⇒ (1) on the big affine smooth category"]
public theorem bigAffineSmooth_isIso_restrictionBaseChange_associatedModule
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (BigAffineSmooth B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (bigAffineSmoothRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (bigAffineSmoothToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

/-- The presenting functor of the big affine syntomic site of `S`. -/
public noncomputable abbrev bigAffineSyntomicToOver (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigAffineSyntomic B S hS ⥤ Over S :=
  BigAffineSyntomic.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.bigAffineSyntomicRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem bigAffineSyntomicRingedSite_O_obj (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (bigAffineSyntomicRingedSite B S hS).O.obj =
      commStructurePresheaf S (bigAffineSyntomicToOver B S hS) := rfl

/-- Every object of the big affine syntomic site of `S` is sent by its presenting functor to an
affine scheme over `S`. -/
public instance isAffine_bigAffineSyntomicToOver (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineSyntomic B S hS) :
    IsAffine ((bigAffineSyntomicToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZV, condition (8) implies condition (1), on `(Aff/S)_syntomic`.** -/
@[stacks 0GZV "(8) ⇒ (1) on the big affine syntomic category"]
public theorem bigAffineSyntomic_isIso_restrictionBaseChange_associatedModule
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (BigAffineSyntomic B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (bigAffineSyntomicRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (bigAffineSyntomicToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

/-- The presenting functor of the big affine fppf site of `S`. -/
public noncomputable abbrev bigAffineFppfToOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigAffineFppf B S hS ⥤ Over S :=
  BigAffineFppf.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.bigAffineFppfRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem bigAffineFppfRingedSite_O_obj (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (bigAffineFppfRingedSite B S hS).O.obj =
      commStructurePresheaf S (bigAffineFppfToOver B S hS) := rfl

/-- Every object of the big affine fppf site of `S` is sent by its presenting functor to an
affine scheme over `S`. -/
public instance isAffine_bigAffineFppfToOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineFppf B S hS) :
    IsAffine ((bigAffineFppfToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZV, condition (8) implies condition (1).** The presheaf `𝒢ᵃ` of Section 35.8
attached to a quasi-coherent `𝒪_S`-module `𝒢` has all its base-change comparisons
`𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)` isomorphisms on `(Aff/S)_fppf`, the category the source states
the lemma for. -/
@[stacks 0GZV "(8) ⇒ (1) on the big affine fppf category"]
public theorem bigAffineFppf_isIso_restrictionBaseChange_associatedModule
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (BigAffineFppf B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (bigAffineFppfRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (bigAffineFppfToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

end AlgebraicGeometry

end
