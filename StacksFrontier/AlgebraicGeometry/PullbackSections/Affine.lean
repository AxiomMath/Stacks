module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Sections of the pullback of a quasi-coherent module over an affine open

Let `f : Y ⟶ X` be a morphism of schemes and `F` a quasi-coherent `𝒪_X`-module. The functor
`AlgebraicGeometry.Scheme.Modules.pullback f` is defined as a left adjoint and so carries no
description of its sections. Over a compatible pair of affine opens there is one: if `U ⊆ X`
and `V ⊆ Y` are affine with `V ⊆ f⁻¹U`, then

  `Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U) ≅ Γ(f^*F, V)`,

and the isomorphism is pinned down by its value on `1 ⊗ a`, which is the pullback of the
section `a` restricted to `V`. This file builds that isomorphism and that normalisation.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackSection`: the pullback of a section of `F` over
  `U` to a section of `f^*F` over an open `V ≤ f⁻¹U`, namely the restriction to `V` of the
  image of the section under the unit of `f^* ⊣ f_*`.
* `AlgebraicGeometry.quasicoherentPullbackSectionsIso`: the affine case,
  `S ⊗_R Γ(G, ⊤) ≅ Γ((Spec φ)^*G, ⊤)` for `φ : R ⟶ S` and `G` quasi-coherent on `Spec R`.
* `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`: the isomorphism
  `Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U) ≅ Γ(f^*F, V)` for a compatible pair of affine opens.
* `AlgebraicGeometry.Scheme.Modules.sectionsLinearMap`: the map on sections over an open induced
  by a morphism of modules, as a linear map over the ring of functions on that open.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`,
  `pullbackSection_comp` and `pullbackSection_congr`: pulling a section back is natural in the
  module, compatible with composition of morphisms of schemes, and compatible with transport
  along an equality of morphisms.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection`: along an
  open immersion the pullback of a section is the restriction of the section.
* `AlgebraicGeometry.quasicoherentPullbackSectionsIso_hom_one_tmul` and
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`: **the normalisation.** Both
  isomorphisms send `1 ⊗ a` to the pullback of the section `a`. This is what makes them usable:
  it identifies them as the canonical base-change comparison rather than as some isomorphism of
  the two sides.
* `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_natural`: the base-change comparison is
  natural in the module, which is the normalisation read as a commuting square.

## Implementation notes

The affine case is assembled from `AlgebraicGeometry.pullbackTildeIso` (Tag 01I9) together with
the identification of a quasi-coherent module on an affine scheme with the associated sheaf of
its global sections, `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`. The general case is
then transported along `hU.fromSpec` and `hV.fromSpec` using
`Scheme.Modules.restrictFunctorIsoPullback`, `pullbackComp` and `pullbackCongr`, and the
normalisation is carried through each of those steps by the `pullbackSection` lemmas; that is
the reason `pullbackSection` is named at all rather than written out at each use.

`AlgebraicGeometry.affineSectionsLinearEquiv` of
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/AffineSections.lean` is reused for the two
outer comparisons `Γ(F.restrict hU.fromSpec, ⊤) ≅ Γ(F, U)`; nothing here rebuilds it.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- Over the full preimage of an open, `AlgebraicGeometry.Scheme.Hom.appLE` is
`AlgebraicGeometry.Scheme.Hom.app`. -/
public theorem Scheme.Hom.appLE_preimage_self {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U := by
  rw [Scheme.Hom.appLE,
    show (homOfLE (le_refl (f ⁻¹ᵁ U))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

namespace Scheme.Modules

/-- The pullback of a section: a section of `F` over `U` becomes, through the unit of
`f^* ⊣ f_*`, a section of `f^*F` over `f⁻¹U`, and is restricted here to an open `V ≤ f⁻¹U`. -/
public def pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (a : F.val.obj (op U)) : ((Scheme.Modules.pullback f).obj F).val.obj (op V) :=
  ((Scheme.Modules.pullback f).obj F).val.map (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) a)

/-- The unit of `f^* ⊣ f_*` is natural, read on sections over an open of the target. -/
public theorem unit_app_val_app_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : X.Modules} (t : F ⟶ G) (U : X.Opens) (a : F.val.obj (op U)) :
    ((Scheme.Modules.pullback f).map t).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U)
        (t.val.app (op U) a) :=
  (congrArg (fun q : F ⟶ (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pullback f).obj G) => q.val.app (op U) a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality t)).symm

/-- Pulling a section back is natural in the module. -/
public theorem pullbackSection_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : X.Modules} (t : F ⟶ G) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (a : F.val.obj (op U)) :
    ((Scheme.Modules.pullback f).map t).val.app (op V) (pullbackSection f F U V h a) =
      pullbackSection f G U V h (t.val.app (op U) a) :=
  (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map t).val
      (homOfLE h).op _).trans
    (congrArg (ConcreteCategory.hom
      (((Scheme.Modules.pullback f).obj G).val.map (homOfLE h).op))
      (unit_app_val_app_naturality f t U a))

/-- A morphism of modules is inverted by its inverse on sections. -/
private theorem inv_app_eq_iff {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (V : X.Opens)
    (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    e.inv.val.app (op V) y = x ↔ e.hom.val.app (op V) x = y := by
  constructor
  · rintro rfl
    exact congrArg (fun t => t.val.app (op V) y) e.inv_hom_id
  · rintro rfl
    exact congrArg (fun t => t.val.app (op V) x) e.hom_inv_id

/-- Restriction maps of the presheaf of a module compose, whatever the morphism `h` is called. -/
private theorem presheaf_map_map_apply {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (f : op U ⟶ op V) (g : op V ⟶ op W) (h : op U ⟶ op W) (a : M.presheaf.obj (op U)) :
    M.presheaf.map g (M.presheaf.map f a) = M.presheaf.map h a := by
  obtain rfl : h = f ≫ g := Subsingleton.elim _ _
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- The unit of `f^* ⊣ f_*` for a composite, read on sections: the comparison
`(f ≫ g)^* ⟶ f^* ∘ g^*` carries the unit of the composite to the composite of the units. -/
public theorem pullbackComp_inv_unit {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app
          (op U) a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).val.app (op (g ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) a) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun t => t.val.app (op U) a) h).symm

/-- Pulling a section back along a composite is pulling it back twice. -/
public theorem pullbackSection_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op V)
        (pullbackSection f ((Scheme.Modules.pullback g).obj M) W V hf
          (pullbackSection g M U W hg a)) =
      pullbackSection (f ≫ g) M U V h a := by
  refine (inv_app_eq_iff ((Scheme.Modules.pullbackComp f g).app M) _ _ _).1 ?_
  symm
  have hnat₁ := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackComp f g).inv.app M).val (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op U) a)
  have hnat₂ := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj M)).val (homOfLE hg).op
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) a)
  dsimp only [Functor.id_obj] at hnat₂
  unfold pullbackSection
  rw [Iso.app_inv, hnat₁, pullbackComp_inv_unit, hnat₂]
  change ConcreteCategory.hom (((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj M)).val.map (homOfLE hf).op)
    (ConcreteCategory.hom (((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj M)).val.map
        ((Opens.map f.base).map (homOfLE hg)).op) _) = _
  refine (PresheafOfModules.map_comp_apply
    (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).val)
    ((Opens.map f.base).map (homOfLE hg)).op (homOfLE hf).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).val.app (op (g ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app
        (op U) a))).symm.trans ?_
  congr 2

/-- Pulling a section back is compatible with transport along an equality of morphisms. -/
public theorem pullbackSection_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackCongr hfg).hom.app M).val.app (op V)
      (pullbackSection f M U V hf a) = pullbackSection g M U V hg a := by
  subst g
  rfl

/-- Over the whole preimage of the whole space the pullback of a section is just the image of
the section under the unit of `f^* ⊣ f_*`. -/
public theorem pullbackSection_top {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens)) (a : M.val.obj (op (⊤ : X.Opens))) :
    pullbackSection f M ⊤ ⊤ h a =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) a := by
  unfold pullbackSection
  have hid : (homOfLE h).op = 𝟙 (op (⊤ : Y.Opens)) := Subsingleton.elim _ _
  rw [hid]
  simp
  rfl

/-- Along an open immersion the comparison of the restriction with the pullback carries the
unit of `f^* ⊣ f_*` to the restriction map. -/
public theorem restrictFunctorIsoPullback_inv_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens) (a : M.val.obj (op U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) a) =
      M.val.map (homOfLE (f.image_preimage_le U)).op a := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have hh := congrArg (fun t => t ≫ (Scheme.Modules.pushforward f).map
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M)) h
  simp only [Scheme.Modules.restrictFunctorIsoPullback, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app] at hh
  exact (congrArg (fun t => t.val.app (op U) a) hh).symm

/-- Along an open immersion, pulling a section back and comparing with the restriction gives
the restriction of the section. -/
public theorem restrictFunctorIsoPullback_inv_pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : f ''ᵁ V ≤ U) (a : M.val.obj (op U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).val.app (op V)
      (pullbackSection f M U V h a) = M.val.map (homOfLE h').op a := by
  have hnat := PresheafOfModules.naturality_apply
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).val (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) a)
  unfold pullbackSection
  rw [hnat, restrictFunctorIsoPullback_inv_unit]
  change (M.restrict f).presheaf.map (homOfLE h).op
    (M.presheaf.map (homOfLE (f.image_preimage_le U)).op a) =
      M.presheaf.map (homOfLE h').op a
  rw [Scheme.Modules.restrict_map]
  exact presheaf_map_map_apply M _ _ _ a

/-- The map on sections over an open induced by a morphism of modules, as a linear map over the
ring of functions on that open. -/
public def sectionsLinearMap {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' _ _ := map_add _ _ _
  map_smul' r x := Hom.app_smul φ r x

@[simp]
public lemma sectionsLinearMap_apply {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) : sectionsLinearMap φ U x = φ.app U x := rfl

end Scheme.Modules

/-- `AlgebraicGeometry.affineSectionsLinearEquiv` is the transport along the equality
`hU.fromSpec ''ᵁ ⊤ = U`; `Scheme.Modules.restrictAppIso` is the identity. -/
public theorem affineSectionsLinearEquiv_eq_map {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (he : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U)
    (t : Γ(M.restrict hU.fromSpec, ⊤)) :
    affineSectionsLinearEquiv M hU t = M.presheaf.map (eqToHom he.symm).op t := by
  rw [affineSectionsLinearEquiv_apply]
  rfl

/-- The affine comparison of sections undoes the pullback of a section along `hU.fromSpec`. -/
public theorem affineSectionsLinearEquiv_pullbackSection {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    affineSectionsLinearEquiv M hU
      (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app M).val.app (op ⊤)
        (Scheme.Modules.pullbackSection hU.fromSpec M U ⊤ h a)) = a := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have he : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have h₁ := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection
    hU.fromSpec M U ⊤ h he.le a
  have h₂ := affineSectionsLinearEquiv_eq_map M hU he
    (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app M).val.app (op ⊤)
      (Scheme.Modules.pullbackSection hU.fromSpec M U ⊤ h a))
  rw [h₂, h₁]
  exact (Scheme.Modules.presheaf_map_map_apply M _ _ (𝟙 _) a).trans (by simp; rfl)

/-- Along `hU.fromSpec`, the comparison of the restriction with the pullback carries a section
to the pullback of the corresponding section over `U`. -/
public theorem restrictFunctorIsoPullback_hom_app_pullbackSection {X : Scheme.{u}}
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U)
    (t : Γ(M.restrict hU.fromSpec, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.app (op ⊤) t =
      Scheme.Modules.pullbackSection hU.fromSpec M U ⊤ h
        (affineSectionsLinearEquiv M hU t) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  refine (Scheme.Modules.inv_app_eq_iff
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M) _ _ _).1
    ((affineSectionsLinearEquiv M hU).injective ?_)
  exact affineSectionsLinearEquiv_pullbackSection M hU h _

/-- **The sections of the pullback on affine schemes.** For a ring map `φ : R ⟶ S` and a
quasi-coherent module `G` on `Spec R`, extending the scalars of the global sections of `G`
along `φ` gives the global sections of the pullback of `G` along `Spec φ`. -/
public def quasicoherentPullbackSectionsIso (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (G : (Spec R).Modules) [G.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj G) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj G) :=
  let eG : tilde ((moduleSpecΓFunctor (R := R)).obj G) ≅ G :=
    @CategoryTheory.asIso (Spec R).Modules (inferInstance : Category (Spec R).Modules)
      _ _ (Scheme.Modules.fromTildeΓ G)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)
  (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := R)).obj G))) ≪≫
    (moduleSpecΓFunctor (R := S)).mapIso
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso eG.symm ≪≫
        (pullbackTildeIso R S φ).app ((moduleSpecΓFunctor (R := R)).obj G)).symm

/-- **The normalisation.** `AlgebraicGeometry.quasicoherentPullbackSectionsIso` sends `1 ⊗ m`
to the image of `m` under the unit of `(Spec φ)^* ⊣ (Spec φ)_*`. -/
public theorem quasicoherentPullbackSectionsIso_hom_one_tmul (R S : CommRingCat.{u})
    (φ : R ⟶ S) (G : (Spec R).Modules) [G.IsQuasicoherent]
    (m : (moduleSpecΓFunctor (R := R)).obj G) :
    (quasicoherentPullbackSectionsIso R S φ G).hom ((1 : S) ⊗ₜ[R, φ.hom] m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app G).val.app
        (op ⊤) m := by
  let M := (moduleSpecΓFunctor (R := R)).obj G
  let eG : tilde M ≅ G :=
    @CategoryTheory.asIso (Spec R).Modules (inferInstance : Category (Spec R).Modules)
      _ _ (Scheme.Modules.fromTildeΓ G)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)
  let eT := (pullbackTildeIso R S φ).app M
  have hΓ (x : M) : (eG.hom.app ⊤) (tilde.toOpen M ⊤ x) = x := by
    have hx := congrArg (fun g => g.hom x) (Scheme.Modules.toOpen_fromTildeΓ_app G ⊤)
    have hx' := by simpa [ModuleCat.hom_comp] using hx
    exact hx'
  have hT : (eT.inv.app ⊤)
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : S) ⊗ₜ[R, φ.hom] m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        (tilde M)).app ⊤ (tilde.toOpen M ⊤ m) := by
    apply (ConcreteCategory.bijective_of_isIso (eT.hom.app ⊤)).injective
    have hi := congrArg (fun q => q.hom
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        ((1 : S) ⊗ₜ[R, φ.hom] m))) (congrArg (fun q => q.app ⊤) eT.inv_hom_id)
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at hi
    refine hi.trans ?_
    exact (pullbackTildeIso_hom_app_unit_toOpen R S φ M m).symm
  change (moduleSpecΓFunctor (R := S)).map
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso eG.symm ≪≫ eT).symm.hom
      ((tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj M)).hom
        ((1 : S) ⊗ₜ[R, φ.hom] m)) = _
  rw [tilde.isoTop_hom]
  change ((Scheme.Modules.pullback (Spec.map φ)).map eG.hom).app ⊤
      ((eT.inv.app ⊤)
        (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
          ((1 : S) ⊗ₜ[R, φ.hom] m))) = _
  rw [hT]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality eG.hom
  let a : Γ((𝟭 (Spec R).Modules).obj (tilde M), ⊤) := tilde.toOpen M ⊤ m
  have hn' := congrArg (fun q => (q.app ⊤) a) hn
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at hn'
  simp only [ConcreteCategory.comp_apply, Functor.id_map] at hn'
  have ha : (eG.hom.app ⊤) a = m := by simpa [a] using hΓ m
  rw [ha] at hn'
  exact hn'.symm

/-- The first step of the outer half of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`: the pullback to `Spec Γ(Y, V)` of the
restriction of `F` to `Spec Γ(X, U)` is the pullback along `hV.fromSpec` of `f^*F`. -/
public def affinePullbackSectionsSquareIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    (Scheme.Modules.pullback (Spec.map (f.appLE U V hVU))).obj (F.restrict hU.fromSpec) ≅
      (Scheme.Modules.pullback hV.fromSpec).obj ((Scheme.Modules.pullback f).obj F) :=
  haveI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hmaps : Spec.map (f.appLE U V hVU) ≫ hU.fromSpec = hV.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU
  (Scheme.Modules.pullback (Spec.map (f.appLE U V hVU))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F) ≪≫
    (Scheme.Modules.pullbackComp (Spec.map (f.appLE U V hVU)) hU.fromSpec).app F ≪≫
    (Scheme.Modules.pullbackCongr hmaps).app F ≪≫
    ((Scheme.Modules.pullbackComp hV.fromSpec f).app F).symm

private theorem pullbackSection_restrictFromSpec
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hVU) ⁻¹ᵁ ⊤)
    (hUtop : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U)
    (hcomp : (⊤ : (Spec Γ(Y, V)).Opens) ≤
      (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec) ⁻¹ᵁ U)
    (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    haveI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    ((Scheme.Modules.pullbackComp (Spec.map (f.appLE U V hVU)) hU.fromSpec).hom.app F).val.app
        (op ⊤)
        (((Scheme.Modules.pullback (Spec.map (f.appLE U V hVU))).map
            ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app F)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU))
            (F.restrict hU.fromSpec) ⊤ ⊤ hg t)) =
      Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec) F U ⊤ hcomp
        (affineSectionsLinearEquiv F hU t) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  set bU := hU.fromSpec with hbU
  set g := Spec.map (f.appLE U V hVU) with hgdef
  set s := affineSectionsLinearEquiv F hU t with hs
  rw [Scheme.Modules.pullbackSection_naturality g
    ((Scheme.Modules.restrictFunctorIsoPullback bU).hom.app F) ⊤ ⊤ hg t]
  have hbUsec : ((Scheme.Modules.restrictFunctorIsoPullback bU).hom.app F).val.app (op ⊤) t =
      Scheme.Modules.pullbackSection bU F U ⊤ hUtop s :=
    restrictFunctorIsoPullback_hom_app_pullbackSection F hU hUtop t
  rw [hbUsec, Scheme.Modules.pullbackSection_comp g bU F U ⊤ ⊤ hUtop hg hcomp s]

private theorem pullbackComp_inv_pullbackSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hVtop : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V)
    (hcomp' : (⊤ : (Spec Γ(Y, V)).Opens) ≤ (hV.fromSpec ≫ f) ⁻¹ᵁ U)
    (s : F.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp hV.fromSpec f).inv.app F).val.app (op ⊤)
        (Scheme.Modules.pullbackSection (hV.fromSpec ≫ f) F U ⊤ hcomp' s) =
      Scheme.Modules.pullbackSection hV.fromSpec ((Scheme.Modules.pullback f).obj F) V ⊤ hVtop
        (Scheme.Modules.pullbackSection f F U V hVU s) := by
  exact (Scheme.Modules.inv_app_eq_iff ((Scheme.Modules.pullbackComp hV.fromSpec f).app F) _ _ _).2
    (Scheme.Modules.pullbackSection_comp hV.fromSpec f F U V ⊤ hVU hVtop hcomp' s)

/-- `AlgebraicGeometry.affinePullbackSectionsSquareIso` carries the pullback of a section of the
restriction of `F` to the pullback of the corresponding section of `f^*F`. -/
public theorem affinePullbackSectionsSquareIso_hom_pullbackSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hVU) ⁻¹ᵁ ⊤)
    (hVtop : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V)
    (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    (affinePullbackSectionsSquareIso f F hU hV hVU).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU))
          (F.restrict hU.fromSpec) ⊤ ⊤ hg t) =
      Scheme.Modules.pullbackSection hV.fromSpec ((Scheme.Modules.pullback f).obj F) V ⊤ hVtop
        (Scheme.Modules.pullbackSection f F U V hVU (affineSectionsLinearEquiv F hU t)) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  set bU := hU.fromSpec with hbU
  set bV := hV.fromSpec with hbV
  set g := Spec.map (f.appLE U V hVU) with hgdef
  have hmaps : g ≫ bU = bV ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU
  have hUtop : (⊤ : (Spec Γ(X, U)).Opens) ≤ bU ⁻¹ᵁ U := by
    rw [hbU, hU.fromSpec_preimage_self]
  have hcomp : (⊤ : (Spec Γ(Y, V)).Opens) ≤ (g ≫ bU) ⁻¹ᵁ U := by
    simpa only [Scheme.Hom.comp_preimage] using
      (le_trans hg (Scheme.Hom.preimage_mono g hUtop))
  have hcomp' : (⊤ : (Spec Γ(Y, V)).Opens) ≤ (bV ≫ f) ⁻¹ᵁ U := by rw [← hmaps]; exact hcomp
  set s := affineSectionsLinearEquiv F hU t with hs
  change (((Scheme.Modules.pullbackComp bV f).app F).inv.val.app (op ⊤)
      (((Scheme.Modules.pullbackCongr hmaps).app F).hom.val.app (op ⊤)
      (((Scheme.Modules.pullbackComp g bU).app F).hom.val.app (op ⊤)
      (((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback bU).app F).hom).val.app (op ⊤)
      (Scheme.Modules.pullbackSection g (F.restrict bU) ⊤ ⊤ hg t))))) = _
  simp only [Iso.app_hom, Iso.app_inv]
  rw [pullbackSection_restrictFromSpec f F hU hVU hg hUtop hcomp t,
    Scheme.Modules.pullbackSection_congr hmaps F U ⊤ hcomp hcomp' s,
    pullbackComp_inv_pullbackSection f F hV hVU hVtop hcomp' s]

/-- The outer half of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`: the sections of
the pullback to `Spec Γ(Y, V)` of the restriction of `F` to `Spec Γ(X, U)` are the sections of
`f^*F` over `V`. -/
public def affinePullbackSectionsOuterIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(Y, V))).obj
        ((Scheme.Modules.pullback (Spec.map (f.appLE U V hVU))).obj
          (F.restrict hU.fromSpec)) ≅
      ModuleCat.of Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  (moduleSpecΓFunctor (R := CommRingCat.of Γ(Y, V))).mapIso
      (affinePullbackSectionsSquareIso f F hU hV hVU) ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(Y, V))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app
        ((Scheme.Modules.pullback f).obj F)).symm ≪≫
    (affineSectionsLinearEquiv ((Scheme.Modules.pullback f).obj F) hV).toModuleIso

/-- The outer half of the base-change comparison carries the pullback of a section of the
restriction of `F` to the pullback of the corresponding section of `F` over `U`. -/
public theorem affinePullbackSectionsOuterIso_hom_pullbackSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hVU) ⁻¹ᵁ ⊤)
    (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    (affinePullbackSectionsOuterIso f F hU hV hVU).hom
        (Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU))
          (F.restrict hU.fromSpec) ⊤ ⊤ hg t) =
      Scheme.Modules.pullbackSection f F U V hVU (affineSectionsLinearEquiv F hU t) := by
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hVtop : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    rw [hV.fromSpec_preimage_self]
  change (affineSectionsLinearEquiv ((Scheme.Modules.pullback f).obj F) hV)
    (((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).inv.app
      ((Scheme.Modules.pullback f).obj F)).val.app (op ⊤)
      ((affinePullbackSectionsSquareIso f F hU hV hVU).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU))
          (F.restrict hU.fromSpec) ⊤ ⊤ hg t))) = _
  rw [affinePullbackSectionsSquareIso_hom_pullbackSection f F hU hV hVU hg hVtop t]
  exact affineSectionsLinearEquiv_pullbackSection ((Scheme.Modules.pullback f).obj F) hV hVtop _

/-- The inner half of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
public def affinePullbackSectionsInnerIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U) :
    (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
      (moduleSpecΓFunctor (R := CommRingCat.of Γ(Y, V))).obj
        ((Scheme.Modules.pullback (Spec.map (f.appLE U V hVU))).obj
          (F.restrict hU.fromSpec)) :=
  haveI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  (ModuleCat.extendScalars (f.appLE U V hVU).hom).mapIso
      (affineSectionsLinearEquiv F hU).toModuleIso.symm ≪≫
    quasicoherentPullbackSectionsIso (CommRingCat.of Γ(X, U)) (CommRingCat.of Γ(Y, V))
      (f.appLE U V hVU) (F.restrict hU.fromSpec)

/-- The inner half of the base-change comparison sends `1 ⊗ a` to the pullback of the section
of the restriction of `F` corresponding to `a`. -/
public theorem affinePullbackSectionsInnerIso_hom_one_tmul
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hVU) ⁻¹ᵁ ⊤) (a : Γ(F, U)) :
    (affinePullbackSectionsInnerIso f F hU hVU).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) =
      Scheme.Modules.pullbackSection (Spec.map (f.appLE U V hVU))
        (F.restrict hU.fromSpec) ⊤ ⊤ hg ((affineSectionsLinearEquiv F hU).symm a) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  change (quasicoherentPullbackSectionsIso (CommRingCat.of Γ(X, U)) (CommRingCat.of Γ(Y, V))
      (f.appLE U V hVU) (F.restrict hU.fromSpec)).hom
      ((ModuleCat.extendScalars (f.appLE U V hVU).hom).map
        (affineSectionsLinearEquiv F hU).toModuleIso.symm.hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a)) = _
  rw [ModuleCat.ExtendScalars.map_tmul,
    Scheme.Modules.pullbackSection_top (Spec.map (f.appLE U V hVU))
      (F.restrict hU.fromSpec) hg ((affineSectionsLinearEquiv F hU).symm a)]
  exact quasicoherentPullbackSectionsIso_hom_one_tmul (CommRingCat.of Γ(X, U))
    (CommRingCat.of Γ(Y, V)) (f.appLE U V hVU) (F.restrict hU.fromSpec)
    ((affineSectionsLinearEquiv F hU).toModuleIso.symm.hom a)

/-- **The sections of the pullback over a compatible pair of affine opens.** For `U ⊆ X` and
`V ⊆ Y` affine with `V ≤ f⁻¹U` and `F` quasi-coherent, extending the scalars of `Γ(F, U)` along
`f.appLE U V` gives the sections of `f^*F` over `V`. -/
public def affinePullbackSectionsBaseChangeIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
      ModuleCat.of Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
  affinePullbackSectionsInnerIso f F hU hVU ≪≫ affinePullbackSectionsOuterIso f F hU hV hVU

/-- **The normalisation.** `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` sends
`1 ⊗ a` to the pullback of the section `a`. -/
public theorem affinePullbackSectionsBaseChangeIso_one_tmul
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (a : Γ(F, U)) :
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) =
      Scheme.Modules.pullbackSection f F U V hVU a := by
  have hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hVU) ⁻¹ᵁ ⊤ := by simp
  change (affinePullbackSectionsOuterIso f F hU hV hVU).hom
    ((affinePullbackSectionsInnerIso f F hU hVU).hom
      ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a)) = _
  rw [affinePullbackSectionsInnerIso_hom_one_tmul f F hU hVU hg a,
    affinePullbackSectionsOuterIso_hom_pullbackSection f F hU hV hVU hg _,
    (affineSectionsLinearEquiv F hU).apply_symm_apply]

/-- A morphism out of an extension of scalars carries `t ⊗ m` to `t` times its value on
`1 ⊗ m`, being semilinear over the larger ring.  Stated on bare variables: the rewriting of
`ModuleCat.ExtendScalars.smul_tmul` is done here, once, rather than against the scheme-theoretic
spelling of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`'s source. -/
private theorem extendScalars_hom_tmul {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (ψ : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) (t : S) (m : M) :
    ψ (t ⊗ₜ[R, φ.hom] m) = t • ψ ((1 : S) ⊗ₜ[R, φ.hom] m) := by
  let := φ.hom.toAlgebra
  have hs : t ⊗ₜ[R, φ.hom] m = t • ((1 : S) ⊗ₜ[R, φ.hom] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (fun z => ψ z) hs).trans (ψ.hom.map_smul t _)

/-- **The normalisation on an arbitrary pure tensor.**
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` sends `t ⊗ a` to `t` times the pullback
of the section `a`.

This is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` together with
`Γ(Y, V)`-linearity of the comparison, `t ⊗ a` being `t • (1 ⊗ a)`.  It is the form in which a
map out of the base change that is only known to be additive can be identified with the
comparison: an additive map agreeing with it on every pure tensor agrees with it, whereas
agreement on `1 ⊗ a` alone identifies the two only after `Γ(Y, V)`-linearity of the other map
has been established separately. -/
public theorem affinePullbackSectionsBaseChangeIso_tmul
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (t : Γ(Y, V)) (a : Γ(F, U)) :
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        (t ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) =
      t • (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) :=
  extendScalars_hom_tmul (f.appLE U V hVU)
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom t a

/-- **The base-change comparison is natural in the module.** A morphism `φ : F ⟶ G` of
quasi-coherent `𝒪_X`-modules acts on the two sides of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` by extension of scalars of its map on
sections over `U` and by its map on sections of the pullbacks over `V`, and the comparison
intertwines the two. Both sides are determined by their values on `1 ⊗ a`, where the square is
the naturality of `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
public theorem affinePullbackSectionsBaseChangeIso_natural
    {X Y : Scheme.{u}} (f : Y ⟶ X) {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫
        ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap ((Scheme.Modules.pullback f).map φ) V) =
      (ModuleCat.extendScalars (f.appLE U V hVU).hom).map
          (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ U)) ≫
        (affinePullbackSectionsBaseChangeIso f G hU hV hVU).hom := by
  refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun a => ?_
  have hL := affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a
  have hNat := Scheme.Modules.pullbackSection_naturality f φ U V hVU a
  have hM := ModuleCat.ExtendScalars.map_tmul (f.appLE U V hVU).hom
    (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ U)) (1 : Γ(Y, V)) a
  have hR := affinePullbackSectionsBaseChangeIso_one_tmul f G hU hV hVU
    (Scheme.Modules.sectionsLinearMap φ U a)
  exact (congrArg (fun z =>
      Scheme.Modules.sectionsLinearMap ((Scheme.Modules.pullback f).map φ) V z) hL).trans
    (hNat.trans (hR.symm.trans (congrArg _ hM.symm)))

end AlgebraicGeometry

end
