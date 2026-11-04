module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Support
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv

/-!
# Stalks of a restriction and of a direct image along an open immersion: support and depth

Let `f : X ⟶ Y` be an open immersion of schemes and `M` an `𝒪_Y`-module. Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` identifies the stalk of `M.restrict f`
at `x` with the stalk of `M` at `f x` as abelian groups, and `Scheme.Hom.stalkMap` identifies
`𝒪_{Y, f x}` with `𝒪_{X, x}` as rings. This file records that the first identification is
semilinear over the second, and draws the two consequences that read a pointwise condition on a
module through a restriction: the support of `M.restrict f` is the preimage of the support of
`M`, and the depth of the stalk of `M.restrict f` at `x` over `𝒪_{X, x}` is the depth of the
stalk of `M` at `f x` over `𝒪_{Y, f x}`. The depth statement is what licenses reading
`depth_{𝒪_{X, x}}(ℱ_x)` on an open subscheme: for `ℱ` a module on an open `U ⊆ X` and `x ∈ U`,
the depth computed on `U` and the depth computed after restricting `U` further to an open
neighbourhood of `x` agree.

The second half of the file does the same for the direct image. For an arbitrary morphism of
schemes `f : X ⟶ Y` and an `𝒪_X`-module `F`, the sections of `f_*F` over an open `V` of `Y` are
the sections of `F` over `f⁻¹V`, with a section of `𝒪_Y` acting through `f^♯`, so the germ map
`(f_*F)_{f x} ⟶ F_x` is defined with no hypothesis on `f`; it is semilinear over `f^♯_x`, and
bijective as soon as the underlying map of `f` is inducing. Along an open immersion the same two
consequences follow: `f x` lies in the support of `f_*F` exactly when `x` lies in the support of
`F`, and the two stalks have the same depth.

That direct-image form is the one that reads a pointwise condition on a module across an
*isomorphism* of schemes, such as a transport along `AlgebraicGeometry.Scheme.isoSpec` or
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`, where the module is carried forward rather than
pulled back; the restriction statement does not apply to it, the two functors being different.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.instModuleStalk`: the module structure of a stalk over the
  stalk of the structure sheaf, with the unification Mathlib's instance leaves to the caller
  already performed.
* `AlgebraicGeometry.Scheme.Modules.pushforwardStalkHom`: the germ map `(f_*F)_{f x} ⟶ F_x` on
  abelian stalks, and `AlgebraicGeometry.Scheme.Modules.pushforwardStalkAddEquiv` the same map
  as an additive isomorphism for `f` with inducing underlying map.

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictStalkAddEquiv_smul`: the stalk comparison
  isomorphism is semilinear over `f.stalkMap x`.
* `AlgebraicGeometry.Scheme.Modules.supportDim_stalk_congr` and
  `AlgebraicGeometry.Scheme.Modules.supportDim_stalk_restrict`: the same two statements for the
  dimension of the support of a stalk.
* `AlgebraicGeometry.Scheme.Modules.depth_stalk_congr`: isomorphic modules on a scheme have
  stalks of the same depth.
* `AlgebraicGeometry.Scheme.Modules.supp_restrict`: `supp (M.restrict f) = f ⁻¹' supp M`.
* `AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict`: the depths of the two stalks agree.
* `AlgebraicGeometry.Scheme.Modules.pushforwardStalkHom_smul`: the direct-image comparison is
  semilinear over `f.stalkMap x`.
* `AlgebraicGeometry.Scheme.Modules.mem_supp_pushforward_iff`: `f x ∈ supp (f_*F) ↔ x ∈ supp F`.
* `AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq_of_isOpenImmersion` and
  `AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq`: the depth of the stalk of
  `f_*F` at `f x` is the depth of the stalk of `F` at `x`, for `f` an open immersion and for
  `f` the forward map of an isomorphism of schemes.

## Implementation notes

Mathlib endows the stalk of a presheaf of modules with a module structure over the stalk of the
sheaf of rings, but for a module on a scheme the two presheaves involved are related by a
`forget₂` that instance resolution does not see through at reducible transparency.
`instModuleStalk` is that same instance with the unification performed once, so that `•` and
`Module.depth` read on stalks without a local `letI`.

The semilinearity is proved on germs. Every element of a stalk is the germ of a section over
some open neighbourhood, and the two neighbourhoods involved — one in `X` for the module
element, one in `Y` for the scalar — are shrunk to a single `U : X.Opens` with the scalar read
over `f ''ᵁ U`. There `Scheme.Modules.restrictAppIso` identifies `Γ(M.restrict f, U)` with
`Γ(M, f ''ᵁ U)`, and the two actions differ by `f.appIso U`, which is
`Scheme.Modules.smul_restrictAppIso_hom_apply`; the germ of `(f.appIso U).hom s` is the image
of the germ of `s` under `f.stalkMap x`, because `Scheme.Hom.appIso_hom` factors `f.appIso U`
through `f.app (f ''ᵁ U)`. The depth statement is then
`Module.depth_eq_of_semilinearEquiv`, with the maximal ideal of `𝒪_{X, x}` carried onto that of
`𝒪_{Y, f x}` by `IsLocalRing.map_ringEquiv_maximalIdeal`.

The direct image needs no comparison of sections: the underlying presheaf of `f_*F` *is* the
topological pushforward of the underlying presheaf of `F`, so Mathlib's
`TopCat.Presheaf.stalkPushforward` states the comparison with no transport, and the scalar
action on the sections of `f_*F` *is* the action through `f^♯` by definition; the one `map_smul`
to check is the single germ computation `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`.

Its depth statement asks for an open immersion and not merely an inducing map. Bijectivity of
the comparison needs only that the underlying map is inducing
(`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`), and that is all the
support statement uses; the depth statement additionally needs `f^♯_x` to be invertible, the two
depths being taken over *different* rings and `Module.depth` transporting along a semilinear
isomorphism only when the ring map is one. An open immersion supplies both.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk of a module on a scheme is a module over the stalk of the structure sheaf. This
is Mathlib's instance on the stalk of a presheaf of modules, with the `forget₂` that instance
resolution does not see through supplied. -/
public instance instModuleStalk {X : Scheme.{u}} (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

section Congr

variable {X : Scheme.{u}} {F G : X.Modules}

/-- The stalk at `x` of a morphism of modules on a scheme, as a map of abelian groups. -/
public abbrev stalkMapOfHom (φ : F ⟶ G) (x : X) :
    F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((toPresheaf X).map φ)

/-- A morphism of modules on a scheme is linear on stalks over the stalk of the structure
sheaf: both the scalar and the module element are germs, and the morphism is linear on
sections. -/
public lemma stalkMapOfHom_smul (φ : F ⟶ G) (x : X) (r : X.presheaf.stalk x)
    (z : F.presheaf.stalk x) :
    (stalkMapOfHom φ x) (r • z) = r • (stalkMapOfHom φ x) z := by
  obtain ⟨U₁, hxU₁, r₁, hr₁⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨U, hUU₁, hxU, t, hz⟩ := TopCat.Presheaf.exists_le_germ_eq F.presheaf z hxU₁
  set r₀ : Γ(X, U) := X.presheaf.map (homOfLE hUU₁).op r₁ with hr₀
  have hr : X.presheaf.germ U x hxU r₀ = r := by
    rw [hr₀, X.presheaf.germ_res_apply (homOfLE hUU₁) x hxU, hr₁]
  have hgermF : ∀ w : Γ(F, U), (stalkMapOfHom φ x) (F.presheaf.germ U x hxU w) =
      G.presheaf.germ U x hxU ((φ.val.app (op U)).hom w) := fun w =>
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU ((toPresheaf X).map φ) w
  have hsmulF : F.presheaf.germ U x hxU (r₀ • t) =
      X.presheaf.germ U x hxU r₀ • F.presheaf.germ U x hxU t :=
    PresheafOfModules.germ_smul F.val x U hxU r₀ t
  set w : Γ(G, U) := (φ.val.app (op U)).hom t with hw
  have hlin : (φ.val.app (op U)).hom (r₀ • t) = r₀ • w :=
    (φ.val.app (op U)).hom.map_smul r₀ t
  have hsmulG : G.presheaf.germ U x hxU (r₀ • w) =
      X.presheaf.germ U x hxU r₀ • G.presheaf.germ U x hxU w :=
    PresheafOfModules.germ_smul G.val x U hxU r₀ w
  rw [← hr, ← hz, ← hsmulF, hgermF, hgermF, hlin, ← hw]
  exact hsmulG

/-- Isomorphic modules on a scheme have stalks of the same depth. -/
public lemma depth_stalk_congr (φ : F ≅ G) (x : X) :
    Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x) =
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (G.presheaf.stalk x) := by
  set ψ : F.presheaf.stalk x ≃+ G.presheaf.stalk x :=
    ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso φ).addCommGroupIsoToAddEquiv
  have hsm : ∀ (r : X.presheaf.stalk x) (z : F.presheaf.stalk x),
      ψ (r • z) = (RingEquiv.refl (X.presheaf.stalk x)) r • ψ z := fun r z =>
    stalkMapOfHom_smul φ.hom x r z
  rw [Module.depth_eq_of_semilinearEquiv (RingEquiv.refl (X.presheaf.stalk x))
    (maximalIdeal (X.presheaf.stalk x)) ψ hsm]
  congr 1
  simp

/-- Isomorphic modules on a scheme have stalks whose supports have the same dimension. -/
public lemma supportDim_stalk_congr (φ : F ≅ G) (x : X) :
    Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x) =
      Module.supportDim (X.presheaf.stalk x) (G.presheaf.stalk x) :=
  Module.supportDim_eq_of_semilinearEquiv (RingEquiv.refl (X.presheaf.stalk x))
    ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso φ).addCommGroupIsoToAddEquiv
    fun r z => stalkMapOfHom_smul φ.hom x r z

end Congr

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)

/-- The comparison isomorphism of stalks under restriction, as an isomorphism of abelian
groups. -/
public def restrictStalkAddEquiv (x : X) :
    (M.restrict f).presheaf.stalk x ≃+ M.presheaf.stalk (f.base x) :=
  ((restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv

/-- `restrictStalkAddEquiv` is the stalk comparison of `restrictStalkNatIso` on elements. -/
@[simp]
public lemma restrictStalkAddEquiv_apply (x : X) (z : (M.restrict f).presheaf.stalk x) :
    restrictStalkAddEquiv f M x z = ((restrictStalkNatIso f x).hom.app M).hom z := rfl

/-- The germ of the stalk comparison isomorphism: it takes the germ at `x` of a section of
`M.restrict f` over `U` to the germ at `f x` of the corresponding section of `M` over
`f ''ᵁ U`. -/
public lemma restrictStalkAddEquiv_germ (x : X) (U : X.Opens) (hxU : x ∈ U)
    (w : Γ(M.restrict f, U)) :
    restrictStalkAddEquiv f M x ((M.restrict f).presheaf.germ U x hxU w) =
      M.presheaf.germ (f ''ᵁ U) (f.base x) ⟨x, hxU, rfl⟩ ((M.restrictAppIso f U).hom w) :=
  ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app f x M hxU) w

/-- The germ over `U` of the section of `𝒪_X` corresponding to a section of `𝒪_Y` over
`f ''ᵁ U` is the image under `f.stalkMap x` of the germ of that section. -/
public lemma germ_appIso_hom_eq_stalkMap (x : X) (U : X.Opens) (hxU : x ∈ U)
    (s : Γ(Y, f ''ᵁ U)) :
    X.presheaf.germ U x hxU ((f.appIso U).hom s) =
      (f.stalkMap x).hom (Y.presheaf.germ (f ''ᵁ U) (f.base x) ⟨x, hxU, rfl⟩ s) := by
  rw [Scheme.Hom.germ_stalkMap_apply f (f ''ᵁ U) x ⟨x, hxU, rfl⟩ s, Scheme.Hom.appIso_hom f U]
  show X.presheaf.germ U x hxU
      (X.presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq f U).symm).op
        (f.app (f ''ᵁ U) s)) = _
  rw [X.presheaf.germ_res_apply (eqToHom (Scheme.Hom.preimage_image_eq f U).symm) x hxU]

/-- Semilinearity of the stalk comparison isomorphism, read on germs. -/
public lemma restrictStalkAddEquiv_germ_smul (x : X) (U : X.Opens) (hxU : x ∈ U)
    (s : Γ(Y, f ''ᵁ U)) (t : Γ(M.restrict f, U)) :
    restrictStalkAddEquiv f M x (X.presheaf.germ U x hxU ((f.appIso U).hom s) •
          (M.restrict f).presheaf.germ U x hxU t) =
      Y.presheaf.germ (f ''ᵁ U) (f.base x) ⟨x, hxU, rfl⟩ s •
        restrictStalkAddEquiv f M x ((M.restrict f).presheaf.germ U x hxU t) := by
  have hsmul : (M.restrict f).presheaf.germ U x hxU (((f.appIso U).hom s) • t) =
      X.presheaf.germ U x hxU ((f.appIso U).hom s) •
        (M.restrict f).presheaf.germ U x hxU t :=
    PresheafOfModules.germ_smul (M.restrict f).val x U hxU _ t
  have hres : (M.restrictAppIso f U).hom (((f.appIso U).hom s) • t) =
      s • (M.restrictAppIso f U).hom t := by
    rw [smul_restrictAppIso_hom_apply f M U ((f.appIso U).hom s) t]
    congr 1
    exact congrArg (fun g => g s) (congrArg ConcreteCategory.hom (f.appIso U).hom_inv_id)
  rw [← hsmul, restrictStalkAddEquiv_germ, restrictStalkAddEquiv_germ, hres]
  exact PresheafOfModules.germ_smul M.val (f.base x) (f ''ᵁ U) ⟨x, hxU, rfl⟩ s
    ((M.restrictAppIso f U).hom t)

/-- The stalk comparison isomorphism is semilinear over `f.stalkMap x`. -/
public lemma restrictStalkAddEquiv_smul (x : X) (s : Y.presheaf.stalk (f.base x))
    (z : (M.restrict f).presheaf.stalk x) :
    restrictStalkAddEquiv f M x ((f.stalkMap x).hom s • z) =
      s • restrictStalkAddEquiv f M x z := by
  obtain ⟨W, hfxW, s₁, hs₁⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf s
  obtain ⟨U, hUW, hxU, t, hz⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (M.restrict f).presheaf z (V := f ⁻¹ᵁ W) hfxW
  have hUW' : f ''ᵁ U ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hUW hy
  set s₀ : Γ(Y, f ''ᵁ U) := Y.presheaf.map (homOfLE hUW').op s₁ with hs
  have hsg : Y.presheaf.germ (f ''ᵁ U) (f.base x) ⟨x, hxU, rfl⟩ s₀ = s := by
    rw [hs, Y.presheaf.germ_res_apply (homOfLE hUW') (f.base x) ⟨x, hxU, rfl⟩, hs₁]
  rw [← hz, ← hsg, ← germ_appIso_hom_eq_stalkMap f x U hxU s₀]
  exact restrictStalkAddEquiv_germ_smul f M x U hxU s₀ t

/-- The support of a restriction is the preimage of the support. -/
public lemma supp_restrict :
    SheafOfModules.supp (M.restrict f) = f.base ⁻¹' SheafOfModules.supp M := by
  ext x
  show x ∈ SheafOfModules.supp (M.restrict f) ↔ f.base x ∈ SheafOfModules.supp M
  refine ((SheafOfModules.mem_supp_iff_nontrivial_stalk (M.restrict f) x).trans ?_).trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk M (f.base x)).symm
  exact Equiv.nontrivial_congr (restrictStalkAddEquiv f M x).toEquiv

/-- The stalk comparison isomorphism is semilinear over the inverse of the ring isomorphism
`f.stalkMap x`. -/
private lemma restrictStalkAddEquiv_smul_symm (x : X) (r : X.presheaf.stalk x)
    (z : (M.restrict f).presheaf.stalk x) :
    restrictStalkAddEquiv f M x (r • z) =
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm r • restrictStalkAddEquiv f M x z := by
  have hz := restrictStalkAddEquiv_smul f M x
    ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm r) z
  rwa [show (f.stalkMap x).hom
      ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm r) = r from
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.apply_symm_apply r] at hz

/-- The depth of a stalk is unchanged by restricting along an open immersion. -/
public lemma depth_stalk_restrict (x : X) :
    Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        ((M.restrict f).presheaf.stalk x) =
      Module.depth (Y.presheaf.stalk (f.base x)) (maximalIdeal (Y.presheaf.stalk (f.base x)))
        (M.presheaf.stalk (f.base x)) := by
  rw [Module.depth_eq_of_semilinearEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm
    (maximalIdeal (X.presheaf.stalk x)) (restrictStalkAddEquiv f M x)
    (restrictStalkAddEquiv_smul_symm f M x)]
  congr 1
  exact map_ringEquiv_maximalIdeal _

/-- The dimension of the support of a stalk is unchanged by restricting along an open
immersion, by the same semilinear comparison as `depth_stalk_restrict`. -/
public lemma supportDim_stalk_restrict (x : X) :
    Module.supportDim (X.presheaf.stalk x) ((M.restrict f).presheaf.stalk x) =
      Module.supportDim (Y.presheaf.stalk (f.base x)) (M.presheaf.stalk (f.base x)) :=
  Module.supportDim_eq_of_semilinearEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm (restrictStalkAddEquiv f M x)
    (restrictStalkAddEquiv_smul_symm f M x)

/-! ### The stalk of a direct image -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (x : X)

/-- The comparison `(f_*F)_{f x} ⟶ F_x` on abelian stalks, Mathlib's
`TopCat.Presheaf.stalkPushforward` of the underlying presheaf of abelian groups. The underlying
presheaf of `f_*F` *is* the topological pushforward of that of `F`, so this needs no
transport. -/
public def pushforwardStalkHom :
    ((pushforward f).obj F).presheaf.stalk (f.base x) ⟶ F.presheaf.stalk x :=
  TopCat.Presheaf.stalkPushforward Ab.{u} f.base F.presheaf x

/-- The comparison is the germ map: it carries the germ at `f x` of a section of `f_*F` over an
open `V` of `Y` — equivalently of `F` over `f⁻¹V` — to the germ at `x` of that same section. -/
public lemma pushforwardStalkHom_germ (V : Y.Opens) (hx : f.base x ∈ V)
    (m : Γ((pushforward f).obj F, V)) :
    pushforwardStalkHom f F x
        (((pushforward f).obj F).presheaf.germ V (f.base x) hx m) =
      F.presheaf.germ (f ⁻¹ᵁ V) x hx m :=
  TopCat.Presheaf.stalkPushforward_germ_apply Ab.{u} f.base F.presheaf V x hx m

/-- The comparison is semilinear over `f.stalkMap x`. A scalar `r` and an element `m` of the
stalk of `f_*F` are germs over a common open `V` of `Y`; the action on the sections of `f_*F`
over `V` is the action of `Γ(X, f⁻¹V)` through `f^♯` by definition, and the germ at `x` of
`f^♯ r` is the image of the germ of `r` at `f x` under `f.stalkMap x`. -/
public lemma pushforwardStalkHom_smul (r : Y.presheaf.stalk (f.base x))
    (m : ((pushforward f).obj F).presheaf.stalk (f.base x)) :
    pushforwardStalkHom f F x (r • m) =
      (f.stalkMap x).hom r • pushforwardStalkHom f F x m := by
  obtain ⟨V₁, hV₁, r₁, hr₁⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  obtain ⟨V, hVV₁, hxV, mV, hm⟩ :=
    TopCat.Presheaf.exists_le_germ_eq ((pushforward f).obj F).presheaf m hV₁
  set rV : Γ(Y, V) := Y.presheaf.map (homOfLE hVV₁).op r₁ with hrV
  have hr : Y.presheaf.germ V (f.base x) hxV rV = r := by
    rw [hrV, Y.presheaf.germ_res_apply (homOfLE hVV₁) (f.base x) hxV, hr₁]
  have hsrc : ((pushforward f).obj F).presheaf.germ V (f.base x) hxV (rV • mV) =
      Y.presheaf.germ V (f.base x) hxV rV •
        ((pushforward f).obj F).presheaf.germ V (f.base x) hxV mV :=
    PresheafOfModules.germ_smul (R := Y.presheaf) ((pushforward f).obj F).val
      (f.base x) V hxV rV mV
  rw [← hr, ← hm, ← hsrc, pushforwardStalkHom_germ, pushforwardStalkHom_germ,
    Scheme.Hom.germ_stalkMap_apply f V x hxV rV]
  exact PresheafOfModules.germ_smul (R := X.presheaf) F.val x (f ⁻¹ᵁ V) hxV ((f.app V) rV) mV

/-- The comparison is an additive isomorphism when the underlying map of `f` is inducing, by
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`. -/
public def pushforwardStalkAddEquiv (hf : Topology.IsInducing f.base) :
    ((pushforward f).obj F).presheaf.stalk (f.base x) ≃+ F.presheaf.stalk x :=
  have : IsIso (pushforwardStalkHom f F x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{u} hf F.presheaf x
  AddEquiv.ofBijective (ConcreteCategory.hom (pushforwardStalkHom f F x))
    (ConcreteCategory.bijective_of_isIso (pushforwardStalkHom f F x))

/-- `pushforwardStalkAddEquiv` is the germ map `pushforwardStalkHom` on elements. -/
@[simp]
public lemma pushforwardStalkAddEquiv_apply (hf : Topology.IsInducing f.base)
    (m : ((pushforward f).obj F).presheaf.stalk (f.base x)) :
    pushforwardStalkAddEquiv f F x hf m = pushforwardStalkHom f F x m := rfl

/-- The support of a direct image, over the image of `f`: for `f` with inducing underlying map,
`f x` lies in the support of `f_*F` exactly when `x` lies in the support of `F`, the two stalks
being isomorphic as abelian groups. -/
public lemma mem_supp_pushforward_iff (hf : Topology.IsInducing f.base) :
    f.base x ∈ SheafOfModules.supp ((pushforward f).obj F) ↔ x ∈ SheafOfModules.supp F :=
  ((SheafOfModules.mem_supp_iff_nontrivial_stalk ((pushforward f).obj F) (f.base x)).trans
      (Equiv.nontrivial_congr (pushforwardStalkAddEquiv f F x hf).toEquiv)).trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).symm

/-- The depth of a stalk is unchanged by taking the direct image along an open immersion: over
`𝒪_{Y, f x}` the stalk of `f_*F` at `f x` has the same depth along the maximal ideal as the
stalk of `F` at `x` has over `𝒪_{X, x}`. The comparison is an `f.stalkMap x`-semilinear
isomorphism, and `f.stalkMap x` carries the maximal ideal to the maximal ideal. -/
public lemma depth_stalk_pushforward_eq_of_isOpenImmersion [IsOpenImmersion f] :
    Module.depth (Y.presheaf.stalk (f.base x)) (maximalIdeal (Y.presheaf.stalk (f.base x)))
        (((pushforward f).obj F).presheaf.stalk (f.base x)) =
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) := by
  have hf : Topology.IsInducing f.base := f.isOpenEmbedding.isInducing
  set e : Y.presheaf.stalk (f.base x) ≃+* X.presheaf.stalk x :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  rw [Module.depth_eq_of_semilinearEquiv e (maximalIdeal (Y.presheaf.stalk (f.base x)))
    (pushforwardStalkAddEquiv f F x hf) (fun r m => pushforwardStalkHom_smul f F x r m)]
  congr 1
  exact map_ringEquiv_maximalIdeal e

end Pushforward

/-! ### The stalk of a direct image along an isomorphism of schemes -/

/-- A module-level stalk comparison across an isomorphism of schemes: for `a : X ≅ Y` the stalk
of `a_*F` at `a x` has the same depth over `𝒪_{Y, a x}` as the stalk of `F` at `x` has over
`𝒪_{X, x}`. An isomorphism of schemes is an open immersion, so this is
`depth_stalk_pushforward_eq_of_isOpenImmersion`. -/
public lemma depth_stalk_pushforward_eq {X Y : Scheme.{u}} (a : X ≅ Y) (F : X.Modules) (x : X) :
    Module.depth (Y.presheaf.stalk (a.hom.base x))
        (maximalIdeal (Y.presheaf.stalk (a.hom.base x)))
        (((pushforward a.hom).obj F).presheaf.stalk (a.hom.base x)) =
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) :=
  depth_stalk_pushforward_eq_of_isOpenImmersion a.hom F x

/-- The support of a direct image along an isomorphism of schemes, at a point of the source. -/
public lemma mem_supp_pushforward_iso_iff {X Y : Scheme.{u}} (a : X ≅ Y) (F : X.Modules)
    (x : X) :
    a.hom.base x ∈ SheafOfModules.supp ((pushforward a.hom).obj F) ↔
      x ∈ SheafOfModules.supp F :=
  mem_supp_pushforward_iff a.hom F x a.hom.isOpenEmbedding.isInducing

end AlgebraicGeometry.Scheme.Modules

end
