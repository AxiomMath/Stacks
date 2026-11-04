module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom

/-!
# Naturality of the affine internal-Hom comparison

For a finitely presented module `M` over a commutative ring `R` and an arbitrary `R`-module `N`,
`AlgebraicGeometry.internalHomTildeIso` identifies the internal Hom of `M̃` and `Ñ` on `Spec R`
with the associated sheaf of `Hom_R(M, N)`. This identification is natural in both arguments, so it
is the canonical isomorphism of [Stacks, Tag 01I8].

## Main definitions

* `ModuleCat.homPostcomp`: post-composition with `u : N ⟶ N'`, as a map of the modules of
  homomorphisms `(M ⟶ N) ⟶ (M ⟶ N')`.
* `ModuleCat.homPrecomp`: pre-composition with `β : M' ⟶ M`, as a map of the modules of
  homomorphisms `(M ⟶ N) ⟶ (M' ⟶ N)`.

## Main results

* `AlgebraicGeometry.internalHomTildeIso_natural_right`: the comparison is natural in the
  target module. The map of internal Homs is any morphism exhibited as post-composition with
  `tilde.map u` by `SheafHom.IsPostcomp`, a property that determines it uniquely.
* `AlgebraicGeometry.internalHomTildeIso_natural_left`: the comparison is contravariantly
  natural in the source module, with the map of internal Homs exhibited as pre-composition with
  `tilde.map β` by `SheafHom.IsPrecomp`.

## Implementation notes

The internal Homs are represented by `SheafHom` packages, which carry no functoriality of their
own: a package for `(M̃, Ñ)` and a package for `(M̃, Ñ')` are unrelated objects. The morphism
between them is therefore taken as a hypothesis, together with the characterization
`SheafHom.IsPostcomp` (respectively `SheafHom.IsPrecomp`) that identifies it as the
post-composition (respectively pre-composition) map on sections over every open. By
`SheafHom.restrict_natural` that characterization pins the morphism down, so quantifying over
it is a statement about the canonical map.

Both sides of each square are morphisms out of a `tilde`, so they are compared through the
`tilde`-global-sections adjunction, which is a bijection on such morphisms; since
`AlgebraicGeometry.tilde.toOpen _ ⊤` is an isomorphism, that reduces each square to an identity
between global sections. There the characterization of the comparison's inverse,
`AlgebraicGeometry.InternalHomTildeIso.inv_app_toOpen`, turns both sides into sheaf maps induced
by `tilde.map`, and the required identity is the defining property of `IsPostcomp`
(respectively `IsPrecomp`) at `⊤` combined with functoriality of `tilde`.

The comparison itself is produced by a tactic block and is not reducible, so nothing below
unfolds it: every step goes through `inv_app_toOpen`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace ModuleCat

/-- Post-composition with `u : N ⟶ N'`, as an `R`-linear map from the module of homomorphisms
`M ⟶ N` to the module of homomorphisms `M ⟶ N'`. -/
noncomputable def homPostcomp {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (u : N ⟶ N') :
    ModuleCat.of R (M ⟶ N) ⟶ ModuleCat.of R (M ⟶ N') :=
  ModuleCat.ofHom (ModuleCat.homLinearEquiv.symm.toLinearMap ∘ₗ
    LinearMap.llcomp R M N N' u.hom ∘ₗ ModuleCat.homLinearEquiv.toLinearMap)

/-- `homPostcomp M u` sends `f : M ⟶ N` to `f ≫ u`. -/
@[simp]
lemma homPostcomp_hom_apply {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (u : N ⟶ N') (f : M ⟶ N) :
    (homPostcomp M u).hom f = f ≫ u := rfl

/-- Pre-composition with `β : M' ⟶ M`, as an `R`-linear map from the module of homomorphisms
`M ⟶ N` to the module of homomorphisms `M' ⟶ N`. -/
noncomputable def homPrecomp {R : CommRingCat.{u}} {M M' : ModuleCat.{u} R}
    (N : ModuleCat.{u} R) (β : M' ⟶ M) :
    ModuleCat.of R (M ⟶ N) ⟶ ModuleCat.of R (M' ⟶ N) :=
  ModuleCat.ofHom (ModuleCat.homLinearEquiv.symm.toLinearMap ∘ₗ
    LinearMap.lcomp R N β.hom ∘ₗ ModuleCat.homLinearEquiv.toLinearMap)

/-- `homPrecomp N β` sends `f : M ⟶ N` to `β ≫ f`. -/
@[simp]
lemma homPrecomp_hom_apply {R : CommRingCat.{u}} {M M' : ModuleCat.{u} R}
    (N : ModuleCat.{u} R) (β : M' ⟶ M) (f : M ⟶ N) :
    (homPrecomp N β).hom f = β ≫ f := rfl

end ModuleCat

namespace AlgebraicGeometry

/-- A morphism out of an associated sheaf is determined by its effect on the canonical global
sections, because `tilde` is left adjoint to global sections. -/
private lemma tilde_hom_ext_toOpen {R : CommRingCat.{u}} {A : ModuleCat.{u} R}
    {F : SheafOfModules (structureSheaf (Spec R).sheaf)} {φ ψ : tilde A ⟶ F}
    (h : ∀ a : A, φ.val.app (op ⊤) ((tilde.toOpen A ⊤).hom a) =
      ψ.val.app (op ⊤) ((tilde.toOpen A ⊤).hom a)) :
    φ = ψ :=
  ((tilde.adjunction (R := R)).homEquiv A F).injective (ModuleCat.hom_ext (LinearMap.ext h))

/-- An isomorphism of sheaves of modules cancels its inverse on sections. -/
private lemma iso_hom_inv_app {C : Type*} [Category C] {K : GrothendieckTopology C}
    {Rr : Sheaf K RingCat} {F G : SheafOfModules Rr} (e : F ≅ G) (U : Cᵒᵖ) (y : G.val.obj U) :
    e.hom.val.app U (e.inv.val.app U y) = y :=
  congrArg (fun φ : G ⟶ G => (ConcreteCategory.hom (φ.val.app U)) y) e.inv_hom_id

/-- The affine internal-Hom comparison is natural in the target module: a morphism of internal
Homs exhibited as post-composition with `tilde.map u` is carried to the associated sheaf of
post-composition with `u`. -/
@[stacks 01I8 "internal_hom"]
theorem internalHomTildeIso_natural_right (R : CommRingCat.{u}) (M N N' : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N))
    (H' : SheafHom (Spec R).sheaf (tilde M) (tilde N'))
    (u : N ⟶ N') (m : H.obj ⟶ H'.obj)
    (hm : SheafHom.IsPostcomp (Spec R).sheaf (tilde.map u) H H' m) :
    m ≫ (internalHomTildeIso R M N' H').iso.hom =
      (internalHomTildeIso R M N H).iso.hom ≫ tilde.map (ModuleCat.homPostcomp M u) := by
  refine (Iso.inv_comp_eq _).mp (tilde_hom_ext_toOpen (fun f => ?_))
  have hstep : m.val.app (op ⊤)
        ((internalHomTildeIso R M N H).iso.inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f)) =
      (internalHomTildeIso R M N' H').iso.inv.val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M ⟶ N')) ⊤).hom (f ≫ u)) := by
    apply (H'.sectionsEquiv ⊤).injective
    rw [(internalHomTildeIso R M N' H').inv_app_toOpen (f ≫ u), hm ⊤ _,
      (internalHomTildeIso R M N H).inv_app_toOpen f, tilde.map_comp]
    rfl
  have hright : (tilde.map (ModuleCat.homPostcomp M u)).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f) =
      (tilde.toOpen (ModuleCat.of R (M ⟶ N')) ⊤).hom (f ≫ u) :=
    congrArg (fun g => g.hom f) (tilde.toOpen_map_app (ModuleCat.homPostcomp M u) ⊤)
  have hleft : ((internalHomTildeIso R M N H).iso.inv ≫ m ≫
        (internalHomTildeIso R M N' H').iso.hom).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f) =
      (internalHomTildeIso R M N' H').iso.hom.val.app (op ⊤)
        (m.val.app (op ⊤) ((internalHomTildeIso R M N H).iso.inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f))) := rfl
  rw [hleft, hstep]
  exact (iso_hom_inv_app _ (op ⊤) _).trans hright.symm

/-- The affine internal-Hom comparison is contravariantly natural in the source module: a
morphism of internal Homs exhibited as pre-composition with `tilde.map β` is carried to the
associated sheaf of pre-composition with `β`. -/
@[stacks 01I8 "internal_hom"]
theorem internalHomTildeIso_natural_left (R : CommRingCat.{u}) (M M' N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] [Module.FinitePresentation R M']
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N))
    (H' : SheafHom (Spec R).sheaf (tilde M') (tilde N))
    (β : M' ⟶ M) (m : H.obj ⟶ H'.obj)
    (hm : SheafHom.IsPrecomp (Spec R).sheaf (tilde.map β) H H' m) :
    m ≫ (internalHomTildeIso R M' N H').iso.hom =
      (internalHomTildeIso R M N H).iso.hom ≫ tilde.map (ModuleCat.homPrecomp N β) := by
  refine (Iso.inv_comp_eq _).mp (tilde_hom_ext_toOpen (fun f => ?_))
  have hstep : m.val.app (op ⊤)
        ((internalHomTildeIso R M N H).iso.inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f)) =
      (internalHomTildeIso R M' N H').iso.inv.val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M' ⟶ N)) ⊤).hom (β ≫ f)) := by
    apply (H'.sectionsEquiv ⊤).injective
    rw [(internalHomTildeIso R M' N H').inv_app_toOpen (β ≫ f), hm ⊤ _,
      (internalHomTildeIso R M N H).inv_app_toOpen f, tilde.map_comp]
    rfl
  have hright : (tilde.map (ModuleCat.homPrecomp N β)).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f) =
      (tilde.toOpen (ModuleCat.of R (M' ⟶ N)) ⊤).hom (β ≫ f) :=
    congrArg (fun g => g.hom f) (tilde.toOpen_map_app (ModuleCat.homPrecomp N β) ⊤)
  have hleft : ((internalHomTildeIso R M N H).iso.inv ≫ m ≫
        (internalHomTildeIso R M' N H').iso.hom).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f) =
      (internalHomTildeIso R M' N H').iso.hom.val.app (op ⊤)
        (m.val.app (op ⊤) ((internalHomTildeIso R M N H).iso.inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤).hom f))) := rfl
  rw [hleft, hstep]
  exact (iso_hom_inv_app _ (op ⊤) _).trans hright.symm

end AlgebraicGeometry

end
