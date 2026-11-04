module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPushforwardFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image on quasi-coherent modules on a groupoid is right adjoint to the inverse image

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over `A` with `f : U ⟶ U'` quasi-compact and quasi-separated, with the square formed by
`R ⟶ R'` over `t`, `t'` and `U ⟶ U'` cartesian, and with `s'` flat.  **Stacks 0GPM** asserts that
the direct image functor `(ℱ, α) ↦ (f_*ℱ, f_*α)` of
`AlgebraicGeometry.Space.groupoidQuasicoherentPushforward` is right adjoint to the inverse image
functor of Stacks 0442, `AlgebraicGeometry.Space.groupoidQuasicoherentPullback`.

The source's reason is that pullback and pushforward of modules are adjoint.  What has to be
checked is that the adjunction bijection of `f^* ⊣ f_*` on the spaces of objects matches the two
compatibility conditions: a morphism `u : f^*𝒩 ⟶ ℳ` intertwines `f^*β` with `α` exactly when its
adjoint `𝒩 ⟶ f_*ℳ` intertwines `β` with `f_*α`.  Under the adjunction of the map on arrows the
second condition becomes the first, by the description of the base change map as the adjoint of
the counit of `f^* ⊣ f_*` transported across the comparison of the two composite inverse images
(`AlgebraicGeometry.Space.homEquiv_symm_moduleBaseChangeApp`).

## Main results

* `AlgebraicGeometry.Space.abstract_compatible_iff`: the correspondence of the two compatibility
  conditions, for an abstract calculus of inverse images, direct images, adjunctions, composition
  comparisons, base change maps and canonical identifications.
* `AlgebraicGeometry.Space.groupoidQuasicoherent_compatible_iff`: the same for quasi-coherent
  modules on the two groupoids.
* `AlgebraicGeometry.Space.groupoidQuasicoherentHomEquiv`: the adjunction bijection.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackPushforwardAdjunction`: **Stacks 0GPM**,
  the direct image functor is right adjoint to the inverse image functor.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackPushforwardAdjunction_unit_app_hom` and
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackPushforwardAdjunction_counit_app_hom`:
  the unit and the counit are those of `f^* ⊣ f_*` on the spaces of objects.

## Implementation notes

The correspondence is proved in `AlgebraicGeometry.Space.abstract_compatible_iff` for *variable*
families, with the inverse images, their comparisons and the canonical identifications along
equal morphisms as arguments, and instantiated once.  At the inverse images of `𝒪`-modules the
canonical identifications appear in two spellings, `AlgebraicGeometry.Space.pullbackTransport`
and the transport along an equality of functors, which the kernel can only identify by unfolding
`AlgebraicGeometry.Space.modulePullback`; in the abstract statement the relation between them is
an argument, supplied by three lemmas proved by `subst`.

## References

* [Stacks Project, Tag 0GPM](https://stacks.math.columbia.edu/tag/0GPM)
* [Stacks Project, Tag 0442](https://stacks.math.columbia.edu/tag/0442)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans transportNatTrans_app)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Transport

/-- The transport of inverse images along the reverse of an equality, followed by the canonical
identification along the equality, is the identity. -/
theorem transportNatTrans_symm_app_comp_pullbackTransport {T Z : AlgebraicSpaces B S hS}
    {a b : T ⟶ Z} (e : a = b) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    (transportNatTrans (congrArg (fun k : T ⟶ Z => modulePullback B S hS k) e).symm).app N ≫
      pullbackTransport N e = 𝟙 _ := by
  subst e
  simp [pullbackTransport, transportNatTrans]

/-- The canonical identification along an equality, followed by the transport of inverse images
along its reverse, is the identity. -/
theorem pullbackTransport_comp_transportNatTrans_symm_app {T Z : AlgebraicSpaces B S hS}
    {a b : T ⟶ Z} (e : a = b) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    pullbackTransport N e ≫
      (transportNatTrans (congrArg (fun k : T ⟶ Z => modulePullback B S hS k) e).symm).app N =
      𝟙 _ := by
  subst e
  simp [pullbackTransport, transportNatTrans]

/-- The canonical identification along the reverse of an equality is the transport of inverse
images along it. -/
theorem pullbackTransport_symm_eq_transportNatTrans_symm_app {T Z : AlgebraicSpaces B S hS}
    {a b : T ⟶ Z} (e : a = b) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    pullbackTransport N e.symm =
      (transportNatTrans (congrArg (fun k : T ⟶ Z => modulePullback B S hS k) e).symm).app N := by
  subst e
  simp [pullbackTransport, transportNatTrans]

end Transport

section Abstract

variable
  (P : ∀ (X Y : AlgebraicSpaces B S hS), (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (Q : ∀ (X Y : AlgebraicSpaces B S hS), (X ⟶ Y) →
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
  (adj : ∀ (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y), P X Y f ⊣ Q X Y f)
  (cmp : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
    P Y Z g ⋙ P X Y f ≅ P X Z (f ≫ g))
  (bca : ∀ (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (g' : X' ⟶ X), g' ≫ f = f' ≫ g → ∀ M : Modules.{u, u} B S hS X.1 X.2,
      (P _ _ g).obj ((Q _ _ f).obj M) ⟶ (Q _ _ f').obj ((P _ _ g').obj M))
  (hsplit : ∀ (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (wg : g' ≫ f = f' ≫ g) (M : Modules.{u, u} B S hS X.1 X.2),
    ((adj _ _ f').homEquiv _ _).symm (bca _ _ _ _ f f' g g' wg M) =
      ((cmp _ _ _ f' g).hom.app ((Q _ _ f).obj M) ≫
          (transportNatTrans (congrArg (fun k : X' ⟶ Y => P _ _ k) wg).symm).app
            ((Q _ _ f).obj M) ≫
          (cmp _ _ _ g' f).inv.app ((Q _ _ f).obj M)) ≫
        (P _ _ g').map ((adj _ _ f).counit.app M))
  (pt : ∀ (T Z : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Z.1 Z.2) (a b : T ⟶ Z),
    a = b → ((P _ _ a).obj M ⟶ (P _ _ b).obj M))
  (hpt₁ : ∀ (T Z : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Z.1 Z.2) (a b : T ⟶ Z)
    (e : a = b),
    (transportNatTrans (congrArg (fun k : T ⟶ Z => P _ _ k) e).symm).app M ≫
      pt _ _ M _ _ e = 𝟙 _)
  (hpt₂ : ∀ (T Z : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Z.1 Z.2) (a b : T ⟶ Z)
    (e : a = b),
    pt _ _ M _ _ e ≫
      (transportNatTrans (congrArg (fun k : T ⟶ Z => P _ _ k) e).symm).app M = 𝟙 _)
  (hpt₃ : ∀ (T Z : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Z.1 Z.2) (a b : T ⟶ Z)
    (e : a = b),
    pt _ _ M _ _ e.symm =
      (transportNatTrans (congrArg (fun k : T ⟶ Z => P _ _ k) e).symm).app M)

include hsplit hpt₁ hpt₂ hpt₃ in
/-- **Compatibility with a transition morphism, across an adjunction `f^* ⊣ f_*`**, for an
abstract inverse-image calculus.  For two commutative squares over `f` and `f'` with horizontal
morphisms `g, g'` and `h, h'`, morphisms `β : g^*𝒩 ⟶ h^*𝒩` and `α : g'^*ℳ ⟶ h'^*ℳ`, an
isomorphism `e` whose underlying morphism is the base change map of the second square, and a
morphism `x : g'^*f^*𝒩 ⟶ h'^*f^*𝒩` whose flattening along `f` is the inverse image of `β` along
`f'` read through the two squares: a morphism `u : f^*𝒩 ⟶ ℳ` intertwines `x` with `α` exactly
when its adjoint `𝒩 ⟶ f_*ℳ` intertwines `β` with the transport of `α` through the two base
change maps. -/
theorem abstract_compatible_iff {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    {g h : Y' ⟶ Y} {g' h' : X' ⟶ X}
    (wg : g' ≫ f = f' ≫ g) (wh : h' ≫ f = f' ≫ h) (wh' : f' ≫ h = h' ≫ f)
    {N : Modules.{u, u} B S hS Y.1 Y.2} {M : Modules.{u, u} B S hS X.1 X.2}
    (β : (P _ _ g).obj N ⟶ (P _ _ h).obj N) (α : (P _ _ g').obj M ⟶ (P _ _ h').obj M)
    (e : (P _ _ h).obj ((Q _ _ f).obj M) ≅ (Q _ _ f').obj ((P _ _ h').obj M))
    (he : e.hom = bca _ _ _ _ f f' h h' wh M)
    (x : (P _ _ g').obj ((P _ _ f).obj N) ⟶ (P _ _ h').obj ((P _ _ f).obj N))
    (hx : (cmp _ _ _ g' f).inv.app N ≫ x ≫ (cmp _ _ _ h' f).hom.app N =
      pt _ _ N _ _ wg ≫
        ((cmp _ _ _ f' g).inv.app N ≫ (P _ _ f').map β ≫ (cmp _ _ _ f' h).hom.app N) ≫
        pt _ _ N _ _ wh')
    (u : (P _ _ f).obj N ⟶ M) :
    β ≫ (P _ _ h).map ((adj _ _ f).homEquiv _ _ u) =
        (P _ _ g).map ((adj _ _ f).homEquiv _ _ u) ≫
          (bca _ _ _ _ f f' g g' wg M ≫ (Q _ _ f').map α ≫ e.inv) ↔
      x ≫ (P _ _ h').map u = (P _ _ g').map u ≫ α := by
  have key : ∀ {k : Y' ⟶ Y} {k' : X' ⟶ X} (wk : k' ≫ f = f' ≫ k),
      ((adj _ _ f').homEquiv _ _).symm
          ((P _ _ k).map ((adj _ _ f).homEquiv _ _ u) ≫ bca _ _ _ _ f f' k k' wk M) =
        (cmp _ _ _ f' k).hom.app N ≫
          (transportNatTrans (congrArg (fun k : X' ⟶ Y => P _ _ k) wk).symm).app N ≫
          (cmp _ _ _ k' f).inv.app N ≫ (P _ _ k').map u := by
    intro k k' wk
    have n1 := (cmp _ _ _ f' k).hom.naturality ((adj _ _ f).homEquiv _ _ u)
    have n2 := (transportNatTrans
      (congrArg (fun k : X' ⟶ Y => P _ _ k) wk).symm).naturality ((adj _ _ f).homEquiv _ _ u)
    have n3 := (cmp _ _ _ k' f).inv.naturality ((adj _ _ f).homEquiv _ _ u)
    simp only [Functor.comp_map] at n1 n3
    rw [Adjunction.homEquiv_naturality_left_symm, hsplit]
    simp only [Category.assoc]
    have hc := ((adj _ _ f).homEquiv_counit (g := (adj _ _ f).homEquiv N M u)).symm
    rw [Equiv.symm_apply_apply] at hc
    rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% n3, ← Functor.map_comp, hc]
  rw [← Iso.cancel_iso_hom_right _ _ e]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, ← Category.assoc _ (bca _ _ _ _ f f' g g' wg M),
    ← ((adj _ _ f').homEquiv _ _).symm.injective.eq_iff,
    Adjunction.homEquiv_naturality_left_symm, key wh,
    Adjunction.homEquiv_naturality_right_symm, key wg]
  have hx' : x = (cmp _ _ _ g' f).hom.app N ≫
      (pt _ _ N _ _ wg ≫
        ((cmp _ _ _ f' g).inv.app N ≫ (P _ _ f').map β ≫ (cmp _ _ _ f' h).hom.app N) ≫
        pt _ _ N _ _ wh.symm) ≫
      (cmp _ _ _ h' f).inv.app N := by
    rw [← hx]
    simp
  subst hx'
  rw [hpt₃ _ _ N _ _ wh]
  simp only [Category.assoc]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · rw [H]
    simp only [Iso.inv_hom_id_app_assoc, reassoc_of% (hpt₂ _ _ N _ _ wg),
      Iso.hom_inv_id_app_assoc]
  · have H' := congrArg (fun z => (cmp _ _ _ f' g).hom.app N ≫
      (transportNatTrans (congrArg (fun k : X' ⟶ Y => P _ _ k) wg).symm).app N ≫
      (cmp _ _ _ g' f).inv.app N ≫ z) H
    simp only [Iso.inv_hom_id_app_assoc, reassoc_of% (hpt₁ _ _ N _ _ wg),
      Iso.hom_inv_id_app_assoc] at H'
    simpa only [Category.assoc] using H'

end Abstract

section Groupoid

open GroupoidInAlgebraicSpaces

variable {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

variable (B S hS)

variable (φ : Hom G G')
  (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
  (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
  (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
  (hsflat : IsFlat B S hS G'.source.hom)

/-- **The two compatibility conditions correspond under the adjunction `f^* ⊣ f_*` on the
spaces of objects.**  A morphism `u : f^*𝒩 ⟶ ℳ` of the underlying modules is compatible with the
transition morphisms of the inverse image `f^*(𝒩, β)` and of `(ℳ, α)` exactly when its adjoint
`𝒩 ⟶ f_*ℳ` is compatible with the transition morphisms of `(𝒩, β)` and of the direct image
`f_*(ℳ, α)`.  This is `AlgebraicGeometry.Space.abstract_compatible_iff` at the inverse and direct
images of `𝒪`-modules, the two squares of the morphism of groupoids and their base change
maps. -/
theorem groupoidQuasicoherent_compatible_iff (N : QuasicoherentModule B S hS G')
    (M : QuasicoherentModule B S hS G)
    (u : (modulePullback B S hS φ.objectsMap).obj N.F.obj ⟶ M.F.obj) :
    QuasicoherentModule.Compatible (M := N)
        (N := groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M)
        ((modulePullbackAdjunction B S hS φ.objectsMap).homEquiv _ _ u) ↔
      QuasicoherentModule.Compatible (M := groupoidQuasicoherentPullbackObj B S hS φ N) (N := M)
        u := by
  unfold QuasicoherentModule.Compatible
  rw [groupoidQuasicoherentPushforwardObj_alpha, groupoidModulePushforwardTransition_eq,
    baseChangeTransition, groupoidQuasicoherentPullbackObj_alpha]
  exact abstract_compatible_iff (@modulePullback B S hS) (@modulePushforward B S hS)
    (@modulePullbackAdjunction B S hS) (@modulePullbackCompIso B S hS)
    (@moduleBaseChangeApp B S hS)
    (fun _ _ _ _ f f' _ _ wg M => homEquiv_symm_moduleBaseChangeApp f f' wg M)
    (@pullbackTransport B S hS)
    (fun _ _ M _ _ e => transportNatTrans_symm_app_comp_pullbackTransport e M)
    (fun _ _ M _ _ e => pullbackTransport_comp_transportNatTrans_symm_app e M)
    (fun _ _ M _ _ e => pullbackTransport_symm_eq_transportNatTrans_symm_app e M)
    φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm φ.arrowsMap_comp_source.symm
    φ.arrowsMap_comp_source N.alpha M.alpha
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat M.F.obj M.F.property)
    (groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat M.F.obj M.F.property)
    (groupoidModulePullbackTransition B S hS φ N.F.obj N.alpha)
    (modulePullbackFlatten_groupoidModulePullbackTransition B S hS φ N.F.obj N.alpha) u

/-- The adjoint `𝒩 ⟶ f_*ℳ`, under `f^* ⊣ f_*` on the spaces of objects, of a morphism of the
underlying modules `f^*𝒩 ⟶ ℳ`, read between the underlying modules of `(𝒩, β)` and of the direct
image `f_*(ℳ, α)`. -/
def groupoidQuasicoherentAdjunct {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (u : (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj ⟶ M.F.obj) :
    N.F.obj ⟶ (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj :=
  (modulePullbackAdjunction B S hS φ.objectsMap).homEquiv _ _ u

/-- The adjoint `f^*𝒩 ⟶ ℳ`, under `f^* ⊣ f_*` on the spaces of objects, of a morphism of the
underlying modules `𝒩 ⟶ f_*ℳ`, read between the underlying modules of the inverse image
`f^*(𝒩, β)` and of `(ℳ, α)`. -/
def groupoidQuasicoherentAdjunctSymm {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (v : N.F.obj ⟶ (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj) :
    (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj ⟶ M.F.obj :=
  ((modulePullbackAdjunction B S hS φ.objectsMap).homEquiv _ _).symm v

/-- The adjoint `𝒩 ⟶ f_*ℳ` of `u : f^*𝒩 ⟶ ℳ` is the image of `u` under the adjunction bijection
of `f^* ⊣ f_*` on the spaces of objects. -/
theorem groupoidQuasicoherentAdjunct_eq {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (u : (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj ⟶ M.F.obj) :
    groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u =
      (modulePullbackAdjunction B S hS φ.objectsMap).homEquiv _ _ u :=
  rfl

/-- The adjoint `f^*𝒩 ⟶ ℳ` of `v : 𝒩 ⟶ f_*ℳ` is the image of `v` under the inverse of the
adjunction bijection of `f^* ⊣ f_*` on the spaces of objects. -/
theorem groupoidQuasicoherentAdjunctSymm_eq {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (v : N.F.obj ⟶ (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj) :
    groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v =
      ((modulePullbackAdjunction B S hS φ.objectsMap).homEquiv _ _).symm v :=
  rfl

/-- The adjoint `f^*𝒩 ⟶ ℳ` of the adjoint `𝒩 ⟶ f_*ℳ` of `u : f^*𝒩 ⟶ ℳ` is `u`. -/
theorem groupoidQuasicoherentAdjunctSymm_adjunct {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (u : (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj ⟶ M.F.obj) :
    groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat
        (groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u) = u :=
  Equiv.symm_apply_apply _ _

/-- The adjoint `𝒩 ⟶ f_*ℳ` of the adjoint `f^*𝒩 ⟶ ℳ` of `v : 𝒩 ⟶ f_*ℳ` is `v`. -/
theorem groupoidQuasicoherentAdjunct_adjunctSymm {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (v : N.F.obj ⟶ (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj) :
    groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat
        (groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v) = v :=
  Equiv.apply_symm_apply _ _

/-- The adjoint of a compatible morphism is compatible. -/
theorem compatible_groupoidQuasicoherentAdjunct {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (u : (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj ⟶ M.F.obj)
    (hu : QuasicoherentModule.Compatible u) :
    QuasicoherentModule.Compatible (groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u) :=
  (groupoidQuasicoherent_compatible_iff B S hS φ hqc hqs hpb hsflat N M u).2 hu

/-- The adjoint of a compatible morphism is compatible. -/
theorem compatible_groupoidQuasicoherentAdjunctSymm {N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G}
    (v : N.F.obj ⟶ (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj)
    (hv : QuasicoherentModule.Compatible v) :
    QuasicoherentModule.Compatible
      (groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v) := by
  refine (groupoidQuasicoherent_compatible_iff B S hS φ hqc hqs hpb hsflat N M _).1 ?_
  rwa [← groupoidQuasicoherentAdjunct_eq, groupoidQuasicoherentAdjunct_adjunctSymm]

/-- **The adjunction bijection** between the morphisms out of the inverse image of a
quasi-coherent module on `(U', R', s', t', c')` and the morphisms into the direct image of a
quasi-coherent module on `(U, R, s, t, c)`: the adjunction bijection of `f^* ⊣ f_*` on the
spaces of objects, which respects the compatibility conditions by
`AlgebraicGeometry.Space.groupoidQuasicoherent_compatible_iff`. -/
def groupoidQuasicoherentHomEquiv (N : QuasicoherentModule B S hS G')
    (M : QuasicoherentModule B S hS G) :
    ((groupoidQuasicoherentPullback B S hS φ).obj N ⟶ M) ≃
      (N ⟶ (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).obj M) where
  toFun u := QuasicoherentModule.homMk (groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat
    u.hom) (compatible_groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u.hom
      (QuasicoherentModule.compatible_hom u))
  invFun v := QuasicoherentModule.homMk
    (groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v.hom)
    (compatible_groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v.hom
      (QuasicoherentModule.compatible_hom v))
  left_inv u := QuasicoherentModule.Hom.ext
    (groupoidQuasicoherentAdjunctSymm_adjunct B S hS φ hqc hqs hpb hsflat u.hom)
  right_inv v := QuasicoherentModule.Hom.ext
    (groupoidQuasicoherentAdjunct_adjunctSymm B S hS φ hqc hqs hpb hsflat v.hom)

/-- The underlying morphism of the image of a morphism under the adjunction bijection is its
adjoint under `f^* ⊣ f_*`. -/
@[simp]
theorem groupoidQuasicoherentHomEquiv_apply_hom (N : QuasicoherentModule B S hS G')
    (M : QuasicoherentModule B S hS G)
    (u : (groupoidQuasicoherentPullback B S hS φ).obj N ⟶ M) :
    (groupoidQuasicoherentHomEquiv B S hS φ hqc hqs hpb hsflat N M u).hom =
      groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u.hom :=
  rfl

/-- The underlying morphism of the inverse image of a morphism under the adjunction bijection is
its adjoint under `f^* ⊣ f_*`. -/
@[simp]
theorem groupoidQuasicoherentHomEquiv_symm_apply_hom (N : QuasicoherentModule B S hS G')
    (M : QuasicoherentModule B S hS G)
    (v : N ⟶ (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).obj M) :
    ((groupoidQuasicoherentHomEquiv B S hS φ hqc hqs hpb hsflat N M).symm v).hom =
      groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v.hom :=
  rfl

/-- The adjunction bijection is natural in the source. -/
theorem groupoidQuasicoherentAdjunctSymm_comp {N' N : QuasicoherentModule B S hS G'}
    {M : QuasicoherentModule B S hS G} (g : N' ⟶ N)
    (v : N ⟶ (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).obj M) :
    groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat (g.hom ≫ v.hom) =
      (modulePullback B S hS φ.objectsMap).map g.hom ≫
        groupoidQuasicoherentAdjunctSymm B S hS φ hqc hqs hpb hsflat v.hom :=
  (modulePullbackAdjunction B S hS φ.objectsMap).homEquiv_naturality_left_symm g.hom v.hom

/-- The adjunction bijection is natural in the target. -/
theorem groupoidQuasicoherentAdjunct_comp {N : QuasicoherentModule B S hS G'}
    {M M' : QuasicoherentModule B S hS G}
    (u : (groupoidQuasicoherentPullback B S hS φ).obj N ⟶ M) (g : M ⟶ M') :
    groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat (u.hom ≫ g.hom) =
      groupoidQuasicoherentAdjunct B S hS φ hqc hqs hpb hsflat u.hom ≫
        (modulePushforward B S hS φ.objectsMap).map g.hom :=
  (modulePullbackAdjunction B S hS φ.objectsMap).homEquiv_naturality_right u.hom g.hom

/-- **Stacks 0GPM.**  Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of
groupoids in algebraic spaces over `A` such that `f : U ⟶ U'` is quasi-compact and
quasi-separated, the square formed by `f : R ⟶ R'`, the target morphisms `t, t'` and
`f : U ⟶ U'` is cartesian, and `s'` is flat.  Then pushforward `(ℱ, α) ↦ (f_*ℱ, f_*α)`
(`AlgebraicGeometry.Space.groupoidQuasicoherentPushforward`) is a functor from the
quasi-coherent modules on `(U, R, s, t, c)` to those on `(U', R', s', t', c')`, and it is right
adjoint to the inverse image functor of Stacks 0442
(`AlgebraicGeometry.Space.groupoidQuasicoherentPullback`). -/
@[stacks 0GPM]
def groupoidQuasicoherentPullbackPushforwardAdjunction :
    groupoidQuasicoherentPullback B S hS φ ⊣
      groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := groupoidQuasicoherentHomEquiv B S hS φ hqc hqs hpb hsflat
      homEquiv_naturality_left_symm := fun {N' N M} g v => by
        refine QuasicoherentModule.Hom.ext ?_
        rw [groupoidQuasicoherentHomEquiv_symm_apply_hom, QuasicoherentModule.comp_hom,
          QuasicoherentModule.comp_hom, groupoidQuasicoherentHomEquiv_symm_apply_hom,
          groupoidQuasicoherentPullback_map, groupoidQuasicoherentPullbackHom_hom,
          groupoidQuasicoherentPullbackMap_eq]
        exact groupoidQuasicoherentAdjunctSymm_comp B S hS φ hqc hqs hpb hsflat g v
      homEquiv_naturality_right := fun {N M M'} u g => by
        refine QuasicoherentModule.Hom.ext ?_
        rw [groupoidQuasicoherentHomEquiv_apply_hom, QuasicoherentModule.comp_hom,
          QuasicoherentModule.comp_hom, groupoidQuasicoherentHomEquiv_apply_hom,
          groupoidQuasicoherentPushforward_map, groupoidQuasicoherentPushforwardHom_hom]
        exact groupoidQuasicoherentAdjunct_comp B S hS φ hqc hqs hpb hsflat u g }

/-- The unit of the adjunction of Stacks 0GPM at a quasi-coherent module on
`(U', R', s', t', c')` has as underlying morphism the unit `𝒩 ⟶ f_*f^*𝒩` of `f^* ⊣ f_*` on the
spaces of objects. -/
@[simp]
theorem groupoidQuasicoherentPullbackPushforwardAdjunction_unit_app_hom
    (N : QuasicoherentModule B S hS G') :
    ((groupoidQuasicoherentPullbackPushforwardAdjunction B S hS φ hqc hqs hpb hsflat).unit.app
        N).hom = (modulePullbackAdjunction B S hS φ.objectsMap).unit.app N.F.obj := by
  rw [groupoidQuasicoherentPullbackPushforwardAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  exact Adjunction.homEquiv_id _ _

/-- The counit of the adjunction of Stacks 0GPM at a quasi-coherent module on
`(U, R, s, t, c)` has as underlying morphism the counit `f^*f_*ℳ ⟶ ℳ` of `f^* ⊣ f_*` on the
spaces of objects. -/
@[simp]
theorem groupoidQuasicoherentPullbackPushforwardAdjunction_counit_app_hom
    (M : QuasicoherentModule B S hS G) :
    ((groupoidQuasicoherentPullbackPushforwardAdjunction B S hS φ hqc hqs hpb hsflat).counit.app
        M).hom = (modulePullbackAdjunction B S hS φ.objectsMap).counit.app M.F.obj := by
  rw [groupoidQuasicoherentPullbackPushforwardAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  exact Adjunction.homEquiv_symm_id _ _

end Groupoid

end AlgebraicGeometry.Space

end
