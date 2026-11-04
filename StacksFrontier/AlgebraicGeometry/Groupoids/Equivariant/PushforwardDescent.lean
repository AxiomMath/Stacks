module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pushed-forward descent morphism along a morphism of groupoid schemes

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoid schemes over `S` with
`f : U ⟶ U'` quasi-compact and quasi-separated, with the square formed by `R ⟶ R'` over `t`, `t'`
and `U ⟶ U'` cartesian, and with `s'` and `t'` flat.  For a quasi-coherent module `(𝓕, α)` on
`(U, R, s, t, c)` this file builds the morphism `f_*α : (t')^* f_*𝓕 ⟶ (s')^* f_*𝓕` and proves that
it is an isomorphism natural in `(𝓕, α)`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.pushforwardTargetBaseChange` and
  `Stacks.Groupoids.GroupoidScheme.pushforwardSourceBaseChange` are the canonical base-change
  morphisms `(t')^* f_* ⟶ f_* t^*` and `(s')^* f_* ⟶ f_* s^*` of the two squares.
* `Stacks.Groupoids.GroupoidScheme.pushforwardTargetBaseChangeIso` and
  `Stacks.Groupoids.GroupoidScheme.pushforwardSourceBaseChangeIso` are those morphisms as
  isomorphisms, at a quasi-coherent module.
* `Stacks.Groupoids.GroupoidScheme.pushforwardDescent` is the morphism `f_*α`.
* `Stacks.Groupoids.GroupoidScheme.pushforwardFunctor` is pushforward along a morphism of
  groupoid schemes, as a functor on quasi-coherent modules equipped with groupoid descent data.
* `Stacks.Groupoids.GroupoidScheme.pullbackPushforwardAdjunction` exhibits that functor as a
  right adjoint of the pullback functor of Tag 03LJ.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isPullback_source_of_isPullback_target`: the square formed by
  `R ⟶ R'` over `s`, `s'` and `U ⟶ U'` is cartesian as soon as the one over `t`, `t'` is.
* `Stacks.Groupoids.GroupoidScheme.pushforwardDescent_naturality`: a morphism of quasi-coherent
  modules on `(U, R, s, t, c)` pushes forward to one intertwining the pushed-forward descent
  morphisms.
* `Stacks.Groupoids.GroupoidScheme.isIso_pushforwardDescent`: the pushed-forward descent morphism
  is an isomorphism.
* `Stacks.Groupoids.GroupoidScheme.reindexHom_pushforwardDescent` reindexes the pushed-forward
  descent morphism along a morphism into the arrow scheme of the target groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.pushforwardDescent_cocycle` and
  `Stacks.Groupoids.GroupoidScheme.pushforwardDescent_identity` are the cocycle condition on the
  scheme of composable arrows and the normalization along the identity section, so that
  `(f_*𝓕, f_*α)` is again a quasi-coherent module on a groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.pushforwardDescent_comm_iff` matches the compatibility
  condition with the pulled-back descent morphism with the one with the pushed-forward descent
  morphism under the inverse-image--direct-image adjunction on the object schemes;  this is what
  makes the two functors adjoint.

## Implementation notes

Only the cartesian square over the target maps is hypothesised, as in the source; the one over the
source maps is derived from it in
`Stacks.Groupoids.GroupoidScheme.isPullback_source_of_isPullback_target` by pasting the given
square between the two squares built from the inverse morphisms of the two groupoids, which are
isomorphisms of the arrow schemes exchanging source and target.

The base-change morphisms are the mates of `Stacks.AlgebraicGeometry.AffinePushforward.
pushforwardSquareIso`, and they are invertible by flat base change for direct images in degree
zero.  So `f_*α` is defined as the conjugate `f_*α = bc_t ∘ f_*(α) ∘ bc_s^{-1}`, which is the
sense in which `f_*α` is a morphism `(t')^* f_*𝓕 ⟶ (s')^* f_*𝓕` rather than a morphism between
the two direct images over the arrow scheme.

The cocycle condition and the normalization are both proved by cancelling a base-change
morphism:  for a morphism `a` into `R'` lifting to a morphism `a'` into `R` over a morphism `p`
of the two schemes `a` and `a'` are defined on, stacking that square under the source square
gives a rectangle whose base-change morphism carries `reindexHom a (f_*α)` to `p_*` of
`reindexHom a' α`, by `Stacks.Groupoids.GroupoidScheme.reindexHom_pushforwardDescent`.  Taking
`a` to be the two projections and the composition morphism of `(U', R', s', t', c')`, and then
the identity section, turns the two conditions for `f_*α` into the ones for `α`.  Only the
base-change morphism at the composition morphism, respectively at the identity section, has to
be invertible, which is why no flatness of `c'` or of `e'` is needed.

Right-adjointness is proved by transporting the two compatibility conditions along the
inverse-image--direct-image adjunction on the arrow schemes.  That uses the base-change morphism
in its second description, as the adjunct of the comparison of the two composite inverse images
around the square rather than as the mate of the comparison of the two composite direct images;
the two descriptions agree by `Stacks.Modules.baseChangeNatTrans_eq_mateEquiv`, which is why
this file imports `StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison`.

## References

* [Stacks Project, Tag 09VH](https://stacks.math.columbia.edu/tag/09VH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Groupoids

namespace GroupoidScheme

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- The square formed by the inverse morphism of a groupoid scheme, its source and target
morphisms and the identity of its object scheme is cartesian. -/
theorem isPullback_inverse_source_target (G : GroupoidScheme S) :
    IsPullback G.inverse.left G.source.left G.target.left (𝟙 G.objects.left) :=
  have : IsIso G.inverse.left := AlgebraicGeometry.groupoidInverse_left_isIso G
  IsPullback.of_horiz_isIso
    ⟨by rw [Category.comp_id, ← Over.comp_left, G.target_inverse]⟩

/-- The square formed by the inverse morphism of a groupoid scheme, its target and source
morphisms and the identity of its object scheme is cartesian. -/
theorem isPullback_inverse_target_source (G : GroupoidScheme S) :
    IsPullback G.inverse.left G.target.left G.source.left (𝟙 G.objects.left) :=
  have : IsIso G.inverse.left := AlgebraicGeometry.groupoidInverse_left_isIso G
  IsPullback.of_horiz_isIso
    ⟨by rw [Category.comp_id, ← Over.comp_left, G.source_inverse]⟩

/-- For a morphism of groupoid schemes whose square over the target morphisms is cartesian, the
square over the source morphisms is cartesian too. -/
theorem isPullback_source_of_isPullback_target (f : Hom G H)
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left) :
    IsPullback f.mapArrows.left G.source.left H.source.left f.mapObjects.left := by
  have hinv : f.mapArrows.left ≫ H.inverse.left = G.inverse.left ≫ f.mapArrows.left :=
    congrArg Over.Hom.left (AlgebraicGeometry.groupoidHom_map_inverse f)
  have hGG : G.inverse.left ≫ G.inverse.left = 𝟙 G.arrows.left := by
    rw [← Over.comp_left, AlgebraicGeometry.groupoidInverse_involutive G, Over.id_left]
  have key := ((isPullback_inverse_source_target G).paste_horiz h).paste_horiz
    (isPullback_inverse_target_source H)
  have e₁ : (G.inverse.left ≫ f.mapArrows.left) ≫ H.inverse.left = f.mapArrows.left := by
    rw [Category.assoc, hinv, ← Category.assoc, hGG, Category.id_comp]
  have e₂ : (𝟙 G.objects.left ≫ f.mapObjects.left) ≫ 𝟙 H.objects.left = f.mapObjects.left := by
    rw [Category.id_comp, Category.comp_id]
  rw [e₁, e₂] at key
  exact key

/-- The canonical base-change morphism `(t')^* f_* ⟶ f_* t^*` of the square formed by the arrow
map of a morphism of groupoid schemes, the two target morphisms and its object map. -/
noncomputable def pushforwardTargetBaseChange (f : Hom G H) :
    Scheme.Modules.pushforward f.mapObjects.left ⋙ Scheme.Modules.pullback H.target.left ⟶
      Scheme.Modules.pullback G.target.left ⋙ Scheme.Modules.pushforward f.mapArrows.left :=
  Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans f.map_target_left.symm

/-- The canonical base-change morphism `(s')^* f_* ⟶ f_* s^*` of the square formed by the arrow
map of a morphism of groupoid schemes, the two source morphisms and its object map. -/
noncomputable def pushforwardSourceBaseChange (f : Hom G H) :
    Scheme.Modules.pushforward f.mapObjects.left ⋙ Scheme.Modules.pullback H.source.left ⟶
      Scheme.Modules.pullback G.source.left ⋙ Scheme.Modules.pushforward f.mapArrows.left :=
  Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans f.map_source_left.symm

section BaseChange

variable (f : Hom G H) [QuasiCompact f.mapObjects.left] [QuasiSeparated f.mapObjects.left]

section Target

variable [Flat H.target.left]

/-- At a quasi-coherent module, the base-change morphism of the square over the target morphisms
is an isomorphism. -/
theorem isIso_pushforwardTargetBaseChange_app
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    IsIso ((pushforwardTargetBaseChange f).app F) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat h.flip F

/-- The base-change isomorphism `(t')^* f_* 𝓕 ≅ f_* t^* 𝓕` at a quasi-coherent module. -/
noncomputable def pushforwardTargetBaseChangeIso
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback H.target.left).obj
        ((Scheme.Modules.pushforward f.mapObjects.left).obj F) ≅
      (Scheme.Modules.pushforward f.mapArrows.left).obj
        ((Scheme.Modules.pullback G.target.left).obj F) :=
  have := isIso_pushforwardTargetBaseChange_app f h F
  asIso ((pushforwardTargetBaseChange f).app F)

/-- The forward direction of the target base-change isomorphism is the base-change morphism. -/
@[simp]
theorem pushforwardTargetBaseChangeIso_hom
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    (pushforwardTargetBaseChangeIso f h F).hom = (pushforwardTargetBaseChange f).app F :=
  rfl

end Target

section Source

variable [Flat H.source.left]

/-- At a quasi-coherent module, the base-change morphism of the square over the source morphisms
is an isomorphism. -/
theorem isIso_pushforwardSourceBaseChange_app
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    IsIso ((pushforwardSourceBaseChange f).app F) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    (isPullback_source_of_isPullback_target f h).flip F

/-- The base-change isomorphism `(s')^* f_* 𝓕 ≅ f_* s^* 𝓕` at a quasi-coherent module. -/
noncomputable def pushforwardSourceBaseChangeIso
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback H.source.left).obj
        ((Scheme.Modules.pushforward f.mapObjects.left).obj F) ≅
      (Scheme.Modules.pushforward f.mapArrows.left).obj
        ((Scheme.Modules.pullback G.source.left).obj F) :=
  have := isIso_pushforwardSourceBaseChange_app f h F
  asIso ((pushforwardSourceBaseChange f).app F)

/-- The forward direction of the source base-change isomorphism is the base-change morphism. -/
@[simp]
theorem pushforwardSourceBaseChangeIso_hom
    (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)
    (F : G.objects.left.Modules) [F.IsQuasicoherent] :
    (pushforwardSourceBaseChangeIso f h F).hom = (pushforwardSourceBaseChange f).app F :=
  rfl

end Source

end BaseChange

section Descent

variable (f : Hom G H) [QuasiCompact f.mapObjects.left] [QuasiSeparated f.mapObjects.left]
  [Flat H.source.left] [Flat H.target.left]
  (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)

/-- The descent morphism of the direct image of a quasi-coherent module on a groupoid scheme:
the direct image of its descent morphism, conjugated by the base-change isomorphisms of the
squares over the target and source morphisms. -/
noncomputable def pushforwardDescent (M : QuasicoherentModule G) :
    (Scheme.Modules.pullback H.target.left).obj
        ((Scheme.Modules.pushforward f.mapObjects.left).obj M.module) ⟶
      (Scheme.Modules.pullback H.source.left).obj
        ((Scheme.Modules.pushforward f.mapObjects.left).obj M.module) :=
  (pushforwardTargetBaseChangeIso f h M.module).hom ≫
    (Scheme.Modules.pushforward f.mapArrows.left).map M.alpha ≫
      (pushforwardSourceBaseChangeIso f h M.module).inv

/-- The defining property of the pushed-forward descent morphism: composed with the base-change
isomorphism of the source square it is the direct image of the original descent morphism
transported through the base-change isomorphism of the target square. -/
theorem pushforwardDescent_comp_pushforwardSourceBaseChange (M : QuasicoherentModule G) :
    pushforwardDescent f h M ≫ (pushforwardSourceBaseChangeIso f h M.module).hom =
      (pushforwardTargetBaseChangeIso f h M.module).hom ≫
        (Scheme.Modules.pushforward f.mapArrows.left).map M.alpha := by
  simp only [pushforwardDescent, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The pushed-forward descent morphism is an isomorphism. -/
instance isIso_pushforwardDescent (M : QuasicoherentModule G) :
    IsIso (pushforwardDescent f h M) := by
  rw [pushforwardDescent]
  infer_instance

/-- The pushed-forward descent morphism is natural: the direct image of a morphism of
quasi-coherent modules on a groupoid scheme intertwines the pushed-forward descent morphisms.
This is the compatibility condition required of a morphism of quasi-coherent modules. -/
theorem pushforwardDescent_naturality {M N : QuasicoherentModule G} (g : M ⟶ N) :
    pushforwardDescent f h M ≫ (Scheme.Modules.pullback H.source.left).map
        ((Scheme.Modules.pushforward f.mapObjects.left).map (QuasicoherentModule.Hom.hom g)) =
      (Scheme.Modules.pullback H.target.left).map
          ((Scheme.Modules.pushforward f.mapObjects.left).map
            (QuasicoherentModule.Hom.hom g)) ≫ pushforwardDescent f h N := by
  have hSnat := (pushforwardSourceBaseChange f).naturality (QuasicoherentModule.Hom.hom g)
  have hTnat := (pushforwardTargetBaseChange f).naturality (QuasicoherentModule.Hom.hom g)
  simp only [Functor.comp_map] at hSnat hTnat
  have hS : (pushforwardSourceBaseChangeIso f h M.module).inv ≫
        (Scheme.Modules.pullback H.source.left).map
          ((Scheme.Modules.pushforward f.mapObjects.left).map (QuasicoherentModule.Hom.hom g)) =
      (Scheme.Modules.pushforward f.mapArrows.left).map
          ((Scheme.Modules.pullback G.source.left).map (QuasicoherentModule.Hom.hom g)) ≫
        (pushforwardSourceBaseChangeIso f h N.module).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      pushforwardSourceBaseChangeIso_hom, pushforwardSourceBaseChangeIso_hom]
    exact hSnat
  have hT : (pushforwardTargetBaseChangeIso f h M.module).hom ≫
        (Scheme.Modules.pushforward f.mapArrows.left).map
          ((Scheme.Modules.pullback G.target.left).map (QuasicoherentModule.Hom.hom g)) =
      (Scheme.Modules.pullback H.target.left).map
          ((Scheme.Modules.pushforward f.mapObjects.left).map (QuasicoherentModule.Hom.hom g)) ≫
        (pushforwardTargetBaseChangeIso f h N.module).hom := by
    rw [pushforwardTargetBaseChangeIso_hom, pushforwardTargetBaseChangeIso_hom]
    exact hTnat.symm
  simp only [pushforwardDescent, Category.assoc]
  rw [hS, ← Functor.map_comp_assoc, QuasicoherentModule.Hom.comm, Functor.map_comp_assoc,
    reassoc_of% hT]

end Descent

end GroupoidScheme

open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (pasteBase)

/-- The base-change morphism of a commutative square depends on its two horizontal morphisms
only through their values:  replacing them by equal ones conjugates it by the comparisons of
inverse images along equal morphisms. -/
theorem pullbackCongr_comp_baseChangeNatTrans {X' X S' S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g₁ g₂ : S' ⟶ S} {g₁' g₂' : X' ⟶ X}
    (p : g₁ = g₂) (p' : g₁' = g₂') (w₁ : g₁' ≫ f = f' ≫ g₁) (w₂ : g₂' ≫ f = f' ≫ g₂)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
        (baseChangeNatTrans w₂).app M =
      (baseChangeNatTrans w₁).app M ≫
        (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullbackCongr p').hom.app M) := by
  cases p
  cases p'
  simp [Scheme.Modules.pullbackCongr]

/-- The base-change morphism of a commutative square, composed with the inverse image along the
base of the adjunct of a morphism out of an inverse image, is the adjunct of that morphism
transported by the comparison of the two composite inverse images around the square. -/
theorem pullback_map_homEquiv_comp_baseChangeNatTrans {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g)
    {N : S.Modules} {M : X.Modules} (u : (Scheme.Modules.pullback f).obj N ⟶ M) :
    (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv N M u) ≫
      (baseChangeNatTrans w).app M =
    (Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _
      ((Stacks.Modules.pullbackSquareIso f f' g g' w).hom.app N ≫
        (Scheme.Modules.pullback g').map u) := by
  rw [← Stacks.Modules.homEquiv_pullbackSquareIso_comp,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  have hnat := (Stacks.Modules.pullbackSquareIso f f' g g' w).hom.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv N M u)
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply]

namespace GroupoidScheme

variable {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
  [QuasiCompact f.mapObjects.left] [QuasiSeparated f.mapObjects.left]
  [Flat H.source.left] [Flat H.target.left]
  (h : IsPullback f.mapArrows.left G.target.left H.target.left f.mapObjects.left)

/-- Reindexing the pushed-forward descent morphism along a morphism `a` into the arrow scheme of
the target groupoid scheme which lifts, over a morphism `q`, to a morphism `aG` into the arrow
scheme of the source groupoid scheme:  measured against the base-change morphisms of the two
rectangles obtained by stacking that square under the source and the target square, it is the
direct image along `q` of the reindexing of the original descent morphism. -/
theorem reindexHom_pushforwardDescent (M : QuasicoherentModule G) {X Y : Scheme.{u}}
    (q : X ⟶ Y) (a : Y ⟶ H.arrows.left) (aG : X ⟶ G.arrows.left)
    (w : aG ≫ f.mapArrows.left = q ≫ a) :
    reindexHom a (pushforwardDescent f h M) ≫
        (baseChangeNatTrans (pasteBase f.map_source_left.symm w)).app M.module =
      (baseChangeNatTrans (pasteBase f.map_target_left.symm w)).app M.module ≫
        (Scheme.Modules.pushforward q).map (reindexHom aG M.alpha) := by
  have hkey := congrArg (Scheme.Modules.pullback a).map
    (pushforwardDescent_comp_pushforwardSourceBaseChange f h M)
  simp only [Functor.map_comp, pushforwardSourceBaseChangeIso_hom,
    pushforwardTargetBaseChangeIso_hom, pushforwardSourceBaseChange,
    pushforwardTargetBaseChange] at hkey
  have hnat := (baseChangeNatTrans w).naturality M.alpha
  simp only [Functor.comp_map] at hnat
  have hR : (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackComp aG G.target.left).hom.app M.module) ≫
      (Scheme.Modules.pushforward q).map (reindexHom aG M.alpha) =
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pullback aG).map M.alpha) ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackComp aG G.source.left).hom.app M.module) := by
    rw [← Functor.map_comp, ← Functor.map_comp, reindexHom]
    simp
  have PT := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_pasteBase_app
    f.map_target_left.symm w M.module
  have PS := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_pasteBase_app
    f.map_source_left.symm w M.module
  rw [reindexHom, PS, PT]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hR, reassoc_of% hkey, ← reassoc_of% hnat]

/-- The pushed-forward descent morphism satisfies the cocycle condition on the scheme of
composable arrows of the target groupoid scheme. -/
theorem pushforwardDescent_cocycle (M : QuasicoherentModule G) :
    successiveDescent H (pushforwardDescent f h M) =
      reindexHom H.comp.left (pushforwardDescent f h M) := by
  have w : ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows) ≫ H.source =
      ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) ≫ H.target := by
    rw [Category.assoc, f.map_source, Category.assoc, f.map_target,
      ← Category.assoc (Limits.pullback.fst G.source G.target),
      ← Category.assoc (Limits.pullback.snd G.source G.target)]
    rw [show Limits.pullback.fst G.source G.target ≫ G.source =
      Limits.pullback.snd G.source G.target ≫ G.target from Limits.pullback.condition]
  obtain ⟨q, hq₁, hq₂, hqc⟩ :
      ∃ q : (Limits.pullback G.source G.target).left ⟶
          (Limits.pullback H.source H.target).left,
        (Limits.pullback.fst G.source G.target).left ≫ f.mapArrows.left =
            q ≫ (Limits.pullback.fst H.source H.target).left ∧
          (Limits.pullback.snd G.source G.target).left ≫ f.mapArrows.left =
            q ≫ (Limits.pullback.snd H.source H.target).left ∧
          G.comp.left ≫ f.mapArrows.left = q ≫ H.comp.left := by
    refine ⟨(Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
      ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w).left, ?_, ?_, ?_⟩
    · exact (congrArg Over.Hom.left (Limits.pullback.lift_fst _ _ w)).symm
    · exact (congrArg Over.Hom.left (Limits.pullback.lift_snd _ _ w)).symm
    · have hcq : Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
          ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w ≫ H.comp =
          G.comp ≫ f.mapArrows := by
        rw [f.comp_mapArrows]
        congr 1
      exact (congrArg Over.Hom.left hcq).symm
  have hpull : ∀ K : GroupoidScheme S, IsPullback (Limits.pullback.fst K.source K.target).left
      (Limits.pullback.snd K.source K.target).left K.source.left K.target.left := fun K =>
    (IsPullback.of_hasPullback K.source K.target).map (Over.forget S)
  have hcs : ∀ K : GroupoidScheme S, K.comp.left ≫ K.source.left =
      (Limits.pullback.snd K.source K.target).left ≫ K.source.left := fun K => by
    rw [← Over.comp_left, ← Over.comp_left, K.source_comp]
  have hsq : IsPullback f.mapArrows.left G.source.left H.source.left f.mapObjects.left :=
    isPullback_source_of_isPullback_target f h
  have houter : IsPullback (q ≫ (Limits.pullback.fst H.source H.target).left)
      (Limits.pullback.snd G.source G.target).left H.source.left
      (f.mapArrows.left ≫ H.target.left) := by
    have hp := (hpull G).paste_horiz hsq
    rw [hq₁, ← f.map_target_left] at hp
    exact hp
  have hq2pb : IsPullback q (Limits.pullback.snd G.source G.target).left
      (Limits.pullback.snd H.source H.target).left f.mapArrows.left :=
    IsPullback.of_right houter hq₂.symm (hpull H)
  have hpb : IsPullback (G.comp.left ≫ G.source.left) q f.mapObjects.left
      (H.comp.left ≫ H.source.left) := by
    rw [hcs G, hcs H]
    exact hq2pb.flip.paste_horiz hsq.flip
  have hflat2 : Flat (Limits.pullback.snd H.source H.target).left :=
    MorphismProperty.of_isPullback (P := @Flat) (hpull H) ‹Flat H.source.left›
  have hflat : Flat (H.comp.left ≫ H.source.left) := by rw [hcs H]; infer_instance
  have hiso : IsIso ((baseChangeNatTrans
      (pasteBase f.map_source_left.symm hqc)).app M.module) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      hpb M.module
  have stepA := pullbackCongr_comp_baseChangeNatTrans
    (congrArg Over.Hom.left H.source_comp).symm (congrArg Over.Hom.left G.source_comp).symm
    (pasteBase f.map_source_left.symm hq₂) (pasteBase f.map_source_left.symm hqc) M.module
  have stepB := reindexHom_pushforwardDescent f h M q
    (Limits.pullback.snd H.source H.target).left
    (Limits.pullback.snd G.source G.target).left hq₂
  have stepC := pullbackCongr_comp_baseChangeNatTrans
    (congrArg Over.Hom.left (Limits.pullback.condition :
      Limits.pullback.fst H.source H.target ≫ H.source =
        Limits.pullback.snd H.source H.target ≫ H.target))
    (congrArg Over.Hom.left (Limits.pullback.condition :
      Limits.pullback.fst G.source G.target ≫ G.source =
        Limits.pullback.snd G.source G.target ≫ G.target))
    (pasteBase f.map_source_left.symm hq₁) (pasteBase f.map_target_left.symm hq₂) M.module
  have stepD := reindexHom_pushforwardDescent f h M q
    (Limits.pullback.fst H.source H.target).left
    (Limits.pullback.fst G.source G.target).left hq₁
  have stepE := pullbackCongr_comp_baseChangeNatTrans
    (congrArg Over.Hom.left H.target_comp) (congrArg Over.Hom.left G.target_comp)
    (pasteBase f.map_target_left.symm hqc) (pasteBase f.map_target_left.symm hq₁) M.module
  have stepF := reindexHom_pushforwardDescent f h M q H.comp.left G.comp.left hqc
  have hcoc := congrArg (Scheme.Modules.pushforward q).map M.cocycle
  unfold successiveDescent at hcoc
  simp only [Functor.map_comp] at hcoc
  rw [← cancel_mono ((baseChangeNatTrans
    (pasteBase f.map_source_left.symm hqc)).app M.module)]
  unfold successiveDescent
  simp only [Category.assoc]
  rw [stepF, stepA, reassoc_of% stepB, reassoc_of% stepC, reassoc_of% stepD,
    reassoc_of% stepE, hcoc]

/-- The pushed-forward descent morphism is normalized along the identity section of the target
groupoid scheme. -/
theorem pushforwardDescent_identity (M : QuasicoherentModule G) :
    identityDescent H (pushforwardDescent f h M) =
      𝟙 ((Scheme.Modules.pushforward f.mapObjects.left).obj M.module) := by
  have he : G.identity.left ≫ f.mapArrows.left =
      f.mapObjects.left ≫ H.identity.left := by
    rw [← Over.comp_left, ← Over.comp_left, f.map_identity]
  have hp : ∀ K : GroupoidScheme S, K.identity.left ≫ K.target.left =
      K.identity.left ≫ K.source.left := fun K =>
    (congrArg Over.Hom.left K.target_identity).trans (congrArg Over.Hom.left K.source_identity).symm
  have hs : G.identity.left ≫ G.source.left = 𝟙 G.objects.left :=
    identity_left_comp_source_left G
  have hs' : H.identity.left ≫ H.source.left = 𝟙 H.objects.left :=
    identity_left_comp_source_left H
  have hpbI : IsPullback (G.identity.left ≫ G.source.left) f.mapObjects.left
      f.mapObjects.left (H.identity.left ≫ H.source.left) := by
    rw [hs, hs']
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hflatI : Flat (H.identity.left ≫ H.source.left) := by rw [hs']; infer_instance
  have hiso : IsIso ((baseChangeNatTrans (pasteBase f.map_source_left.symm he)).app M.module) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      hpbI M.module
  have hrG : reindexHom G.identity.left M.alpha =
      (Scheme.Modules.pullbackCongr (hp G)).hom.app M.module := by
    rw [reindexHom_identity G M.alpha M.identity, pullbackCongr_hom_app_comp]
  have hbridge := reindexHom_pushforwardDescent f h M f.mapObjects.left H.identity.left
    G.identity.left he
  have hcongr := pullbackCongr_comp_baseChangeNatTrans
    (hp H) (hp G)
    (pasteBase f.map_target_left.symm he) (pasteBase f.map_source_left.symm he) M.module
  have hr : reindexHom H.identity.left (pushforwardDescent f h M) =
      (Scheme.Modules.pullbackCongr (hp H)).hom.app
        ((Scheme.Modules.pushforward f.mapObjects.left).obj M.module) := by
    rw [← cancel_mono ((baseChangeNatTrans
      (pasteBase f.map_source_left.symm he)).app M.module), hbridge, hcongr, hrG]
  simp [identityDescent, hr, Scheme.Modules.pullbackCongr]

/-- **Stacks Project, Tag 09VH.** Pushforward along a morphism of groupoid schemes, as a functor
on quasi-coherent modules equipped with groupoid descent data:  on objects it sends `(𝓕, α)` to
`(f_*𝓕, f_*α)`, and on morphisms it is the direct image of morphisms of modules. -/
@[stacks 09VH "the functor", sga "3 I 6.6.2" "more general"]
noncomputable def pushforwardFunctor :
    QuasicoherentModule G ⥤ QuasicoherentModule H where
  obj M :=
    { module := (Scheme.Modules.pushforward f.mapObjects.left).obj M.module
      isQuasicoherent := inferInstance
      alpha := pushforwardDescent f h M
      cocycle := pushforwardDescent_cocycle f h M
      identity := pushforwardDescent_identity f h M }
  map {M N} g :=
    { hom := (Scheme.Modules.pushforward f.mapObjects.left).map
        (QuasicoherentModule.Hom.hom g)
      comm := pushforwardDescent_naturality f h g }
  map_id M := by
    apply QuasicoherentModule.Hom.ext
    change (Scheme.Modules.pushforward f.mapObjects.left).map (𝟙 M.module) = 𝟙 _
    simp
  map_comp {M N K} g k := QuasicoherentModule.Hom.ext
    ((Scheme.Modules.pushforward f.mapObjects.left).map_comp
      (QuasicoherentModule.Hom.hom g) (QuasicoherentModule.Hom.hom k))

/-- **Stacks Project, Tag 09VH.** Pushforward along a morphism of groupoid schemes pushes the
underlying module forward along the map on objects. -/
@[stacks 09VH "underlying modules"]
theorem pushforwardFunctor_obj_module (M : QuasicoherentModule G) :
    ((pushforwardFunctor f h).obj M).module =
      (Scheme.Modules.pushforward f.mapObjects.left).obj M.module := by
  simp [pushforwardFunctor]

/-- **Stacks Project, Tag 09VH.** The descent morphism of a pushed-forward module is the
pushed-forward descent morphism. -/
@[stacks 09VH "descent morphisms"]
theorem pushforwardFunctor_obj_alpha (M : QuasicoherentModule G) :
    Eq.ndrec (motive := fun X =>
      (Scheme.Modules.pullback H.target.left).obj X ⟶
        (Scheme.Modules.pullback H.source.left).obj X)
      ((pushforwardFunctor f h).obj M).alpha (pushforwardFunctor_obj_module f h M) =
      pushforwardDescent f h M := by
  simp [pushforwardFunctor]

/-- **Stacks Project, Tag 09VH.** Pushforward of a morphism of quasi-coherent modules on a
groupoid scheme is the direct image of morphisms of modules. -/
@[stacks 09VH "morphisms"]
theorem pushforwardFunctor_map_hom {M N : QuasicoherentModule G} (g : M ⟶ N) :
    (pushforwardFunctor_obj_module f h M) ▸
      (pushforwardFunctor_obj_module f h N) ▸
        (QuasicoherentModule.Hom.hom ((pushforwardFunctor f h).map g)) =
      (Scheme.Modules.pushforward f.mapObjects.left).map
        (QuasicoherentModule.Hom.hom g) := by
  simp [pushforwardFunctor]

omit [QuasiCompact f.mapObjects.left] [QuasiSeparated f.mapObjects.left]
  [Flat H.source.left] [Flat H.target.left] in
/-- The pulled-back descent morphism is the inverse image along the arrow map of the original
descent morphism, read through the comparisons of the two composite inverse images around the
target and the source square. -/
theorem pullbackSquareIso_hom_comp_pullbackDescent (N : QuasicoherentModule H) :
    (Scheme.Modules.pullback f.mapArrows.left).map N.alpha ≫
        (Stacks.Modules.pullbackSquareIso f.mapObjects.left f.mapArrows.left
          H.source.left G.source.left f.map_source_left.symm).hom.app N.module =
      (Stacks.Modules.pullbackSquareIso f.mapObjects.left f.mapArrows.left
          H.target.left G.target.left f.map_target_left.symm).hom.app N.module ≫
        pullbackDescent f N := by
  simp only [pullbackDescent, reindexHom, Stacks.Modules.pullbackSquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    pullbackCongr_hom_app_comp_assoc, pullbackCongr_hom_app_self, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

/-- A morphism of modules out of the inverse image of the underlying module of a quasi-coherent
module on the target groupoid scheme is compatible with the pulled-back descent morphism exactly
when its adjunct is compatible with the pushed-forward descent morphism. -/
theorem pushforwardDescent_comm_iff (M : QuasicoherentModule G) (N : QuasicoherentModule H)
    (u : (Scheme.Modules.pullback f.mapObjects.left).obj N.module ⟶ M.module) :
    (N.alpha ≫ (Scheme.Modules.pullback H.source.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
            N.module M.module u) =
        (Scheme.Modules.pullback H.target.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
            N.module M.module u) ≫ pushforwardDescent f h M) ↔
      (pullbackDescent f N ≫ (Scheme.Modules.pullback G.source.left).map u =
        (Scheme.Modules.pullback G.target.left).map u ≫ M.alpha) := by
  have hbcS : IsIso ((baseChangeNatTrans f.map_source_left.symm).app M.module) :=
    isIso_pushforwardSourceBaseChange_app f h M.module
  have hdesc := pushforwardDescent_comp_pushforwardSourceBaseChange f h M
  simp only [pushforwardSourceBaseChangeIso_hom, pushforwardTargetBaseChangeIso_hom,
    pushforwardSourceBaseChange, pushforwardTargetBaseChange] at hdesc
  have EQ : (N.alpha ≫ (Scheme.Modules.pullback H.source.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module u)) ≫
      (baseChangeNatTrans f.map_source_left.symm).app M.module =
      (Scheme.Modules.pullbackPushforwardAdjunction f.mapArrows.left).homEquiv _ _
        ((Scheme.Modules.pullback f.mapArrows.left).map N.alpha ≫
          (Stacks.Modules.pullbackSquareIso f.mapObjects.left f.mapArrows.left
            H.source.left G.source.left f.map_source_left.symm).hom.app N.module ≫
          (Scheme.Modules.pullback G.source.left).map u) := by
    rw [Category.assoc, pullback_map_homEquiv_comp_baseChangeNatTrans,
      ← Adjunction.homEquiv_naturality_left]
  have EQ2 : ((Scheme.Modules.pullback H.target.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module u) ≫ pushforwardDescent f h M) ≫
      (baseChangeNatTrans f.map_source_left.symm).app M.module =
      (Scheme.Modules.pullbackPushforwardAdjunction f.mapArrows.left).homEquiv _ _
        ((Stacks.Modules.pullbackSquareIso f.mapObjects.left f.mapArrows.left
            H.target.left G.target.left f.map_target_left.symm).hom.app N.module ≫
          (Scheme.Modules.pullback G.target.left).map u ≫ M.alpha) := by
    rw [Category.assoc, hdesc, ← Category.assoc,
      pullback_map_homEquiv_comp_baseChangeNatTrans,
      ← Adjunction.homEquiv_naturality_right, Category.assoc]
  rw [← cancel_mono ((baseChangeNatTrans f.map_source_left.symm).app M.module), EQ, EQ2,
    Equiv.apply_eq_iff_eq, reassoc_of% pullbackSquareIso_hom_comp_pullbackDescent]
  exact cancel_epi _

/-- The adjunct of a morphism of modules compatible with the pulled-back descent morphism is
compatible with the pushed-forward descent morphism. -/
theorem pushforwardDescent_comm (M : QuasicoherentModule G) (N : QuasicoherentModule H)
    (u : (Scheme.Modules.pullback f.mapObjects.left).obj N.module ⟶ M.module)
    (hu : pullbackDescent f N ≫ (Scheme.Modules.pullback G.source.left).map u =
      (Scheme.Modules.pullback G.target.left).map u ≫ M.alpha) :
    N.alpha ≫ (Scheme.Modules.pullback H.source.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module u) =
      (Scheme.Modules.pullback H.target.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module u) ≫ pushforwardDescent f h M :=
  (pushforwardDescent_comm_iff f h M N u).2 hu

/-- The inverse adjunct of a morphism of modules compatible with the pushed-forward descent
morphism is compatible with the pulled-back descent morphism. -/
theorem pullbackDescent_comm (M : QuasicoherentModule G) (N : QuasicoherentModule H)
    (v : N.module ⟶ (Scheme.Modules.pushforward f.mapObjects.left).obj M.module)
    (hv : N.alpha ≫ (Scheme.Modules.pullback H.source.left).map v =
      (Scheme.Modules.pullback H.target.left).map v ≫ pushforwardDescent f h M) :
    pullbackDescent f N ≫ (Scheme.Modules.pullback G.source.left).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module).symm v) =
      (Scheme.Modules.pullback G.target.left).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
          N.module M.module).symm v) ≫ M.alpha := by
  have key := (pushforwardDescent_comm_iff f h M N
    (((Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
      N.module M.module).symm v)).1
  rw [Equiv.apply_symm_apply] at key
  exact key hv

/-- **Stacks Project, Tag 09VH.** Pushforward along a morphism of groupoid schemes is right
adjoint to the pullback functor of Tag 03LJ:  on underlying modules the adjunction is the
inverse-image--direct-image adjunction along the map on objects, under which the two
compatibility conditions with the descent morphisms correspond. -/
@[stacks 09VH "right adjointness to the pullback functor of Tag 03LJ"]
noncomputable def pullbackPushforwardAdjunction :
    pullbackFunctor f ⊣ pushforwardFunctor f h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N M =>
        { toFun := fun u =>
            { hom := (Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
                N.module M.module (QuasicoherentModule.Hom.hom u)
              comm := pushforwardDescent_comm f h M N (QuasicoherentModule.Hom.hom u)
                (QuasicoherentModule.Hom.comm u) }
          invFun := fun v =>
            { hom := ((Scheme.Modules.pullbackPushforwardAdjunction
                f.mapObjects.left).homEquiv N.module M.module).symm
                (QuasicoherentModule.Hom.hom v)
              comm := pullbackDescent_comm f h M N (QuasicoherentModule.Hom.hom v)
                (QuasicoherentModule.Hom.comm v) }
          left_inv := fun _ => QuasicoherentModule.Hom.ext (Equiv.symm_apply_apply _ _)
          right_inv := fun _ => QuasicoherentModule.Hom.ext (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm := fun k g => QuasicoherentModule.Hom.ext
        ((Scheme.Modules.pullbackPushforwardAdjunction
          f.mapObjects.left).homEquiv_naturality_left_symm
          (QuasicoherentModule.Hom.hom k) (QuasicoherentModule.Hom.hom g))
      homEquiv_naturality_right := fun u g => QuasicoherentModule.Hom.ext
        ((Scheme.Modules.pullbackPushforwardAdjunction
          f.mapObjects.left).homEquiv_naturality_right
          (QuasicoherentModule.Hom.hom u) (QuasicoherentModule.Hom.hom g)) }

/-- On underlying modules the adjunction between pullback and pushforward of quasi-coherent
modules on groupoid schemes is the inverse-image--direct-image adjunction along the map on
objects. -/
theorem pullbackPushforwardAdjunction_homEquiv_hom (N : QuasicoherentModule H)
    (M : QuasicoherentModule G) (u : (pullbackFunctor f).obj N ⟶ M) :
    QuasicoherentModule.Hom.hom
        ((pullbackPushforwardAdjunction f h).homEquiv N M u) =
      (Scheme.Modules.pullbackPushforwardAdjunction f.mapObjects.left).homEquiv
        N.module M.module (QuasicoherentModule.Hom.hom u) := by
  rw [pullbackPushforwardAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl


end GroupoidScheme

end Stacks.Groupoids

end
