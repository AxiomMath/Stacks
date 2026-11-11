module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ActionGroupoid

/-!
# Equivariant modules for an action of a group scheme

Let a group scheme `G` over `Y` act on a scheme `X` over `Y`.  An *equivariant quasi-coherent
module* on `X` is a quasi-coherent module `F` on `X` together with a descent morphism from the
pullback of `F` along the action map to its pullback along the projection, subject to a cocycle
law on pairs of composable arrows and a normalization along the unit section.  These are exactly
the quasi-coherent modules on the action groupoid scheme.

## Main definitions

* `AlgebraicGeometry.successiveAction` and `AlgebraicGeometry.identityAction` are the two sides
  of the cocycle and normalization conditions, written in the coordinates of the action.
* `AlgebraicGeometry.EquivariantModule` is an equivariant quasi-coherent module with its
  cocycle read on the object of composable pairs of the action, and
  `AlgebraicGeometry.EquivariantModule.Hom` a morphism of such.  Stacks' notion (Tag 03LF), with
  its cocycle on `G ×_Y G ×_Y X`, is `AlgebraicGeometry.EquivariantQuasicoherentModule` in
  `StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.EquivariantQuasicoherentModule`,
  where Stacks 03LL is proved.
* `Stacks.Groupoids.IsDescentCocycle` is the cocycle condition for a descent morphism along a
  span of schemes, stated for an arbitrary scheme of composable pairs.

## Main results

* `AlgebraicGeometry.equivariantModuleEquivalence` is the canonical equivalence between
  equivariant quasi-coherent modules for an action and quasi-coherent modules on the associated
  action groupoid scheme.
* `AlgebraicGeometry.equivariantModuleEquivalence_functor_obj_module`,
  `AlgebraicGeometry.equivariantModuleEquivalence_functor_obj_alpha` and
  `AlgebraicGeometry.equivariantModuleEquivalence_functor_map_hom` identify that equivalence:
  it changes neither the underlying module, nor the descent morphism, nor the underlying
  morphism of modules.
* `Stacks.Groupoids.isDescentCocycle_precomp` and
  `Stacks.Groupoids.isDescentCocycle_iff_of_iso` transport the cocycle condition along a
  change of the scheme of composable pairs.

## Implementation notes

The action-coordinate category is defined here because the groupoid-module structure is not
itself a definition in the coordinates of the original action.  The two cocycle conditions are
compared through `Stacks.Groupoids.IsDescentCocycle`, which abstracts both: a descent morphism
`α` between the pullbacks along two morphisms `t, s : R ⟶ U` satisfies the cocycle condition
relative to three morphisms `p, q, c : D ⟶ R` out of a scheme of composable pairs, and changing
`D` by an isomorphism compatible with `p`, `q` and `c` does not change the condition.  The
action groupoid and the action present the same span with two isomorphic schemes of composable
pairs.

## References

* [Stacks Project, Tag 03LF](https://stacks.math.columbia.edu/tag/03LF)
* [Stacks Project, Tag 03LL](https://stacks.math.columbia.edu/tag/03LL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-- The cocycle condition on a descent morphism `α` between the pullbacks of a module along
`t` and along `s`, read on a scheme `D` of composable pairs with first arrow `p`, second arrow
`q` and composite `c`. -/
def IsDescentCocycle {D R U : Scheme.{u}} (p q c : D ⟶ R) (t s : R ⟶ U)
    (ht : c ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : c ≫ s = q ≫ s) {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F) : Prop :=
  (Scheme.Modules.pullbackCongr ht).hom.app F ≫ reindexHom p α ≫
      (Scheme.Modules.pullbackCongr hm).hom.app F ≫ reindexHom q α ≫
      (Scheme.Modules.pullbackCongr hs.symm).hom.app F =
    reindexHom c α

/-- The cocycle condition is stable under precomposing the three morphisms out of the scheme of
composable pairs with a fixed morphism. -/
theorem isDescentCocycle_comp_left {D E R U : Scheme.{u}} (f : E ⟶ D) (p q c : D ⟶ R)
    (t s : R ⟶ U) (ht : c ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : c ≫ s = q ≫ s)
    {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
    (hc : IsDescentCocycle p q c t s ht hm hs α)
    (ht' : (f ≫ c) ≫ t = (f ≫ p) ≫ t) (hm' : (f ≫ p) ≫ s = (f ≫ q) ≫ t)
    (hs' : (f ≫ c) ≫ s = (f ≫ q) ≫ s) :
    IsDescentCocycle (f ≫ p) (f ≫ q) (f ≫ c) t s ht' hm' hs' α := by
  have h := congrArg (reindexHom f (g := c ≫ t) (h := c ≫ s) (F := F)) hc
  simp only [reindexHom_comp, reindexHom_congr, reindexHom_assoc_rev] at h
  have h' := congrArg (fun z =>
    (Scheme.Modules.pullbackCongr (Category.assoc f c t)).hom.app F ≫ z ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f c s).symm).hom.app F) h
  simpa only [IsDescentCocycle, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id] using h'

/-- The cocycle condition transports along a morphism of schemes of composable pairs compatible
with the two arrows and their composite. -/
theorem isDescentCocycle_precomp {D E R U : Scheme.{u}} (f : E ⟶ D) (p q c : D ⟶ R)
    (t s : R ⟶ U) (ht : c ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : c ≫ s = q ≫ s)
    {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
    (hc : IsDescentCocycle p q c t s ht hm hs α) (p' q' c' : E ⟶ R)
    (hp : f ≫ p = p') (hq : f ≫ q = q') (hcc : f ≫ c = c')
    (ht' : c' ≫ t = p' ≫ t) (hm' : p' ≫ s = q' ≫ t) (hs' : c' ≫ s = q' ≫ s) :
    IsDescentCocycle p' q' c' t s ht' hm' hs' α := by
  subst hp hq hcc
  exact isDescentCocycle_comp_left f p q c t s ht hm hs α hc ht' hm' hs'

/-- Two presentations of the scheme of composable pairs related by an isomorphism compatible
with the two arrows and their composite impose the same cocycle condition. -/
theorem isDescentCocycle_iff_of_iso {D E R U : Scheme.{u}} (e : E ≅ D) (p q c : D ⟶ R)
    (t s : R ⟶ U) (ht : c ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : c ≫ s = q ≫ s)
    {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
    (p' q' c' : E ⟶ R) (hp : e.hom ≫ p = p') (hq : e.hom ≫ q = q') (hc : e.hom ≫ c = c')
    (ht' : c' ≫ t = p' ≫ t) (hm' : p' ≫ s = q' ≫ t) (hs' : c' ≫ s = q' ≫ s) :
    IsDescentCocycle p q c t s ht hm hs α ↔ IsDescentCocycle p' q' c' t s ht' hm' hs' α :=
  ⟨fun h => isDescentCocycle_precomp e.hom p q c t s ht hm hs α h p' q' c' hp hq hc ht' hm' hs',
    fun h => isDescentCocycle_precomp e.inv p' q' c' t s ht' hm' hs' α h p q c
      ((Iso.inv_comp_eq e).2 hp.symm) ((Iso.inv_comp_eq e).2 hq.symm)
      ((Iso.inv_comp_eq e).2 hc.symm) ht hm hs⟩

end Stacks.Groupoids

namespace AlgebraicGeometry

open Stacks.Groupoids

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

omit [ModObj G X] in
/-- The unit section of an action is a section of the projection. -/
theorem actionIdentity_source : Stacks.Groupoids.ActionGroupoid.identity G X ≫ snd G X = 𝟙 X :=
  Stacks.Groupoids.ActionGroupoid.identity_source G X

/-- The unit section of an action is a section of the action map. -/
theorem actionIdentity_target : Stacks.Groupoids.ActionGroupoid.identity G X ≫ γ[G,X] = 𝟙 X :=
  Stacks.Groupoids.ActionGroupoid.identity_target G X

omit [ModObj G X] in
/-- The unit section of an action is a section of the projection, on underlying schemes. -/
theorem actionIdentity_source_left :
    (Stacks.Groupoids.ActionGroupoid.identity G X).left ≫ (snd G X).left = 𝟙 X.left :=
  congrArg Over.Hom.left (actionIdentity_source Y G X)

/-- The unit section of an action is a section of the action map, on underlying schemes. -/
theorem actionIdentity_target_left :
    (Stacks.Groupoids.ActionGroupoid.identity G X).left ≫ γ[G,X].left = 𝟙 X.left :=
  congrArg Over.Hom.left (actionIdentity_target Y G X)

/-- Applying a descent morphism for an action to the two arrows of a composable pair in
succession. -/
noncomputable def successiveAction {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    (Scheme.Modules.pullback
        ((Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left)).obj F ⟶
      (Scheme.Modules.pullback
        ((Stacks.Groupoids.ActionGroupoid.composition G X ≫ snd G X).left)).obj F :=
  (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (actionComposition_target Y G X))).hom.app F ≫
    reindexHom (pullback.fst (snd G X) γ[G,X]).left α ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (pullback.condition : pullback.fst (snd G X) γ[G,X] ≫ snd G X =
        pullback.snd (snd G X) γ[G,X] ≫ γ[G,X]))).hom.app F ≫
    reindexHom (pullback.snd (snd G X) γ[G,X]).left α ≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (actionComposition_source Y G X).symm)).hom.app F

/-- The endomorphism obtained by restricting a descent morphism for an action to the unit
section. -/
noncomputable def identityAction {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) : F ⟶ F :=
  (Scheme.Modules.pullbackId X.left).inv.app F ≫
    (Scheme.Modules.pullbackCongr (actionIdentity_target_left Y G X).symm).hom.app F ≫
    reindexHom (Stacks.Groupoids.ActionGroupoid.identity G X).left α ≫
    (Scheme.Modules.pullbackCongr (actionIdentity_source_left Y G X)).hom.app F ≫
    (Scheme.Modules.pullbackId X.left).hom.app F

/-- A quasi-coherent module on `X` equivariant for a given action of `G`, with its cocycle
condition read on the object `pullback (snd G X) γ[G,X]` of composable pairs of the action
rather than on `G ×_Y G ×_Y X`: a quasi-coherent module `F` with a map `α : a^*F ⟶ pr_1^*F`
satisfying that cocycle condition and restricting to the identity along the unit section.
Stacks' own notion (Tag 03LF), with its cocycle on `G ×_Y G ×_Y X`, is
`AlgebraicGeometry.EquivariantQuasicoherentModule`, and
`AlgebraicGeometry.equivariantQuasicoherentModuleEquivEquivariantModule` identifies the two. -/
@[sga "3 I 6.5"]
structure EquivariantModule where
  /-- The underlying module on the scheme acted on. -/
  module : X.left.Modules
  /-- The underlying module is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The descent morphism, from the pullback along the action to the pullback along the
  projection. -/
  alpha : (Scheme.Modules.pullback γ[G,X].left).obj module ⟶
    (Scheme.Modules.pullback (snd G X).left).obj module
  /-- Applying the descent morphism to two composable arrows in succession is the same as
  applying it to their composite. -/
  cocycle : successiveAction Y G X alpha =
    reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left alpha
  /-- The descent morphism restricts to the identity along the unit section. -/
  identity : identityAction Y G X alpha = 𝟙 module

namespace EquivariantModule

variable {Y G X}

/-- The quasicoherence witness carried by an equivariant module is available to typeclass
inference. -/
instance (M : EquivariantModule Y G X) : M.module.IsQuasicoherent := M.isQuasicoherent

/-- A morphism of equivariant modules is a morphism of the underlying modules which
intertwines the two descent morphisms. -/
@[ext]
structure Hom (M N : EquivariantModule Y G X) where
  /-- The underlying morphism of modules. -/
  hom : M.module ⟶ N.module
  /-- Compatibility with the descent morphisms. -/
  comm : M.alpha ≫ (Scheme.Modules.pullback (snd G X).left).map hom =
    (Scheme.Modules.pullback γ[G,X].left).map hom ≫ N.alpha

/-- Equivariant quasi-coherent modules and their equivariant morphisms form a category. -/
instance : Category (EquivariantModule Y G X) where
  Hom := Hom
  id M :=
    { hom := 𝟙 M.module
      comm := by
        simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm, Category.assoc,
          g.comm, ← Category.assoc] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

end EquivariantModule

/-- The cocycle condition for a descent morphism on an action is the general cocycle condition
for the span formed by the action map and the projection, read on the scheme of composable
pairs of the action. -/
theorem isDescentCocycle_iff_successiveAction_eq {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    IsDescentCocycle (pullback.fst (snd G X) γ[G,X]).left
        (pullback.snd (snd G X) γ[G,X]).left (Stacks.Groupoids.ActionGroupoid.composition G X).left
        γ[G,X].left (snd G X).left
        (congrArg Over.Hom.left (actionComposition_target Y G X))
        (congrArg Over.Hom.left (pullback.condition :
          pullback.fst (snd G X) γ[G,X] ≫ snd G X =
            pullback.snd (snd G X) γ[G,X] ≫ γ[G,X]))
        (congrArg Over.Hom.left (actionComposition_source Y G X)) α ↔
      successiveAction Y G X α =
        reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left α :=
  Iff.rfl

/-- The cocycle condition for a descent morphism on a groupoid scheme is the general cocycle
condition for the span formed by its target and source. -/
theorem isDescentCocycle_iff_successiveDescent_eq (H : GroupoidScheme S)
    {F : H.objects.left.Modules}
    (α : (Scheme.Modules.pullback H.target.left).obj F ⟶
      (Scheme.Modules.pullback H.source.left).obj F) :
    IsDescentCocycle (pullback.fst H.source H.target).left
        (pullback.snd H.source H.target).left H.comp.left H.target.left H.source.left
        (congrArg Over.Hom.left H.target_comp)
        (congrArg Over.Hom.left (pullback.condition :
          pullback.fst H.source H.target ≫ H.source =
            pullback.snd H.source H.target ≫ H.target))
        (congrArg Over.Hom.left H.source_comp) α ↔
      GroupoidScheme.successiveDescent H α = reindexHom H.comp.left α :=
  Iff.rfl

/-- The cocycle condition for an action and the cocycle condition on the associated action
groupoid scheme are the same condition: the two schemes of composable pairs are canonically
isomorphic, compatibly with the two arrows and their composite. -/
theorem successiveAction_eq_iff_successiveDescent_eq {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    successiveAction Y G X α = reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left α ↔
      GroupoidScheme.successiveDescent (groupoidSchemeOfAction Y G X).groupoid α =
        reindexHom (groupoidSchemeOfAction Y G X).groupoid.comp.left α := by
  have hc : ((Over.forget S).mapIso
        (groupoidSchemeOfAction Y G X).compositionDomainIso).hom ≫
      (Stacks.Groupoids.ActionGroupoid.composition G X).left =
        (groupoidSchemeOfAction Y G X).groupoid.comp.left :=
    (congrArg Over.Hom.left (eq_of_heq (groupoidSchemeOfAction Y G X).comp_eq)).symm
  refine (isDescentCocycle_iff_successiveAction_eq Y G X α).symm.trans (Iff.trans ?_
    (isDescentCocycle_iff_successiveDescent_eq (groupoidSchemeOfAction Y G X).groupoid α))
  exact isDescentCocycle_iff_of_iso
    ((Over.forget S).mapIso (groupoidSchemeOfAction Y G X).compositionDomainIso)
    _ _ _ _ _ _ _ _ α _ _ _
    (congrArg Over.Hom.left (groupoidSchemeOfAction Y G X).compositionDomainIso_fst)
    (congrArg Over.Hom.left (groupoidSchemeOfAction Y G X).compositionDomainIso_snd) hc _ _ _

/-- Restricting a descent morphism to the unit section of an action is restricting it to the
identity section of the action groupoid scheme. -/
theorem identityAction_eq_identityDescent {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    identityAction Y G X α =
      GroupoidScheme.identityDescent (groupoidSchemeOfAction Y G X).groupoid α :=
  rfl

/-- An equivariant module for an action is a quasi-coherent module on the action groupoid
scheme. -/
@[simps obj_module obj_alpha map_hom]
noncomputable def toActionGroupoidModule :
    EquivariantModule Y G X ⥤
      GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid where
  obj M :=
    { module := M.module
      isQuasicoherent := M.isQuasicoherent
      alpha := M.alpha
      cocycle := (successiveAction_eq_iff_successiveDescent_eq Y G X M.alpha).mp M.cocycle
      identity :=
        (identityAction_eq_identityDescent Y G X M.alpha).symm.trans M.identity }
  map f := { hom := f.hom, comm := f.comm }
  map_id _ := GroupoidScheme.QuasicoherentModule.Hom.ext rfl
  map_comp _ _ := GroupoidScheme.QuasicoherentModule.Hom.ext rfl

/-- A quasi-coherent module on the action groupoid scheme is an equivariant module for the
action. -/
@[simps obj_module obj_alpha map_hom]
noncomputable def ofActionGroupoidModule :
    GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid ⥤
      EquivariantModule Y G X where
  obj M :=
    { module := M.module
      isQuasicoherent := M.isQuasicoherent
      alpha := M.alpha
      cocycle := (successiveAction_eq_iff_successiveDescent_eq Y G X M.alpha).mpr M.cocycle
      identity := (identityAction_eq_identityDescent Y G X M.alpha).trans M.identity }
  map f := { hom := f.hom, comm := f.comm }
  map_id _ := EquivariantModule.Hom.ext rfl
  map_comp _ _ := EquivariantModule.Hom.ext rfl

/-- Equivariant modules for an action of a group scheme, with the cocycle read on composable
pairs, are the same as quasi-coherent modules on the associated action groupoid scheme.  The two
cocycle conditions are read on isomorphic presentations of the same scheme of composable pairs,
so this is close to definitional; Stacks 03LL, starting from the cocycle on `G ×_Y G ×_Y X`, is
`AlgebraicGeometry.equivariantQuasicoherentModuleEquivalence`. -/
noncomputable def equivariantModuleEquivalence :
    EquivariantModule Y G X ≌
      GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid :=
  CategoryTheory.Equivalence.mk (toActionGroupoidModule Y G X) (ofActionGroupoidModule Y G X)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
      EquivariantModule.Hom.ext ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
      GroupoidScheme.QuasicoherentModule.Hom.ext
        ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm))

/-- The functor underlying the canonical comparison is the comparison written out on objects
and morphisms. -/
theorem equivariantModuleEquivalence_functor :
    (equivariantModuleEquivalence Y G X).functor = toActionGroupoidModule Y G X :=
  rfl

/-- The canonical comparison leaves the underlying quasi-coherent module unchanged. -/
theorem equivariantModuleEquivalence_functor_obj_module (M : EquivariantModule Y G X) :
    ((toActionGroupoidModule Y G X).obj M).module = M.module :=
  rfl

/-- The canonical comparison leaves the descent morphism unchanged. -/
theorem equivariantModuleEquivalence_functor_obj_alpha (M : EquivariantModule Y G X) :
    ((toActionGroupoidModule Y G X).obj M).alpha = M.alpha :=
  rfl

/-- On morphisms the canonical comparison is the identity on the underlying morphism of
modules. -/
theorem equivariantModuleEquivalence_functor_map_hom {M N : EquivariantModule Y G X}
    (f : M ⟶ N) :
    ((toActionGroupoidModule Y G X).map f).hom = f.hom :=
  rfl

end AlgebraicGeometry

end
