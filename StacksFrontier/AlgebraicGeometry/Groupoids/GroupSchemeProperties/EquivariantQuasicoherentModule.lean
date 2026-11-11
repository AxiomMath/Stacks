module

public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.EquivariantModule

/-!
# Equivariant quasi-coherent modules in the coordinates of the action

Let a group scheme `(G, m)` over `Y` act on a scheme `X` over `Y` by `a : G ×_Y X ⟶ X`.
Stacks' definition of a `G`-equivariant quasi-coherent module (Tag 03LF) is a quasi-coherent
module `F` on `X` with a map `α : a^*F ⟶ pr^*F` on `G ×_Y X` whose cocycle condition lives on
the triple product `G ×_Y G ×_Y X`: the three maps `1_G × a`, `m × 1_X` and the projection
`(g, g', x) ↦ (g', x)` to `G ×_Y X` are used to compare
`(m × 1_X)^*α` with `pr^*α ∘ (1_G × a)^*α`.  Stacks Tag 03LL says these are exactly the
quasi-coherent modules on the action groupoid `(X, G ×_Y X, s, t, c)`, whose cocycle condition
lives on the scheme `R ×_{s, X, t} R` of composable pairs.

## Main definitions

* `Stacks.Groupoids.ActionGroupoid.tripleIsoComposablePairs` identifies `G ⊗ (G ⊗ X)` with the
  object of composable pairs of the action groupoid, by `(g, g', x) ↦ ((g, g' • x), (g', x))`.
* `AlgebraicGeometry.IsEquivariantCocycle` is the cocycle condition of Stacks 03LF, on
  `G ⊗ (G ⊗ X)`.
* `AlgebraicGeometry.EquivariantQuasicoherentModule` is Stacks' equivariant quasi-coherent
  module, and `AlgebraicGeometry.EquivariantQuasicoherentModule.Hom` a morphism of such.

## Main results

* `Stacks.Groupoids.ActionGroupoid.tripleIsoComposablePairs_hom_fst`,
  `Stacks.Groupoids.ActionGroupoid.tripleIsoComposablePairs_hom_snd` and
  `Stacks.Groupoids.ActionGroupoid.tripleIsoComposablePairs_hom_composition`: under that
  identification the first arrow is `1_G × a`, the second arrow is the projection and the
  composite is `m × 1_X`.
* `AlgebraicGeometry.isEquivariantCocycle_iff_successiveDescent_eq`: the cocycle condition of
  03LF is the cocycle condition of a quasi-coherent module on the action groupoid.
* `AlgebraicGeometry.equivariantQuasicoherentModuleEquivalence` is Stacks 03LL: the rule
  `(F, α) ↦ (F, α)` is an equivalence between equivariant quasi-coherent modules and
  quasi-coherent modules on the action groupoid scheme.
* `AlgebraicGeometry.equivariantQuasicoherentModuleEquivEquivariantModule` identifies Stacks'
  notion with `AlgebraicGeometry.EquivariantModule`, whose cocycle is stated on the object of
  composable pairs.

## Implementation notes

The triple product `G ×_Y G ×_Y X` is the iterated monoidal product `G ⊗ (G ⊗ X)` in
`Over Y`, and `m × 1_X` is `(α_ G G X).inv ≫ μ[G] ▷ X`.  The unit condition of 03LF,
`(e × 1_X)^*α = id`, is `AlgebraicGeometry.identityAction`, which pulls `α` back along
`x ↦ (e, x)`.

## References

* [Stacks Project, Tag 03LF](https://stacks.math.columbia.edu/tag/03LF)
* [Stacks Project, Tag 03LL](https://stacks.math.columbia.edu/tag/03LL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

namespace Stacks.Groupoids.ActionGroupoid

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  (G X : C) [GrpObj G] [ModObj G X]

/-- The map `(g, g', x) ↦ ((g, g' • x), (g', x))` from the triple product to the object of
composable pairs of the action groupoid. -/
noncomputable def tripleToComposablePairs : G ⊗ (G ⊗ X) ⟶ pullback (snd G X) γ[G,X] :=
  pullback.lift (G ◁ γ[G,X]) (snd G (G ⊗ X)) (whiskerLeft_snd _ _)

/-- The first arrow of the composable pair attached to `(g, g', x)` is `(g, g' • x)`. -/
@[reassoc (attr := simp)]
theorem tripleToComposablePairs_fst :
    tripleToComposablePairs G X ≫ pullback.fst (snd G X) γ[G,X] = G ◁ γ[G,X] :=
  pullback.lift_fst _ _ _

/-- The second arrow of the composable pair attached to `(g, g', x)` is `(g', x)`. -/
@[reassoc (attr := simp)]
theorem tripleToComposablePairs_snd :
    tripleToComposablePairs G X ≫ pullback.snd (snd G X) γ[G,X] = snd G (G ⊗ X) :=
  pullback.lift_snd _ _ _

/-- The triple product `G ⊗ (G ⊗ X)` is the object of composable pairs of the action groupoid:
`(g, g', x)` is the pair of arrows `(g, g' • x)` and `(g', x)`. -/
noncomputable def tripleIsoComposablePairs : G ⊗ (G ⊗ X) ≅ pullback (snd G X) γ[G,X] where
  hom := tripleToComposablePairs G X
  inv := lift (pullback.fst (snd G X) γ[G,X] ≫ fst G X) (pullback.snd (snd G X) γ[G,X])
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, tripleToComposablePairs_fst_assoc, whiskerLeft_fst,
        Category.id_comp]
      rfl
    · rw [Category.assoc, lift_snd, tripleToComposablePairs_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, tripleToComposablePairs_fst, Category.id_comp]
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerLeft_fst]
        exact lift_fst _ _
      · rw [Category.assoc, whiskerLeft_snd]
        exact (lift_snd_assoc _ _ _).trans
          (pullback.condition (f := snd G X) (g := γ[G,X])).symm
    · rw [Category.assoc, tripleToComposablePairs_snd]
      exact (lift_snd _ _).trans (Category.id_comp _).symm

/-- Under `tripleIsoComposablePairs`, the first arrow of a composable pair is `1_G × a`. -/
theorem tripleIsoComposablePairs_hom_fst :
    (tripleIsoComposablePairs G X).hom ≫ pullback.fst (snd G X) γ[G,X] = G ◁ γ[G,X] :=
  tripleToComposablePairs_fst G X

/-- Under `tripleIsoComposablePairs`, the second arrow of a composable pair is the projection
`(g, g', x) ↦ (g', x)`. -/
theorem tripleIsoComposablePairs_hom_snd :
    (tripleIsoComposablePairs G X).hom ≫ pullback.snd (snd G X) γ[G,X] = snd G (G ⊗ X) :=
  tripleToComposablePairs_snd G X

/-- Under `tripleIsoComposablePairs`, composition in the action groupoid is `m × 1_X`. -/
theorem tripleIsoComposablePairs_hom_composition :
    (tripleIsoComposablePairs G X).hom ≫ composition G X = (α_ G G X).inv ≫ μ[G] ▷ X := by
  rw [show (tripleIsoComposablePairs G X).hom =
      pullback.lift (G ◁ γ[G,X]) (snd G (G ⊗ X)) (whiskerLeft_snd _ _) from rfl,
    composition_eval]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Hom.mul_def, Category.assoc, whiskerRight_fst, ← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · simp

end Stacks.Groupoids.ActionGroupoid

namespace AlgebraicGeometry

open Stacks.Groupoids

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

/-- The composite of `m × 1_X` with the action is the composite of `1_G × a` with the action:
`(g g') • x = g • (g' • x)`. -/
theorem multiplication_action_eq_whiskerLeft_action :
    ((α_ G G X).inv ≫ μ[G] ▷ X) ≫ γ[G,X] = (G ◁ γ[G,X]) ≫ γ[G,X] := by
  rw [Category.assoc]
  exact (Iso.inv_comp_eq _).2 (ModObj.mul_smul (M := G) (X := X))

/-- The composite of `1_G × a` with the projection is the composite of the projection with the
action. -/
theorem whiskerLeft_action_snd :
    (G ◁ γ[G,X]) ≫ snd G X = snd G (G ⊗ X) ≫ γ[G,X] :=
  whiskerLeft_snd _ _

omit [ModObj G X] in
/-- The composite of `m × 1_X` with the projection is the composite of the projection with
itself. -/
theorem multiplication_snd :
    ((α_ G G X).inv ≫ μ[G] ▷ X) ≫ snd G X = snd G (G ⊗ X) ≫ snd G X := by
  simp

/-- The cocycle condition of an equivariant module (Stacks 03LF), on `G ×_Y G ×_Y X`: the map
`(m × 1_X)^*α` agrees with `pr^*α ∘ (1_G × a)^*α`, where `pr : (g, g', x) ↦ (g', x)`, after the
canonical identifications of the pullbacks of `F` along equal composites. -/
def IsEquivariantCocycle {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) : Prop :=
  IsDescentCocycle (G ◁ γ[G,X]).left (snd G (G ⊗ X)).left ((α_ G G X).inv ≫ μ[G] ▷ X).left
    γ[G,X].left (snd G X).left
    (congrArg Over.Hom.left (multiplication_action_eq_whiskerLeft_action Y G X))
    (congrArg Over.Hom.left (whiskerLeft_action_snd Y G X))
    (congrArg Over.Hom.left (multiplication_snd Y G X)) α

/-- The cocycle condition of Stacks 03LF on `G ×_Y G ×_Y X` is the cocycle condition on the
object of composable pairs of the action, transported along
`Stacks.Groupoids.ActionGroupoid.tripleIsoComposablePairs`. -/
theorem isEquivariantCocycle_iff_successiveAction_eq {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    IsEquivariantCocycle Y G X α ↔
      successiveAction Y G X α =
        reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left α :=
  ((isDescentCocycle_iff_successiveAction_eq Y G X α).symm.trans
    (isDescentCocycle_iff_of_iso
      ((Over.forget Y.left).mapIso (ActionGroupoid.tripleIsoComposablePairs G X))
      _ _ _ _ _ _ _ _ α _ _ _
      (congrArg Over.Hom.left (ActionGroupoid.tripleIsoComposablePairs_hom_fst G X))
      (congrArg Over.Hom.left (ActionGroupoid.tripleIsoComposablePairs_hom_snd G X))
      (congrArg Over.Hom.left (ActionGroupoid.tripleIsoComposablePairs_hom_composition G X))
      _ _ _)).symm

/-- The cocycle condition of Stacks 03LF on `G ×_Y G ×_Y X` is the cocycle condition of a
quasi-coherent module on the action groupoid scheme, on `R ×_{s, X, t} R`. -/
theorem isEquivariantCocycle_iff_successiveDescent_eq {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F) :
    IsEquivariantCocycle Y G X α ↔
      GroupoidScheme.successiveDescent (groupoidSchemeOfAction Y G X).groupoid α =
        reindexHom (groupoidSchemeOfAction Y G X).groupoid.comp.left α :=
  (isEquivariantCocycle_iff_successiveAction_eq Y G X α).trans
    (successiveAction_eq_iff_successiveDescent_eq Y G X α)

/-- **Stacks Project, Tag 03LF.** A `G`-equivariant quasi-coherent module on `X`: a
quasi-coherent module `F` on `X` with a map `α : a^*F ⟶ pr_1^*F` on `G ×_Y X` such that
`(m × 1_X)^*α = pr^*α ∘ (1_G × a)^*α` on `G ×_Y G ×_Y X` and `(e × 1_X)^*α` is the identity of
`F`. -/
@[stacks 03LF "equivariant quasi-coherent module", sga "3 I 6.5.1" "equivariant module"]
structure EquivariantQuasicoherentModule where
  /-- The underlying module on the scheme acted on. -/
  module : X.left.Modules
  /-- The underlying module is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The map `α : a^*F ⟶ pr_1^*F`. -/
  alpha : (Scheme.Modules.pullback γ[G,X].left).obj module ⟶
    (Scheme.Modules.pullback (snd G X).left).obj module
  /-- The cocycle condition on `G ×_Y G ×_Y X`. -/
  cocycle : IsEquivariantCocycle Y G X alpha
  /-- The pullback `(e × 1_X)^*α` is the identity map. -/
  identity : identityAction Y G X alpha = 𝟙 module

namespace EquivariantQuasicoherentModule

variable {Y G X}

/-- The quasicoherence witness carried by an equivariant quasi-coherent module is available to
typeclass inference. -/
instance (M : EquivariantQuasicoherentModule Y G X) : M.module.IsQuasicoherent :=
  M.isQuasicoherent

/-- A morphism of equivariant quasi-coherent modules is a morphism of the underlying modules
which intertwines the two maps `α`. -/
@[ext]
structure Hom (M N : EquivariantQuasicoherentModule Y G X) where
  /-- The underlying morphism of modules. -/
  hom : M.module ⟶ N.module
  /-- Compatibility with the maps `α`. -/
  comm : M.alpha ≫ (Scheme.Modules.pullback (snd G X).left).map hom =
    (Scheme.Modules.pullback γ[G,X].left).map hom ≫ N.alpha

/-- Equivariant quasi-coherent modules and their equivariant morphisms form a category. -/
instance : Category (EquivariantQuasicoherentModule Y G X) where
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

end EquivariantQuasicoherentModule

/-- An equivariant quasi-coherent module is a quasi-coherent module on the action groupoid
scheme, with the same module and the same `α`. -/
@[simps obj_module obj_alpha map_hom]
noncomputable def EquivariantQuasicoherentModule.toActionGroupoidModule :
    EquivariantQuasicoherentModule Y G X ⥤
      GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid where
  obj M :=
    { module := M.module
      isQuasicoherent := M.isQuasicoherent
      alpha := M.alpha
      cocycle := (isEquivariantCocycle_iff_successiveDescent_eq Y G X M.alpha).mp M.cocycle
      identity :=
        (identityAction_eq_identityDescent Y G X M.alpha).symm.trans M.identity }
  map f := { hom := f.hom, comm := f.comm }
  map_id _ := GroupoidScheme.QuasicoherentModule.Hom.ext rfl
  map_comp _ _ := GroupoidScheme.QuasicoherentModule.Hom.ext rfl

/-- A quasi-coherent module on the action groupoid scheme is an equivariant quasi-coherent
module, with the same module and the same `α`. -/
@[simps obj_module obj_alpha map_hom]
noncomputable def EquivariantQuasicoherentModule.ofActionGroupoidModule :
    GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid ⥤
      EquivariantQuasicoherentModule Y G X where
  obj M :=
    { module := M.module
      isQuasicoherent := M.isQuasicoherent
      alpha := M.alpha
      cocycle := (isEquivariantCocycle_iff_successiveDescent_eq Y G X M.alpha).mpr M.cocycle
      identity := (identityAction_eq_identityDescent Y G X M.alpha).trans M.identity }
  map f := { hom := f.hom, comm := f.comm }
  map_id _ := EquivariantQuasicoherentModule.Hom.ext rfl
  map_comp _ _ := EquivariantQuasicoherentModule.Hom.ext rfl

/-- **Stacks Project, Tag 03LL.** The rule `(F, α) ↦ (F, α)` is an equivalence between
`G`-equivariant quasi-coherent modules on `X` (Stacks 03LF, cocycle on `G ×_Y G ×_Y X`) and
quasi-coherent modules on the action groupoid scheme `(X, G ×_Y X, s, t, c)` (cocycle on
`R ×_{s, X, t} R`). -/
@[stacks 03LL "the equivalence (F, α) ↦ (F, α)"]
noncomputable def equivariantQuasicoherentModuleEquivalence :
    EquivariantQuasicoherentModule Y G X ≌
      GroupoidScheme.QuasicoherentModule (groupoidSchemeOfAction Y G X).groupoid :=
  CategoryTheory.Equivalence.mk (EquivariantQuasicoherentModule.toActionGroupoidModule Y G X)
    (EquivariantQuasicoherentModule.ofActionGroupoidModule Y G X)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
      EquivariantQuasicoherentModule.Hom.ext
        ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
      GroupoidScheme.QuasicoherentModule.Hom.ext
        ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm))

/-- **Stacks Project, Tag 03LL.** The equivalence keeps the underlying quasi-coherent module. -/
@[stacks 03LL "underlying module"]
theorem equivariantQuasicoherentModuleEquivalence_functor_obj_module
    (M : EquivariantQuasicoherentModule Y G X) :
    ((equivariantQuasicoherentModuleEquivalence Y G X).functor.obj M).module = M.module :=
  rfl

/-- **Stacks Project, Tag 03LL.** The equivalence keeps the map `α`. -/
@[stacks 03LL "the map α"]
theorem equivariantQuasicoherentModuleEquivalence_functor_obj_alpha
    (M : EquivariantQuasicoherentModule Y G X) :
    ((equivariantQuasicoherentModuleEquivalence Y G X).functor.obj M).alpha = M.alpha :=
  rfl

/-- **Stacks Project, Tag 03LL.** On morphisms the equivalence is the identity on the underlying
morphism of modules. -/
@[stacks 03LL "morphisms"]
theorem equivariantQuasicoherentModuleEquivalence_functor_map_hom
    {M N : EquivariantQuasicoherentModule Y G X} (f : M ⟶ N) :
    ((equivariantQuasicoherentModuleEquivalence Y G X).functor.map f).hom = f.hom :=
  rfl

/-- Stacks' equivariant quasi-coherent modules (cocycle on `G ×_Y G ×_Y X`) are the same as
`AlgebraicGeometry.EquivariantModule` (cocycle on the object of composable pairs of the action),
by `(F, α) ↦ (F, α)`. -/
@[stacks 03LF "equivalent formulation on composable pairs"]
noncomputable def equivariantQuasicoherentModuleEquivEquivariantModule :
    EquivariantQuasicoherentModule Y G X ≌ EquivariantModule Y G X where
  functor :=
    { obj M :=
        { module := M.module
          isQuasicoherent := M.isQuasicoherent
          alpha := M.alpha
          cocycle := (isEquivariantCocycle_iff_successiveAction_eq Y G X M.alpha).mp M.cocycle
          identity := M.identity }
      map f := { hom := f.hom, comm := f.comm }
      map_id _ := EquivariantModule.Hom.ext rfl
      map_comp _ _ := EquivariantModule.Hom.ext rfl }
  inverse :=
    { obj M :=
        { module := M.module
          isQuasicoherent := M.isQuasicoherent
          alpha := M.alpha
          cocycle := (isEquivariantCocycle_iff_successiveAction_eq Y G X M.alpha).mpr M.cocycle
          identity := M.identity }
      map f := { hom := f.hom, comm := f.comm }
      map_id _ := EquivariantQuasicoherentModule.Hom.ext rfl
      map_comp _ _ := EquivariantQuasicoherentModule.Hom.ext rfl }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
    EquivariantQuasicoherentModule.Hom.ext
      ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
    EquivariantModule.Hom.ext ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)
  functor_unitIso_comp _ := EquivariantModule.Hom.ext (Category.id_comp _)

end AlgebraicGeometry

end
