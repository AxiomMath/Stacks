module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# Quasi-coherent modules on a groupoid scheme, and pullback along a morphism

For a groupoid scheme with object scheme `U` and arrow scheme `R`, a quasi-coherent module is
a quasi-coherent module `F` on `U` together with a morphism `α : t^* F ⟶ s^* F` subject to a
cocycle condition on the scheme of composable arrows and a normalization along the identity
section. A morphism of groupoid schemes induces a pullback operation on such data.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Hom` is a morphism of groupoid schemes.
* `Stacks.Groupoids.reindexHom` pulls a morphism between two pullbacks of a module back once
  more, inserting the canonical comparisons between iterated pullbacks and pullback along a
  composite.
* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule` is a quasi-coherent module equipped
  with a groupoid descent morphism satisfying the cocycle and identity conditions, and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.Hom` is a morphism of such.
* `Stacks.Groupoids.GroupoidScheme.pullbackDescent` is the canonical pullback of a descent
  morphism along a morphism of groupoid schemes.

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.comp_mapArrows` is the compatibility of a morphism of
  groupoid schemes with composition of arrows, in the form of a commuting square of the
  composition morphisms rather than a condition on generalized points.
* `Stacks.Groupoids.reindexHom_id`, `Stacks.Groupoids.reindexHom_comp` and
  `Stacks.Groupoids.reindexHom_naturality` are the calculus of `reindexHom`.
* `Stacks.Groupoids.GroupoidScheme.pullbackDescent_naturality` says that a morphism of
  quasi-coherent modules on `H` pulls back to a morphism intertwining the pulled-back descent
  morphisms.

## Implementation notes

Pullbacks of modules form a pseudofunctor rather than a strictly functorial operation.
Consequently `reindexHom` inserts the canonical comparison isomorphisms between iterated
pullback and pullback along a composite, and the cocycle and identity laws use these
comparisons together with transport along the defining equations of a groupoid scheme. Thus they
state the displayed diagrams of the source without treating canonically isomorphic pullbacks as
definitionally equal.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 03LI](https://stacks.math.columbia.edu/tag/03LI)
* [Stacks Project, Tag 03LJ](https://stacks.math.columbia.edu/tag/03LJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

namespace GroupoidScheme

/-- Composition of two composable generalized arrows of a groupoid scheme. -/
@[implicit_reducible]
noncomputable def compose {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target) : T ⟶ G.arrows :=
  pullback.lift f g w ≫ G.comp

/-- A morphism of groupoid schemes. -/
@[stacks 0231 "part (2): morphisms of groupoid schemes"]
structure Hom {S : Scheme.{u}} (G H : GroupoidScheme S) where
  /-- The map on objects. -/
  mapObjects : G.objects ⟶ H.objects
  /-- The map on arrows. -/
  mapArrows : G.arrows ⟶ H.arrows
  map_source : mapArrows ≫ H.source = G.source ≫ mapObjects
  map_target : mapArrows ≫ H.target = G.target ≫ mapObjects
  map_identity : mapObjects ≫ H.identity = G.identity ≫ mapArrows
  map_comp : ∀ (T : Over S) (f g : T ⟶ G.arrows)
      (w : f ≫ G.source = g ≫ G.target)
      (w' : (f ≫ mapArrows) ≫ H.source = (g ≫ mapArrows) ≫ H.target),
    G.compose f g w ≫ mapArrows = H.compose (f ≫ mapArrows) (g ≫ mapArrows) w'

namespace Hom

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- Compatibility with the source maps, on underlying schemes. -/
theorem map_source_left (f : Hom G H) :
    f.mapArrows.left ≫ H.source.left = G.source.left ≫ f.mapObjects.left := by
  rw [← Over.comp_left, ← Over.comp_left, f.map_source]

/-- Compatibility with the target maps, on underlying schemes. -/
theorem map_target_left (f : Hom G H) :
    f.mapArrows.left ≫ H.target.left = G.target.left ≫ f.mapObjects.left := by
  rw [← Over.comp_left, ← Over.comp_left, f.map_target]

/-- The morphism on schemes of composable arrows induced by a morphism of groupoid schemes. -/
noncomputable def mapComposable (f : Hom G H) :
    pullback G.source G.target ⟶ pullback H.source H.target :=
  pullback.map _ _ _ _ f.mapArrows f.mapArrows f.mapObjects
    (by rw [f.map_source]) (by rw [f.map_target])

/-- Compatibility of a morphism of groupoid schemes with composition, as a commuting square
of the composition morphisms. -/
theorem comp_mapArrows (f : Hom G H) :
    G.comp ≫ f.mapArrows = f.mapComposable ≫ H.comp := by
  have w : pullback.fst G.source G.target ≫ G.source =
      pullback.snd G.source G.target ≫ G.target := pullback.condition
  have w' : (pullback.fst G.source G.target ≫ f.mapArrows) ≫ H.source =
      (pullback.snd G.source G.target ≫ f.mapArrows) ≫ H.target := by
    rw [Category.assoc, Category.assoc, f.map_source, f.map_target, ← Category.assoc,
      ← Category.assoc, w]
  have h := f.map_comp (pullback G.source G.target) (pullback.fst G.source G.target)
    (pullback.snd G.source G.target) w w'
  rw [GroupoidScheme.compose, GroupoidScheme.compose, pullback.lift_fst_snd,
    Category.id_comp] at h
  rw [h]
  congr 1

end Hom

end GroupoidScheme

/-- Pull a morphism between two pullbacks of a module back once more, with the canonical
identifications of the iterated pullbacks with pullback along the corresponding composites. -/
@[implicit_reducible]
noncomputable def reindexHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules} (α : (Scheme.Modules.pullback g).obj F ⟶
      (Scheme.Modules.pullback h).obj F) :
    (Scheme.Modules.pullback (f ≫ g)).obj F ⟶ (Scheme.Modules.pullback (f ≫ h)).obj F :=
  (Scheme.Modules.pullbackComp f g).inv.app F ≫ (Scheme.Modules.pullback f).map α ≫
    (Scheme.Modules.pullbackComp f h).hom.app F

/-- Reindexing the identity of a pullback gives the identity. -/
@[simp]
theorem reindexHom_id {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    reindexHom f (𝟙 ((Scheme.Modules.pullback g).obj F)) =
      𝟙 ((Scheme.Modules.pullback (f ≫ g)).obj F) := by
  simp [reindexHom]

/-- Reindexing commutes with composition. -/
@[simp, reassoc]
theorem reindexHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h i : Y ⟶ Z} {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F)
    (β : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback i).obj F) :
    reindexHom f (α ≫ β) = reindexHom f α ≫ reindexHom f β := by
  simp [reindexHom]

/-- `reindexHom` is natural in the module: a morphism intertwining two descent morphisms
intertwines their reindexings. -/
@[reassoc]
theorem reindexHom_naturality {X Y Z : Scheme.{u}} (u : X ⟶ Y) {g h : Y ⟶ Z}
    {F F' : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F)
    (α' : (Scheme.Modules.pullback g).obj F' ⟶ (Scheme.Modules.pullback h).obj F')
    (φ : F ⟶ F')
    (hφ : α ≫ (Scheme.Modules.pullback h).map φ = (Scheme.Modules.pullback g).map φ ≫ α') :
    reindexHom u α ≫ (Scheme.Modules.pullback (u ≫ h)).map φ =
      (Scheme.Modules.pullback (u ≫ g)).map φ ≫ reindexHom u α' := by
  simp only [reindexHom, Category.assoc]
  rw [← (Scheme.Modules.pullbackComp u h).hom.naturality φ,
    (Scheme.Modules.pullbackComp u g).inv.naturality_assoc φ]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, hφ]

namespace GroupoidScheme

/-- The morphism on the scheme of composable arrows obtained by applying a descent morphism
first to the first arrow and then to the second arrow. -/
noncomputable def successiveDescent {S : Scheme.{u}} (G : GroupoidScheme S)
    {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) :
    (Scheme.Modules.pullback (G.comp.left ≫ G.target.left)).obj F ⟶
      (Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).obj F :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.target_comp)).hom.app F ≫
    reindexHom (pullback.fst G.source G.target).left α ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (pullback.condition : pullback.fst G.source G.target ≫ G.source =
        pullback.snd G.source G.target ≫ G.target))).hom.app F ≫
    reindexHom (pullback.snd G.source G.target).left α ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.source_comp).symm).hom.app F

/-- The endomorphism of a module obtained by pulling a descent morphism back along the identity
section and making the canonical identifications with pullback along the identity. -/
noncomputable def identityDescent {S : Scheme.{u}} (G : GroupoidScheme S)
    {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) : F ⟶ F :=
  (Scheme.Modules.pullbackId G.objects.left).inv.app F ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.target_identity).symm).hom.app F ≫
    reindexHom G.identity.left α ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.source_identity)).hom.app F ≫
    (Scheme.Modules.pullbackId G.objects.left).hom.app F

/-- A quasi-coherent module on a groupoid scheme, with its descent morphism, cocycle law, and
normalization along the identity section. -/
@[stacks 03LI]
structure QuasicoherentModule {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The module on the object scheme. -/
  module : G.objects.left.Modules
  /-- The underlying module is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The descent morphism from pullback along the target to pullback along the source. -/
  alpha : (Scheme.Modules.pullback G.target.left).obj module ⟶
    (Scheme.Modules.pullback G.source.left).obj module
  /-- On the scheme of composable arrows, applying `alpha` to the two arrows in succession is
  the same as applying it to their composite. -/
  cocycle : successiveDescent G alpha = reindexHom G.comp.left alpha
  /-- Pullback of `alpha` along the identity section is the identity of the module. -/
  identity : identityDescent G alpha = 𝟙 module

namespace QuasicoherentModule

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- The quasicoherence witness carried by a module on a groupoid is available to typeclass
inference. -/
instance (M : QuasicoherentModule G) : M.module.IsQuasicoherent :=
  M.isQuasicoherent

/-- A morphism of quasi-coherent modules on a groupoid scheme is a morphism of the underlying
modules which intertwines their descent morphisms. -/
@[ext]
structure Hom (M N : QuasicoherentModule G) where
  /-- The morphism of underlying modules on the object scheme. -/
  hom : M.module ⟶ N.module
  /-- Compatibility with the descent morphisms. -/
  comm : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map hom =
    (Scheme.Modules.pullback G.target.left).map hom ≫ N.alpha

/-- Quasi-coherent modules on a groupoid scheme and their compatible module morphisms form a
category. -/
instance : Category (QuasicoherentModule G) where
  Hom := Hom
  id M := { hom := 𝟙 M.module, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm,
        Category.assoc, g.comm, ← Category.assoc] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The forgetful functor from quasi-coherent modules on a groupoid scheme to modules on its
object scheme. -/
@[implicit_reducible]
def forget (G : GroupoidScheme S) :
    QuasicoherentModule G ⥤ G.objects.left.Modules where
  obj M := M.module
  map f := f.hom

end QuasicoherentModule

/-- The descent morphism obtained by pulling back along the arrow map of a morphism of
groupoid schemes and using the canonical comparisons between composite pullbacks. -/
noncomputable def pullbackDescent {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    (M : QuasicoherentModule H) :
    (Scheme.Modules.pullback G.target.left).obj
        ((Scheme.Modules.pullback f.mapObjects.left).obj M.module) ⟶
      (Scheme.Modules.pullback G.source.left).obj
        ((Scheme.Modules.pullback f.mapObjects.left).obj M.module) :=
  (Scheme.Modules.pullbackComp G.target.left f.mapObjects.left).hom.app M.module ≫
    (Scheme.Modules.pullbackCongr f.map_target_left.symm).hom.app M.module ≫
    reindexHom f.mapArrows.left M.alpha ≫
    (Scheme.Modules.pullbackCongr f.map_source_left).hom.app M.module ≫
    (Scheme.Modules.pullbackComp G.source.left f.mapObjects.left).inv.app M.module

/-- The pulled-back descent morphism is natural: a morphism of quasi-coherent modules on `H`
pulls back to a morphism intertwining the pulled-back descent morphisms. -/
theorem pullbackDescent_naturality {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    {M N : QuasicoherentModule H} (g : M ⟶ N) :
    pullbackDescent f M ≫ (Scheme.Modules.pullback G.source.left).map
        ((Scheme.Modules.pullback f.mapObjects.left).map
          (QuasicoherentModule.Hom.hom g)) =
      (Scheme.Modules.pullback G.target.left).map
          ((Scheme.Modules.pullback f.mapObjects.left).map
            (QuasicoherentModule.Hom.hom g)) ≫ pullbackDescent f N := by
  simp only [pullbackDescent, Category.assoc, ← Functor.comp_map]
  rw [← (Scheme.Modules.pullbackComp G.source.left f.mapObjects.left).inv.naturality,
    ← (Scheme.Modules.pullbackCongr f.map_source_left).hom.naturality_assoc,
    reindexHom_naturality_assoc f.mapArrows.left M.alpha N.alpha _ g.comm,
    ← (Scheme.Modules.pullbackCongr f.map_target_left.symm).hom.naturality_assoc,
    ← (Scheme.Modules.pullbackComp G.target.left f.mapObjects.left).hom.naturality_assoc]

end GroupoidScheme

end Stacks.Groupoids

end
