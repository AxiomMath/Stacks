module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# Colimits of quasi-coherent modules on a groupoid scheme

The category of quasi-coherent modules equipped with descent data for a groupoid scheme admits
all colimits.  A colimit is computed on the underlying modules on the scheme of objects, and the
descent morphism of the colimit is the one induced by the descent morphisms of the diagram.

## Main results

* `AlgebraicGeometry.GroupoidScheme.identityDescent_naturality` and
  `AlgebraicGeometry.GroupoidScheme.successiveDescent_naturality`: pulling a descent morphism
  back along the identity section, and applying it to two composable arrows in succession, are
  both natural in the module.
* `AlgebraicGeometry.instHasColimits`: quasi-coherent modules on a groupoid scheme have all
  colimits.

## Implementation notes

The existence of colimits is stated as a `HasColimits` instance, making the result directly
available to the category-theoretic colimit API.  Quasi-coherence of the colimit of the
underlying modules is
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`, and the cocycle
and identity conditions for the induced descent morphism follow from the naturality of
`Stacks.Groupoids.reindexHom` in the module.

## References

* [Stacks Project, Tag 077R](https://stacks.math.columbia.edu/tag/077R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidScheme

universe u

/-- Two commuting squares side by side give a commuting square for the composites. -/
lemma comp_naturality {C : Type*} [Category C]
    {A B D A' B' D' : C} {f : A ⟶ B} {g : B ⟶ D}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : D ⟶ D'}
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') :
    (f ≫ g) ≫ c = a ≫ (f' ≫ g') := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

/-- `Stacks.Groupoids.GroupoidScheme.identityDescent` is natural in the module. -/
theorem identityDescent_naturality {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {M N : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj M ⟶
      (Scheme.Modules.pullback G.source.left).obj M)
    (β : (Scheme.Modules.pullback G.target.left).obj N ⟶
      (Scheme.Modules.pullback G.source.left).obj N) (k : M ⟶ N)
    (w : α ≫ (Scheme.Modules.pullback G.source.left).map k =
      (Scheme.Modules.pullback G.target.left).map k ≫ β) :
    identityDescent G α ≫ k = k ≫ identityDescent G β := by
  have hα := reindexHom_naturality G.identity.left α β k w
  have hId := (Scheme.Modules.pullbackId G.objects.left).hom.naturality k
  have hS := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left G.source_identity)).hom.naturality k
  have hT := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left G.target_identity).symm).hom.naturality k
  have hInv := (Scheme.Modules.pullbackId G.objects.left).inv.naturality k
  simp only [Functor.id_map] at hId hInv
  simp only [Over.id_left, Over.comp_left] at hS hT
  simpa only [identityDescent, Category.assoc] using
    comp_naturality hInv.symm
      (comp_naturality hT.symm
        (comp_naturality hα
          (comp_naturality hS.symm hId.symm)))

/-- `Stacks.Groupoids.GroupoidScheme.successiveDescent` is natural in the module. -/
theorem successiveDescent_naturality {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {M N : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj M ⟶
      (Scheme.Modules.pullback G.source.left).obj M)
    (β : (Scheme.Modules.pullback G.target.left).obj N ⟶
      (Scheme.Modules.pullback G.source.left).obj N) (k : M ⟶ N)
    (w : α ≫ (Scheme.Modules.pullback G.source.left).map k =
      (Scheme.Modules.pullback G.target.left).map k ≫ β) :
    successiveDescent G α ≫
        (Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map k =
      (Scheme.Modules.pullback (G.comp.left ≫ G.target.left)).map k ≫
        successiveDescent G β := by
  have hfst := reindexHom_naturality
    (pullback.fst G.source G.target).left α β k w
  have hsnd := reindexHom_naturality
    (pullback.snd G.source G.target).left α β k w
  have hT := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left G.target_comp)).hom.naturality k
  have hM := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left
      (pullback.condition : pullback.fst G.source G.target ≫ G.source =
        pullback.snd G.source G.target ≫ G.target))).hom.naturality k
  have hS := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left G.source_comp).symm).hom.naturality k
  simp only [Over.comp_left] at hT hM hS
  simpa only [successiveDescent, Category.assoc] using
    comp_naturality hT.symm
      (comp_naturality hfst
        (comp_naturality hM.symm
          (comp_naturality hsnd hS.symm)))

/-- A diagram of quasi-coherent modules on a groupoid scheme, read as a diagram of modules on
its scheme of objects. -/
private abbrev underlying {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {J : Type u} [Category.{u} J]
    (D : Functor J (QuasicoherentModule G)) : Functor J G.objects.left.Modules :=
  D ⋙ QuasicoherentModule.forget G

/-- The descent morphism induced on the colimit of the underlying modules of a diagram of
quasi-coherent modules on a groupoid scheme. -/
private noncomputable def colimitAlpha {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {J : Type u} [Category.{u} J]
    (D : Functor J (QuasicoherentModule G)) :
    (Scheme.Modules.pullback G.target.left).obj (colimit (underlying G D)) ⟶
      (Scheme.Modules.pullback G.source.left).obj (colimit (underlying G D)) :=
  (preservesColimitIso (Scheme.Modules.pullback G.target.left) (underlying G D)).hom ≫
    colimit.desc ((underlying G D) ⋙ Scheme.Modules.pullback G.target.left)
      (Cocone.mk _ {
        app := fun j ↦ (D.obj j).alpha ≫
          (Scheme.Modules.pullback G.source.left).map (colimit.ι (underlying G D) j)
        naturality := by
          intro i j f
          simp only [Functor.comp_map, QuasicoherentModule.forget, Functor.const_obj_map,
            ]
          rw [← Category.assoc, ← (D.map f).comm, Category.assoc, ← Functor.map_comp]
          exact congrArg ((D.obj i).alpha ≫ ·)
            (congrArg ((Scheme.Modules.pullback G.source.left).map ·)
              (colimit.w (underlying G D) f)) })

/-- The induced descent morphism on a colimit restricts to the descent morphism of each term of
the diagram. -/
private lemma colimitAlpha_fac {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {J : Type u} [Category.{u} J] (D : Functor J (QuasicoherentModule G)) (j : J) :
    (Scheme.Modules.pullback G.target.left).map (colimit.ι (underlying G D) j) ≫
        colimitAlpha G D =
      (D.obj j).alpha ≫
        (Scheme.Modules.pullback G.source.left).map (colimit.ι (underlying G D) j) := by
  simp [colimitAlpha]

/-- The colimit of a diagram of quasi-coherent modules on a groupoid scheme, as a
quasi-coherent module with descent data. -/
private noncomputable def colimitObj {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {J : Type u} [SmallCategory J]
    (D : J ⥤ QuasicoherentModule G) : QuasicoherentModule G where
  module := colimit (underlying G D)
  isQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
      (fun j ↦ (D.obj j).isQuasicoherent) (colimit.isColimit (underlying G D))
  alpha := colimitAlpha G D
  cocycle := by
    apply (isColimitOfPreserves
      (Scheme.Modules.pullback (G.comp.left ≫ G.target.left))
      (colimit.isColimit (underlying G D))).hom_ext
    intro j
    have w := (colimitAlpha_fac G D j).symm
    have hs := successiveDescent_naturality G (D.obj j).alpha
      (colimitAlpha G D) (colimit.ι (underlying G D) j) w
    have hr := reindexHom_naturality G.comp.left (D.obj j).alpha
      (colimitAlpha G D) (colimit.ι (underlying G D) j) w
    change (Scheme.Modules.pullback (G.comp.left ≫ G.target.left)).map
        (colimit.ι (underlying G D) j) ≫ successiveDescent G (colimitAlpha G D) =
      (Scheme.Modules.pullback (G.comp.left ≫ G.target.left)).map
        (colimit.ι (underlying G D) j) ≫ reindexHom G.comp.left (colimitAlpha G D)
    rw [← hs, ← hr, (D.obj j).cocycle]
  identity := by
    apply colimit.hom_ext
    intro j
    have h := identityDescent_naturality G (D.obj j).alpha
      (colimitAlpha G D) (colimit.ι (underlying G D) j)
      (colimitAlpha_fac G D j).symm
    rw [← h, (D.obj j).identity]
    simp

/-- The colimit cocone of a diagram of quasi-coherent modules on a groupoid scheme. -/
private noncomputable def colimitCocone {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {J : Type u} [SmallCategory J]
    (D : J ⥤ QuasicoherentModule G) : Cocone D where
  pt := colimitObj G D
  ι := {
    app := fun j ↦ {
      hom := colimit.ι (underlying G D) j
      comm := (colimitAlpha_fac G D j).symm }
    naturality _ _ f := QuasicoherentModule.Hom.ext (colimit.w (underlying G D) f) }

/-- The canonical map out of the underlying colimit restricts to the component of the cocone. -/
private lemma colimit_ι_desc_forget {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {J : Type u} [SmallCategory J] (D : J ⥤ QuasicoherentModule G)
    (c : Cocone D) (j : J) :
    colimit.ι (underlying G D) j ≫
      colimit.desc (underlying G D) ((QuasicoherentModule.forget G).mapCocone c) =
      (c.ι.app j).hom := by
  simp [QuasicoherentModule.forget]

/-- The cocone on the underlying colimit is a colimit cocone of quasi-coherent modules with
descent data. -/
private noncomputable def colimitIsColimit {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {J : Type u} [SmallCategory J]
    (D : J ⥤ QuasicoherentModule G) : IsColimit (colimitCocone G D) where
  desc c := {
    hom := colimit.desc (underlying G D) ((QuasicoherentModule.forget G).mapCocone c)
    comm := by
      apply (isColimitOfPreserves (Scheme.Modules.pullback G.target.left)
        (colimit.isColimit (underlying G D))).hom_ext
      intro j
      change (Scheme.Modules.pullback G.target.left).map
          (colimit.ι (underlying G D) j) ≫ colimitAlpha G D ≫
          (Scheme.Modules.pullback G.source.left).map
            (colimit.desc (underlying G D) ((QuasicoherentModule.forget G).mapCocone c)) =
        (Scheme.Modules.pullback G.target.left).map
          (colimit.ι (underlying G D) j) ≫
          (Scheme.Modules.pullback G.target.left).map
            (colimit.desc (underlying G D) ((QuasicoherentModule.forget G).mapCocone c)) ≫
          c.pt.alpha
      rw [← Category.assoc, colimitAlpha_fac]
      simp only [Category.assoc, ← Functor.map_comp, colimit.ι_desc,
        Functor.mapCocone_ι_app, QuasicoherentModule.forget]
      have hd := colimit_ι_desc_forget G D c j
      calc
        _ = (Scheme.Modules.pullback G.target.left).map (c.ι.app j).hom ≫
            c.pt.alpha := (c.ι.app j).comm
        _ = _ := by
          rw [← hd, Functor.map_comp]
          simp only [QuasicoherentModule.forget, Category.assoc] }
  fac c j := by
    apply QuasicoherentModule.Hom.ext
    exact colimit_ι_desc_forget G D c j
  uniq c m hm := by
    apply QuasicoherentModule.Hom.ext
    apply colimit.hom_ext
    intro j
    exact (congrArg QuasicoherentModule.Hom.hom (hm j)).trans
      (colimit_ι_desc_forget G D c j).symm

end AlgebraicGeometry.GroupoidScheme

namespace AlgebraicGeometry

universe u

/-- The category of quasi-coherent modules on a groupoid scheme admits all colimits. -/
@[stacks 077R]
instance instHasColimits {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    HasColimits (Stacks.Groupoids.GroupoidScheme.QuasicoherentModule G) := by
  refine ⟨fun J _ ↦ ⟨fun D ↦ ⟨_root_.AlgebraicGeometry.GroupoidScheme.colimitCocone G D,
    _root_.AlgebraicGeometry.GroupoidScheme.colimitIsColimit G D⟩⟩⟩

end AlgebraicGeometry

end
