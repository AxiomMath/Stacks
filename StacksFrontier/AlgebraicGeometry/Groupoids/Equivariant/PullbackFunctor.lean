module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PullbackDescent

/-!
# Pullback of quasi-coherent modules along a morphism of groupoid schemes

A morphism `f` of groupoid schemes over `S` carries a quasi-coherent module with descent data on
the target groupoid to one on the source groupoid: the underlying module is pulled back along the
map on objects, and its descent morphism is
`Stacks.Groupoids.GroupoidScheme.pullbackDescent`.  This file proves the cocycle law for that
descent morphism and assembles the resulting functor.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.pullbackFunctor` is pullback along a morphism of groupoid
  schemes, as a functor on quasi-coherent modules with descent data.

## Main results

* `Stacks.Groupoids.GroupoidScheme.pullbackDescent_cocycle` is the cocycle law for the
  pulled-back descent morphism.
* `Stacks.Groupoids.GroupoidScheme.pullbackFunctor_obj_module`,
  `Stacks.Groupoids.GroupoidScheme.pullbackFunctor_obj_alpha` and
  `Stacks.Groupoids.GroupoidScheme.pullbackFunctor_map_hom` specify the functor on underlying
  modules, on descent morphisms and on morphisms.

## Implementation notes

The cocycle law is the cocycle law of the module on the target groupoid, reindexed along the
morphism of schemes of composable arrows induced by `f`.  That reindexing is isolated in the
private lemma below, which states it in substituted form: for morphisms `a`, `b` and `c` into the
scheme of arrows that the two projections and the composition morphism become, and with the
comparisons of pullbacks forced on the statement by the pseudofunctoriality of pullback as
hypotheses, so that any proof of them may be supplied.  Factoring the cocycle law this way is
what makes its proof term small enough for the kernel to recheck.

For the same reason the pullbacks along a composite are moved through the comparisons for equal
morphisms by the rewriting rules `Stacks.Groupoids.pullbackCongr_pullbackComp` and
`pullbackComp_inv_pullbackCongr`, rather than by cancelling an isomorphism on each side of the
goal: the two produce the same normal form, but the rewriting rules do it in a quarter of the
elaboration and well inside the kernel's budget.

## References

* [Stacks Project, Tag 03LJ](https://stacks.math.columbia.edu/tag/03LJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Groupoids

/-- The comparison of pullbacks along equal morphisms commutes past the inverse of the comparison
for a composite. -/
@[reassoc]
private theorem pullbackComp_inv_pullbackCongr {X Y Z : Scheme.{u}}
    {g h : X ⟶ Y} (p : g = h) (m : Y ⟶ Z) (F : Z.Modules) :
    (Scheme.Modules.pullbackComp g m).inv.app F ≫
      (Scheme.Modules.pullbackCongr p).hom.app ((Scheme.Modules.pullback m).obj F) =
    (Scheme.Modules.pullbackCongr (congrArg (fun k => k ≫ m) p)).hom.app F ≫
      (Scheme.Modules.pullbackComp h m).inv.app F := by
  cases p
  simp [Scheme.Modules.pullbackCongr]

namespace GroupoidScheme

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- The cocycle law of a quasi-coherent module on a groupoid scheme, reindexed along a morphism
into the scheme of composable arrows and rewritten in terms of the morphisms `a`, `b` and `c`
that the two projections and the composition morphism become, and conjugated by the comparisons of
pullback along two further morphisms `dt` and `ds` equal to the target and source composites.
The equalities are the comparisons of pullbacks that the pseudofunctoriality of pullback forces
into the statement; they are hypotheses so that any proof of them may be supplied.  This is the
shape in which the cocycle law for the pulled-back descent morphism consumes it. -/
@[reassoc]
private theorem reindexed_cocycle_conj (M : QuasicoherentModule H) {X : Scheme.{u}}
    (u : X ⟶ (Limits.pullback H.source H.target).left)
    {a b c : X ⟶ H.arrows.left}
    (ha : u ≫ (Limits.pullback.fst H.source H.target).left = a)
    (hb : u ≫ (Limits.pullback.snd H.source H.target).left = b)
    (hu : u ≫ H.comp.left = c)
    {dt ds : X ⟶ H.objects.left}
    (k₁ : dt = a ≫ H.target.left)
    (k₂ : a ≫ H.source.left = b ≫ H.target.left)
    (k₃ : b ≫ H.source.left = ds)
    (k₄ : dt = c ≫ H.target.left)
    (k₅ : c ≫ H.source.left = ds) :
    (Scheme.Modules.pullbackCongr k₁).hom.app M.module ≫ reindexHom a M.alpha ≫
        (Scheme.Modules.pullbackCongr k₂).hom.app M.module ≫ reindexHom b M.alpha ≫
        (Scheme.Modules.pullbackCongr k₃).hom.app M.module =
      (Scheme.Modules.pullbackCongr k₄).hom.app M.module ≫ reindexHom c M.alpha ≫
        (Scheme.Modules.pullbackCongr k₅).hom.app M.module := by
  have f₁ : u ≫ H.comp.left ≫ H.target.left =
      (u ≫ (Limits.pullback.fst H.source H.target).left) ≫ H.target.left := by
    rwa [ha, ← Category.assoc, hu, ← k₄]
  have f₂ : (u ≫ (Limits.pullback.fst H.source H.target).left) ≫ H.source.left =
      (u ≫ (Limits.pullback.snd H.source H.target).left) ≫ H.target.left := by
    rwa [ha, hb]
  have f₃ : (u ≫ (Limits.pullback.snd H.source H.target).left) ≫ H.source.left =
      u ≫ H.comp.left ≫ H.source.left := by
    rwa [hb, ← Category.assoc, hu, k₅]
  have hc := congrArg (reindexHom u) M.cocycle
  rw [reindexHom_successiveDescent H u M.alpha f₁ f₂ f₃, reindexHom_assoc_rev,
    reindexHom_congr_source ha M.alpha, reindexHom_congr_source hb M.alpha,
    reindexHom_congr_source hu M.alpha] at hc
  have g₁ : dt = u ≫ H.comp.left ≫ H.target.left := by
    rw [← hu, Category.assoc] at k₄
    exact k₄
  have g₃ : u ≫ H.comp.left ≫ H.source.left = ds := by
    rw [← hu, Category.assoc] at k₅
    exact k₅
  have hh := congrArg (fun z => (Scheme.Modules.pullbackCongr g₁).hom.app M.module ≫ z ≫
    (Scheme.Modules.pullbackCongr g₃).hom.app M.module) hc
  simpa only [Category.assoc, pullbackCongr_hom_app_comp,
    pullbackCongr_hom_app_comp_assoc, pullbackCongr_hom_app_self,
    Category.id_comp, Category.comp_id] using hh

/-- The pulled-back descent morphism satisfies the cocycle condition on the scheme of composable
arrows. -/
theorem pullbackDescent_cocycle (f : Hom G H) (M : QuasicoherentModule H) :
    successiveDescent G (pullbackDescent f M) =
      reindexHom G.comp.left (pullbackDescent f M) := by
  have w : ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows) ≫ H.source =
      ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) ≫ H.target := by
    rw [Category.assoc, f.map_source, Category.assoc, f.map_target,
      ← Category.assoc (Limits.pullback.fst G.source G.target),
      ← Category.assoc (Limits.pullback.snd G.source G.target),
      show Limits.pullback.fst G.source G.target ≫ G.source =
        Limits.pullback.snd G.source G.target ≫ G.target from Limits.pullback.condition]
  have hq₁ : (Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
        ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w).left ≫
        (Limits.pullback.fst H.source H.target).left =
      (Limits.pullback.fst G.source G.target).left ≫ f.mapArrows.left :=
    congrArg Over.Hom.left (Limits.pullback.lift_fst _ _ w)
  have hq₂ : (Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
        ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w).left ≫
        (Limits.pullback.snd H.source H.target).left =
      (Limits.pullback.snd G.source G.target).left ≫ f.mapArrows.left :=
    congrArg Over.Hom.left (Limits.pullback.lift_snd _ _ w)
  have hqc : (Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
        ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w).left ≫ H.comp.left =
      G.comp.left ≫ f.mapArrows.left := by
    have hcq : Limits.pullback.lift ((Limits.pullback.fst G.source G.target) ≫ f.mapArrows)
        ((Limits.pullback.snd G.source G.target) ≫ f.mapArrows) w ≫ H.comp =
        G.comp ≫ f.mapArrows := by
      rw [f.comp_mapArrows]
      congr 1
    exact congrArg Over.Hom.left hcq
  have ht : G.comp.left ≫ G.target.left =
      (Limits.pullback.fst G.source G.target).left ≫ G.target.left :=
    congrArg Over.Hom.left G.target_comp
  have hm : (Limits.pullback.fst G.source G.target).left ≫ G.source.left =
      (Limits.pullback.snd G.source G.target).left ≫ G.target.left :=
    congrArg Over.Hom.left (Limits.pullback.condition :
      Limits.pullback.fst G.source G.target ≫ G.source =
        Limits.pullback.snd G.source G.target ≫ G.target)
  have hs : (Limits.pullback.snd G.source G.target).left ≫ G.source.left =
      G.comp.left ≫ G.source.left :=
    (congrArg Over.Hom.left G.source_comp).symm
  have k₁ : (G.comp.left ≫ G.target.left) ≫ f.mapObjects.left =
      ((Limits.pullback.fst G.source G.target).left ≫ f.mapArrows.left) ≫ H.target.left :=
    (congrArg (fun z => z ≫ f.mapObjects.left) ht).trans
      (map_target_left_assoc f (Limits.pullback.fst G.source G.target).left)
  have k₂ : ((Limits.pullback.fst G.source G.target).left ≫ f.mapArrows.left) ≫
      H.source.left =
      ((Limits.pullback.snd G.source G.target).left ≫ f.mapArrows.left) ≫ H.target.left := by
    rw [map_source_left_assoc f (Limits.pullback.fst G.source G.target).left,
      ← map_target_left_assoc f (Limits.pullback.snd G.source G.target).left, hm]
  have k₃ : ((Limits.pullback.snd G.source G.target).left ≫ f.mapArrows.left) ≫
      H.source.left = (G.comp.left ≫ G.source.left) ≫ f.mapObjects.left :=
    (map_source_left_assoc f (Limits.pullback.snd G.source G.target).left).trans
      (congrArg (fun z => z ≫ f.mapObjects.left) hs)
  unfold successiveDescent
  rw [reindexHom_pullbackDescent f M _ (map_target_left_assoc f _)
      (map_source_left_assoc f _),
    reindexHom_pullbackDescent f M _ (map_target_left_assoc f _)
      (map_source_left_assoc f _),
    reindexHom_pullbackDescent f M _ (map_target_left_assoc f _)
      (map_source_left_assoc f _)]
  simp only [Over.comp_left, Category.assoc, pullbackCongr_pullbackComp_assoc,
    pullbackComp_inv_pullbackCongr, Iso.inv_hom_id_app_assoc,
    pullbackCongr_hom_app_comp_assoc]
  rw [reindexed_cocycle_conj_assoc M _ hq₁ hq₂ hqc k₁ k₂ k₃
    (map_target_left_assoc f G.comp.left) (map_source_left_assoc f G.comp.left)]

/-- **Stacks Project, Tag 03LJ.** Pullback along a morphism of groupoid schemes, as a functor on
quasi-coherent modules equipped with groupoid descent data.  On objects it sends `(F, α)` to
`(f⁺F, f⁺α)`, using the canonical comparison isomorphisms for pullback along composites; on
morphisms it is the usual pullback of morphisms of modules. -/
@[stacks 03LJ "the functor"]
noncomputable def pullbackFunctor (f : Hom G H) :
    QuasicoherentModule H ⥤ QuasicoherentModule G where
  obj M :=
    { module := (Scheme.Modules.pullback f.mapObjects.left).obj M.module
      isQuasicoherent :=
        Stacks.Modules.isQuasicoherent_pullback f.mapObjects.left M.module M.isQuasicoherent
      alpha := pullbackDescent f M
      cocycle := pullbackDescent_cocycle f M
      identity := pullbackDescent_identity f M }
  map {M N} g :=
    { hom := (Scheme.Modules.pullback f.mapObjects.left).map g.hom
      comm := pullbackDescent_naturality f g }
  map_id M := by
    apply QuasicoherentModule.Hom.ext
    change (Scheme.Modules.pullback f.mapObjects.left).map (𝟙 M.module) = 𝟙 _
    simp
  map_comp {M N K} g h := by
    apply QuasicoherentModule.Hom.ext
    exact (Scheme.Modules.pullback f.mapObjects.left).map_comp _ _

/-- **Stacks Project, Tag 03LJ.** Pullback along a morphism of groupoid schemes pulls back the
underlying module along the map on objects. -/
@[stacks 03LJ "underlying modules"]
theorem pullbackFunctor_obj_module (f : Hom G H) (M : QuasicoherentModule H) :
    ((pullbackFunctor f).obj M).module =
      (Scheme.Modules.pullback f.mapObjects.left).obj M.module := by
  simp [pullbackFunctor]

/-- **Stacks Project, Tag 03LJ.** The descent morphism of a pulled-back module is the canonical
pullback of the original descent morphism. -/
@[stacks 03LJ "descent morphisms"]
theorem pullbackFunctor_obj_alpha (f : Hom G H) (M : QuasicoherentModule H) :
    Eq.ndrec (motive := fun X =>
      (Scheme.Modules.pullback G.target.left).obj X ⟶
        (Scheme.Modules.pullback G.source.left).obj X)
      ((pullbackFunctor f).obj M).alpha (pullbackFunctor_obj_module f M) =
      pullbackDescent f M := by
  simp [pullbackFunctor]

/-- **Stacks Project, Tag 03LJ.** Pullback of a morphism of quasi-coherent modules on a groupoid
scheme is the usual pullback of morphisms of modules. -/
@[stacks 03LJ "morphisms"]
theorem pullbackFunctor_map_hom (f : Hom G H) {M N : QuasicoherentModule H} (g : M ⟶ N) :
    (pullbackFunctor_obj_module f M) ▸
      (pullbackFunctor_obj_module f N) ▸
        (QuasicoherentModule.Hom.hom ((pullbackFunctor f).map g)) =
      (Scheme.Modules.pullback f.mapObjects.left).map g.hom := by
  simp [pullbackFunctor]

end GroupoidScheme

end Stacks.Groupoids

end
