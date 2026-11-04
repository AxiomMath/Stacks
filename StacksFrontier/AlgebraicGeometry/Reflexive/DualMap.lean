module

public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance

/-!
# The dual of a morphism, and the reflexive hull as a functor

Let `X` be a scheme.  The dual `F^∨ = SheafHom(F, 𝒪_X)` of an `𝒪_X`-module is contravariantly
functorial: a morphism `f : F ⟶ G` precomposes a local functional on `G` with `f`, giving
`dualMap f : G^∨ ⟶ F^∨`.  Iterating, the reflexive hull `F^∨∨` is a covariant endofunctor and
the canonical map `j_F : F ⟶ F^∨∨` of `toDoubleDual` is a natural transformation from the
identity functor to it.

The hull satisfies the triangle identity `j_{F^∨} ≫ (j_F)^∨ = 𝟙` of a unit, so the canonical
map of a dual module is always a split monomorphism, and if `F^∨∨` is itself reflexive then
`(j_F)^∨∨ = j_{F^∨∨}`.

## Main definitions

* `dualMap f`: the dual `G^∨ ⟶ F^∨` of a morphism `f : F ⟶ G`, and `dualFunctor X` the
  resulting contravariant functor.
* `doubleDualMap f`: the hull `F^∨∨ ⟶ G^∨∨` of a morphism, `reflexiveHullFunctor X` the
  resulting endofunctor, and `toDoubleDualNatTrans X` the canonical map as a natural
  transformation `𝟭 ⟶ reflexiveHullFunctor X`.

## Main results

* `dualPairing_dualMap`: the defining formula for the dual of a morphism.
* `hom_ext_dualSheaf`: extensionality for morphisms into a dual module.
* `toDoubleDual_naturality`: the canonical map to the double dual is natural.
* `toDoubleDual_dualMap_comp`: the triangle identity, and
  `isSplitMono_toDoubleDual_dualSheaf`: the canonical map of a dual module is a split
  monomorphism.
* `doubleDualMap_toDoubleDual`: if the hull of `F` is reflexive, the hull of `j_F` is
  `j_{F^∨∨}`.
* `dualPairing_terminal`: a section of the dual paired at an object `W` of the slice site is
  the restricted section paired at the terminal object of the slice site over `W.left`.

## Implementation notes

The dual of a morphism is Tag 03EN's `internalHomMapLeft`, which is precomposition on the
slice site, so `dualPairing_dualMap` holds by definitional unfolding and functoriality of the
dual is definitional once `hom_ext_dualSheaf` has reduced morphism equality to equality of
values.

The hull is spelled out as `dualSheaf (dualSheaf F)` rather than abbreviated; see
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/Hull.lean` for the named `reflexiveHull`.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-! ### The dual as a contravariant functor -/

/-- The dual of a morphism `f : F ⟶ G`, the morphism `G^∨ ⟶ F^∨` given by precomposition
with `f`. -/
public noncomputable def dualMap {F G : X.Modules} (f : F ⟶ G) : dualSheaf G ⟶ dualSheaf F :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft X.sheaf.obj f.val⟩

/-- The defining formula for the dual of a morphism: it precomposes a local functional
with `f`. -/
public theorem dualPairing_dualMap {F G : X.Modules} (f : F ⟶ G) {U : X.Opens}
    (t : Γ(dualSheaf G, U)) (W : Over U) (x : Γ(F, W.left)) :
    dualPairing F (Scheme.Modules.Hom.app (dualMap f) U t) W x =
      dualPairing G t W (Scheme.Modules.Hom.app f W.left x) :=
  rfl

/-- Extensionality for morphisms into a dual module: two such agree as soon as all the values
of their sections agree. -/
public theorem hom_ext_dualSheaf {F G : X.Modules} {f g : F ⟶ dualSheaf G}
    (h : ∀ (U : X.Opens) (x : Γ(F, U)) (W : Over U) (y : Γ(G, W.left)),
      dualPairing G (Scheme.Modules.Hom.app f U x) W y =
        dualPairing G (Scheme.Modules.Hom.app g U x) W y) :
    f = g := by
  refine Scheme.Modules.hom_ext f g fun U => ?_
  ext x
  exact dualPairing_ext (fun W y => h U x W y)

@[simp] public theorem dualMap_id (F : X.Modules) : dualMap (𝟙 F) = 𝟙 (dualSheaf F) :=
  hom_ext_dualSheaf (fun _ _ _ _ => rfl)

public theorem dualMap_comp {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  hom_ext_dualSheaf (fun _ _ _ _ => rfl)

/-- The dual, as a contravariant functor on the modules of a scheme. -/
public noncomputable def dualFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.Modules where
  obj F := dualSheaf F.unop
  map f := dualMap f.unop
  map_id _ := dualMap_id _
  map_comp f g := dualMap_comp g.unop f.unop

/-- **The dual of an isomorphism of modules, as an isomorphism of their duals.**

This is `Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor` evaluated at `Iso.op`, written
out directly. The difference is not cosmetic: in `(dualFunctor X).mapIso e.op` the two objects
are the *values of the functor*, `(dualFunctor X).obj (op M)` rather than `dualSheaf M`, and the
two are identified only up to unfolding, which leaves the `Quiver.Hom` instance of a composite
built from such a morphism on a different path from the one `simp` reassociates along. Here both
objects are duals on the nose. -/
public noncomputable def dualSheafIsoOfIso {M N : X.Modules} (e : M ≅ N) :
    dualSheaf N ≅ dualSheaf M where
  hom := dualMap e.hom
  inv := dualMap e.inv
  hom_inv_id := by rw [← dualMap_comp, e.inv_hom_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, e.hom_inv_id, dualMap_id]

/-! ### The reflexive hull as a covariant functor -/

/-- The reflexive hull `F^∨∨` of a morphism, covariantly. -/
public noncomputable def doubleDualMap {F G : X.Modules} (f : F ⟶ G) :
    dualSheaf (dualSheaf F) ⟶ dualSheaf (dualSheaf G) :=
  dualMap (dualMap f)

@[simp] public theorem doubleDualMap_id (F : X.Modules) :
    doubleDualMap (𝟙 F) = 𝟙 (dualSheaf (dualSheaf F)) :=
  hom_ext_dualSheaf (fun _ _ _ _ => rfl)

public theorem doubleDualMap_comp {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) :
    doubleDualMap (f ≫ g) = doubleDualMap f ≫ doubleDualMap g := by
  rw [doubleDualMap, dualMap_comp, dualMap_comp, doubleDualMap, doubleDualMap]

/-- The reflexive hull as an endofunctor of the modules of a scheme. -/
public noncomputable def reflexiveHullFunctor (X : Scheme.{u}) : X.Modules ⥤ X.Modules where
  obj F := dualSheaf (dualSheaf F)
  map f := doubleDualMap f
  map_id _ := doubleDualMap_id _
  map_comp f g := doubleDualMap_comp f g

/-! ### Naturality and the triangle identity -/

/-- Restricting a section of `F^∨` along an arbitrary inclusion of opens restricts the
corresponding morphism.  This is `dualPairing_map` with the inclusion given as a morphism of
`X.Opens` rather than as an inequality. -/
public theorem dualPairing_map' (F : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (t : Γ(dualSheaf F, U)) (W : Over V) (x : Γ(F, W.left)) :
    dualPairing F ((dualSheaf F).presheaf.map i.op t) W x =
      dualPairing F t (Over.mk (W.hom ≫ i)) x :=
  rfl

/-- Evaluation of a local functional is its value at the terminal object of the slice site. -/
public theorem evalAt_eq_dualPairing (F : X.Modules) {V : X.Opens} (lam : Γ(dualSheaf F, V))
    (x : Γ(F, V)) : evalAt F lam x = dualPairing F lam (Over.mk (𝟙 V)) x :=
  rfl

/-- The canonical map to the double dual is natural. -/
public theorem toDoubleDual_naturality {F G : X.Modules} (f : F ⟶ G) :
    f ≫ toDoubleDual G = toDoubleDual F ≫ doubleDualMap f := by
  refine hom_ext_dualSheaf (fun U x W lam => ?_)
  have hL : dualPairing (dualSheaf G)
      (Scheme.Modules.Hom.app (f ≫ toDoubleDual G) U x) W lam =
      evalAt G lam (G.presheaf.map W.hom.op (Scheme.Modules.Hom.app f U x)) :=
    toDoubleDual_dualPairing G (Scheme.Modules.Hom.app f U x) W lam
  have hR : dualPairing (dualSheaf G)
      (Scheme.Modules.Hom.app (toDoubleDual F ≫ doubleDualMap f) U x) W lam =
      evalAt G lam (Scheme.Modules.Hom.app f W.left (F.presheaf.map W.hom.op x)) :=
    (dualPairing_dualMap (dualMap f) (Scheme.Modules.Hom.app (toDoubleDual F) U x) W lam).trans
      ((toDoubleDual_dualPairing F x W
          (Scheme.Modules.Hom.app (dualMap f) W.left lam)).trans
        (dualPairing_dualMap f lam (Over.mk (𝟙 W.left)) (F.presheaf.map W.hom.op x)))
  rw [hL, hR]
  exact congrArg (evalAt G (V := W.left) lam)
    (PresheafOfModules.naturality_apply f.val W.hom.op x).symm

/-- The canonical map to the double dual, as a natural transformation from the identity to the
reflexive hull. -/
@[simps]
public noncomputable def toDoubleDualNatTrans (X : Scheme.{u}) :
    𝟭 X.Modules ⟶ reflexiveHullFunctor X where
  app F := toDoubleDual F
  naturality _ _ f := toDoubleDual_naturality f

/-- **The triangle identity.**  The canonical map of a dual module is split by the dual of the
canonical map.  In particular the canonical map of a dual module is a split monomorphism. -/
public theorem toDoubleDual_dualMap_comp (F : X.Modules) :
    toDoubleDual (dualSheaf F) ≫ dualMap (toDoubleDual F) = 𝟙 (dualSheaf F) := by
  refine hom_ext_dualSheaf (fun U t W x => ?_)
  calc dualPairing F
        (Scheme.Modules.Hom.app (toDoubleDual (dualSheaf F) ≫ dualMap (toDoubleDual F)) U t) W x
      = dualPairing (dualSheaf (dualSheaf F))
          (Scheme.Modules.Hom.app (toDoubleDual (dualSheaf F)) U t) W
          (Scheme.Modules.Hom.app (toDoubleDual F) W.left x) :=
        dualPairing_dualMap (toDoubleDual F)
          (Scheme.Modules.Hom.app (toDoubleDual (dualSheaf F)) U t) W x
    _ = evalAt (dualSheaf F) (Scheme.Modules.Hom.app (toDoubleDual F) W.left x)
          ((dualSheaf F).presheaf.map W.hom.op t) :=
        toDoubleDual_dualPairing (dualSheaf F) t W _
    _ = evalAt F ((dualSheaf F).presheaf.map W.hom.op t) x :=
        toDoubleDual_val_app_apply F W.left x ((dualSheaf F).presheaf.map W.hom.op t)
    _ = dualPairing F t (Over.mk ((Over.mk (𝟙 W.left)).hom ≫ W.hom)) x :=
        dualPairing_map' F W.hom t (Over.mk (𝟙 W.left)) x
    _ = dualPairing F t W x := rfl

/-- The canonical map of a dual module is a split monomorphism. -/
public theorem isSplitMono_toDoubleDual_dualSheaf (F : X.Modules) :
    IsSplitMono (toDoubleDual (dualSheaf F)) :=
  IsSplitMono.mk' ⟨dualMap (toDoubleDual F), toDoubleDual_dualMap_comp F⟩

/-- **The hull is idempotent on units.**  If the reflexive hull of `F` is reflexive, then the
hull of the canonical map of `F` is the canonical map of the hull.

Both morphisms are split by the dual of the canonical map of `F^∨`, which is therefore an
isomorphism, and a monomorphism can be cancelled. -/
public theorem doubleDualMap_toDoubleDual (F : X.Modules)
    [IsIso (toDoubleDual (dualSheaf (dualSheaf F)))] :
    doubleDualMap (toDoubleDual F) = toDoubleDual (dualSheaf (dualSheaf F)) := by
  have ha : toDoubleDual (dualSheaf (dualSheaf F)) ≫ dualMap (toDoubleDual (dualSheaf F)) =
      𝟙 (dualSheaf (dualSheaf F)) := toDoubleDual_dualMap_comp (dualSheaf F)
  have hf : doubleDualMap (toDoubleDual F) ≫ dualMap (toDoubleDual (dualSheaf F)) =
      𝟙 (dualSheaf (dualSheaf F)) := by
    rw [doubleDualMap, ← dualMap_comp, toDoubleDual_dualMap_comp]
    exact hom_ext_dualSheaf (fun _ _ _ _ => rfl)
  have : IsIso (dualMap (toDoubleDual (dualSheaf F))) := by
    rw [IsIso.eq_inv_of_hom_inv_id ha]; infer_instance
  exact (cancel_mono _).mp (hf.trans ha.symm)

/-! ### Restriction of sections along the slice site -/

/-- Restriction along the identity acts trivially on sections of a module. -/
private theorem map_id_apply (F : X.Modules) (U : X.Opens) (x : Γ(F, U)) :
    F.presheaf.map (𝟙 (op U)) x = x := by
  rw [F.presheaf.map_id]; rfl

/-- Restriction along the identity acts trivially on functions. -/
private theorem structure_map_id_apply (U : X.Opens) (y : Γ(X, U)) :
    X.presheaf.map (𝟙 (op U)) y = y := by
  rw [X.presheaf.map_id]; rfl

/-- A section of the dual, paired at an object `W` of the slice site, is the
restricted section paired at the terminal object of the slice site over `W.left`. -/
public theorem dualPairing_terminal (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) (x : Γ(F, W.left)) :
    dualPairing F ((dualSheaf F).presheaf.map (homOfLE (leOfHom W.hom)).op t)
        (Over.mk (𝟙 W.left)) x = dualPairing F t W x := by
  refine (dualPairing_map F (leOfHom W.hom) t (Over.mk (𝟙 W.left)) x).trans ?_
  refine Eq.trans (congrArg (fun y => dualPairing F t
    (Over.mk ((Over.mk (𝟙 W.left)).hom ≫ homOfLE (leOfHom W.hom))) y)
      (map_id_apply F W.left x).symm) ?_
  refine (dualPairing_naturality F t
    (Over.homMk (𝟙 W.left) (Subsingleton.elim _ _) :
      (Over.mk ((Over.mk (𝟙 W.left)).hom ≫ homOfLE (leOfHom W.hom)) : Over U) ⟶ W) x).trans ?_
  exact structure_map_id_apply W.left _

/-- Restriction of a section does not depend on the chosen inclusion. -/
public theorem presheaf_map_hom_eq (F : X.Modules) {U : X.Opens} (t : Γ(F, U)) (W : Over U) :
    F.presheaf.map W.hom.op t = F.presheaf.map (homOfLE (leOfHom W.hom)).op t :=
  congrArg (fun h : W.left ⟶ U => F.presheaf.map h.op t) (Subsingleton.elim _ _)

/-- Restriction of a section of the dual does not depend on the chosen inclusion. -/
public theorem dualSheaf_map_eq (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) :
    (dualSheaf F).presheaf.map W.hom.op t =
      (dualSheaf F).presheaf.map (homOfLE (leOfHom W.hom)).op t :=
  presheaf_map_hom_eq (dualSheaf F) t W

end Stacks.AlgebraicGeometry.ReflexiveModules
