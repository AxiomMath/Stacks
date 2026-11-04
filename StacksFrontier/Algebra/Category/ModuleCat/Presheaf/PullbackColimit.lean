module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# A concrete model for the pullback of presheaves of modules: the colimit factor

Mathlib defines `PresheafOfModules.pullback φ`, for `φ : S ⟶ F.op ⋙ R` a morphism of presheaves
of rings, as `(PresheafOfModules.pushforward φ).leftAdjoint`: an abstract left adjoint, with no
description of its sections.  Since `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`, and
left adjoints of a composite compose in the other order, that left adjoint factors as

`pullback φ ≅ extendScalars φ ⋙ L₀`,

where `extendScalars φ` is objectwise extension of scalars — built, with its adjunction, in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel` — and `L₀` is the left adjoint
of `PresheafOfModules.pushforward₀ F R`.  This file builds `L₀` as the objectwise colimit

`(L₀ A)(U) = colim_{(V, U ⟶ F V)} R(U) ⊗_{R(F V)} A(V)`

over the comma category `CostructuredArrow F.op U`, together with its adjunction, and so
completes the concrete model: `pullbackIso` identifies Mathlib's abstract `pullback` with the
composite, and `pullbackObjIso` reads off its sections.

For `F = Opens.map f` the index category is filtered
(`Stacks.PullbackModel.isFiltered_costructuredArrow_opensMap`, restated as the instance
`isFiltered_index`), so the colimit is a filtered colimit, which is the form Stacks 01CD needs.

## Main definitions

* `Stacks.PullbackColimit.baseChangeHom`: the base change of a semilinear map along a
  *triangle* of ring homomorphisms (the case `σ = id` of
  `Stacks.PullbackModel.baseChangeMap`), read as a morphism between the two base changes
  rather than into a restriction of scalars.
* `Stacks.PullbackColimit.diagram`: the diagram
  `(V, U ⟶ F V) ↦ R(U) ⊗_{R(F V)} A(V)` over `CostructuredArrow F.op U` whose colimit is
  `(L₀ A)(U)`, with `diagramObj` and `diagramMap` its values on objects and morphisms.
* `Stacks.PullbackColimit.germ`: the image in the colimit of a pure tensor `r ⊗ a`, and
  `Stacks.PullbackColimit.unit` the germ `1 ⊗ a` at the terminal index `(V, 𝟙)`, which is the
  unit of the adjunction on sections.
* `Stacks.PullbackColimit.obj`: the value of `L₀` on an object, as a presheaf of modules, with
  restriction maps `restrictionMap` built from `restrictionCocone`.
* `Stacks.PullbackColimit.toPushforward`, `fromPushforward` and
  `Stacks.PullbackColimit.homEquiv`: the two adjoint transposes and the bijection they form.
* `Stacks.PullbackColimit.colimitPullback`: **`L₀` itself**, and
  `Stacks.PullbackColimit.colimitPullbackAdjunction` its adjunction.
* `Stacks.PullbackColimit.modelAdjunction`: the composite adjunction
  `extendScalars α ⋙ L₀ ⊣ pushforward α`.

## Main results

* `Stacks.PullbackColimit.hom_ext`: a morphism out of the colimit is determined by its values
  on the germs `1 ⊗ a`.
* `Stacks.PullbackColimit.colimitPullbackAdjunction`: **the objectwise colimit is left adjoint
  to `PresheafOfModules.pushforward₀ F R`**, hence the instance
  `isRightAdjoint_pushforward₀` (which Mathlib has for `pushforward φ` but not for
  `pushforward₀`) and `colimitPullbackIsoLeftAdjoint`, identifying the construction with the
  abstract left adjoint.
* `Stacks.PullbackColimit.pullbackIso`: **Mathlib's `PresheafOfModules.pullback` is objectwise
  extension of scalars followed by the objectwise colimit**, canonically.  No smallness
  hypothesis beyond the one Mathlib itself uses for `pullback` is needed, and the isomorphism
  is produced by the construction rather than by the adjoint functor theorem.
* `Stacks.PullbackColimit.pullbackObjIso`: consequently the sections of the pullback over `U`
  are `colim_{(V, U ⟶ F V)} R(U) ⊗_{R(F V)} (R(F V) ⊗_{S(V)} N(V))`, and
  `modelAdjunction_unit_app_apply` computes the unit of the adjunction on sections as the germ
  of `1 ⊗ n`.  This is exactly what the abstract left adjoint does not provide.
* `Stacks.PullbackColimit.obj_map_germ`, `restrictionMap_germ`, `descMap_germ`,
  `toPushforward_app_apply`, `unit_restrict`: the restriction maps, the functoriality and both
  directions of the adjunction isomorphism, computed on germs of pure tensors.

## Implementation notes

The functoriality of `L₀` in the module argument is *not* constructed by hand: only the value
on objects and the hom bijection, natural in the target, are given, and
`CategoryTheory.Adjunction.leftAdjointOfEquiv` produces the functor and
`Adjunction.adjunctionOfEquivLeft` the adjunction from that datum.  This is why `colimitPullback`
has no `map_id`/`map_comp` obligations here.

Two instance-hygiene difficulties recur, and both are handled structurally rather than by
transparency options.

The first is the one `PullbackModel` describes: `(ModuleCat.extendScalars f).obj M` has
underlying type `B ⊗[A] M` only for the `Module A B` structure that `ModuleCat.restrictScalars f`
installs, which is definitionally but not syntactically `Module.compHom B f`, and a `rw` or
`simp` lemma whose left-hand side mentions a bare `⊗ₜ` silently fails to fire.  Every statement
here is therefore phrased through `Stacks.PullbackModel.tmul`, and the computation rules
`tmul_add`, `tmul_one_add`, `tmul_one_smul`, `tmul_smul_right` are derived from the fact that
the unit of `ModuleCat.extendRestrictScalarsAdj` *is* `m ↦ tmul f 1 m` (`adj_unit_apply`), so
that additivity and semilinearity come from its being a morphism of `ModuleCat` rather than from
`TensorProduct` lemmas that would need the instance spelled a particular way.

The second is that a ring of sections carries two definitionally equal `Ring` structures, one
through `R.obj U` as a `CommRingCat` and one through `(R ⋙ forget₂ CommRingCat RingCat).obj U`
as a `RingCat`, and that the sections of `pushforward₀ F R M` over `V` are `M(F V)` in the first
spelling and `((pushforward₀ F R).obj M).obj V` in the second.  Mixing them makes a term
type-incorrect at `implicit` transparency, which is what `rw` reports.  `pushforwardApp` fixes
one spelling for the components of a morphism into a pushforward, and `unit` is typed through
`colimit (diagram ...)` rather than through `obj`, for the same reason.

**Universes.**  The two sites are `C D : Type u` with `[SmallCategory C] [SmallCategory D]`, and
the rings and the module sections are at a free universe `w` subject to `[UnivLE.{u, w}]`: the
sections may live in any universe at least as large as the sites'.  Three constraints produce
that shape and nothing else does.

* The module universe must be at least the site universe, which is what `UnivLE.{u, w}` says.
  `SmallCategory` makes the index category `CostructuredArrow F.op U` a `u`-small category, and
  `ModuleCat.{w}` has colimits of that shape exactly then; this is the only use of smallness.
  The hypothesis is stated as `UnivLE` rather than by spelling the sections'
  universe `max u w`, because a `max` in that position makes every call site solve
  `max ?w u =?= u` for a metavariable, which is not uniquely solvable and costs enough
  elaboration time that `PullbackMonoidalSite.presheafPullbackMonoidal` runs out of heartbeats.
* The ring universe must equal the module universe, because `ModuleCat.extendScalars` for
  `f : A →+* B` with `A B : Type t` lands in `ModuleCat.{max t v}`, so `diagramObj` stays in
  one universe only when the ring universe is at most the module universe, and
  `ModuleCat.extendScalars` is stated with its two rings in one universe.  `CommRingCat` rather
  than `RingCat` is forced by `ModuleCat.extendScalars` too, which exists only for commutative
  rings.
* The two sites must share a universe.  This one is a limitation of instance resolution, not of
  the mathematics: with `C : Type u` and `D : Type u'` the colimit `colimit (diagram F R A U)`
  is rejected, because the index category's smallness decomposes into `Small.{_, u} C` and
  `Small.{_, u'} D` and `UnivLE.self` solves the second by assigning the module universe
  metavariable to `u'`, after which `max u u' w =?= u'` fails.  The failure survives spelling
  the codomain of `colimit` out and supplying `HasColimit` as a local instance.

`(PresheafOfModules.pushforward φ).IsRightAdjoint` is *not* taken from Mathlib, whose instance
is restricted to module sections in the sites' own universe; `isRightAdjoint_pushforward` below
derives it from `modelAdjunction` instead, which is what makes `pullbackIso` available at the
larger module universe.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 008T](https://stacks.math.columbia.edu/tag/008T)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe w u

namespace Stacks.PullbackColimit

open PresheafOfModules Stacks.PullbackModel

/-! ### Base change along a commuting triangle -/

section BaseChange

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]

/-- The base change of a semilinear map along a *triangle* of ring homomorphisms: the case
`σ = id` of `Stacks.PullbackModel.baseChangeMap`, read as a morphism between the base changes
themselves rather than into a restriction of scalars. -/
noncomputable def baseChangeHom (αV : A →+* B) (αW : A' →+* B) {ρ : A →+* A'}
    (hα : ∀ r, αV r = αW (ρ r)) {M : ModuleCat.{u} A} {M' : ModuleCat.{u} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') :
    (ModuleCat.extendScalars αV).obj M ⟶ (ModuleCat.extendScalars αW).obj M' :=
  baseChangeMap αV αW (σ := RingHom.id B) hα φ ≫
    (ModuleCat.restrictScalarsId'App (RingHom.id B) rfl _).hom

/-- `baseChangeHom` sends the pure tensor `b ⊗ m` to `b ⊗ φ m`. -/
lemma baseChangeHom_tmul (αV : A →+* B) (αW : A' →+* B) {ρ : A →+* A'}
    (hα : ∀ r, αV r = αW (ρ r)) {M : ModuleCat.{u} A} {M' : ModuleCat.{u} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') (b : B) (m : M) :
    baseChangeHom αV αW hα φ (tmul αV b m) = tmul αW b (φ m) := rfl

/-- A pure tensor is a scalar multiple of one with first factor `1`. -/
lemma tmul_eq_smul (f : A →+* B) {M : ModuleCat.{u} A} (b : B) (m : M) :
    tmul f b m = b • tmul f 1 m := by
  rw [smul_tmul, mul_one]

/-- The unit of `ModuleCat.extendRestrictScalarsAdj` sends `m` to `1 ⊗ m`. -/
lemma adj_unit_apply (f : A →+* B) {M : ModuleCat.{u} A} (m : M) :
    (ModuleCat.extendRestrictScalarsAdj f).unit.app M m = tmul f 1 m := rfl

/-- The pure tensor `1 ⊗ m` is additive in `m`. -/
lemma tmul_one_add (f : A →+* B) {M : ModuleCat.{u} A} (m m' : M) :
    tmul f 1 (m + m') = tmul f 1 m + tmul f 1 m' :=
  map_add (ModuleCat.Hom.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)) m m'

/-- A scalar `s` in the second factor of `1 ⊗ (s • m)` moves to the first as `f s`. -/
lemma tmul_one_smul (f : A →+* B) {M : ModuleCat.{u} A} (s : A) (m : M) :
    tmul f 1 (s • m) = tmul f (f s) m := by
  have h : tmul f 1 (s • m) = f s • tmul f 1 m :=
    map_smul (ModuleCat.Hom.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)) s m
  rw [h, smul_tmul, mul_one]

/-- A pure tensor `b ⊗ m` is additive in `m`. -/
lemma tmul_add (f : A →+* B) {M : ModuleCat.{u} A} (b : B) (m m' : M) :
    tmul f b (m + m') = tmul f b m + tmul f b m' := by
  rw [tmul_eq_smul f b (m + m'), tmul_eq_smul f b m, tmul_eq_smul f b m', tmul_one_add,
    smul_add]

/-- `b ⊗ (s • m) = (b * f s) ⊗ m`. -/
lemma tmul_smul_right (f : A →+* B) {M : ModuleCat.{u} A} (b : B) (s : A) (m : M) :
    tmul f b (s • m) = tmul f (b * f s) m := by
  rw [tmul_eq_smul f b (s • m), tmul_one_smul, smul_tmul]

end BaseChange

/-! ### The diagram -/

section Diagram

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{w})
  (A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
  [hUL : UnivLE.{u, w}]

include hUL

omit hUL in
/-- The restriction map of `R` along an identity is the identity, on elements. -/
lemma map_id_hom_apply (U : Dᵒᵖ) (s : ↑(R.obj U)) : (R.map (𝟙 U)).hom s = s := by
  rw [R.map_id]
  rfl

omit hUL in
/-- The scalars of two terms of the diagram are compatible: a morphism `ψ : T ⟶ T'` of the
index category factors `R(U)` through `R(F T')`. -/
lemma scalars_comm {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj (F.op.obj T.left))) :
    (R.map T.hom).hom r = (R.map T'.hom).hom ((R.map (F.op.map ψ.left)).hom r) := by
  conv_lhs => rw [← CostructuredArrow.w ψ, R.map_comp]
  rfl

omit hUL in
/-- The scalars of the terms of the diagram are compatible with a restriction in `U`. -/
lemma scalars_comm_restrict {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U)
    (r : ↑(R.obj (F.op.obj T.left))) :
    (R.map g).hom ((R.map T.hom).hom r) = (R.map (T.hom ≫ g)).hom r := by
  rw [R.map_comp]
  rfl

/-- The term `R(U) ⊗_{R(F V)} A(V)` of the colimit, at the object `T = (V, U ⟶ F V)` of the
index category. -/
noncomputable abbrev diagramObj {U : Dᵒᵖ} (T : CostructuredArrow F.op U) :
    ModuleCat.{w} ↑(R.obj U) :=
  (ModuleCat.extendScalars (R.map T.hom).hom).obj (A.obj T.left)

/-- The transition map of the colimit along a morphism of the index category: the base change
of a restriction map of `A`. -/
noncomputable def diagramMap {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T') :
    diagramObj F R A T ⟶ diagramObj F R A T' :=
  baseChangeHom (R.map T.hom).hom (R.map T'.hom).hom (scalars_comm F R ψ)
    (A.restrictₛₗ ψ.left)

omit hUL in
/-- `diagramMap ψ` sends `r ⊗ m` to `r ⊗ m|_ψ`, the restriction of `m` along `ψ.left`. -/
lemma diagramMap_tmul {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj U)) (m : A.obj T.left) :
    diagramMap F R A ψ (tmul (R.map T.hom).hom r m)
      = tmul (R.map T'.hom).hom r (A.restrictₛₗ ψ.left m) := rfl

/-- The diagram `(V, U ⟶ F V) ↦ R(U) ⊗_{R(F V)} A(V)` over the index category
`CostructuredArrow F.op U`, whose colimit is the value at `U` of the left adjoint of
`PresheafOfModules.pushforward₀ F R`. -/
noncomputable def diagram (U : Dᵒᵖ) :
    CostructuredArrow F.op U ⥤ ModuleCat.{w} ↑(R.obj U) where
  obj T := diagramObj F R A T
  map ψ := diagramMap F R A ψ
  map_id T := by
    refine extendScalars_hom_ext _ fun m => ?_
    change tmul (R.map T.hom).hom 1 (A.restrictₛₗ (𝟙 T.left) m)
        = tmul (R.map T.hom).hom 1 m
    rw [restrictₛₗ_id_apply]
  map_comp {T T' T''} ψ χ := by
    refine extendScalars_hom_ext _ fun m => ?_
    change tmul (R.map T''.hom).hom 1 (A.restrictₛₗ (ψ.left ≫ χ.left) m)
        = diagramMap F R A χ (diagramMap F R A ψ (tmul (R.map T.hom).hom 1 m))
    rw [diagramMap_tmul, diagramMap_tmul, restrictₛₗ_comp_apply]

omit hUL in
/-- The transition map of `diagram` along `ψ` sends `r ⊗ m` to `r ⊗ m|_ψ`. -/
lemma diagram_map_tmul {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj U)) (m : A.obj T.left) :
    (diagram F R A U).map ψ (tmul (R.map T.hom).hom r m)
      = tmul (R.map T'.hom).hom r (A.restrictₛₗ ψ.left m) := rfl

/-! ### Germs -/

/-- The image in the colimit of the pure tensor `r ⊗ a`.  Every section of the colimit is a
sum of such germs, and `hom_ext` says that a morphism out of the colimit is determined by its
values on the germs `1 ⊗ a`. -/
noncomputable def germ {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) : ↑(colimit (diagram F R A U)) :=
  colimit.ι (diagram F R A U) T (tmul (R.map T.hom).hom r a)

/-- Scalar multiplication of a germ multiplies its first factor:
`r • germ r' a = germ (r * r') a`. -/
lemma germ_smul {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r r' : ↑(R.obj U))
    (a : A.obj T.left) : r • germ F R A T r' a = germ F R A T (r * r') a :=
  (map_smul (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T)) r
    (tmul (R.map T.hom).hom r' a)).symm

/-- A germ is additive in its second factor. -/
lemma germ_add_right {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a a' : A.obj T.left) :
    germ F R A T r (a + a') = germ F R A T r a + germ F R A T r a' :=
  (congrArg (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T))
      (tmul_add (R.map T.hom).hom r a a')).trans
    (map_add (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T)) _ _)

/-- A scalar `s` of `R(F V)` in the second factor of a germ moves to the first factor as its
image in `R(U)`. -/
lemma germ_smul_right {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (s : ↑(R.obj (F.op.obj T.left))) (a : A.obj T.left) :
    germ F R A T r (s • a) = germ F R A T (r * (R.map T.hom).hom s) a :=
  congrArg (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T))
    (tmul_smul_right (R.map T.hom).hom r s a)

/-- A germ may be re-indexed along any morphism of the index category. -/
lemma germ_map {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T') (r : ↑(R.obj U))
    (a : A.obj T.left) : germ F R A T r a = germ F R A T' r (A.restrictₛₗ ψ.left a) :=
  (ConcreteCategory.congr_hom (colimit.w (diagram F R A U) ψ)
    (tmul (R.map T.hom).hom r a)).symm

/-- Germs indexed by equal arrows agree. -/
lemma germ_congr {U : Dᵒᵖ} {V : Cᵒᵖ} {h h' : F.op.obj V ⟶ U} (e : h = h') (r : ↑(R.obj U))
    (a : A.obj V) :
    germ F R A (CostructuredArrow.mk h) r a = germ F R A (CostructuredArrow.mk h') r a := by
  subst e
  rfl

/-- A morphism out of the colimit is determined by its values on the germs `1 ⊗ a`. -/
lemma hom_ext {U : Dᵒᵖ} {N : ModuleCat.{w} ↑(R.obj U)}
    {x y : colimit (diagram F R A U) ⟶ N}
    (h : ∀ (T : CostructuredArrow F.op U) (a : A.obj T.left),
      x (germ F R A T 1 a) = y (germ F R A T 1 a)) : x = y := by
  refine colimit.hom_ext fun T => extendScalars_hom_ext _ fun a => ?_
  exact h T a

/-! ### The colimit as a presheaf of modules -/

/-- The cocone defining the restriction map of the colimit presheaf along `g : U ⟶ U'`. -/
noncomputable def restrictionCocone {U U' : Dᵒᵖ} (g : U ⟶ U') : Cocone (diagram F R A U) where
  pt := (ModuleCat.restrictScalars (R.map g).hom).obj (colimit (diagram F R A U'))
  ι :=
    { app T :=
        baseChangeMap (R.map T.hom).hom (R.map (T.hom ≫ g)).hom (σ := (R.map g).hom)
            (ρ := RingHom.id _) (scalars_comm_restrict F R g T) LinearMap.id ≫
          (ModuleCat.restrictScalars (R.map g).hom).map
            (colimit.ι (diagram F R A U') (CostructuredArrow.mk (T.hom ≫ g)))
      naturality {T T'} ψ := by
        refine extendScalars_hom_ext _ fun a => ?_
        change germ F R A (CostructuredArrow.mk (T'.hom ≫ g)) ((R.map g).hom 1)
              (A.restrictₛₗ ψ.left a)
            = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom 1) a
        exact (germ_map F R A
          (CostructuredArrow.homMk (f := CostructuredArrow.mk (T.hom ≫ g))
            (f' := CostructuredArrow.mk (T'.hom ≫ g)) ψ.left
            (by
              change F.op.map ψ.left ≫ T'.hom ≫ g = T.hom ≫ g
              rw [← Category.assoc, CostructuredArrow.w ψ])) _ a).symm }

/-- The restriction map of the colimit presheaf along `g : U ⟶ U'`. -/
noncomputable def restrictionMap {U U' : Dᵒᵖ} (g : U ⟶ U') :
    colimit (diagram F R A U) ⟶
      (ModuleCat.restrictScalars (R.map g).hom).obj (colimit (diagram F R A U')) :=
  colimit.desc _ (restrictionCocone F R A g)

/-- The restriction map along `g` sends the germ of `r ⊗ a` at `(V, h)` to the germ of
`g(r) ⊗ a` at `(V, h ≫ g)`. -/
lemma restrictionMap_germ {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U)
    (r : ↑(R.obj U)) (a : A.obj T.left) :
    restrictionMap F R A g (germ F R A T r a)
      = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a :=
  ConcreteCategory.congr_hom (colimit.ι_desc (restrictionCocone F R A g) T)
    (tmul (R.map T.hom).hom r a)

/-- **The value of `L₀` on an object**: the presheaf of `R`-modules whose sections over `U`
are the colimit `colim_{V, U ⟶ F V} R(U) ⊗_{R(F V)} A(V)`. -/
noncomputable def obj : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) where
  obj U := colimit (diagram F R A U)
  map g := restrictionMap F R A g
  map_id U := by
    refine hom_ext F R A fun T a => ?_
    rw [restrictionMap_germ, map_one]
    exact germ_congr F R A (Category.comp_id T.hom) 1 a
  map_comp {U U' U''} g h := by
    refine hom_ext F R A fun T a => ?_
    change restrictionMap F R A (g ≫ h) (germ F R A T 1 a)
        = restrictionMap F R A h (restrictionMap F R A g (germ F R A T 1 a))
    rw [restrictionMap_germ, restrictionMap_germ, restrictionMap_germ, map_one, map_one,
      map_one]
    exact germ_congr F R A (Category.assoc T.hom g h).symm 1 a

/-- The restriction maps of `obj` send the germ of `r ⊗ a` at `(V, h)` to the germ of
`g(r) ⊗ a` at `(V, h ≫ g)`. -/
lemma obj_map_germ {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) :
    (obj F R A).map g (germ F R A T r a)
      = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a :=
  restrictionMap_germ F R A g T r a

end Diagram

/-! ### The adjunction -/

section Adjunction

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{w})
  {A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
  {M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
  [hUL : UnivLE.{u, w}]

include hUL

/-- The unit of the adjunction on sections: a section of `A` over `V`, read as a section of
`L₀ A` over `F V`. -/
noncomputable def unit (A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (a : A.obj V) : ↑(colimit (diagram F R A (F.op.obj V))) :=
  germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a

/-- `unit` is additive. -/
lemma unit_add (V : Cᵒᵖ) (a a' : A.obj V) :
    unit F R A V (a + a') = unit F R A V a + unit F R A V a' :=
  germ_add_right F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a a'

/-- `unit` is `R(F V)`-linear. -/
lemma unit_smul (V : Cᵒᵖ) (s : ↑(R.obj (F.op.obj V))) (a : A.obj V) :
    unit F R A V (s • a) = s • unit F R A V a := by
  have h1 : unit F R A V (s • a)
      = germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V)))
        (1 * (R.map (𝟙 (F.op.obj V))).hom s) a :=
    germ_smul_right F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 s a
  have h2 : (1 * (R.map (𝟙 (F.op.obj V))).hom s : ↑(R.obj (F.op.obj V))) = s * 1 := by
    rw [map_id_hom_apply, one_mul, mul_one]
  rw [h1, h2]
  exact (germ_smul F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) s 1 a).symm

/-- `unit` commutes with restriction: restricting `unit a` along `F g` is `unit` of the
restriction of `a` along `g`. -/
lemma unit_restrict {V V' : Cᵒᵖ} (g : V ⟶ V') (a : A.obj V) :
    (obj F R A).map (F.op.map g) (unit F R A V a) = unit F R A V' (A.restrictₛₗ g a) := by
  rw [unit, obj_map_germ, map_one]
  exact germ_map F R A
    (CostructuredArrow.homMk (f := CostructuredArrow.mk (𝟙 (F.op.obj V) ≫ F.op.map g))
      (f' := CostructuredArrow.mk (𝟙 (F.op.obj V'))) g
      (by
        show F.op.map g ≫ 𝟙 (F.op.obj V') = 𝟙 (F.op.obj V) ≫ F.op.map g
        rw [Category.comp_id, Category.id_comp])) 1 a

/-- The adjoint transpose of a morphism `L₀ A ⟶ M`. -/
noncomputable def toPushforward (x : obj F R A ⟶ M) :
    A ⟶ (pushforward₀OfCommRingCat F R).obj M where
  app V := ModuleCat.ofHom
    { toFun a := Hom.app x (F.op.obj V) (unit F R A V a)
      map_add' a a' := by rw [unit_add]; exact map_add _ _ _
      map_smul' s a := by rw [unit_smul]; exact map_smul _ _ _ }
  naturality {V V'} g := by
    ext a
    change Hom.app x (F.op.obj V') (unit F R A V' (A.restrictₛₗ g a))
        = M.restrictₛₗ (F.op.map g) (Hom.app x (F.op.obj V) (unit F R A V a))
    rw [← unit_restrict]
    exact naturality_apply x (F.op.map g) (unit F R A V a)

/-- The component of `toPushforward x` at `V` sends `a` to `x (unit a)`. -/
lemma toPushforward_app_apply (x : obj F R A ⟶ M) (V : Cᵒᵖ) (a : A.obj V) :
    Hom.app (toPushforward F R x) V a = Hom.app x (F.op.obj V) (unit F R A V a) := rfl

/-- The component at `V` of a morphism `A ⟶ pushforward₀ F R M`, read as a map into
`M(F V)`.  The value of `Hom.app` carries the scalar ring in the `pushforward₀` spelling, and
rewriting through `M`'s own restriction maps needs it in `M`'s spelling. -/
noncomputable def pushforwardApp (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (V : Cᵒᵖ)
    (a : A.obj V) : M.obj (F.op.obj V) :=
  Hom.app u V a

omit hUL in
/-- `pushforwardApp u` commutes with restriction along `g` and `F g`. -/
lemma pushforwardApp_restrict (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {V V' : Cᵒᵖ}
    (g : V ⟶ V') (a : A.obj V) :
    pushforwardApp F R u V' (A.restrictₛₗ g a)
      = M.restrictₛₗ (F.op.map g) (pushforwardApp F R u V a) :=
  naturality_apply u g a

/-- The leg at `T` of the cocone defining the inverse adjoint transpose: the base change of
`u` over `V = T.left`, followed by restriction to `U`. -/
noncomputable def descLeg (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {U : Dᵒᵖ}
    (T : CostructuredArrow F.op U) : diagramObj F R A T ⟶ M.obj U :=
  ((ModuleCat.extendRestrictScalarsAdj (R.map T.hom).hom).homEquiv (A.obj T.left)
    (M.obj U)).symm (Hom.app u T.left ≫ M.map T.hom)

omit hUL in
/-- `descLeg u T` sends `1 ⊗ a` to the restriction of `u a` along `T.hom`. -/
lemma descLeg_tmul (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {U : Dᵒᵖ}
    (T : CostructuredArrow F.op U) (a : A.obj T.left) :
    descLeg F R u T (tmul (R.map T.hom).hom 1 a)
      = M.restrictₛₗ T.hom (pushforwardApp F R u T.left a) :=
  homEquiv_symm_apply_tmul _ _ _

/-- The cocone out of which the inverse adjoint transpose is built: on the term
`R(U) ⊗_{R(F V)} A(V)` it is `r ⊗ a ↦ r • (u a)|_U`. -/
noncomputable def descCocone (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ) :
    Cocone (diagram F R A U) where
  pt := M.obj U
  ι :=
    { app T := descLeg F R u T
      naturality {T T'} ψ := by
        refine extendScalars_hom_ext _ fun a => ?_
        change descLeg F R u T' (diagramMap F R A ψ (tmul (R.map T.hom).hom 1 a))
            = descLeg F R u T (tmul (R.map T.hom).hom 1 a)
        rw [diagramMap_tmul, descLeg_tmul, descLeg_tmul, pushforwardApp_restrict,
          ← restrictₛₗ_comp_apply, CostructuredArrow.w ψ] }

/-- The inverse adjoint transpose, objectwise. -/
noncomputable def descMap (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ) :
    colimit (diagram F R A U) ⟶ M.obj U :=
  colimit.desc _ (descCocone F R u U)

/-- `descMap u U` sends the germ of `1 ⊗ a` at `T` to the restriction of `u a` along `T.hom`. -/
lemma descMap_germ (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ)
    (T : CostructuredArrow F.op U) (a : A.obj T.left) :
    descMap F R u U (germ F R A T 1 a)
      = M.restrictₛₗ T.hom (pushforwardApp F R u T.left a) :=
  (ConcreteCategory.congr_hom (colimit.ι_desc (descCocone F R u U) T)
    (tmul (R.map T.hom).hom 1 a)).trans (descLeg_tmul F R u T a)

/-- The inverse adjoint transpose of a morphism `A ⟶ pushforward₀ F R M`. -/
noncomputable def fromPushforward (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) :
    obj F R A ⟶ M where
  app U := descMap F R u U
  naturality {U U'} g := by
    refine hom_ext F R A fun T a => ?_
    change descMap F R u U' ((obj F R A).map g (germ F R A T 1 a))
        = M.restrictₛₗ g (descMap F R u U (germ F R A T 1 a))
    rw [obj_map_germ, map_one, descMap_germ, descMap_germ]
    change M.restrictₛₗ (T.hom ≫ g) (pushforwardApp F R u T.left a)
        = M.restrictₛₗ g (M.restrictₛₗ T.hom (pushforwardApp F R u T.left a))
    rw [restrictₛₗ_comp_apply]

/-- **Extension of scalars and the filtered colimit are left adjoint to the pushforward of
presheaves of modules**, on hom sets: the bijection of the adjunction `L₀ ⊣ pushforward₀`. -/
noncomputable def homEquiv (A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ _ _))
    (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (obj F R A ⟶ M) ≃ (A ⟶ (pushforward₀OfCommRingCat F R).obj M) where
  toFun x := toPushforward F R x
  invFun u := fromPushforward F R u
  left_inv x := by
    refine PresheafOfModules.hom_ext fun U => hom_ext F R A fun T a => ?_
    change descMap F R (toPushforward F R x) U (germ F R A T 1 a) = Hom.app x U (germ F R A T 1 a)
    rw [descMap_germ]
    change M.restrictₛₗ T.hom (Hom.app x (F.op.obj T.left) (unit F R A T.left a))
        = Hom.app x U (germ F R A T 1 a)
    rw [show M.restrictₛₗ T.hom (Hom.app x (F.op.obj T.left) (unit F R A T.left a))
          = Hom.app x U ((obj F R A).map T.hom (unit F R A T.left a)) from
        (naturality_apply x T.hom (unit F R A T.left a)).symm,
      unit, obj_map_germ, map_one]
    exact congrArg (Hom.app x U) (germ_congr F R A (Category.id_comp T.hom) 1 a)
  right_inv u := by
    refine PresheafOfModules.hom_ext fun V => ?_
    ext a
    change descMap F R u (F.op.obj V) (germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a)
        = pushforwardApp F R u V a
    rw [descMap_germ]
    change M.restrictₛₗ (𝟙 (F.op.obj V)) (pushforwardApp F R u V a)
        = pushforwardApp F R u V a
    rw [restrictₛₗ_id_apply]

/-- `homEquiv` is natural in the target module `M`. -/
lemma homEquiv_naturality (A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ _ _))
    (M M' : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) (g : M ⟶ M')
    (x : obj F R A ⟶ M) :
    homEquiv F R A M' (x ≫ g) = homEquiv F R A M x ≫ (pushforward₀OfCommRingCat F R).map g := by
  refine PresheafOfModules.hom_ext fun V => ?_
  rfl

/-- **`L₀`: the left adjoint of `PresheafOfModules.pushforward₀ F R`**, as the objectwise
filtered colimit `U ↦ colim_{V, U ⟶ F V} R(U) ⊗_{R(F V)} A(V)`. -/
noncomputable def colimitPullback :
    PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) :=
  Adjunction.leftAdjointOfEquiv (G := pushforward₀OfCommRingCat F R) (homEquiv F R)
    (homEquiv_naturality F R)

/-- The value of `colimitPullback F R` on `A` is `obj F R A`. -/
lemma colimitPullback_obj
    (A : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)) :
    (colimitPullback F R).obj A = obj F R A := rfl

/-- **The adjunction `L₀ ⊣ pushforward₀ F R`.** -/
noncomputable def colimitPullbackAdjunction :
    colimitPullback F R ⊣ pushforward₀OfCommRingCat F R :=
  Adjunction.adjunctionOfEquivLeft (G := pushforward₀OfCommRingCat F R) (homEquiv F R)
    (homEquiv_naturality F R)

/-- `colimitPullback F R` is a left adjoint. -/
instance : (colimitPullback F R).IsLeftAdjoint :=
  (colimitPullbackAdjunction F R).isLeftAdjoint

/-- `PresheafOfModules.pushforward₀ F R` is a right adjoint, with left adjoint
`colimitPullback F R`. -/
instance isRightAdjoint_pushforward₀ :
    (pushforward₀OfCommRingCat F R :
      PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) ⥤
        PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)).IsRightAdjoint :=
  (colimitPullbackAdjunction F R).isRightAdjoint

/-- The objectwise colimit **is** the left adjoint of `pushforward₀ F R`, canonically. -/
noncomputable def colimitPullbackIsoLeftAdjoint :
    colimitPullback F R ≅ (pushforward₀OfCommRingCat F R).leftAdjoint :=
  Adjunction.leftAdjointUniq (colimitPullbackAdjunction F R) (Adjunction.ofIsRightAdjoint _)

end Adjunction

/-! ### The concrete model for `PresheafOfModules.pullback` -/

section Pullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {S : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Dᵒᵖ ⥤ CommRingCat.{w}}
  (α : S ⟶ F.op ⋙ R) [hUL : UnivLE.{u, w}]

include hUL

/-- `α`, read as a morphism of presheaves of not necessarily commutative rings: the shape
`PresheafOfModules.pushforward` and `PresheafOfModules.pullback` expect. -/
abbrev toRingCatPullback : (S ⋙ forget₂ CommRingCat RingCat) ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat) :=
  toRingCat α

omit hUL in
/-- The pushforward along `α` is extension of scalars followed by the pushforward along `F`,
read in the other order: `pushforward α = pushforward₀ F R ⋙ restrictScalars α`. -/
lemma pushforward_eq :
    PresheafOfModules.pushforward.{w} (toRingCatPullback α) =
      pushforward₀OfCommRingCat F R ⋙
        PresheafOfModules.restrictScalars.{w} (toRingCat α) := rfl

/-- **Extension of scalars followed by the objectwise colimit is left adjoint to the
pushforward**: the concrete model for `PresheafOfModules.pullback`. -/
noncomputable def modelAdjunction :
    extendScalars α ⋙ colimitPullback F R ⊣ PresheafOfModules.pushforward.{w}
      (toRingCatPullback α) :=
  (extendScalarsAdjunction α).comp (colimitPullbackAdjunction F R)

/-- **The pushforward of presheaves of modules along `α` is a right adjoint**, at any universe
of module sections: `modelAdjunction` exhibits a left adjoint for it. Mathlib's own instance
`PresheafOfModules.instIsRightAdjointPushforward` is restricted to module sections in the
universe of the two sites, so it does not apply here; the model does, because the colimit
computing it is taken in `ModuleCat.{w}` and only needs the index category to be
`u`-small. -/
instance isRightAdjoint_pushforward :
    (PresheafOfModules.pushforward.{w} (toRingCatPullback α)).IsRightAdjoint :=
  (modelAdjunction α).isRightAdjoint

/-- **The concrete model for the pullback of presheaves of modules**: Mathlib's abstract
`PresheafOfModules.pullback` is canonically isomorphic to objectwise extension of scalars
followed by the objectwise filtered colimit. -/
noncomputable def pullbackIso :
    PresheafOfModules.pullback.{w} (toRingCatPullback α) ≅
      extendScalars α ⋙ colimitPullback F R :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction.{w} (toRingCatPullback α))
    (modelAdjunction α)

/-- The unit of the model adjunction, on sections: a section `n` of `N` over `V` goes to the
germ at `(V, 𝟙)` of the pure tensor `1 ⊗ n`. -/
lemma modelAdjunction_unit_app_apply
    (N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ) (n : N.obj V) :
    Hom.app ((modelAdjunction α).unit.app N) V n
      = unit F R ((extendScalars α).obj N) V (tmul (α.app V).hom 1 n) := rfl

/-- **The sections of `PresheafOfModules.pullback`**: over `U` they are the colimit of
`R(U) ⊗_{R(F V)} (R(F V) ⊗_{S(V)} N(V))` over the opens-like index category
`CostructuredArrow F.op U`.  This is exactly what the abstract left adjoint does not
provide. -/
noncomputable def pullbackObjIso (N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat))
    (U : Dᵒᵖ) :
    ((PresheafOfModules.pullback.{w} (toRingCatPullback α)).obj N).obj U ≅
      colimit (diagram F R ((extendScalars α).obj N) U) :=
  (PresheafOfModules.evaluation.{w} (R ⋙ forget₂ CommRingCat RingCat) U).mapIso
    ((pullbackIso α).app N)

end Pullback

/-! ### The case of a continuous map of topological spaces -/

section Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- For `F = Opens.map f` the index category of the colimit is filtered, by
`Stacks.PullbackModel.isFiltered_costructuredArrow_opensMap`: the opens `V` of `Y` with
`U ⊆ f⁻¹V` contain `⊤` and are closed under intersection.  So the colimit computing `L₀`,
and hence the pullback of presheaves of modules along a continuous map, is a *filtered*
colimit. -/
instance isFiltered_index (U : (Opens ↑X)ᵒᵖ) :
    IsFiltered (CostructuredArrow (Opens.map f).op U) :=
  isFiltered_costructuredArrow_opensMap f U.unop

end Topology

end Stacks.PullbackColimit
