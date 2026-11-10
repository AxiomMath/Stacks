module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import StacksCore.Tactic.StacksAttribute

/-!
# The cochain complex computing homomorphisms of modules on a category

Let `C` be a small category carrying the chaotic topology and let `O : Cᵒᵖ ⥤ RingCat` be a sheaf
of rings on it, so that `O`-modules are presheaves of modules over `O`. For `O`-modules `G` and
`F`, Stacks 08S0 forms the cochain complex `K^•(G, F)` whose group in degree `n` is the product,
over the strings `U₀ ⟶ ⋯ ⟶ Uₙ` of `n` composable arrows of `C`, of the groups
`Hom_{O(Uₙ)}(G(Uₙ), F(U₀))`, where `F(U₀)` is an `O(Uₙ)`-module through the restriction map
`O(Uₙ) ⟶ O(U₀)`. The differential is the alternating sum of the cofaces: the outer two restrict
in the target and in the source, the inner ones omit a vertex of the string.

This file constructs that complex, bifunctorially in the pair `(G, F)`, records its differential
explicitly, and identifies its degree-zero cohomology with the group of homomorphisms `G ⟶ F`:
a degree-zero cochain is a family of linear maps `G(U) ⟶ F(U)`, and it is a cocycle exactly when
that family is a morphism of presheaves of modules.

## Main definitions

* `Stacks.CategoryExt.extCochain`: the degree-`n` cochains of `K^•(G, F)`, an element being a
  family of maps `G(Uₙ) ⟶ F(U₀)` semilinear along the restriction maps of `O`.
* `Stacks.CategoryExt.extCochainCosimplicialBifunctor`: the cosimplicial group of cochains, as a
  bifunctor contravariant in the source module and covariant in the target module.
* `Stacks.CategoryExt.extCochainComplexBifunctor` and `Stacks.CategoryExt.extCochainComplex`: the
  associated alternating-coface cochain complex.

## Main results

* `Stacks.CategoryExt.extCochainComplex_d_apply`: the differential is the alternating sum of the
  coface maps, and `Stacks.CategoryExt.extCochainSimplexMap_apply` evaluates each of them.
* `Stacks.CategoryExt.extCochainComplex_d_one_apply`: the degree-one differential in the form
  `φ_{U₀ → U₁} ∘ ρ^{U₂}_{U₁} - φ_{U₀ → U₂} + ρ^{U₁}_{U₀} ∘ φ_{U₁ → U₂}`.
* `Stacks.CategoryExt.extCochainComplexHomologyZeroIso`: the degree-zero cohomology of
  `K^•(G, F)` is the group of homomorphisms `G ⟶ F`.

## Implementation notes

A cochain is restricted along a factorisation of arrows of `C` by
`Stacks.CategoryExt.extCochainRestrict`; every coface, and more generally the action of every
morphism of `SimplexCategory`, is an instance of it, so the cosimplicial identities follow from
`Stacks.CategoryExt.extCochainRestrict_comp` together with functoriality of the strings. Taking
the alternating-coface complex of a cosimplicial object then supplies `d ∘ d = 0`.

The restriction maps of a module are used in their semilinear form
`PresheafOfModules.restrictₛₗ`, which lands in the module itself rather than in its restriction
of scalars; this keeps the cochain groups free of coercions. The two ends of a string
`x : ComposableArrows C n` are written `x.obj 0` and `x.obj (Fin.last n)` rather than `x.left`
and `x.right`, and its composite as `stringSpine x`, so that the indices agree on the nose with
those produced by reindexing along a morphism of `SimplexCategory`. The category `C` is taken
small so that the cochain groups and the homomorphism groups of `O`-modules live in the same
universe.

The identification of the higher cohomology of `K^•(G, F)` with `Ext^i_O(G, F)`, valid when
`G(U)` is a projective `O(U)`-module for every `U` or when `F(U)` is injective over `O(V)` for
every arrow `U ⟶ V`, is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExtCochainComplexComputesExt`,
which needs the `Ext` groups and the theory of universal δ-functors; this file constructs the
complex, its differential and its degree-zero cohomology.

## References

* [Stacks Project, Tag 08S0](https://stacks.math.columbia.edu/tag/08S0)
* [Stacks Project, Tag 08RZ](https://stacks.math.columbia.edu/tag/08RZ)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace Stacks.CategoryExt

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ RingCat.{v}}

/-- The composite arrow from the first to the last object of a string of composable arrows. -/
abbrev stringSpine {n : ℕ} (x : ComposableArrows C n) : x.obj 0 ⟶ x.obj (Fin.last n) :=
  x.map (homOfLE (Fin.zero_le (Fin.last n)))

/-- The degree-`n` cochains of the complex computing homomorphisms from `G` to `F`: a family,
indexed by the strings `U₀ ⟶ ⋯ ⟶ Uₙ` of `n` composable arrows of `C`, of maps `G(Uₙ) ⟶ F(U₀)`
semilinear along the restriction map `O(Uₙ) ⟶ O(U₀)`. -/
@[sga "4 V 2.3.6" "Item (d)"]
abbrev extCochain (G F : PresheafOfModules.{m} O) (n : ℕ) : Type (max u m) :=
  ∀ x : ComposableArrows C n,
    G.obj (op (x.obj (Fin.last n))) →ₛₗ[(O.map (stringSpine x).op).hom] F.obj (op (x.obj 0))

/-- Two composable arrows of a string compose to the arrow between the same two objects. -/
lemma map_comp_two {n : ℕ} (x : ComposableArrows C n) {i j k : Fin (n + 1)}
    (f : i ⟶ j) (g : j ⟶ k) (f' : i ⟶ k) : x.map f ≫ x.map g = x.map f' := by
  rw [← x.map_comp]
  rfl

/-- Three composable arrows of a string compose to the arrow between the same two objects. -/
lemma map_comp_three {n : ℕ} (x : ComposableArrows C n) {i j k l : Fin (n + 1)}
    (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (f' : i ⟶ l) :
    x.map f ≫ x.map g ≫ x.map h = x.map f' := by
  rw [← x.map_comp, ← x.map_comp]
  rfl

/-- Restriction of a module along an arrow of `C` which is the identity acts trivially. -/
lemma restrictₛₗ_eq_id_apply (M : PresheafOfModules.{m} O) {X : C} (f : X ⟶ X) (hf : f = 𝟙 X)
    (s : M.obj (op X)) : M.restrictₛₗ f.op s = s := by
  change M.presheaf.map f.op s = s
  rw [hf, op_id, M.presheaf.map_id]
  rfl

/-- Restriction of a module along the identity acts trivially. -/
lemma restrictₛₗ_id_apply (M : PresheafOfModules.{m} O) {X : C} (s : M.obj (op X)) :
    M.restrictₛₗ (𝟙 X).op s = s :=
  restrictₛₗ_eq_id_apply M _ rfl s

/-- Restriction of a module along a composite of two arrows of `C`. -/
lemma restrictₛₗ_comp_apply (M : PresheafOfModules.{m} O) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hh : f ≫ g = h) (s : M.obj (op Z)) :
    M.restrictₛₗ f.op (M.restrictₛₗ g.op s) = M.restrictₛₗ h.op s := by
  change M.map f.op (M.map g.op s) = M.map h.op s
  rw [← M.map_comp_apply, ← op_comp, hh]

/-- Restriction of the sheaf of rings along an arrow which is the identity acts trivially. -/
lemma ring_map_op_eq_id_apply {X : C} (f : X ⟶ X) (hf : f = 𝟙 X) (r : O.obj (op X)) :
    (O.map f.op).hom r = r := by
  rw [hf, op_id, O.map_id]
  rfl

/-- A map semilinear along a restriction map which is the identity is linear. -/
def ofSemilinearId {M N : PresheafOfModules.{m} O} {X : C} (f : X ⟶ X) (hf : f = 𝟙 X)
    (φ : M.obj (op X) →ₛₗ[(O.map f.op).hom] N.obj (op X)) : M.obj (op X) ⟶ N.obj (op X) :=
  ModuleCat.ofHom
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r s ↦ (map_smulₛₗ φ r s).trans
        (congrArg (fun t ↦ t • φ s) (ring_map_op_eq_id_apply f hf r)) }

/-- A linear map is semilinear along a restriction map which is the identity. -/
def toSemilinearId {M N : PresheafOfModules.{m} O} {X : C} (f : X ⟶ X) (hf : f = 𝟙 X)
    (φ : M.obj (op X) ⟶ N.obj (op X)) :
    M.obj (op X) →ₛₗ[(O.map f.op).hom] N.obj (op X) where
  toFun := φ.hom
  map_add' := map_add φ.hom
  map_smul' r s := (map_smul φ.hom r s).trans
    (congrArg (fun t ↦ t • φ.hom s) (ring_map_op_eq_id_apply f hf r).symm)

section Restrict

variable {G F : PresheafOfModules.{m} O}

/-- A map `G(Y) ⟶ F(X)` semilinear along `f : X ⟶ Y` is restricted to a map `G(Y') ⟶ F(X')`
semilinear along `f' : X' ⟶ Y'` by a factorisation `f' = a ≫ f ≫ b`. -/
def extCochainRestrict {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f')
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) :
    G.obj (op Y') →ₛₗ[(O.map f'.op).hom] F.obj (op X') where
  toFun s := F.restrictₛₗ a.op (φ (G.restrictₛₗ b.op s))
  map_add' s t := by simp only [map_add]
  map_smul' r s := by
    have hO : (O.map f'.op).hom r =
        (O.map a.op).hom ((O.map f.op).hom ((O.map b.op).hom r)) := by
      rw [← h, op_comp, op_comp, O.map_comp, O.map_comp]
      rfl
    simp only [map_smulₛₗ, hO]

/-- The restriction of `φ` sends `s` to the restriction along `a` of `φ` applied to the
restriction of `s` along `b`. -/
lemma extCochainRestrict_apply {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f')
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) (s : G.obj (op Y')) :
    extCochainRestrict a b h φ s = F.restrictₛₗ a.op (φ (G.restrictₛₗ b.op s)) :=
  rfl

/-- Restricting along a factorisation whose target component is the identity. -/
lemma extCochainRestrict_apply_of_id_right {X Y X' : C} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (a : X' ⟶ X) (b : Y ⟶ Y) (h : a ≫ f ≫ b = f') (hb : b = 𝟙 Y)
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) (s : G.obj (op Y)) :
    extCochainRestrict a b h φ s = F.restrictₛₗ a.op (φ s) :=
  congrArg (fun z ↦ F.restrictₛₗ a.op (φ z)) (restrictₛₗ_eq_id_apply G b hb s)

/-- Restricting along a factorisation whose source component is the identity. -/
lemma extCochainRestrict_apply_of_id_left {X Y Y' : C} {f : X ⟶ Y} {f' : X ⟶ Y'}
    (a : X ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f') (ha : a = 𝟙 X)
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) (s : G.obj (op Y')) :
    extCochainRestrict a b h φ s = φ (G.restrictₛₗ b.op s) :=
  restrictₛₗ_eq_id_apply F a ha (φ (G.restrictₛₗ b.op s))

/-- Restricting along a factorisation both of whose components are the identity. -/
lemma extCochainRestrict_apply_of_id {X Y : C} {f f' : X ⟶ Y}
    (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f ≫ b = f') (ha : a = 𝟙 X) (hb : b = 𝟙 Y)
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) (s : G.obj (op Y)) :
    extCochainRestrict a b h φ s = φ s :=
  (extCochainRestrict_apply_of_id_right a b h hb φ s).trans
    (restrictₛₗ_eq_id_apply F a ha (φ s))

/-- Restricting along a trivial factorisation changes nothing. -/
lemma extCochainRestrict_eq_self {X Y : C} {f : X ⟶ Y} (a : X ⟶ X) (b : Y ⟶ Y)
    (h : a ≫ f ≫ b = f) (ha : a = 𝟙 X) (hb : b = 𝟙 Y)
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) :
    extCochainRestrict a b h φ = φ := by
  ext s
  exact extCochainRestrict_apply_of_id a b h ha hb φ s

/-- Restriction is additive. -/
lemma extCochainRestrict_zero {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f') :
    extCochainRestrict (G := G) (F := F) a b h 0 = 0 := by
  ext s
  simp only [extCochainRestrict_apply, LinearMap.zero_apply, map_zero]

/-- Restriction is additive. -/
lemma extCochainRestrict_add {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f')
    (φ ψ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) :
    extCochainRestrict a b h (φ + ψ) =
      extCochainRestrict a b h φ + extCochainRestrict a b h ψ := by
  ext s
  simp only [extCochainRestrict_apply, LinearMap.add_apply, map_add]

/-- Restricting twice is restricting along the composed factorisation. -/
lemma extCochainRestrict_comp {X Y X' Y' X'' Y'' : C}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ f ≫ b = f')
    (a' : X'' ⟶ X') (b' : Y' ⟶ Y'') (h' : a' ≫ f' ≫ b' = f'')
    (a'' : X'' ⟶ X) (b'' : Y ⟶ Y'') (h'' : a'' ≫ f ≫ b'' = f'')
    (hA : a' ≫ a = a'') (hB : b ≫ b' = b'')
    (φ : G.obj (op Y) →ₛₗ[(O.map f.op).hom] F.obj (op X)) :
    extCochainRestrict a' b' h' (extCochainRestrict a b h φ) =
      extCochainRestrict a'' b'' h'' φ := by
  ext s
  rw [extCochainRestrict_apply, extCochainRestrict_apply, extCochainRestrict_apply,
    restrictₛₗ_comp_apply G _ _ _ hB, restrictₛₗ_comp_apply F _ _ _ hA]

end Restrict

section Complex

variable (G F : PresheafOfModules.{m} O)

/-- The action of a morphism of `SimplexCategory` on cochains: reindex the string of arrows,
then restrict in the source and in the target. -/
def extCochainSimplexMap {a b : SimplexCategory} (α : a ⟶ b) :
    extCochain G F a.len →+ extCochain G F b.len where
  toFun φ x := extCochainRestrict
    (x.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))
    (x.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last a.len)))))
    (map_comp_three x _ _ _ _)
    (φ (((nerve C).map α.op) x))
  map_zero' := funext fun _ ↦ extCochainRestrict_zero _ _ _
  map_add' _ _ := funext fun _ ↦ extCochainRestrict_add _ _ _ _ _

/-- Evaluation of the action of a morphism of `SimplexCategory` on a cochain at a string. -/
lemma extCochainSimplexMap_apply {a b : SimplexCategory} (α : a ⟶ b)
    (φ : extCochain G F a.len) (x : ComposableArrows C b.len)
    (s : G.obj (op (x.obj (Fin.last b.len)))) :
    extCochainSimplexMap G F α φ x s =
      F.restrictₛₗ (x.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))).op
        ((φ (((nerve C).map α.op) x))
          (G.restrictₛₗ
            (x.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last a.len))))).op s)) :=
  rfl

/-- The cosimplicial group of cochains computing homomorphisms from `G` to `F`. -/
def extCochainCosimplicialObject : CosimplicialObject AddCommGrpCat.{max u m} where
  obj a := AddCommGrpCat.of (extCochain G F a.len)
  map α := AddCommGrpCat.ofHom (extCochainSimplexMap G F α)
  map_id _ := ConcreteCategory.hom_ext _ _ fun _ ↦ funext fun x ↦
    extCochainRestrict_eq_self _ _ (map_comp_three x _ _ _ _) (x.map_id _) (x.map_id _) _
  map_comp _ β := ConcreteCategory.hom_ext _ _ fun _ ↦ funext fun x ↦
    (extCochainRestrict_comp _ _ (map_comp_three ((nerve C).map β.op x) _ _ _ _)
      _ _ (map_comp_three x _ _ _ _) _ _ (map_comp_three x _ _ _ _)
      (map_comp_two x _ _ _) (map_comp_two x _ _ _) _).symm

end Complex

section Bifunctor

/-- A pair of morphisms of modules acts on a map `G(Y) ⟶ F(X)` semilinear along `u : X ⟶ Y`. -/
def extCochainHomMap {G G' F F' : PresheafOfModules.{m} O} (g : G' ⟶ G) (f : F ⟶ F')
    {X Y : C} (u : X ⟶ Y) (φ : G.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X)) :
    G'.obj (op Y) →ₛₗ[(O.map u.op).hom] F'.obj (op X) where
  toFun s := f.app (op X) (φ (g.app (op Y) s))
  map_add' s t := by simp only [map_add]
  map_smul' r s := by rw [map_smul, map_smulₛₗ, map_smul]

/-- The action of `(g, f)` on `φ` sends `s` to `f (φ (g s))`. -/
lemma extCochainHomMap_apply {G G' F F' : PresheafOfModules.{m} O} (g : G' ⟶ G) (f : F ⟶ F')
    {X Y : C} (u : X ⟶ Y) (φ : G.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X))
    (s : G'.obj (op Y)) :
    extCochainHomMap g f u φ s = f.app (op X) (φ (g.app (op Y) s)) :=
  rfl

/-- Restriction of a module, read as a semilinear map, is natural. -/
lemma restrictₛₗ_naturality_apply {M N : PresheafOfModules.{m} O} (t : M ⟶ N) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (s : M.obj X) :
    N.restrictₛₗ f (t.app X s) = t.app Y (M.restrictₛₗ f s) :=
  (PresheafOfModules.naturality_apply t f s).symm

/-- The action of a pair of morphisms of modules commutes with restriction. -/
lemma extCochainHomMap_restrict {G G' F F' : PresheafOfModules.{m} O} (g : G' ⟶ G) (f : F ⟶ F')
    {X Y X' Y' : C} {u : X ⟶ Y} {u' : X' ⟶ Y'}
    (a : X' ⟶ X) (b : Y ⟶ Y') (h : a ≫ u ≫ b = u')
    (φ : G.obj (op Y) →ₛₗ[(O.map u.op).hom] F.obj (op X)) :
    extCochainHomMap g f u' (extCochainRestrict a b h φ) =
      extCochainRestrict a b h (extCochainHomMap g f u φ) := by
  ext s
  rw [extCochainHomMap_apply, extCochainRestrict_apply, extCochainRestrict_apply,
    extCochainHomMap_apply, restrictₛₗ_naturality_apply g b.op s,
    ← restrictₛₗ_naturality_apply f a.op]

/-- The action of a pair of morphisms of modules on cochains. -/
def extCochainMap {G G' F F' : PresheafOfModules.{m} O} (g : G' ⟶ G) (f : F ⟶ F') (n : ℕ) :
    extCochain G F n →+ extCochain G' F' n where
  toFun φ x := extCochainHomMap g f (stringSpine x) (φ x)
  map_zero' := funext fun _ ↦ LinearMap.ext fun _ ↦ by simp [extCochainHomMap_apply]
  map_add' _ _ := funext fun _ ↦ LinearMap.ext fun _ ↦ by simp [extCochainHomMap_apply]

/-- The cosimplicial group of cochains, as a bifunctor: contravariant in the source module and
covariant in the target module. -/
def extCochainCosimplicialBifunctor (C : Type u) [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{v}) :
    ((PresheafOfModules.{m} O)ᵒᵖ × PresheafOfModules.{m} O) ⥤
      CosimplicialObject AddCommGrpCat.{max u m} where
  obj P := extCochainCosimplicialObject P.1.unop P.2
  map h :=
    { app := fun a ↦ AddCommGrpCat.ofHom (extCochainMap h.1.unop h.2 a.len)
      naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ ↦ funext fun x ↦
        extCochainHomMap_restrict h.1.unop h.2 _ _ (map_comp_three x _ _ _ _) _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 08S0.** The cochain complex computing homomorphisms of `O`-modules, as a bifunctor
contravariant in the source module and covariant in the target module. -/
@[stacks 08S0 "the cochain bifunctor"]
def extCochainComplexBifunctor (C : Type u) [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{v}) :
    ((PresheafOfModules.{m} O)ᵒᵖ × PresheafOfModules.{m} O) ⥤
      CochainComplex AddCommGrpCat.{max u m} ℕ :=
  extCochainCosimplicialBifunctor C O ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

end Bifunctor

section Complex

variable (G F : PresheafOfModules.{m} O)

/-- The complex `K^•(G, F)` of Stacks 08S0 attached to a pair of `O`-modules. -/
abbrev extCochainComplex : CochainComplex AddCommGrpCat.{max u m} ℕ :=
  (extCochainComplexBifunctor C O).obj (op G, F)

/-- The degree-`n` group of `K^•(G, F)` is the group of degree-`n` cochains. -/
lemma extCochainComplex_X (n : ℕ) :
    (extCochainComplex G F).X n = AddCommGrpCat.of (extCochain G F n) :=
  rfl

/-- Equal degree-`n` cochains agree at every string of arrows. -/
lemma extCochainComplex_congr_apply {n : ℕ} {φ ψ : (extCochainComplex G F).X n} (hφ : φ = ψ)
    (x : ComposableArrows C n) (s : G.obj (op (x.obj (Fin.last n)))) :
    (φ : extCochain G F n) x s = (ψ : extCochain G F n) x s := by
  rw [hφ]

/-- The differential of `K^•(G, F)` is the alternating sum of the coface maps. -/
@[stacks 08S0 "the alternating differential"]
lemma extCochainComplex_d_apply (n : ℕ) (φ : extCochain G F n)
    (x : ComposableArrows C (n + 1)) (s : G.obj (op (x.obj (Fin.last (n + 1))))) :
    (extCochainComplex G F).d n (n + 1) φ x s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (extCochainSimplexMap G F (SimplexCategory.δ i) φ x s) := by
  change ((AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (extCochainCosimplicialObject G F)).d n (n + 1) φ) x s = _
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  let ev : (AddCommGrpCat.of (extCochain G F n) ⟶
      AddCommGrpCat.of (extCochain G F (n + 1))) →+ F.obj (op (x.obj 0)) :=
    { toFun := fun t ↦ t φ x s
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    AddCommGrpCat.ofHom (extCochainSimplexMap G F (SimplexCategory.δ i))) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_zsmul ev _ _

/-- The first coface acts on a cochain by restricting its value along the first arrow. -/
private lemma extCochainSimplexMap_δ_zero_apply {n : ℕ} (φ : extCochain G F n)
    (x : ComposableArrows C (n + 1)) (s : G.obj (op (x.obj (Fin.last (n + 1))))) :
    extCochainSimplexMap G F (SimplexCategory.δ (0 : Fin (n + 2))) φ x s =
      F.restrictₛₗ (x.map' 0 1).op (φ ((nerve C).δ 0 x) s) :=
  extCochainRestrict_apply_of_id_right _ _ (map_comp_three x _ _ _ _) (x.map_id _) _ s

/-- The degree-zero differential of `K^•(G, F)`: on an arrow `U₀ ⟶ U₁` it is
`ρ^{U₁}_{U₀} ∘ φ_{U₁} - φ_{U₀} ∘ ρ^{U₁}_{U₀}`. -/
@[stacks 08S0 "the degree-zero differential"]
lemma extCochainComplex_d_zero_apply (φ : extCochain G F 0) (x : ComposableArrows C 1)
    (s : G.obj (op (x.obj (Fin.last 1)))) (p q : F.obj (op (x.obj 0)))
    (hp : p = F.restrictₛₗ (stringSpine x).op (φ ((nerve C).δ 0 x) s))
    (hq : q = φ ((nerve C).δ 1 x) (G.restrictₛₗ (stringSpine x).op s)) :
    (extCochainComplex G F).d 0 1 φ x s = p - q := by
  have t₀ : extCochainSimplexMap G F (SimplexCategory.δ (0 : Fin 2)) φ x s = p :=
    (extCochainSimplexMap_δ_zero_apply G F φ x s).trans hp.symm
  have t₁ : extCochainSimplexMap G F (SimplexCategory.δ (1 : Fin 2)) φ x s = q :=
    (extCochainRestrict_apply_of_id_left _ _ (map_comp_three x _ _ _ _)
      (x.map_id _) _ s).trans hq.symm
  have harith : ∀ a b : F.obj (op (x.obj 0)),
      ((-1 : ℤ) ^ ((0 : Fin 2) : ℕ)) • a + ((-1 : ℤ) ^ ((1 : Fin 2) : ℕ)) • b = a - b := by
    intro a b
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
    rw [← sub_eq_add_neg]
  have h := extCochainComplex_d_apply G F 0 φ x s
  rw [Fin.sum_univ_two] at h
  exact h.trans ((harith _ _).trans (congrArg₂ (· - ·) t₀ t₁))

/-- The degree-one differential of `K^•(G, F)`: on a string `U₀ ⟶ U₁ ⟶ U₂` it is
`φ_{U₀ → U₁} ∘ ρ^{U₂}_{U₁} - φ_{U₀ → U₂} + ρ^{U₁}_{U₀} ∘ φ_{U₁ → U₂}`. -/
@[stacks 08S0 "the degree-one differential"]
lemma extCochainComplex_d_one_apply (φ : extCochain G F 1) (x : ComposableArrows C 2)
    (s : G.obj (op (x.obj (Fin.last 2)))) (p q r : F.obj (op (x.obj 0)))
    (hp : p = φ ((nerve C).δ 2 x) (G.restrictₛₗ (x.map' 1 2).op s))
    (hq : q = φ ((nerve C).δ 1 x) s)
    (hr : r = F.restrictₛₗ (x.map' 0 1).op (φ ((nerve C).δ 0 x) s)) :
    (extCochainComplex G F).d 1 2 φ x s = p - q + r := by
  have t₀ : extCochainSimplexMap G F (SimplexCategory.δ (0 : Fin 3)) φ x s = r :=
    (extCochainSimplexMap_δ_zero_apply G F φ x s).trans hr.symm
  have t₁ : extCochainSimplexMap G F (SimplexCategory.δ (1 : Fin 3)) φ x s = q :=
    (extCochainRestrict_apply_of_id _ _ (map_comp_three x _ _ _ _)
      (x.map_id _) (x.map_id _) _ s).trans hq.symm
  have t₂ : extCochainSimplexMap G F (SimplexCategory.δ (2 : Fin 3)) φ x s = p :=
    (extCochainRestrict_apply_of_id_left _ _ (map_comp_three x _ _ _ _)
      (x.map_id _) _ s).trans hp.symm
  have harith : ∀ a b c : F.obj (op (x.obj 0)),
      ((-1 : ℤ) ^ ((0 : Fin 3) : ℕ)) • a + ((-1 : ℤ) ^ ((1 : Fin 3) : ℕ)) • b +
        ((-1 : ℤ) ^ ((2 : Fin 3) : ℕ)) • c = c - b + a := by
    intro a b c
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq,
      one_zsmul, neg_one_zsmul]
    abel
  have h := extCochainComplex_d_apply G F 1 φ x s
  rw [Fin.sum_univ_three] at h
  exact h.trans ((harith _ _ _).trans
    (congrArg₂ (· + ·) (congrArg₂ (· - ·) t₂ t₁) t₀))

end Complex

section DegreeZero

variable {G F : PresheafOfModules.{m} O}

/-- A degree-zero cochain evaluated at the one-object string on `U`, read as a linear map
`G(U) ⟶ F(U)`. -/
def extCochainZeroApp (φ : extCochain G F 0) (U : Cᵒᵖ) : G.obj U ⟶ F.obj U :=
  ofSemilinearId ((ComposableArrows.mk₀ U.unop).map (𝟙 (0 : Fin 1))) rfl
    (φ (ComposableArrows.mk₀ U.unop))

/-- The linear map attached to a degree-zero cochain is its value at the one-object string. -/
lemma extCochainZeroApp_apply (φ : extCochain G F 0) (U : Cᵒᵖ) (s : G.obj U) :
    extCochainZeroApp φ U s = φ (ComposableArrows.mk₀ U.unop) s :=
  rfl

/-- The degree-zero cochain attached to a morphism of `O`-modules. -/
def homToExtCochainZero (ψ : G ⟶ F) : extCochain G F 0 := fun x ↦
  toSemilinearId (x.map (𝟙 (0 : Fin 1))) (x.map_id _) (ψ.app (op (x.obj 0)))

/-- Degree-zero cochains at equal strings agree. -/
lemma extCochainZero_congr (φ : extCochain G F 0) {x y : ComposableArrows C 0} (hxy : x = y)
    (s : G.obj (op (x.obj (Fin.last 0)))) (t : G.obj (op (y.obj (Fin.last 0))))
    (hst : HEq s t) : HEq (φ x s) (φ y t) := by
  subst hxy
  cases hst
  rfl

/-- A degree-zero cocycle is a compatible family of linear maps. -/
lemma extCochainZeroApp_naturality (φ : extCochain G F 0)
    (hφ : ∀ (y : ComposableArrows C 1) (t : G.obj (op (y.obj (Fin.last 1)))),
      (extCochainComplex G F).d 0 1 φ y t = 0)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    G.map f ≫ (ModuleCat.restrictScalars (O.map f).hom).map (extCochainZeroApp φ V) =
      extCochainZeroApp φ U ≫ F.map f := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  have hd := extCochainComplex_d_zero_apply G F φ (ComposableArrows.mk₁ f.unop) s
    (F.restrictₛₗ f (φ ((nerve C).δ 0 (ComposableArrows.mk₁ f.unop)) s))
    (φ ((nerve C).δ 1 (ComposableArrows.mk₁ f.unop)) (G.restrictₛₗ f s)) rfl rfl
  have h : F.restrictₛₗ f (φ ((nerve C).δ 0 (ComposableArrows.mk₁ f.unop)) s) =
      φ ((nerve C).δ 1 (ComposableArrows.mk₁ f.unop)) (G.restrictₛₗ f s) :=
    sub_eq_zero.1 (hd.symm.trans (hφ (ComposableArrows.mk₁ f.unop) s))
  have hd0 : (nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f.unop) =
      ComposableArrows.mk₀ U.unop := ComposableArrows.ext₀ rfl
  have hd1 : (nerve C).δ (1 : Fin 2) (ComposableArrows.mk₁ f.unop) =
      ComposableArrows.mk₀ V.unop := ComposableArrows.ext₀ rfl
  have k0 : φ ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f.unop)) s =
      φ (ComposableArrows.mk₀ U.unop) s :=
    eq_of_heq (extCochainZero_congr φ hd0 s s HEq.rfl)
  have k1 : φ ((nerve C).δ (1 : Fin 2) (ComposableArrows.mk₁ f.unop)) (G.restrictₛₗ f s) =
      φ (ComposableArrows.mk₀ V.unop) (G.restrictₛₗ f s) :=
    eq_of_heq (extCochainZero_congr φ hd1 _ _ HEq.rfl)
  exact k1.symm.trans (h.symm.trans (congrArg (fun z ↦ F.restrictₛₗ f z) k0))

/-- A degree-zero cocycle of `K^•(G, F)` is a morphism of `O`-modules. -/
def extCochainZeroToHom (φ : extCochain G F 0)
    (hφ : ∀ (y : ComposableArrows C 1) (t : G.obj (op (y.obj (Fin.last 1)))),
      (extCochainComplex G F).d 0 1 φ y t = 0) : G ⟶ F where
  app U := extCochainZeroApp φ U
  naturality f := extCochainZeroApp_naturality φ hφ f

end DegreeZero

section Comparison

/-- The group of morphisms of `O`-modules maps to the degree-zero cochains. -/
def homToExtCochainZeroHom (G F : PresheafOfModules.{m} O) :
    AddCommGrpCat.of (G ⟶ F) ⟶ (extCochainComplex G F).X 0 :=
  AddCommGrpCat.ofHom
    { toFun := homToExtCochainZero
      map_zero' := funext fun _ ↦ LinearMap.ext fun _ ↦ rfl
      map_add' := fun _ _ ↦ funext fun _ ↦ LinearMap.ext fun _ ↦ rfl }

/-- The degree-zero cochain of a morphism of `O`-modules is a cocycle. -/
lemma homToExtCochainZeroHom_d (G F : PresheafOfModules.{m} O) :
    homToExtCochainZeroHom G F ≫ (extCochainComplex G F).d 0 1 = 0 := by
  apply ConcreteCategory.hom_ext
  intro ψ
  funext x
  refine LinearMap.ext fun s ↦ ?_
  have h := extCochainComplex_d_zero_apply G F (homToExtCochainZero ψ) x s
    (F.restrictₛₗ (stringSpine x).op (homToExtCochainZero ψ ((nerve C).δ 0 x) s))
    (homToExtCochainZero ψ ((nerve C).δ 1 x) (G.restrictₛₗ (stringSpine x).op s)) rfl rfl
  exact h.trans (sub_eq_zero.2
    (PresheafOfModules.naturality_apply ψ (stringSpine x).op s).symm)

/-- The morphism of `O`-modules attached to a degree-zero cycle. -/
def extCochainCyclesZeroToHom (G F : PresheafOfModules.{m} O) :
    (extCochainComplex G F).cycles 0 ⟶ AddCommGrpCat.of (G ⟶ F) :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦ extCochainZeroToHom ((extCochainComplex G F).iCycles 0 c)
        (fun y t ↦ extCochainComplex_congr_apply G F
          (ConcreteCategory.congr_hom ((extCochainComplex G F).iCycles_d 0 1) c) y t)
      map_zero' := by
        refine PresheafOfModules.hom_ext fun U ↦
          ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
        have h : (extCochainComplex G F).iCycles 0
            (0 : (extCochainComplex G F).cycles 0) = 0 := map_zero _
        exact extCochainComplex_congr_apply G F h (ComposableArrows.mk₀ U.unop) s
      map_add' := fun c d ↦ by
        refine PresheafOfModules.hom_ext fun U ↦
          ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
        have h : (extCochainComplex G F).iCycles 0 (c + d) =
            (extCochainComplex G F).iCycles 0 c +
              (extCochainComplex G F).iCycles 0 d := map_add _ _ _
        exact extCochainComplex_congr_apply G F h (ComposableArrows.mk₀ U.unop) s }

/-- The degree-zero cycle attached to a morphism of `O`-modules. -/
def homToExtCochainCyclesZero (G F : PresheafOfModules.{m} O) :
    AddCommGrpCat.of (G ⟶ F) ⟶ (extCochainComplex G F).cycles 0 :=
  (extCochainComplex G F).liftCycles (homToExtCochainZeroHom G F) 1 (by simp)
    (homToExtCochainZeroHom_d G F)

/-- The degree-zero cycle attached to a morphism of `O`-modules has as underlying cochain the
degree-zero cochain attached to it. -/
lemma homToExtCochainCyclesZero_iCycles (G F : PresheafOfModules.{m} O) :
    homToExtCochainCyclesZero G F ≫ (extCochainComplex G F).iCycles 0 =
      homToExtCochainZeroHom G F :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The degree-zero cycles of `K^•(G, F)` are the morphisms `G ⟶ F`. -/
def extCochainComplexCyclesZeroIso (G F : PresheafOfModules.{m} O) :
    (extCochainComplex G F).cycles 0 ≅ AddCommGrpCat.of (G ⟶ F) where
  hom := extCochainCyclesZeroToHom G F
  inv := homToExtCochainCyclesZero G F
  hom_inv_id := by
    apply (cancel_mono ((extCochainComplex G F).iCycles 0)).mp
    rw [Category.assoc, homToExtCochainCyclesZero_iCycles, Category.id_comp]
    apply ConcreteCategory.hom_ext
    intro c
    funext x
    obtain ⟨U, rfl⟩ : ∃ U : C, x = ComposableArrows.mk₀ U :=
      ⟨x.obj 0, ComposableArrows.ext₀ rfl⟩
    rfl
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro ψ
    refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    have h : (extCochainComplex G F).iCycles 0 (homToExtCochainCyclesZero G F ψ) =
        homToExtCochainZeroHom G F ψ :=
      ConcreteCategory.congr_hom (homToExtCochainCyclesZero_iCycles G F) ψ
    exact extCochainComplex_congr_apply G F h (ComposableArrows.mk₀ U.unop) s

/-- **Stacks 08S0.** The degree-zero cohomology of `K^•(G, F)` is the group of homomorphisms
of `O`-modules from `G` to `F`. -/
@[stacks 08S0 "degree-zero cohomology"]
def extCochainComplexHomologyZeroIso (G F : PresheafOfModules.{m} O) :
    (extCochainComplex G F).homology 0 ≅ AddCommGrpCat.of (G ⟶ F) :=
  (extCochainComplex G F).isoHomologyπ₀.symm ≪≫ extCochainComplexCyclesZeroIso G F

end Comparison

end Stacks.CategoryExt
