module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The coefficient presheaf of the relative Čech complex

Let `f : X ⟶ S` be a morphism of schemes.  Tag 01XL computes `R f_* F` for a quasi-coherent
`𝒪_X`-module `F` by the Čech complex of a finite affine open covering, whose degree `p` term is
the direct sum over `(p+1)`-tuples `i₀ … i_p` of `f_{i₀ … i_p *} F|_{U_{i₀ … i_p}}`.  The
coefficient system underlying that complex is defined on all of `Over X`:  an object
`A : Over X` with structure morphism `a = A.hom` is sent to `(a ≫ f)_* a^* F`, and the
intersections `U_{i₀ … i_p}` are the products of the `Over.mk (T.f i)` in `Over X`.

This file constructs that coefficient system, functorially in the quasi-coherent module.

## Main definitions

* `relativeMonad`:  the presheaf `(Over X)ᵒᵖ ⥤ (X.Modules ⥤ X.Modules)` sending `A` to the monad
  `a^* ⊣ a_*` of its structure morphism, i.e. to `a_* a^*`.
* `relativeCechPresheaf`:  the coefficient presheaf of Tag 01XL, a functor from quasi-coherent
  `𝒪_X`-modules to presheaves on `(Over X)ᵒᵖ` with values in `𝒪_S`-modules, whose value at
  `(F, A)` is `(a ≫ f)_* a^* F`.

## Main results

* `relativeCechPresheaf_obj_obj`:  the value of the coefficient presheaf is literally
  `(a ≫ f)_* a^* F`.
* `relativeMonad_map`:  the restriction map of the coefficient system is the canonical one,
  built from the unit of `h^* ⊣ h_*` and the comparison isomorphisms for composites.
* `relativeCechPresheaf_map`:  the restriction map of the coefficient presheaf *itself* — one
  level up from `relativeMonad_map` — is that same canonical map, pushed forward along `f`.
* `relativeCechRestriction_eq`:  the canonical restriction map written out as the explicit
  five-fold composite (unit, `pushforwardComp`, `pullbackComp`, `pullbackCongr`,
  `pushforwardCongr`) agrees with `relativeUnit`, up to the transport along `u ≫ b = a`.

## Implementation notes

The only obstruction to defining the coefficient presheaf is that `pullback` is a pseudofunctor
rather than a functor:  `(u ≫ b)^*` and `b^* u^*`... `u^* b^*` are merely isomorphic, by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.  Pushforward, on the other hand, *is* strictly
functorial in this Mathlib: `pushforward u ⋙ pushforward b = pushforward (u ≫ b)` holds by
`rfl`, and the components of `pushforwardComp` and `pushforwardId` are definitionally
identities.  Because composition of morphisms of schemes is also strictly associative and
unital, all the transports appearing in the cocycle condition reduce to identities definitionally,
and the two functor axioms come down to Mathlib's coherence lemmas
(see also `relativeCechRestriction_head`, which is one such `rfl`).

The identification of the presheaf's restriction map with the canonical one is *true* by
`rfl`, but the conversion is far too expensive for the kernel's budget when asked in one
step.  It is therefore factored into three cheap layers — `relativeCechPresheaf_obj_map_flip`
discharges the `Functor.flip` layer by the *general* lemma `Functor.flip_obj_map` rather than
by `rfl`, `relativeCechPresheafUncurried_map_app` does the whiskering layer by `rfl`, and the
last layer is a `congrArg` over `relativeMonad_map`, so that the deep unfolding happens under
a congruence instead of inside the enclosing functor's `map`.  The same discipline governs
`relativeCechRestriction_eq`:  each identification of two definitionally equal but
differently *spelled* objects is isolated in a lemma all of whose data are variables, where
the conversion is cheap, and never performed inside the large goal.  Mathlib's coherence lemmas
used are
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`,
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality`,
`CategoryTheory.conjugateEquiv_pullbackComp_inv` and
`CategoryTheory.conjugateEquiv_pullbackId_hom`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCech

variable {W X Y Z : Scheme.{u}}

/-! ### Strict functoriality of pushforward -/

/-- Pushforward along a composite is the composite of the pushforwards, on morphisms. -/
public theorem pushforward_comp_map (u : Y ⟶ Z) (b : Z ⟶ X) {M N : Y.Modules} (g : M ⟶ N) :
    (pushforward (u ≫ b)).map g = (pushforward b).map ((pushforward u).map g) := rfl

/-- Pushforward along a composite, with the composite of functors on the left. -/
public theorem pushforward_comp_functor_map (u : Y ⟶ Z) (b : Z ⟶ X) {M N : Y.Modules}
    (g : M ⟶ N) :
    (pushforward u ⋙ pushforward b).map g = (pushforward (u ≫ b)).map g := rfl

/-- Three nested pushforwards agree with the pushforward along the composite, on objects. -/
public theorem pushforward_obj_triple (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X) (M : X.Modules) :
    (pushforward c).obj ((pushforward v).obj ((pushforward u).obj
        ((pullback (u ≫ v ≫ c)).obj M)))
      = (pullback (u ≫ v ≫ c) ⋙ pushforward (u ≫ v ≫ c)).obj M := rfl

/-- The comparison morphism for a composite of pushforwards is the identity. -/
public theorem pushforwardComp_hom_app (u : Y ⟶ Z) (b : Z ⟶ X) (M : Y.Modules) :
    (pushforwardComp u b).hom.app M = 𝟙 _ := rfl

/-- Composing a pushforward of a morphism with a pushforward along a composite:  a
type-preserving reassociation, true by `rfl` because pushforward is strictly functorial. -/
public theorem pushforward_map_comp (u : Y ⟶ Z) (b : Z ⟶ X) {M : Z.Modules} {N P : Y.Modules}
    (f : M ⟶ (pushforward u).obj N) (g : N ⟶ P) :
    (pushforward b).map f ≫ (pushforward (u ≫ b)).map g
      = (pushforward b).map (f ≫ (pushforward u).map g) := rfl

/-- Absorbing an `eqToHom` through a functor. -/
public theorem map_comp_eqToHom {Y' : Scheme.{u}} (F : Y'.Modules ⥤ X.Modules)
    {A B B' : Y'.Modules} (f : A ⟶ B) (h : B = B') {E : X.Modules}
    (e : F.obj B' = E) (e' : F.obj B = E) :
    F.map (f ≫ eqToHom h) ≫ eqToHom e = F.map f ≫ eqToHom e' := by
  subst h
  simp

/-! ### The coherence identities used for the two functor axioms -/

/-- The cocycle identity for `pullbackComp`, read off from Mathlib's pseudofunctor
associativity. -/
public theorem pullbackComp_assoc (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X)
    (e : (pullback (u ≫ v ≫ c) : X.Modules ⥤ W.Modules) = pullback ((u ≫ v) ≫ c)) :
    Functor.whiskerRight (pullbackComp v c).hom (pullback u) ≫
        ((pullbackComp u (v ≫ c)).hom ≫ eqToHom e)
      = (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pullback c) (pullbackComp u v).hom ≫
        (pullbackComp (u ≫ v) c).hom := by
  have h := (Iso.inv_comp_eq _).mp
    (pseudofunctor_associativity (f := u) (g := v) (h := c))
  rw [← h, ← Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id,
    Functor.whiskerRight_id', Category.id_comp]

/-- The componentwise form of `pullbackComp_assoc`. -/
public theorem pullbackComp_assoc_app (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X) (M : X.Modules)
    (e : (pullback ((u ≫ v) ≫ c)).obj M = (pullback (u ≫ v ≫ c)).obj M) :
    (pullback u).map ((pullbackComp v c).hom.app M) ≫ (pullbackComp u (v ≫ c)).hom.app M
      = (pullbackComp u v).hom.app ((pullback c).obj M) ≫
        ((pullbackComp (u ≫ v) c).hom.app M ≫ eqToHom e) := by
  have h := NatTrans.congr_app (pullbackComp_assoc u v c rfl) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at h
  exact h

/-- The unit of `(u ≫ v)^* ⊣ (u ≫ v)_*` compared with the unit of the composite adjunction. -/
public theorem unit_comp_app (u : Y ⟶ Z) (v : Z ⟶ X) (N : X.Modules) :
    ((pullbackPushforwardAdjunction v).comp (pullbackPushforwardAdjunction u)).unit.app N
      = (pullbackPushforwardAdjunction (u ≫ v)).unit.app N ≫
        (pushforward (u ≫ v)).map ((pullbackComp u v).inv.app N) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction v).comp
    (pullbackPushforwardAdjunction u)) (pullbackPushforwardAdjunction (u ≫ v))
    (pullbackComp u v).inv N
  rw [conjugateEquiv_pullbackComp_inv] at h
  exact h

/-- The unit of `(𝟙 Z)^* ⊣ (𝟙 Z)_*` is inverse to `pullbackId`. -/
public theorem unit_id_app (Z : Scheme.{u}) (M : Z.Modules) :
    (pullbackPushforwardAdjunction (𝟙 Z)).unit.app M ≫
        (pushforward (𝟙 Z)).map ((pullbackId Z).hom.app M)
      = (pushforwardId Z).inv.app M := by
  have h := unit_conjugateEquiv (Adjunction.id (C := Z.Modules))
    (pullbackPushforwardAdjunction (𝟙 Z)) (pullbackId Z).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  exact h.symm.trans (Category.id_comp _)

/-- The transpose along a composite adjunction is the iterated transpose. -/
public theorem comp_homEquiv_apply (u : W ⟶ Y) (v : Y ⟶ Z) (N : Z.Modules) {Q : W.Modules}
    (g : (pullback v ⋙ pullback u).obj N ⟶ Q) :
    ((pullbackPushforwardAdjunction v).comp (pullbackPushforwardAdjunction u)).homEquiv N Q g
      = (pullbackPushforwardAdjunction v).homEquiv _ _
          ((pullbackPushforwardAdjunction u).homEquiv _ _ g) := by
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Transposing along `(u ≫ v)^* ⊣ (u ≫ v)_*` and along the composite adjunction agree, once
the comparison isomorphism `pullbackComp` is inserted. -/
public theorem homEquiv_pullbackComp (u : W ⟶ Y) (v : Y ⟶ Z) (N : Z.Modules) {P : W.Modules}
    (k : (pullback (u ≫ v)).obj N ⟶ P)
    (e : ∀ Q : W.Modules,
      (pushforward (u ≫ v)).obj Q = (pushforward u ⋙ pushforward v).obj Q) :
    ((pullbackPushforwardAdjunction v).comp (pullbackPushforwardAdjunction u)).homEquiv N P
        ((pullbackComp u v).hom.app N ≫ k)
      = (pullbackPushforwardAdjunction (u ≫ v)).homEquiv _ _ k ≫ eqToHom (e P) := by
  have h := unit_comp_app u v N
  have key :((pullbackPushforwardAdjunction v).comp
        (pullbackPushforwardAdjunction u)).unit.app N ≫
        (pushforward u ⋙ pushforward v).map ((pullbackComp u v).hom.app N)
      = (pullbackPushforwardAdjunction (u ≫ v)).unit.app N ≫ eqToHom (e _) := by
    have h3 := congrArg
      (fun t => t ≫ (pushforward (u ≫ v)).map ((pullbackComp u v).hom.app N)) h
    simp only [Category.assoc] at h3
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at h3
    exact h3
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Functor.map_comp,
    ← Category.assoc, key, Category.assoc]
  rfl

/-! ### The restriction maps of the coefficient system -/

/-- For `u : Y ⟶ Z` and `b : Z ⟶ X`, the canonical map `b_* b^* ⟶ (u ≫ b)_* (u ≫ b)^*`:
the unit of `u^* ⊣ u_*` inserted in the middle, followed by the comparison isomorphism for the
composite `u ≫ b`. -/
public noncomputable def relativeUnit (u : Y ⟶ Z) (b : Z ⟶ X) :
    pullback b ⋙ pushforward b ⟶ pullback (u ≫ b) ⋙ pushforward (u ≫ b) :=
  Functor.whiskerRight
      (Functor.whiskerLeft (pullback b) (pullbackPushforwardAdjunction u).unit) (pushforward b) ≫
    Functor.whiskerRight (pullbackComp u b).hom (pushforward (u ≫ b))

/-- The components of `relativeUnit`. -/
public theorem relativeUnit_app (u : Y ⟶ Z) (b : Z ⟶ X) (M : X.Modules) :
    (relativeUnit u b).app M =
      (pushforward b).map ((pullbackPushforwardAdjunction u).unit.app ((pullback b).obj M) ≫
        (pushforward u).map ((pullbackComp u b).hom.app M)) := by
  show (Functor.whiskerRight
      (Functor.whiskerLeft (pullback b) (pullbackPushforwardAdjunction u).unit)
        (pushforward b)).app M ≫
      (Functor.whiskerRight (pullbackComp u b).hom (pushforward (u ≫ b))).app M = _
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp]
  rfl

/-- The components of `relativeUnit`, as a transpose along `u^* ⊣ u_*`. -/
public theorem relativeUnit_app' (u : Y ⟶ Z) (b : Z ⟶ X) (M : X.Modules) :
    (relativeUnit u b).app M =
      (pushforward b).map ((pullbackPushforwardAdjunction u).homEquiv _ _
        ((pullbackComp u b).hom.app M)) := by
  rw [relativeUnit_app, Adjunction.homEquiv_apply]

/-- The composite of two components of `relativeUnit`, as a single transpose.  This holds by
`rfl`:  pushforward is strictly functorial, and composition of morphisms of modules is strictly
associative. -/
public theorem relativeUnit_app_comp (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X) (M : X.Modules)
    (e : (pushforward c).obj ((pushforward v).obj ((pushforward u).obj
          ((pullback (u ≫ v ≫ c)).obj M)))
        = (pullback (u ≫ v ≫ c) ⋙ pushforward (u ≫ v ≫ c)).obj M) :
    (relativeUnit v c).app M ≫ (relativeUnit u (v ≫ c)).app M
      = (pushforward c).map ((pullbackPushforwardAdjunction v).homEquiv _ _
          ((pullbackComp v c).hom.app M ≫ (pullbackPushforwardAdjunction u).homEquiv _ _
            ((pullbackComp u (v ≫ c)).hom.app M))) ≫ eqToHom e := by
  rw [relativeUnit_app', relativeUnit_app']
  rfl

/-- The key cocycle identity, at the level of the adjunction transposes. -/
public theorem relativeUnit_key (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X) (M : X.Modules)
    (e : (pushforward (u ≫ v)).obj ((pullback ((u ≫ v) ≫ c)).obj M)
        = (pushforward v).obj ((pushforward u).obj ((pullback (u ≫ v ≫ c)).obj M))) :
    (pullbackPushforwardAdjunction v).homEquiv _ _
        ((pullbackComp v c).hom.app M ≫ (pullbackPushforwardAdjunction u).homEquiv _ _
          ((pullbackComp u (v ≫ c)).hom.app M))
      = (pullbackPushforwardAdjunction (u ≫ v)).homEquiv _ _
          ((pullbackComp (u ≫ v) c).hom.app M) ≫ eqToHom e := by
  rw [← Adjunction.homEquiv_naturality_left, pullbackComp_assoc_app u v c M rfl,
    ← comp_homEquiv_apply]
  exact homEquiv_pullbackComp u v ((pullback c).obj M) _ (fun _ => rfl)

/-- The cocycle identity for `relativeUnit`, componentwise. -/
public theorem relativeUnit_comp_app (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X) (M : X.Modules)
    (e : (pullback ((u ≫ v) ≫ c) ⋙ pushforward ((u ≫ v) ≫ c)).obj M
        = (pullback (u ≫ v ≫ c) ⋙ pushforward (u ≫ v ≫ c)).obj M) :
    (relativeUnit v c).app M ≫ (relativeUnit u (v ≫ c)).app M
      = (relativeUnit (u ≫ v) c).app M ≫ eqToHom e := by
  rw [relativeUnit_app_comp u v c M (pushforward_obj_triple u v c M),
    relativeUnit_key u v c M rfl, relativeUnit_app' (u ≫ v) c M]
  exact map_comp_eqToHom (pushforward c) _ _ _ _

/-- `relativeUnit` at the identity is the identity. -/
public theorem relativeUnit_id (Z : Scheme.{u}) (b : Z ⟶ X) :
    relativeUnit (𝟙 Z) b = 𝟙 (pullback b ⋙ pushforward b) := by
  refine NatTrans.ext (funext fun M => ?_)
  have key : (pullbackId Z).hom.app ((pullback b).obj M)
      = (pullbackComp (𝟙 Z) b).hom.app M :=
    NatTrans.congr_app ((Iso.inv_comp_eq _).mp (pseudofunctor_right_unitality (f := b))) M
  have step : (pullbackPushforwardAdjunction (𝟙 Z)).unit.app ((pullback b).obj M) ≫
        (pushforward (𝟙 Z)).map ((pullbackComp (𝟙 Z) b).hom.app M)
      = (pushforwardId Z).inv.app ((pullback b).obj M) :=
    (congrArg (fun t => (pullbackPushforwardAdjunction (𝟙 Z)).unit.app ((pullback b).obj M) ≫
      (pushforward (𝟙 Z)).map t) key).symm.trans (unit_id_app Z ((pullback b).obj M))
  exact (relativeUnit_app (𝟙 Z) b M).trans
    ((congrArg ((pushforward b).map) step).trans
      (CategoryTheory.Functor.map_id (pushforward b) ((pullback b).obj M)))

/-! ### The presheaf of monads -/

/-- The restriction map of the coefficient system attached to a morphism `u` of schemes
together with a factorisation `u ≫ b = a`. -/
public noncomputable def relativeUnit' (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X) (h : u ≫ b = a) :
    pullback b ⋙ pushforward b ⟶ pullback a ⋙ pushforward a :=
  relativeUnit u b ≫ eqToHom (congrArg (fun m : Y ⟶ X => pullback m ⋙ pushforward m) h)

/-- `relativeUnit'` at the identity is the identity. -/
public theorem relativeUnit'_id (Z : Scheme.{u}) (b : Z ⟶ X) (h : 𝟙 Z ≫ b = b) :
    relativeUnit' (𝟙 Z) b b h = 𝟙 (pullback b ⋙ pushforward b) :=
  relativeUnit_id Z b

/-- The cocycle identity for `relativeUnit'`: restriction along `v` then along `u` is restriction
along `u ≫ v`. -/
public theorem relativeUnit'_comp (u : W ⟶ Y) (v : Y ⟶ Z) (c : Z ⟶ X)
    (b : Y ⟶ X) (hb : v ≫ c = b) (a : W ⟶ X) (ha : u ≫ b = a) (ha' : (u ≫ v) ≫ c = a) :
    relativeUnit' v c b hb ≫ relativeUnit' u b a ha = relativeUnit' (u ≫ v) c a ha' := by
  subst hb
  subst ha
  exact NatTrans.ext (funext fun M => relativeUnit_comp_app u v c M rfl)

/-- The presheaf of monads on `Over X`: an object `A` with structure morphism `a` is sent to
`a_* a^*`, and a morphism is sent to the canonical restriction map. -/
public noncomputable def relativeMonad (X : Scheme.{u}) :
    (Over X)ᵒᵖ ⥤ (X.Modules ⥤ X.Modules) where
  obj A := pullback A.unop.hom ⋙ pushforward A.unop.hom
  map {A B} φ := relativeUnit' φ.unop.left A.unop.hom B.unop.hom (Over.w φ.unop)
  map_id _ := relativeUnit'_id _ _ _
  map_comp {A B C} φ ψ :=
    (relativeUnit'_comp ψ.unop.left φ.unop.left A.unop.hom B.unop.hom (Over.w φ.unop)
      C.unop.hom (Over.w ψ.unop) (Over.w (ψ.unop ≫ φ.unop))).symm

/-- The restriction maps of the presheaf of monads are the canonical ones. -/
public theorem relativeMonad_map (X : Scheme.{u}) {A B : Over X} (h : A ⟶ B) :
    (relativeMonad X).map h.op = relativeUnit' h.left B.hom A.hom (Over.w h) := rfl

/-! ### The coefficient presheaf of Tag 01XL -/

variable {S : Scheme.{u}}

/-- The coefficient presheaf of the relative Čech complex of Tag 01XL: the functor sending a
quasi-coherent `𝒪_X`-module `F` to the presheaf on `Over X` whose value at `A`, with structure
morphism `a`, is `(a ≫ f)_* a^* F`, with the canonical restriction maps. -/
@[stacks 01XL "the coefficient presheaf"]
public noncomputable def relativeCechPresheaf (f : X ⟶ S) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      ((Over X)ᵒᵖ ⥤ S.Modules) :=
  (relativeMonad X ⋙ (Functor.whiskeringRight _ _ _).obj (pushforward f) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))).flip

/-- The value of the coefficient presheaf is the direct image of the restriction. -/
public theorem relativeCechPresheaf_obj_obj (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (A : Over X) :
    ((relativeCechPresheaf f).obj F).obj (op A)
      = (pushforward (A.hom ≫ f)).obj ((pullback A.hom).obj F.obj) := rfl

/-- The coefficient presheaf is functorial in the quasi-coherent module, through the
pushforward of the restriction. -/
public theorem relativeCechPresheaf_map_app (f : X ⟶ S)
    {F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (A : Over X) :
    ((relativeCechPresheaf f).map φ).app (op A)
      = (pushforward (A.hom ≫ f)).map ((pullback A.hom).map φ.hom) := rfl

/-! ### The restriction maps of the coefficient presheaf

Tag 01XL names the restriction map of the coefficient presheaf explicitly, as the unit of
`u^* ⊣ u_*` followed by the four canonical comparison isomorphisms of a composite.  This
section writes that composite out and identifies it with `relativeUnit`. -/

/-- Mathlib's `pushforwardCongr` at a reflexivity proof is the identity. -/
public theorem pushforwardCongr_refl (u : Y ⟶ X) (M : Y.Modules) :
    (pushforwardCongr (rfl : u = u)).hom.app M = 𝟙 _ := by
  ext U
  simp

/-- Mathlib's `pullbackCongr` at a reflexivity proof is the identity. -/
public theorem pullbackCongr_refl (u : Y ⟶ X) (M : X.Modules) :
    (pullbackCongr (rfl : u = u)).hom.app M = 𝟙 _ := by
  simp [pullbackCongr]

/-- `pushforwardCongr` is a transport:  componentwise it is the `eqToHom` of the induced
equality of objects.  Stating the target equality as a hypothesis rather than deriving it keeps
the two sides of the conclusion at whatever spelling the caller needs. -/
public theorem pushforwardCongr_hom_app_eqToHom {u v : Y ⟶ X} (huv : u = v) (M : Y.Modules)
    (e : (pushforward u).obj M = (pushforward v).obj M) :
    (pushforwardCongr huv).hom.app M = eqToHom e := by
  subst huv
  rw [pushforwardCongr_refl, eqToHom_refl]

/-- `pullbackCongr` is a transport:  componentwise it is the `eqToHom` of the induced equality
of objects. -/
public theorem pullbackCongr_hom_app_eqToHom {u v : Y ⟶ X} (huv : u = v) (M : X.Modules)
    (e : (pullback u).obj M = (pullback v).obj M) :
    (pullbackCongr huv).hom.app M = eqToHom e := by
  subst huv
  rw [pullbackCongr_refl, eqToHom_refl]

/-- Tag 01XL's canonical restriction map, written out:  for `u : Y ⟶ Z`, `b : Z ⟶ X` and a
factorisation `u ≫ b = a`, the map `(b ≫ f)_* b^* F ⟶ (a ≫ f)_* a^* F` given by the unit of
`u^* ⊣ u_*` followed by the comparison isomorphisms `pushforwardComp`, `pullbackComp`,
`pullbackCongr` and `pushforwardCongr`.  At `(u, b, a, hh) = (h.left, B.hom, A.hom, Over.w h)`
for a morphism `h : A ⟶ B` of `Over X` this is the restriction map of the coefficient
presheaf. -/
public noncomputable def relativeCechRestriction (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X)
    (hh : u ≫ b = a) (f : X ⟶ S) (F : X.Modules) :
    (pushforward (b ≫ f)).obj ((pullback b).obj F) ⟶
      (pushforward (a ≫ f)).obj ((pullback a).obj F) :=
  (pushforward (b ≫ f)).map ((pullbackPushforwardAdjunction u).unit.app ((pullback b).obj F)) ≫
    (pushforwardComp u (b ≫ f)).hom.app _ ≫
    (pushforward (u ≫ (b ≫ f))).map ((pullbackComp u b).hom.app F) ≫
    (pushforward (u ≫ (b ≫ f))).map ((pullbackCongr hh).hom.app F) ≫
    (pushforwardCongr (by rw [← Category.assoc, hh])).hom.app _

/-- A functor's image of a transport followed by a transport is one transport.  Stated for
abstract objects, so that the kernel never compares two spellings of the same object. -/
private theorem map_eqToHom_comp_eqToHom {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B : C} {E : D} (e₁ : A = B) (e₂ : G.obj B = E) (hE : G.obj A = E) :
    G.map (eqToHom e₁) ≫ eqToHom e₂ = eqToHom hE := by
  subst e₁ e₂
  simp

/-- Two successive transports compose to one.  Every datum here is a variable, which is what
makes the conversion between the two spellings of the source object cheap. -/
public theorem relativeCechRestriction_tail_eqToHom (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X)
    (f : X ⟶ S) (F : X.Modules)
    (e₁ : (pullback (u ≫ b)).obj F = (pullback a).obj F)
    (e₂ : (pushforward (u ≫ b ≫ f)).obj ((pullback a).obj F)
        = (pushforward (a ≫ f)).obj ((pullback a).obj F))
    (hE : (pushforward (u ≫ b ≫ f)).obj ((pullback (u ≫ b)).obj F)
        = (pushforward (a ≫ f)).obj ((pullback a).obj F)) :
    (pushforward (u ≫ b ≫ f)).map (eqToHom e₁) ≫ eqToHom e₂ = eqToHom hE :=
  map_eqToHom_comp_eqToHom _ e₁ e₂ hE

/-- The last two factors of `relativeCechRestriction` are together a single transport. -/
public theorem relativeCechRestriction_tail (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X)
    (hh : u ≫ b = a) (f : X ⟶ S) (F : X.Modules) (hp : u ≫ b ≫ f = a ≫ f)
    (hE : (pushforward (u ≫ b ≫ f)).obj ((pullback (u ≫ b)).obj F)
        = (pushforward (a ≫ f)).obj ((pullback a).obj F)) :
    (pushforward (u ≫ b ≫ f)).map ((pullbackCongr hh).hom.app F) ≫
        (pushforwardCongr hp).hom.app ((pullback a).obj F)
      = eqToHom hE := by
  rw [pullbackCongr_hom_app_eqToHom hh F (congrArg (fun m : Y ⟶ X => (pullback m).obj F) hh),
    pushforwardCongr_hom_app_eqToHom hp ((pullback a).obj F)
      (congrArg (fun m : Y ⟶ S => (pushforward m).obj ((pullback a).obj F)) hp),
    relativeCechRestriction_tail_eqToHom u b a f F _ _ hE]

/-- The first three factors of `relativeCechRestriction` are `relativeUnit u b` pushed forward
along `f`.  This holds by `rfl`:  `pushforwardComp` is definitionally an identity, `𝟙 ≫ ·` and
composition of module sheaf morphisms are definitionally unital and associative, and pushforward
is strictly functorial.  The trailing `e` is carried along so that the statement can absorb the
transport without any re-association. -/
public theorem relativeCechRestriction_head (u : Y ⟶ Z) (b : Z ⟶ X) (f : X ⟶ S) (F : X.Modules)
    {T : S.Modules} (e : (pushforward (u ≫ b ≫ f)).obj ((pullback (u ≫ b)).obj F) ⟶ T) :
    (pushforward (b ≫ f)).map
          ((pullbackPushforwardAdjunction u).unit.app ((pullback b).obj F)) ≫
        ((pushforwardComp u (b ≫ f)).hom.app ((pullback u).obj ((pullback b).obj F)) ≫
          ((pushforward (u ≫ b ≫ f)).map ((pullbackComp u b).hom.app F) ≫ e))
      = (pushforward f).map ((relativeUnit u b).app F) ≫ e := rfl

/-- Tag 01XL's explicit restriction map is `relativeUnit u b` pushed forward along `f`,
followed by the transport along `u ≫ b = a`. -/
public theorem relativeCechRestriction_eq (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X) (hh : u ≫ b = a)
    (f : X ⟶ S) (F : X.Modules) (hp : u ≫ b ≫ f = a ≫ f)
    (hE : (pushforward (u ≫ b ≫ f)).obj ((pullback (u ≫ b)).obj F)
        = (pushforward (a ≫ f)).obj ((pullback a).obj F)) :
    relativeCechRestriction u b a hh f F
      = (pushforward f).map ((relativeUnit u b).app F) ≫ eqToHom hE :=
  (congrArg
      (fun t => (pushforward (b ≫ f)).map
            ((pullbackPushforwardAdjunction u).unit.app ((pullback b).obj F)) ≫
          ((pushforwardComp u (b ≫ f)).hom.app ((pullback u).obj ((pullback b).obj F)) ≫
            ((pushforward (u ≫ b ≫ f)).map ((pullbackComp u b).hom.app F) ≫ t)))
      (relativeCechRestriction_tail u b a hh f F hp hE)).trans
    (relativeCechRestriction_head u b f F (eqToHom hE))

/-! ### The coefficient presheaf is the canonical one

`relativeCechPresheaf` is a `Functor.flip`, so its restriction maps are the *components* of
the maps of the uncurried functor.  Naming the uncurried functor is what lets the `flip` layer
be discharged by `Functor.flip_obj_map` instead of by an unaffordable `rfl`. -/

/-- The uncurried form of the coefficient presheaf:  `relativeCechPresheaf f` is its flip. -/
public noncomputable def relativeCechPresheafUncurried (f : X ⟶ S) :
    (Over X)ᵒᵖ ⥤
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ S.Modules) :=
  relativeMonad X ⋙ (Functor.whiskeringRight _ _ _).obj (pushforward f) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))

/-- The coefficient presheaf is the flip of its uncurried form. -/
public theorem relativeCechPresheaf_eq_flip (f : X ⟶ S) :
    relativeCechPresheaf f = (relativeCechPresheafUncurried f).flip := rfl

/-- The restriction maps of the coefficient presheaf are the components of the maps of the
uncurried functor. -/
public theorem relativeCechPresheaf_obj_map_flip (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : Over X} (h : A ⟶ B) :
    ((relativeCechPresheaf f).obj F).map h.op
      = ((relativeCechPresheafUncurried f).map h.op).app F :=
  Functor.flip_obj_map (relativeCechPresheafUncurried f) F h.op

/-- Unwinding the two whiskerings of the uncurried functor. -/
public theorem relativeCechPresheafUncurried_map_app (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : Over X} (h : A ⟶ B) :
    ((relativeCechPresheafUncurried f).map h.op).app F
      = (pushforward f).map (((relativeMonad X).map h.op).app F.obj) := rfl

/-- The restriction map of the coefficient presheaf is the canonical restriction map of the
presheaf of monads, pushed forward along `f`. -/
public theorem relativeCechPresheaf_obj_map (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : Over X} (h : A ⟶ B) :
    ((relativeCechPresheaf f).obj F).map h.op
      = (pushforward f).map ((relativeUnit' h.left B.hom A.hom (Over.w h)).app F.obj) :=
  (relativeCechPresheaf_obj_map_flip f F h).trans
    ((relativeCechPresheafUncurried_map_app f F h).trans
      (congrArg (fun t => (pushforward f).map (NatTrans.app t F.obj)) (relativeMonad_map X h)))

/-- The value of the coefficient presheaf at `A` *is* `(a ≫ f)_* a^* F`:  the comparison
isomorphism of Tag 01XL is the identity. -/
public noncomputable def relativeCechPresheafObjIso (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (A : Over X) :
    ((relativeCechPresheaf f).obj F).obj (op A) ≅
      (pushforward (A.hom ≫ f)).obj ((pullback A.hom).obj F.obj) :=
  Iso.refl _

/-- Conjugating by `relativeCechPresheafObjIso` changes nothing, since that isomorphism is the
identity. -/
public theorem relativeCechPresheafObjIso_conj (f : X ⟶ S)
    (F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (A B : Over X)
    (m : ((relativeCechPresheaf f).obj F).obj (op B)
      ⟶ ((relativeCechPresheaf f).obj G).obj (op A)) :
    (relativeCechPresheafObjIso f F B).inv ≫ m ≫ (relativeCechPresheafObjIso f G A).hom
      = m := rfl

/-- Tag 01XL's assertion that the maps of the coefficient presheaf are the canonical
restriction maps, read through `relativeCechPresheafObjIso`. -/
public theorem relativeCechPresheaf_map (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : Over X} (h : A ⟶ B) :
    (relativeCechPresheafObjIso f F B).inv ≫ ((relativeCechPresheaf f).obj F).map h.op ≫
        (relativeCechPresheafObjIso f F A).hom
      = (pushforward f).map ((relativeUnit' h.left B.hom A.hom (Over.w h)).app F.obj) :=
  (relativeCechPresheafObjIso_conj f F F A B _).trans
    (relativeCechPresheaf_obj_map f F h)

/-- Tag 01XL's naturality assertion, read through `relativeCechPresheafObjIso`. -/
public theorem relativeCechPresheaf_map_app_iso (f : X ⟶ S)
    {F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (A : Over X) :
    (relativeCechPresheafObjIso f F A).inv ≫ ((relativeCechPresheaf f).map φ).app (op A) ≫
        (relativeCechPresheafObjIso f G A).hom
      = (pushforward (A.hom ≫ f)).map ((pullback A.hom).map φ.hom) :=
  (relativeCechPresheafObjIso_conj f F G A A _).trans
    (relativeCechPresheaf_map_app f φ A)

end Stacks.AlgebraicGeometry.RelativeCech
