module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThree

/-! # Every descent pair is locally the descent pair of an object

We prove, for the third stage of the construction of the stackification of a fibred category,
clause (2) of Stacks 02ZN: every object of the third stage is, locally on the base, in the
essential image of the 1-morphism from the fibred category.

The content is the *contraction* of a descent datum onto one of its objects. Let `D` be a descent
datum relative to a sieve `R` on `U` and let `f : V ⟶ U` be an arrow of `R`. For every arrow
`g : W ⟶ V` with `g ≫ f` in `R`, the gluing isomorphism of `D` at the pair of arrows `(f, g ≫ f)`
and the pair of morphisms `(g, 𝟙)`, followed by the contraction of the chosen pullback along an
identity, is an isomorphism `g^* (D.obj f) ≅ D.obj (g ≫ f)`
(`CategoryTheory.Functor.SieveDescentDatum.contract`). These isomorphisms are compatible with the
gluing isomorphisms of `D` — that is the cocycle condition of `D`, read at the triple of arrows
`(f, g ≫ f, g' ≫ f)`, and it is `CategoryTheory.Functor.SieveDescentDatum.contract_glue`. They
therefore assemble into an isomorphism of descent pairs between the pullback of `(R, D)` along `f`
and the pair of the object `D.obj f`, over the identity of `V`.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberCongr`, the comparison of the chosen pullbacks along two
  equal morphisms of the base;
* `CategoryTheory.Functor.SieveDescentDatum.contract`, the contraction of a descent datum onto one
  of its objects;
* `CategoryTheory.Functor.DescentPair.ofFiber`, the descent pair of an object of a fibre, with the
  object of the base recorded literally;
* `CategoryTheory.Functor.DescentPair.contractIso`, the isomorphism above.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.contract_glue` and
  `CategoryTheory.Functor.SieveDescentDatum.contract_glue_inv`, the compatibility of the
  contractions with the gluing isomorphisms;
* `CategoryTheory.Functor.exists_isHomLift_id_iso_toDescentPair_obj` and
  `CategoryTheory.Functor.exists_isHomLift_id_iso_toStageThree_obj`, clause (2) of Stacks 02ZN for
  the third stage and for the composite of the three stages;
* `CategoryTheory.Functor.essImage_pullbackFiber_toStageThree`, the same clause in the
  essential-image spelling that Stacks 02ZN, 02ZP, 06NS and 04Y2 use.
-/


@[expose] public section

universe vb

set_option backward.isDefEq.respectTransparency false

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

section Congr

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered]

/-- The chosen pullbacks along two equal morphisms of the base are canonically isomorphic. -/
noncomputable def pullbackFiberCongr {V U : 𝒮} (x : p.Fiber U) {f f' : V ⟶ U} (h : f = f') :
    pullbackFiber p x f ≅ pullbackFiber p x f' :=
  fiberIsoOfCartesian f' (IsPreFibered.pullbackMap x.2 f) (IsPreFibered.pullbackMap x.2 f')
    (h ▸ IsPreFibered.pullbackMap.IsCartesian x.2 f)
    (IsPreFibered.pullbackMap.IsCartesian x.2 f')

/-- The comparison `pullbackFiberCongr x h` followed by the chosen pullback map along `f'` is the
chosen pullback map along `f`. -/
@[reassoc (attr := simp)]
theorem pullbackFiberCongr_hom_fac {V U : 𝒮} (x : p.Fiber U) {f f' : V ⟶ U} (h : f = f') :
    Fiber.fiberInclusion.map (pullbackFiberCongr x h).hom ≫ IsPreFibered.pullbackMap x.2 f' =
      IsPreFibered.pullbackMap x.2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse of `pullbackFiberCongr x h` followed by the chosen pullback map along `f` is the
chosen pullback map along `f'`. -/
@[reassoc (attr := simp)]
theorem pullbackFiberCongr_inv_fac {V U : 𝒮} (x : p.Fiber U) {f f' : V ⟶ U} (h : f = f') :
    Fiber.fiberInclusion.map (pullbackFiberCongr x h).inv ≫ IsPreFibered.pullbackMap x.2 f =
      IsPreFibered.pullbackMap x.2 f' :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- The comparison of the chosen pullback along `f` with itself is the identity. -/
@[simp]
theorem pullbackFiberCongr_refl {V U : 𝒮} (x : p.Fiber U) {f : V ⟶ U} (h : f = f) :
    (pullbackFiberCongr x h).hom = 𝟙 _ :=
  fiberIsoOfCartesian_self _ _ _

/-- The inverse of the comparison of the chosen pullback along `f` with itself is the identity. -/
@[simp]
theorem pullbackFiberCongr_refl_inv {V U : 𝒮} (x : p.Fiber U) {f : V ⟶ U} (h : f = f) :
    (pullbackFiberCongr x h).inv = 𝟙 _ := by
  simpa [pullbackFiberCongr_refl x h] using (pullbackFiberCongr x h).inv_hom_id

/-- The comparison of the chosen pullbacks along equal morphisms `f = f'` is the morphism `eqToHom`
of the equality of the two chosen pullbacks. -/
theorem pullbackFiberCongr_hom_eq_eqToHom {V U : 𝒮} (x : p.Fiber U) {f f' : V ⟶ U} (h : f = f') :
    (pullbackFiberCongr x h).hom =
      eqToHom (show pullbackFiber p x f = pullbackFiber p x f' by rw [h]) := by
  subst h; simp

/-- The comparison of two chosen pullbacks of a chosen pullback is the comparison of the two
chosen pullbacks along the composites. -/
@[stacks 026D "`can_ij = (α_{pr₁, f_j})_X ∘ (α_{pr₀, f_i})_X⁻¹`, where `can` is the gluing
  isomorphism `pullbackFiberComparison` of the canonical descent datum of Stacks 026E (2); stated
  as the commuting square, with `α⁻¹` the contraction `pullbackFiberCompIso` of Stacks 02XO and
  `f_i ∘ pr₀ = f_j ∘ pr₁` carried by `pullbackFiberCongr`"]
theorem pullbackFiberComparison_comp_compIso {T : 𝒮} (y : p.Fiber T) {V W Z : 𝒮} {g : V ⟶ T}
    {g' : W ⟶ T} (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ g = ε' ≫ g') :
    (pullbackFiberComparison y ε ε' heq).hom ≫ (pullbackFiberCompIso y g' ε').hom =
      (pullbackFiberCompIso y g ε).hom ≫ (pullbackFiberCongr y heq).hom := by
  refine fiber_hom_ext_of_cartesian (ε' ≫ g') (IsPreFibered.pullbackMap y.2 (ε' ≫ g'))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp

/-- Contracting the chosen pullback along an identity, after the comparison of a twofold chosen
pullback with the chosen pullback along the composite. -/
theorem pullbackFiberCompIso_inv_comp_idIso {T Z : 𝒮} (u : p.Fiber T) (ε : Z ⟶ T) :
    (pullbackFiberCompIso u (𝟙 T) ε).inv ≫ pullbackFiberHom (pullbackFiberIdIso u).hom ε =
      (pullbackFiberCongr u (comp_id ε)).hom := by
  refine fiber_hom_ext_of_cartesian ε (IsPreFibered.pullbackMap u.2 ε)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp

end Congr

/-! ### Contracting a descent datum onto one of its objects -/

namespace SieveDescentDatum

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} {R : Sieve U}

/-- The chosen pullback, along `ε`, of the object a descent datum attaches to an arrow `a` of its
sieve, compared with the object it attaches to an arrow `b` that the composite `ε ≫ a` equals.
This is the gluing isomorphism of `a` and `b` at the pair `(ε, 𝟙)`, followed by the contraction of
the chosen pullback along the identity. -/
noncomputable def contract (D : SieveDescentDatum p R) {V Z : 𝒮} {a : V ⟶ U} (ha : R a)
    (ε : Z ⟶ V) {b : Z ⟶ U} (hb : R b) (h : ε ≫ a = b) :
    pullbackFiber p (D.obj a ha) ε ≅ D.obj b hb :=
  D.iso ha hb ε (𝟙 Z) (by rw [h, Category.id_comp]) ≪≫ pullbackFiberIdIso _

/-- The gluing isomorphism of a descent datum does not depend on which of two equal morphisms its
first index is read as. -/
theorem iso_congr_src (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f)
    {g : W ⟶ U} (hg : R g) {ε ε₀ : Z ⟶ V} (he : ε = ε₀) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) (heq₀ : ε₀ ≫ f = ε' ≫ g) :
    (pullbackFiberCongr (D.obj f hf) he).hom ≫ (D.iso hf hg ε₀ ε' heq₀).hom =
      (D.iso hf hg ε ε' heq).hom := by
  subst he; simp

/-- The gluing isomorphism of a descent datum does not depend on which of two equal morphisms its
second index is read as. -/
theorem iso_congr_tgt (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f)
    {g : W ⟶ U} (hg : R g) (ε : Z ⟶ V) {ε' ε₀ : Z ⟶ W} (he : ε' = ε₀)
    (heq : ε ≫ f = ε' ≫ g) (heq₀ : ε ≫ f = ε₀ ≫ g) :
    (D.iso hf hg ε ε' heq).hom ≫ (pullbackFiberCongr (D.obj g hg) he).hom =
      (D.iso hf hg ε ε₀ heq₀).hom := by
  subst he; simp

/-- The contraction does not depend on which of two equal morphisms it is taken along. -/
theorem contract_congr (D : SieveDescentDatum p R) {V Z : 𝒮} {a : V ⟶ U} (ha : R a)
    {ε ε₀ : Z ⟶ V} (he : ε = ε₀) {b : Z ⟶ U} (hb : R b) (h : ε ≫ a = b) (h₀ : ε₀ ≫ a = b) :
    (D.contract ha ε hb h).hom =
      (pullbackFiberCongr (D.obj a ha) he).hom ≫ (D.contract ha ε₀ hb h₀).hom := by
  subst he; simp

/-- **The base change of a contraction.** Base changing the contraction of a descent datum onto one
of its objects along `ε` is the comparison of the two chosen pullbacks, followed by the gluing
isomorphism read at `(ε ≫ g, ε)`. -/
theorem pullbackFiberHom_contract (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f)
    (g : W ⟶ V) {a : W ⟶ U} (ha : R a) (hga : g ≫ f = a) (ε : Z ⟶ W) :
    pullbackFiberHom (D.contract hf g ha hga).hom ε =
      (pullbackFiberCompIso (D.obj f hf) g ε).hom ≫
        (D.iso hf ha (ε ≫ g) ε (by rw [assoc, hga])).hom := by
  have hip := D.iso_pullback hf ha g (𝟙 W) (by rw [hga, Category.id_comp]) ε
  have hip2 : (pullbackFiberCompIso (D.obj f hf) g ε).inv ≫
      pullbackFiberHom (D.iso hf ha g (𝟙 W) (by rw [hga, Category.id_comp])).hom ε =
      (D.iso hf ha (ε ≫ g) (ε ≫ 𝟙 W)
          (by rw [assoc, hga, assoc, Category.id_comp])).hom ≫
        (pullbackFiberCompIso (D.obj a ha) (𝟙 W) ε).inv := by
    rw [← hip]; simp
  rw [contract, Iso.trans_hom, pullbackFiberHom_comp, ← Iso.inv_comp_eq, ← Category.assoc, hip2,
    Category.assoc, pullbackFiberCompIso_inv_comp_idIso,
    iso_congr_tgt D hf ha (ε ≫ g) (comp_id ε)]

/-- **The contractions of a descent datum onto its objects are compatible with its gluing
isomorphisms.** This is the cocycle condition of the datum, read at the triple of arrows
`(f, g ≫ f, g' ≫ f)`. -/
theorem contract_glue (D : SieveDescentDatum p R) {V W W' Z : 𝒮} {f : V ⟶ U} (hf : R f)
    (g : W ⟶ V) {a : W ⟶ U} (ha : R a) (hga : g ≫ f = a)
    (g' : W' ⟶ V) {a' : W' ⟶ U} (ha' : R a') (hga' : g' ≫ f = a')
    (ε : Z ⟶ W) (ε' : Z ⟶ W') (heq : ε ≫ g = ε' ≫ g') (h₂ : ε ≫ a = ε' ≫ a') :
    pullbackFiberHom (D.contract hf g ha hga).hom ε ≫ (D.iso ha ha' ε ε' h₂).hom =
      (pullbackFiberComparison (D.obj f hf) ε ε' heq).hom ≫
        pullbackFiberHom (D.contract hf g' ha' hga').hom ε' := by
  rw [pullbackFiberHom_contract, pullbackFiberHom_contract, Category.assoc,
    D.cocycle hf ha ha' (ε ≫ g) ε ε' (by rw [assoc, hga]) h₂ (by rw [assoc, hga, h₂]),
    ← Category.assoc (pullbackFiberComparison (D.obj f hf) ε ε' heq).hom,
    pullbackFiberComparison_comp_compIso,
    Category.assoc (pullbackFiberCompIso (D.obj f hf) g ε).hom,
    iso_congr_src D hf ha' heq ε']

/-- The inverse form of `CategoryTheory.Functor.SieveDescentDatum.contract_glue`. -/
theorem contract_glue_inv (D : SieveDescentDatum p R) {V W W' Z : 𝒮} {f : V ⟶ U} (hf : R f)
    (g : W ⟶ V) {a : W ⟶ U} (ha : R a) (hga : g ≫ f = a)
    (g' : W' ⟶ V) {a' : W' ⟶ U} (ha' : R a') (hga' : g' ≫ f = a')
    (ε : Z ⟶ W) (ε' : Z ⟶ W') (heq : ε ≫ g = ε' ≫ g') (h₂ : ε ≫ a = ε' ≫ a') :
    pullbackFiberHom (D.contract hf g ha hga).inv ε ≫
        (pullbackFiberComparison (D.obj f hf) ε ε' heq).hom =
      (D.iso ha ha' ε ε' h₂).hom ≫ pullbackFiberHom (D.contract hf g' ha' hga').inv ε' := by
  have h := D.contract_glue hf g ha hga g' ha' hga' ε ε' heq h₂
  rw [← pullbackFiberIso_hom (D.contract hf g ha hga) ε,
    ← pullbackFiberIso_hom (D.contract hf g' ha' hga') ε'] at h
  rw [← pullbackFiberIso_inv (D.contract hf g ha hga) ε,
    ← pullbackFiberIso_inv (D.contract hf g' ha' hga') ε', Iso.inv_comp_eq,
    ← Category.assoc (pullbackFiberIso (D.contract hf g ha hga) ε).hom, h,
    Category.assoc (pullbackFiberComparison (D.obj f hf) ε ε' heq).hom, Iso.hom_inv_id,
    Category.comp_id]

end SieveDescentDatum

/-! ### Every descent pair is locally in the image of the 1-morphism

This is clause (2) of Stacks 02ZN for the third stage: the restriction of a pair `A` to an arrow
`f` of its covering sieve is isomorphic, over the identity of the base, to the pair of the object
`A.datum.obj f`. -/

section LocalEssSurj

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-- The descent pair of an object of the fibre over `V`: the maximal sieve on `V`, with the descent
datum formed by the chosen pullbacks of the object. Unlike
`CategoryTheory.Functor.DescentPair.ofObj` this records the object of the base as the literal
`V`. -/
@[reducible]
noncomputable def DescentPair.ofFiber {V : 𝒮} (x : p.Fiber V) (J : GrothendieckTopology 𝒮) :
    DescentPair p J where
  pt := V
  sieve := ⊤
  sieve_mem := J.top_mem V
  datum := SieveDescentDatum.ofFiber x ⊤

/-- The descent pair of an object of a fibre is the descent pair of the underlying object of
`𝒳`. -/
theorem DescentPair.ofFiber_eq_ofObj {V : 𝒮} (x : p.Fiber V) (J : GrothendieckTopology 𝒮) :
    DescentPair.ofFiber x J = DescentPair.ofObj p J x.1 := by
  obtain ⟨x₀, rfl⟩ := x
  rfl

/-- The morphism datum, over the identity of `V`, from the descent pair of the object that `A`
attaches to an arrow `f : V ⟶ A.pt` of its covering sieve, to the pullback of `A` along `f`. On an
arrow `g` of the pullback sieve it is the contraction of the datum of `A` onto the object attached
to `g ≫ f`. -/
noncomputable def DescentPairData.ofContract (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    DescentPairData (DescentPair.ofFiber (A.datum.obj f hf) J) (A.pullback f) where
  base := 𝟙 V
  hom :=
    { sieve := A.sieve.pullback f
      sieve_mem := J.pullback_stable _ A.sieve_mem
      le_dom := le_top
      mem_cod := fun _ _ hg ↦ by rwa [comp_id]
      map := fun _ g _ k hk h ↦
        (A.datum.contract hf g (b := k ≫ f) hk (by rw [← h, comp_id])).hom
      map_glue := fun _ _ _ g _ g' _ _ hk h _ hk' h' ε ε' heq ↦ by
        obtain rfl := (comp_id g).symm.trans h
        obtain rfl := (comp_id g').symm.trans h'
        exact A.datum.contract_glue hf g (a := g ≫ f) hk rfl g' (a' := g' ≫ f) hk' rfl ε ε' heq
          (by rw [← assoc, ← assoc, heq]) }

/-- The morphism datum `DescentPairData.ofContract A f hf` lies over the identity of `V`. -/
@[simp]
theorem DescentPairData.ofContract_base (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) : (DescentPairData.ofContract A f hf).base = 𝟙 V := rfl

/-- On an arrow `g` of the pullback sieve, `DescentPairData.ofContract A f hf` is the contraction
of the datum of `A` onto the object attached to `k ≫ f`. -/
theorem DescentPairData.ofContract_hom_map (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) {W : 𝒮} (g : W ⟶ V) (hg : (A.sieve.pullback f).arrows g)
    {k : W ⟶ V} (hk : (A.sieve.pullback f).arrows k) (h : g ≫ 𝟙 V = k) :
    (DescentPairData.ofContract A f hf).hom.map g hg hk h =
      (A.datum.contract hf g (b := k ≫ f) hk (by rw [← h, comp_id])).hom := rfl

/-- The morphism datum, over the identity of `V`, from the pullback of `A` along an arrow `f` of
its covering sieve to the descent pair of the object `A` attaches to `f`: the inverse of
`CategoryTheory.Functor.DescentPairData.ofContract`. -/
noncomputable def DescentPairData.toContract (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    DescentPairData (A.pullback f) (DescentPair.ofFiber (A.datum.obj f hf) J) where
  base := 𝟙 V
  hom :=
    { sieve := A.sieve.pullback f
      sieve_mem := J.pullback_stable _ A.sieve_mem
      le_dom := le_refl _
      mem_cod := fun _ _ _ ↦ trivial
      map := fun _ g hg _ _ h ↦ (A.datum.contract hf g (b := g ≫ f) hg rfl).inv ≫
        (pullbackFiberCongr (A.datum.obj f hf) ((comp_id g).symm.trans h)).hom
      map_glue := fun _ _ _ g hg g' hg' _ _ h _ _ h' ε ε' heq ↦ by
        obtain rfl := (comp_id g).symm.trans h
        obtain rfl := (comp_id g').symm.trans h'
        simp only [pullbackFiberCongr_refl, Category.comp_id]
        exact A.datum.contract_glue_inv hf g (a := g ≫ f) hg rfl g' (a' := g' ≫ f) hg' rfl
          ε ε' heq (by rw [← assoc, ← assoc, heq]) }

/-- The morphism datum `DescentPairData.toContract A f hf` lies over the identity of `V`. -/
@[simp]
theorem DescentPairData.toContract_base (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) : (DescentPairData.toContract A f hf).base = 𝟙 V := rfl

/-- On an arrow `g` of the pullback sieve, `DescentPairData.toContract A f hf` is the inverse of
the contraction of the datum of `A` onto the object attached to `g ≫ f`, followed by the comparison
of the chosen pullbacks along `g` and `k`. -/
theorem DescentPairData.toContract_hom_map (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) {W : 𝒮} (g : W ⟶ V) (hg : (A.sieve.pullback f).arrows g)
    {k : W ⟶ V} (hk : (⊤ : Sieve V).arrows k) (h : g ≫ 𝟙 V = k) :
    (DescentPairData.toContract A f hf).hom.map g hg hk h =
      (A.datum.contract hf g (b := g ≫ f) hg rfl).inv ≫
        (pullbackFiberCongr (A.datum.obj f hf) ((comp_id g).symm.trans h)).hom := rfl

/-- **Every descent pair is locally the descent pair of an object.** The pullback of `A` along an
arrow `f : V ⟶ A.pt` of its covering sieve is isomorphic, by an isomorphism over the identity of
`V`, to the descent pair of the object `A.datum.obj f`. -/
noncomputable def DescentPair.contractIso (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) : DescentPair.ofFiber (A.datum.obj f hf) J ≅ A.pullback f where
  hom := DescentMor.mk (DescentPairData.ofContract A f hf)
  inv := DescentMor.mk (DescentPairData.toContract A f hf)
  hom_inv_id := by
    refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (by simp) ?_)
    intro W g hg hg' k hk h h'
    obtain rfl := (comp_id g).symm.trans h'
    refine Eq.trans (DescentPairData.comp_hom_map (DescentPairData.ofContract A f hf)
      (DescentPairData.toContract A f hf) g hg.1 hg.2 hk (by simp) hg h) ?_
    simp only [DescentPairData.ofContract, DescentPairData.toContract, DescentPairData.id,
      DescentPairHom.id]
    rw [A.datum.contract_congr hf (comp_id g).symm (b := (g ≫ 𝟙 V) ≫ f) hg.2
        (by rw [comp_id]) rfl]
    simp [Category.assoc, Iso.hom_inv_id_assoc, pullbackFiberCongr_hom_eq_eqToHom,
      eqToHom_trans]
  inv_hom_id := by
    refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (by simp) ?_)
    intro W g hg hg' k hk h h'
    obtain rfl := (comp_id g).symm.trans h'
    refine Eq.trans (DescentPairData.comp_hom_map (DescentPairData.toContract A f hf)
      (DescentPairData.ofContract A f hf) g hg.1 hg.2 hk (by simp) hg h) ?_
    simp only [DescentPairData.ofContract, DescentPairData.toContract, DescentPairData.id,
      DescentPairHom.id, Category.assoc]
    rw [← A.datum.contract_congr hf (comp_id g).symm (b := g ≫ f) hg.1 rfl (by rw [comp_id]),
      Iso.inv_hom_id]
    simp [eqToHom_refl]

/-- The forward morphism of `DescentPair.contractIso A f hf` is the class of
`DescentPairData.ofContract A f hf`. -/
@[simp]
theorem DescentPair.contractIso_hom (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    (A.contractIso f hf).hom = DescentMor.mk (DescentPairData.ofContract A f hf) := rfl

/-- The isomorphism of `CategoryTheory.Functor.DescentPair.contractIso` lies over the identity. -/
theorem isHomLift_contractIso_hom (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    (p.descentPairProj J).IsHomLift (𝟙 V) (A.contractIso f hf).hom :=
  have h : (p.descentPairProj J).IsHomLift (DescentPairData.ofContract A f hf).base
      (DescentMor.mk (DescentPairData.ofContract A f hf) :
        DescentPair.ofFiber (A.datum.obj f hf) J ⟶ A.pullback f) :=
    DescentMor.isHomLift_mk _
  h

/-- **Clause (2) of Stacks 02ZN for the third stage.** The pullback of a descent pair `A` along any
arrow `f : V ⟶ A.pt` of its covering sieve is isomorphic, by an isomorphism over the identity of
`V`, to the image under `CategoryTheory.Functor.toDescentPair` of an object of `𝒳`; and the
covering sieve of `A` is a covering sieve. -/
theorem exists_isHomLift_id_iso_toDescentPair_obj (A : DescentPair p J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    ∃ (x : 𝒳) (e : (toDescentPair p J).obj x ≅ A.pullback f),
      (p.descentPairProj J).IsHomLift (𝟙 V) e.hom := by
  refine ⟨(A.datum.obj f hf).1, ?_⟩
  have h : (toDescentPair p J).obj (A.datum.obj f hf).1 =
      DescentPair.ofFiber (A.datum.obj f hf) J :=
    (DescentPair.ofFiber_eq_ofObj (A.datum.obj f hf) J).symm
  rw [h]
  exact ⟨A.contractIso f hf, isHomLift_contractIso_hom A f hf⟩

end LocalEssSurj

/-! ### Clause (2) of Stacks 02ZN for the composite of the three stages -/

section StageThreeEssSurj

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮)

/-- **Clause (2) of Stacks 02ZN for the composite of the three stages.** Every object `A` of the
third stage carries a covering sieve — its own — along each arrow of which its pullback is
isomorphic, over the identity of the base, to the image under
`CategoryTheory.Functor.toStageThree` of an object of `𝒳`. -/
theorem exists_isHomLift_id_iso_toStageThree_obj (A : p.StageThree J) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : A.sieve.arrows f) :
    ∃ (x : 𝒳) (e : (p.toStageThree J).obj x ≅ A.pullback f),
      (p.stageThreeProj J).IsHomLift (𝟙 V) e.hom := by
  obtain ⟨x, e, he⟩ := exists_isHomLift_id_iso_toDescentPair_obj A f hf
  exact ⟨x.as.as, e, he⟩

/-- The covering sieve along which
`CategoryTheory.Functor.exists_isHomLift_id_iso_toStageThree_obj` exhibits a pair as locally in
the image is a covering sieve. -/
theorem stageThree_sieve_mem (A : p.StageThree J) : A.sieve ∈ J ((p.stageThreeProj J).obj A) :=
  A.sieve_mem

end StageThreeEssSurj

/-! ### Clause (2) of Stacks 02ZN in its essential-image form

The comparison API uses one hom universe for the source and target of the
stackification, independently of the base hom universe `vb`. The source hom universe
`max t₁ t₂ w vb` absorbs the universe of the descent data, so the three stages and the
morphism-presheaf maps use the same universe. In particular, the base may have its
objects in a larger universe than its morphisms. No change of base site is needed. -/

section EssImage

universe w t₁ t₂

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞)

/-- **Clause (2) of Stacks 02ZN for the composite of the three stages**, in the essential-image
form: for every object `U` of the base and every object `x'` of the fibre of the third stage over
`U` there is a covering sieve of `U` such that for each of its arrows `f : V ⟶ U` the chosen
pullback `x'|_V` lies in the essential image of the functor `𝒴_V ⥤ (𝒴')_V` induced by
`CategoryTheory.Functor.toStageThree`. -/
theorem essImage_pullbackFiber_toStageThree (U : 𝒞) (x' : (q.stageThreeProj J).Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (isFibredOneMorphism_toStageThree q J).comp_eq V).essImage
        (pullbackFiber (q.stageThreeProj J) x' f) := by
  obtain ⟨A, rfl⟩ := x'
  refine ⟨A.sieve, A.sieve_mem, fun V f hf ↦ ?_⟩
  obtain ⟨x, e, he⟩ := exists_isHomLift_id_iso_toStageThree_obj q J A f hf
  have hlift := he
  have hx : q.obj x = V := by
    have h0 := IsHomLift.domain_eq (q.stageThreeProj J) (𝟙 V) e.hom
    rwa [← Functor.comp_obj, toStageThree_comp_stageThreeProj] at h0
  have hcart : (q.stageThreeProj J).IsCartesian f
      (DescentMor.mk (DescentPairData.pullbackHom A f) : A.pullback f ⟶ A) :=
    have := isStronglyCartesian_pullbackHom A f
    inferInstance
  have hV : (q.stageThreeProj J).obj (A.pullback f) = V := rfl
  have hA : (q.stageThreeProj J).obj A = A.pt := rfl
  have hfib : ((fiberFunctorOfCompEq (isFibredOneMorphism_toStageThree q J).comp_eq V).obj
        (Fiber.mk hx)) ≅ (Fiber.mk hV) := Fiber.isoMk e he
  have hcmp : (Fiber.mk hV : (q.stageThreeProj J).Fiber V) ≅
      pullbackFiber (q.stageThreeProj J) (Fiber.mk hA) f :=
    (fiberIsoOfCartesian f (IsPreFibered.pullbackMap (Fiber.mk hA).2 f)
      (DescentMor.mk (DescentPairData.pullbackHom A f))
      (IsPreFibered.pullbackMap.IsCartesian _ _) hcart).symm
  exact ⟨Fiber.mk hx, ⟨hfib ≪≫ hcmp⟩⟩

end EssImage

end CategoryTheory.Functor
