module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwo

/-! # Adjoining the objects that descent data prescribe

This is the third and last stage of the construction of the stackification of a fibred category.
The first two stages arranged that the presheaves of morphisms are sheaves; what is missing is that
descent data are effective, and this stage adjoins, for every covering sieve `R` of an object `U`
of the base and every descent datum `D` relative to `R`, an object whose restrictions are the
objects of `D`, glued by the gluing isomorphisms of `D`.

The objects of the new category are therefore the pairs `(R, D)`, and a morphism from `(R, D)` over
`U` to `(R', D')` over `U'` consists of a morphism `u : U ⟶ U'` of the base together with a
morphism of descent data from `D` to the pullback of `D'` along `u`, defined only on a covering
sieve refining `R` — two such data being identified when they agree on a common covering sieve, as
in the second stage. Since a descent datum indexes its objects by the *arrows* of its sieve, the
pullback of a descent datum along `u` is indexed by the arrows `f` with `f ≫ u` in the sieve, and
the coherence `(f ≫ u) ≫ u' = f ≫ (u ≫ u')` is not an identity of arrows; the two comparison
lemmas `CategoryTheory.Functor.DescentPairHom.map_source_congr` and
`CategoryTheory.Functor.DescentPairHom.map_target_congr` are what absorbs it, and they are the only
place in this file where `eqToHom` occurs.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.restrict` and
  `CategoryTheory.Functor.SieveDescentDatum.pullback`: a descent datum restricted to a smaller
  sieve, and pulled back along a morphism of the base.
* `CategoryTheory.Functor.DescentPair`: a covering sieve of an object of the base together with a
  descent datum relative to it. These are the objects of the third stage.
* `CategoryTheory.Functor.DescentPairHom`: a morphism of such pairs lying over a given morphism of
  the base, before the identification of data agreeing on a covering sieve;
  `CategoryTheory.Functor.DescentPairData` bundles it with that morphism of the base, and
  `CategoryTheory.Functor.DescentMor` is the quotient by agreement on a covering sieve. These are
  the morphisms of the third stage.
* `CategoryTheory.Functor.descentPairProj`: the structure functor to `𝒮`.
* `CategoryTheory.Functor.DescentPair.pullback`: the pullback of a pair along a morphism of the
  base, which is the chosen cartesian lift.
* `CategoryTheory.Functor.toDescentPair`: the 1-morphism from `𝒳`, sending an object to the descent
  datum formed by its chosen pullbacks along the maximal sieve.
* `CategoryTheory.Functor.StageThree`, `CategoryTheory.Functor.stageThreeProj` and
  `CategoryTheory.Functor.toStageThree`: the above applied to the second stage, and the composite
  of all three stages.

## Main results

* the `Category` instance on `CategoryTheory.Functor.DescentPair`: identities, composition and the
  category axioms for the pairs and their morphisms.
* `CategoryTheory.Functor.isStronglyCartesian_pullbackHom` and
  `CategoryTheory.Functor.isFibered_descentPairProj`: the canonical morphism from the pullback of a
  pair is strongly cartesian, so the structure functor is fibred.
* `CategoryTheory.Functor.DescentPair.restrictIso`: a pair and its restriction to a smaller
  covering sieve are isomorphic, by an isomorphism over the identity of the base
  (`CategoryTheory.Functor.isHomLift_restrictIso_hom`). This is the sense in which two pairs are
  *identified*: no quotient is taken on the objects, and two pairs agreeing on a common covering
  refinement are isomorphic over the identity.
* `CategoryTheory.Functor.toDescentPair_comp_descentPairProj`: the 1-morphism from `𝒳` is
  *strictly* over `𝒮`.
* `CategoryTheory.Functor.isStronglyCartesian_toDescentPair_map`: it preserves strongly cartesian
  morphisms, and `CategoryTheory.Functor.isFibredOneMorphism_toDescentPair` packages the two
  statements as the assertion that it is a 1-morphism of fibred categories over `𝒮`.

## Obligations that remain before Stacks 02ZN

The following are **not** proved here, and no declaration here should be read as claiming them.

1. That the morphism presheaves of `CategoryTheory.Functor.DescentPair` are sheaves. This is
   *settled elsewhere*, not here: the separatedness half is
   `CategoryTheory.Functor.locallyEqual_descentPairProj_iff` in `StageThreeMorSheaf.lean` and the
   gluing half is `CategoryTheory.Functor.exists_amalgamation_descentPairProj` in
   `StageThreeGluing.lean`, which together give
   `CategoryTheory.Functor.isMorSheaf_descentPairProj`. The gluing half is proved for
   `CategoryTheory.Functor.DescentMor` directly, exactly as
   `CategoryTheory.Functor.exists_amalgamation_morPlusProj` was for the second stage.

   A warning about a route that does *not* work: it is tempting to deduce the sheaf condition from
   full faithfulness of
   `CategoryTheory.Functor.toDescentPair` together with the local essential surjectivity of
   item 2, on the grounds that being a sheaf is a local condition. **It is not.** The module
   docstring of `StageThreeMorSheaf.lean` records the counterexample: for the category of elements
   of the presheaf on the two-point discrete space with two sections over the whole space and one
   over each point, `Mor(x, y)` is empty over the whole space and terminal over each point, so it
   is a sheaf on each member of a covering without being a sheaf. What is true is
   `CategoryTheory.Presieve.isSheafFor_trans`, whose first hypothesis is the sheaf condition for
   the covering sieve itself — precisely the leg locality does not supply.
2. That every pair is locally in the image of `toDescentPair`: for `f : V ⟶ A.pt` in `A.sieve`, the
   pullback `CategoryTheory.Functor.DescentPair.pullback A f` should be isomorphic, over the
   identity of `V`, to `CategoryTheory.Functor.DescentPair.ofObj` of the object `A.datum.obj f`.
   The isomorphism is built from the gluing isomorphisms `A.datum.iso` taken at the pair of arrows
   `(g ≫ f, f)` with the pair of morphisms `(𝟙, g)`; this is clause (2) of Stacks 02ZN for the
   composite of the three stages, and it is the key input to items 1 and 3.
3. That every descent datum for `CategoryTheory.Functor.descentPairProj` is effective, that is
   `CategoryTheory.Functor.HasEffectiveDescent`, and hence, with items 1 and 2,
   `CategoryTheory.Functor.IsStack`.
4. The translation of all of this into the presheaf-on-`Over U` language in which
   `CategoryTheory.Functor.IsMorSheaf` is phrased, which item 1 of the list in
   `StacksFrontier/CategoryTheory/Sites/Stackification/StageTwo.lean` also asks for.
5. Clauses (1) and (2) of Stacks 02ZN for the composite `CategoryTheory.Functor.toStageThree`, and
   uniqueness of the stackification up to unique 2-isomorphism.

## References

This is the third stage of the proof of Stacks 02ZN. Nothing in this file may be read as claiming
Stacks 02ZN, or any of the statements 02ZP, 0435, 0436 that go with it.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-! ### Restricting and pulling back a descent datum -/

namespace SieveDescentDatum

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered]

/-- The restriction of a descent datum along an inclusion of sieves: keep the objects and the
gluing isomorphisms attached to the arrows of the smaller sieve.

Reducible for the same reason as `CategoryTheory.Functor.DescentPair.pullback`: it occurs in the
*type* of the comparison morphisms below, and proofs about those are not type-correct at the
transparency `rw` and `simp` use unless it can be unfolded there. -/
@[reducible]
def restrict {U : 𝒮} {R T : Sieve U} (D : SieveDescentDatum p R) (hT : T ≤ R) :
    SieveDescentDatum p T where
  obj {_} f hf := D.obj f (hT _ hf)
  iso {_ _ _} {_} hf {_} hg ε ε' heq := D.iso (hT _ hf) (hT _ hg) ε ε' heq
  cocycle {_ _ _ _} {_} hf {_} hg {_} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ :=
    D.cocycle (hT _ hf) (hT _ hg) (hT _ hh) ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
  iso_pullback {_ _ _ _} {_} hf {_} hg ε ε' heq γ :=
    D.iso_pullback (hT _ hf) (hT _ hg) ε ε' heq γ

/-- The object the restriction of `D` attaches to an arrow `f` is the one `D` attaches to `f`. -/
@[simp]
theorem restrict_obj {U : 𝒮} {R T : Sieve U} (D : SieveDescentDatum p R) (hT : T ≤ R) {V : 𝒮}
    (f : V ⟶ U) (hf : T.arrows f) : (D.restrict hT).obj f hf = D.obj f (hT _ hf) := rfl

/-- An arrow `f` of the pullback of a sieve `R` along `v` gives the arrow `f ≫ v` of `R`. -/
theorem mem_of_mem_pullback {U U' : 𝒮} {R : Sieve U} {v : U' ⟶ U} {V : 𝒮} {f : V ⟶ U'}
    (hf : (R.pullback v).arrows f) : R.arrows (f ≫ v) := hf

/-- The pullback of a descent datum along a morphism `v` of the base: the object attached to an
arrow `f` of the pullback sieve is the one `D` attaches to `f ≫ v`. -/
@[implicit_reducible]
def pullback {U U' : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R) (v : U' ⟶ U) :
    SieveDescentDatum p (R.pullback v) where
  obj {_} f hf := D.obj (f ≫ v) hf
  iso {_ _ _} {f} hf {g} hg ε ε' heq :=
    D.iso (f := f ≫ v) hf (g := g ≫ v) hg ε ε' (by rw [← assoc, ← assoc, heq])
  cocycle {_ _ _ _} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ _ _ _ :=
    D.cocycle (f := f ≫ v) hf (g := g ≫ v) hg (h := h ≫ v) hh ε₁ ε₂ ε₃ _ _ _
  iso_pullback {_ _ _ _} {f} hf {g} hg ε ε' _ γ :=
    D.iso_pullback (f := f ≫ v) hf (g := g ≫ v) hg ε ε' _ γ

/-- The object the pullback of `D` along `v` attaches to `f` is the one `D` attaches to `f ≫ v`. -/
@[simp]
theorem pullback_obj {U U' : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R) (v : U' ⟶ U) {V : 𝒮}
    (f : V ⟶ U') (hf : (R.pullback v).arrows f) :
    (D.pullback v).obj f hf = D.obj (f ≫ v) hf := rfl

end SieveDescentDatum

/-! ### The pairs, and the morphisms between them -/

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-- A *descent pair* for `p` and `J`: an object `pt` of the base, a covering sieve of `pt`, and a
descent datum relative to that sieve. These are the objects of the third stage; the object it
prescribes is adjoined by declaring the pair to *be* that object. -/
structure DescentPair (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) where
  /-- The object of the base that the pair lies over. -/
  pt : 𝒮
  /-- The covering sieve the descent datum is relative to. -/
  sieve : Sieve pt
  /-- The sieve is a covering sieve. -/
  sieve_mem : sieve ∈ J pt
  /-- The descent datum. -/
  datum : SieveDescentDatum p sieve

/-- A morphism of descent pairs lying over a morphism `u` of the base, before the identification of
data agreeing on a covering sieve: a covering sieve refining that of `A`, whose arrows `u` carries
into the sieve of `B`, together with a morphism `A.datum.obj f ⟶ B.datum.obj (f ≫ u)` of the fibre
for each of its arrows `f`, compatible with the gluing isomorphisms of the two data.

The arrow `f ≫ u` is not passed directly but as an arrow `g` of `B.sieve` together with the
equation `f ≫ u = g`; this is what makes the composite of two such morphisms need no transport,
the transport being confined to `CategoryTheory.Functor.DescentPairHom.map_source_congr` and
`CategoryTheory.Functor.DescentPairHom.map_target_congr`. -/
structure DescentPairHom (A B : DescentPair p J) (u : A.pt ⟶ B.pt) where
  /-- The sieve on which the morphism is defined. -/
  sieve : Sieve A.pt
  /-- The defining sieve is a covering sieve. -/
  sieve_mem : sieve ∈ J A.pt
  /-- The defining sieve refines the sieve of the source. -/
  le_dom : sieve ≤ A.sieve
  /-- The base morphism carries the defining sieve into the sieve of the target. -/
  mem_cod : ∀ ⦃V : 𝒮⦄ (f : V ⟶ A.pt), sieve.arrows f → B.sieve.arrows (f ≫ u)
  /-- The morphism of fibres attached to an arrow of the defining sieve. -/
  map : ∀ ⦃V : 𝒮⦄ (f : V ⟶ A.pt) (hf : sieve.arrows f) ⦃g : V ⟶ B.pt⦄
    (hg : B.sieve.arrows g), f ≫ u = g → (A.datum.obj f (le_dom _ hf) ⟶ B.datum.obj g hg)
  /-- The attached morphisms are compatible with the gluing isomorphisms of the two data. -/
  map_glue : ∀ ⦃V W Z : 𝒮⦄ (f : V ⟶ A.pt) (hf : sieve.arrows f) (f' : W ⟶ A.pt)
    (hf' : sieve.arrows f') ⦃g : V ⟶ B.pt⦄ (hg : B.sieve.arrows g) (h : f ≫ u = g)
    ⦃g' : W ⟶ B.pt⦄ (hg' : B.sieve.arrows g') (h' : f' ≫ u = g')
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ f'),
    pullbackFiberHom (map f hf hg h) ε ≫
        (B.datum.iso hg hg' ε ε' (by rw [← h, ← h', ← assoc, ← assoc, heq])).hom =
      (A.datum.iso (le_dom _ hf) (le_dom _ hf') ε ε' heq).hom ≫
        pullbackFiberHom (map f' hf' hg' h') ε'

namespace DescentPairHom

variable {A B : DescentPair p J} {u : A.pt ⟶ B.pt}

/-- The morphism attached to an arrow does not depend on which of two equal arrows of the source it
is read as. This, with `CategoryTheory.Functor.DescentPairHom.map_target_congr`, is what absorbs
the failure of `(f ≫ u) ≫ u'` and `f ≫ (u ≫ u')` to be the same arrow. -/
theorem map_source_congr (F : DescentPairHom A B u) {V : 𝒮} {f f' : V ⟶ A.pt} (e : f = f')
    (hf : F.sieve.arrows f) (hf' : F.sieve.arrows f') {g : V ⟶ B.pt} (hg : B.sieve.arrows g)
    (h : f ≫ u = g) (h' : f' ≫ u = g) :
    eqToHom (show A.datum.obj f (F.le_dom _ hf) = A.datum.obj f' (F.le_dom _ hf') by
      subst e; rfl) ≫ F.map f' hf' hg h' = F.map f hf hg h := by
  subst e
  simp

/-- The morphism attached to an arrow does not depend on which of two equal arrows of the target it
is read as. -/
theorem map_target_congr (F : DescentPairHom A B u) {V : 𝒮} (f : V ⟶ A.pt)
    (hf : F.sieve.arrows f) {g g' : V ⟶ B.pt} (e : g = g') (hg : B.sieve.arrows g)
    (hg' : B.sieve.arrows g') (h : f ≫ u = g) (h' : f ≫ u = g') :
    F.map f hf hg h ≫ eqToHom (show B.datum.obj g hg = B.datum.obj g' hg' by subst e; rfl) =
      F.map f hf hg' h' := by
  subst e
  simp

/-! #### Identities and composition -/

/-- The identity morphism of a descent pair: defined on the whole sieve of the pair, and attaching
to each of its arrows the identity — which the equation `f ≫ 𝟙 = g` presents as a transport. -/
def id (A : DescentPair p J) : DescentPairHom A A (𝟙 A.pt) where
  sieve := A.sieve
  sieve_mem := A.sieve_mem
  le_dom := le_refl _
  mem_cod _ _ hf := by rwa [comp_id]
  map _ f hf _ hg h := eqToHom (by obtain rfl := (comp_id f).symm.trans h; rfl)
  map_glue _ _ _ f hf f' hf' _ hg h _ hg' h' ε ε' heq := by
    obtain rfl := (comp_id f).symm.trans h
    obtain rfl := (comp_id f').symm.trans h'
    simp

/-- The composite of two morphisms of descent pairs: defined on the intersection of the defining
sieve of the first with the pullback, along its base morphism, of the defining sieve of the second,
and attaching to an arrow the composite of the two attached morphisms of fibres. -/
@[implicit_reducible]
def comp {A B C : DescentPair p J} {u : A.pt ⟶ B.pt} {u' : B.pt ⟶ C.pt}
    (F : DescentPairHom A B u) (G : DescentPairHom B C u') : DescentPairHom A C (u ≫ u') where
  sieve := F.sieve ⊓ G.sieve.pullback u
  sieve_mem := J.intersection_covering F.sieve_mem (J.pullback_stable _ G.sieve_mem)
  le_dom := le_trans inf_le_left F.le_dom
  mem_cod _ _ hf := by rw [← assoc]; exact G.mem_cod _ hf.2
  map _ f hf _ hg h :=
    F.map f hf.1 (F.mem_cod _ hf.1) rfl ≫ G.map (f ≫ u) hf.2 hg (by rwa [assoc])
  map_glue _ _ _ f hf f' hf' _ hg h _ hg' h' ε ε' heq := by
    have heq₂ : ε ≫ (f ≫ u) = ε' ≫ (f' ≫ u) := by rw [← assoc, ← assoc, heq]
    have hG := G.map_glue (f ≫ u) hf.2 (f' ≫ u) hf'.2 hg (by rwa [assoc]) hg'
      (by rwa [assoc]) ε ε' heq₂
    have hF := F.map_glue f hf.1 f' hf'.1 (F.mem_cod _ hf.1) rfl (F.mem_cod _ hf'.1) rfl ε ε' heq
    simp only [pullbackFiberHom_comp, assoc, hG]
    simp [← assoc, hF]

/-- The sieve of a composite is the intersection of the sieve of `F` with the pullback along `u` of
the sieve of `G`. -/
@[simp]
theorem comp_sieve {A B C : DescentPair p J} {u : A.pt ⟶ B.pt} {u' : B.pt ⟶ C.pt}
    (F : DescentPairHom A B u) (G : DescentPairHom B C u') :
    (F.comp G).sieve = F.sieve ⊓ G.sieve.pullback u := rfl

/-- The morphism of fibres a composite attaches to an arrow `f` is the composite of the one `F`
attaches to `f` with the one `G` attaches to `f ≫ u`. -/
@[simp]
theorem comp_map {A B C : DescentPair p J} {u : A.pt ⟶ B.pt} {u' : B.pt ⟶ C.pt}
    (F : DescentPairHom A B u) (G : DescentPairHom B C u') {V : 𝒮} (f : V ⟶ A.pt)
    (hf : (F.sieve ⊓ G.sieve.pullback u).arrows f) {g : V ⟶ C.pt} (hg : C.sieve.arrows g)
    (h : f ≫ (u ≫ u') = g) :
    (F.comp G).map f hf hg h =
      F.map f hf.1 (F.mem_cod _ hf.1) rfl ≫ G.map (f ≫ u) hf.2 hg (by rw [assoc]; exact h) :=
  rfl

end DescentPairHom

/-! ### The morphisms of the third stage -/

/-- A morphism datum of descent pairs together with the morphism of the base it lies over. The
morphisms of the third stage are these modulo agreement on a covering sieve. -/
structure DescentPairData (A B : DescentPair p J) where
  /-- The morphism of the base. -/
  base : A.pt ⟶ B.pt
  /-- The morphism of descent pairs over it. -/
  hom : DescentPairHom A B base

namespace DescentPairData

variable {A B C : DescentPair p J}

/-- The identity datum. -/
def id (A : DescentPair p J) : DescentPairData A A := ⟨𝟙 A.pt, DescentPairHom.id A⟩

/-- The composite of two morphism data. -/
@[implicit_reducible]
def comp (X : DescentPairData A B) (Y : DescentPairData B C) : DescentPairData A C :=
  ⟨X.base ≫ Y.base, X.hom.comp Y.hom⟩

/-- The identity datum lies over the identity of the base. -/
@[simp]
theorem id_base (A : DescentPair p J) : (DescentPairData.id A).base = 𝟙 A.pt := rfl

/-- The composite of two morphism data lies over the composite of their base morphisms. -/
@[simp]
theorem comp_base (X : DescentPairData A B) (Y : DescentPairData B C) :
    (X.comp Y).base = X.base ≫ Y.base := rfl

/-- The morphism of fibres that the composite attaches to an arrow, with every proof supplied
explicitly so that the equation can be rewritten with. -/
theorem comp_hom_map (X : DescentPairData A B) (Y : DescentPairData B C) {V : 𝒮} (f : V ⟶ A.pt)
    (hf₁ : X.hom.sieve.arrows f) (hf₂ : Y.hom.sieve.arrows (f ≫ X.base)) {g : V ⟶ C.pt}
    (hg : C.sieve.arrows g) (h : (f ≫ X.base) ≫ Y.base = g)
    (hf : (X.comp Y).hom.sieve.arrows f) (h₀ : f ≫ (X.comp Y).base = g) :
    (X.comp Y).hom.map f hf hg h₀ =
      X.hom.map f hf₁ (X.hom.mem_cod _ hf₁) rfl ≫ Y.hom.map (f ≫ X.base) hf₂ hg h := rfl

/-- Two morphism data are *identified* when they lie over the same morphism of the base and their
attached morphisms of fibres agree on a common covering sieve. This is the same identification as
in the second stage, made on the morphisms of descent data instead of the morphisms of `𝒳`. -/
def Rel (X Y : DescentPairData A B) : Prop :=
  X.base = Y.base ∧ ∃ (T : Sieve A.pt) (_ : T ∈ J A.pt) (h₁ : T ≤ X.hom.sieve)
    (h₂ : T ≤ Y.hom.sieve), ∀ ⦃V : 𝒮⦄ (f : V ⟶ A.pt) (hf : T.arrows f) ⦃g : V ⟶ B.pt⦄
      (hg : B.sieve.arrows g) (h : f ≫ X.base = g) (h' : f ≫ Y.base = g),
      X.hom.map f (h₁ _ hf) hg h = Y.hom.map f (h₂ _ hf) hg h'

/-- Identified morphism data lie over the same morphism of the base. -/
theorem Rel.base_eq {X Y : DescentPairData A B} (h : X.Rel Y) : X.base = Y.base := h.1

/-- To identify two morphism data it suffices that they lie over the same morphism of the base and
agree on the intersection of their defining sieves. -/
theorem rel_of_agree {X Y : DescentPairData A B} (hbase : X.base = Y.base)
    (hagree : ∀ ⦃V : 𝒮⦄ (f : V ⟶ A.pt) (hf : X.hom.sieve.arrows f) (hf' : Y.hom.sieve.arrows f)
      ⦃g : V ⟶ B.pt⦄ (hg : B.sieve.arrows g) (h : f ≫ X.base = g) (h' : f ≫ Y.base = g),
      X.hom.map f hf hg h = Y.hom.map f hf' hg h') : X.Rel Y :=
  ⟨hbase, X.hom.sieve ⊓ Y.hom.sieve,
    J.intersection_covering X.hom.sieve_mem Y.hom.sieve_mem, fun _ _ hf ↦ hf.1,
    fun _ _ hf ↦ hf.2, fun _ f hf _ hg h h' ↦ hagree f hf.1 hf.2 hg h h'⟩

/-- Identification of morphism data is reflexive. -/
@[refl]
theorem Rel.refl (X : DescentPairData A B) : X.Rel X :=
  ⟨rfl, X.hom.sieve, X.hom.sieve_mem, le_refl _, le_refl _, fun _ _ _ _ _ _ _ ↦ rfl⟩

/-- Identification of morphism data is symmetric. -/
theorem Rel.symm {X Y : DescentPairData A B} (h : X.Rel Y) : Y.Rel X := by
  obtain ⟨hbase, T, hT, h₁, h₂, hagree⟩ := h
  exact ⟨hbase.symm, T, hT, h₂, h₁, fun _ f hf _ hg h h' ↦ (hagree f hf hg h' h).symm⟩

/-- Identification of morphism data is transitive. -/
theorem Rel.trans {X Y Z : DescentPairData A B} (hXY : X.Rel Y) (hYZ : Y.Rel Z) : X.Rel Z := by
  obtain ⟨hbase, T, hT, h₁, h₂, hagree⟩ := hXY
  obtain ⟨hbase', T', hT', k₁, k₂, kagree⟩ := hYZ
  refine ⟨hbase.trans hbase', T ⊓ T', J.intersection_covering hT hT',
    fun _ _ hf ↦ h₁ _ hf.1, fun _ _ hf ↦ k₂ _ hf.2, fun _ f hf g hg h h' ↦ ?_⟩
  have hmid : f ≫ Y.base = g := by rwa [← hbase]
  exact (hagree f hf.1 hg h hmid).trans (kagree f hf.2 hg hmid h')

/-- Morphism data of descent pairs, up to agreement on a covering sieve. -/
instance setoid (A B : DescentPair p J) : _root_.Setoid (DescentPairData A B) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- Composition respects the identification of morphism data. -/
theorem Rel.comp {X X' : DescentPairData A B} {Y Y' : DescentPairData B C} (hX : X.Rel X')
    (hY : Y.Rel Y') : (X.comp Y).Rel (X'.comp Y') := by
  obtain ⟨u, F⟩ := X
  obtain ⟨u', F'⟩ := X'
  obtain ⟨w, G⟩ := Y
  obtain ⟨w', G'⟩ := Y'
  obtain ⟨hbase, T, hT, h₁, h₂, hagree⟩ := hX
  obtain ⟨kbase, T', hT', k₁, k₂, kagree⟩ := hY
  obtain rfl : u = u' := hbase
  obtain rfl : w = w' := kbase
  refine ⟨rfl, T ⊓ T'.pullback u, J.intersection_covering hT (J.pullback_stable _ hT'),
    fun _ _ hf ↦ ⟨h₁ _ hf.1, k₁ _ hf.2⟩, fun _ _ hf ↦ ⟨h₂ _ hf.1, k₂ _ hf.2⟩,
    fun _ f hf g hg h _ ↦ ?_⟩
  have q : (f ≫ u) ≫ w = g := by rwa [assoc]
  exact congrArg₂ (fun a b ↦ a ≫ b) (hagree f hf.1 (F.mem_cod _ (h₁ _ hf.1)) rfl rfl)
    (kagree (f ≫ u) hf.2 hg q q)

/-- Composing with the identity datum on the left changes a morphism datum only up to
identification. -/
theorem id_comp_rel (X : DescentPairData A B) : ((DescentPairData.id A).comp X).Rel X := by
  refine rel_of_agree (Category.id_comp _) ?_
  intro V f hf hf' g hg h h'
  exact DescentPairHom.map_source_congr X.hom (comp_id f).symm hf' hf.2 hg h'
    (by rwa [comp_id])

/-- Composing with the identity datum on the right changes a morphism datum only up to
identification. -/
theorem comp_id_rel (X : DescentPairData A B) : (X.comp (DescentPairData.id B)).Rel X := by
  refine rel_of_agree (Category.comp_id _) ?_
  intro V f hf hf' g hg h h'
  exact DescentPairHom.map_target_congr X.hom f hf' h' (X.hom.mem_cod _ hf') hg rfl h'

/-- Composition of morphism data is associative up to identification. The two composites are
literally different: the arrow at which the third datum is read is `(f ≫ u) ≫ u'` on one side and
`f ≫ (u ≫ u')` on the other, and the two comparison lemmas of
`CategoryTheory.Functor.DescentPairHom` are what identifies them. -/
theorem comp_assoc_rel {D : DescentPair p J} (X : DescentPairData A B) (Y : DescentPairData B C)
    (Z : DescentPairData C D) : ((X.comp Y).comp Z).Rel (X.comp (Y.comp Z)) := by
  refine rel_of_agree (by simp) ?_
  intro V f hf hf' g hg h h'
  have e : (f ≫ X.base) ≫ Y.base = f ≫ (X.base ≫ Y.base) := assoc _ _ _
  have h₁ : (f ≫ (X.base ≫ Y.base)) ≫ Z.base = g := by simp only [assoc]; exact h'
  have h₃ : ((f ≫ X.base) ≫ Y.base) ≫ Z.base = g := by rwa [e]
  have hgm : C.sieve.arrows (f ≫ (X.base ≫ Y.base)) := (X.comp Y).hom.mem_cod _ hf.1
  have hG := DescentPairHom.map_target_congr Y.hom (f ≫ X.base) hf.1.2 e
    (Y.hom.mem_cod _ hf.1.2) hgm rfl e
  have hH := DescentPairHom.map_source_congr Z.hom e hf'.2.2 hf.2 hg h₃ h₁
  have key : Y.hom.map (f ≫ X.base) hf.1.2 hgm e ≫
        Z.hom.map (f ≫ (X.base ≫ Y.base)) hf.2 hg h₁ =
      Y.hom.map (f ≫ X.base) hf.1.2 (Y.hom.mem_cod _ hf.1.2) rfl ≫
        Z.hom.map ((f ≫ X.base) ≫ Y.base) hf'.2.2 hg h₃ := by
    rw [← hG, assoc, hH]
  exact (assoc (X.hom.map f hf.1.1 (X.hom.mem_cod _ hf.1.1) rfl) _ _).trans
    (congrArg (X.hom.map f hf.1.1 (X.hom.mem_cod _ hf.1.1) rfl ≫ ·) key)

end DescentPairData

/-- The morphisms of the third stage: morphism data of descent pairs, up to agreement on a covering
sieve. -/
def DescentMor (A B : DescentPair p J) : Type (max u₁ v₁ v₂) :=
  _root_.Quotient (DescentPairData.setoid A B)

namespace DescentMor

variable {A B C : DescentPair p J}

/-- The class of a morphism datum. -/
abbrev mk (X : DescentPairData A B) : DescentMor A B := _root_.Quotient.mk _ X

/-- Every morphism of the third stage is the class of a morphism datum. -/
theorem exists_rep (F : DescentMor A B) : ∃ X : DescentPairData A B, mk X = F :=
  _root_.Quotient.exists_rep F

/-- Two morphism data have the same class exactly when they are identified. -/
theorem mk_eq_iff (X Y : DescentPairData A B) : mk X = mk Y ↔ X.Rel Y :=
  ⟨fun h ↦ _root_.Quotient.exact h, fun h ↦ _root_.Quotient.sound h⟩

/-- The composite of two morphisms of the third stage. -/
def comp : DescentMor A B → DescentMor B C → DescentMor A C :=
  _root_.Quotient.lift₂ (fun X Y ↦ mk (X.comp Y))
    fun _ _ _ _ hX hY ↦ _root_.Quotient.sound (DescentPairData.Rel.comp hX hY)

/-- The composite of the classes of two morphism data is the class of their composite. -/
@[simp]
theorem comp_mk (X : DescentPairData A B) (Y : DescentPairData B C) :
    comp (mk X) (mk Y) = mk (X.comp Y) := rfl

/-- The morphism of the base that a morphism of the third stage lies over. -/
def base : DescentMor A B → (A.pt ⟶ B.pt) :=
  _root_.Quotient.lift DescentPairData.base fun _ _ h ↦ h.base_eq

/-- The class of a morphism datum lies over the base morphism of that datum. -/
@[simp]
theorem base_mk (X : DescentPairData A B) : base (mk X) = X.base := rfl

end DescentMor

/-- **The third stage of the construction of the stackification of a fibred category**, as a
category: the objects are the pairs (covering sieve, descent datum) and the morphisms are the
morphism data modulo agreement on a covering sieve. -/
instance : Category.{max u₁ v₁ v₂} (DescentPair p J) where
  Hom := DescentMor
  id A := DescentMor.mk (DescentPairData.id A)
  comp := DescentMor.comp
  id_comp F := by
    obtain ⟨X, rfl⟩ := DescentMor.exists_rep F
    exact (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.id_comp_rel X)
  comp_id F := by
    obtain ⟨X, rfl⟩ := DescentMor.exists_rep F
    exact (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.comp_id_rel X)
  assoc F G H := by
    obtain ⟨X, rfl⟩ := DescentMor.exists_rep F
    obtain ⟨Y, rfl⟩ := DescentMor.exists_rep G
    obtain ⟨Z, rfl⟩ := DescentMor.exists_rep H
    exact (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.comp_assoc_rel X Y Z)

/-! ### The structure functor of the third stage, and its fibredness -/

/-- The structure functor of the third stage: a pair goes to the object of the base its covering
sieve is a sieve on, and a morphism to the morphism of the base it lies over. -/
@[implicit_reducible]
def descentPairProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) :
    DescentPair p J ⥤ 𝒮 where
  obj A := A.pt
  map F := DescentMor.base F
  map_id _ := rfl
  map_comp F G := by
    obtain ⟨X, rfl⟩ := DescentMor.exists_rep F
    obtain ⟨Y, rfl⟩ := DescentMor.exists_rep G
    rfl

/-- The structure functor sends a pair to the object its covering sieve is a sieve on. -/
@[simp]
theorem descentPairProj_obj (A : DescentPair p J) : (p.descentPairProj J).obj A = A.pt := rfl

/-- The structure functor sends the class of a morphism datum to its base morphism. -/
@[simp]
theorem descentPairProj_map_mk {A B : DescentPair p J} (X : DescentPairData A B) :
    (p.descentPairProj J).map (DescentMor.mk X : A ⟶ B) = X.base := rfl

namespace DescentMor

/-- The class of a morphism datum lies over the morphism of the base it is declared to lie over. -/
theorem isHomLift_mk {A B : DescentPair p J} (X : DescentPairData A B) :
    (p.descentPairProj J).IsHomLift X.base (DescentMor.mk X : A ⟶ B) :=
  have h : (p.descentPairProj J).IsHomLift
      ((p.descentPairProj J).map (DescentMor.mk X : A ⟶ B)) (DescentMor.mk X : A ⟶ B) :=
    inferInstance
  h

/-- The base morphism of a morphism datum is the unique morphism of the base that its class lies
over. -/
theorem base_eq_of_isHomLift {A B : DescentPair p J} (X : DescentPairData A B)
    {f : (p.descentPairProj J).obj A ⟶ (p.descentPairProj J).obj B}
    (hf : (p.descentPairProj J).IsHomLift f (DescentMor.mk X : A ⟶ B)) : X.base = f :=
  have := hf
  (IsHomLift.eq_of_isHomLift (p.descentPairProj J) f (DescentMor.mk X : A ⟶ B)).symm

end DescentMor

/-- The pullback of a descent pair along a morphism of the base: pull back both the covering sieve
and the descent datum.

This is marked `@[reducible]` because it appears in the *type* of the canonical morphism below: the
object of the base underlying it is `U₀`, and a proof about that morphism is not even type-correct
at the transparency `rw` and instance search use unless that is visible. -/
@[reducible]
def DescentPair.pullback (A : DescentPair p J) {U₀ : 𝒮} (v : U₀ ⟶ A.pt) : DescentPair p J where
  pt := U₀
  sieve := A.sieve.pullback v
  sieve_mem := J.pullback_stable _ A.sieve_mem
  datum := A.datum.pullback v

/-- The compatibility with gluing isomorphisms of a family of *identity* morphisms of fibres. -/
theorem pullbackFiberHom_id_glue {V W Z : 𝒮} {y : p.Fiber V} {y' : p.Fiber W} (ε : Z ⟶ V)
    (ε' : Z ⟶ W) (I : pullbackFiber p y ε ≅ pullbackFiber p y' ε') :
    pullbackFiberHom (𝟙 y) ε ≫ I.hom = I.hom ≫ pullbackFiberHom (𝟙 y') ε' := by
  simp

/-- The canonical morphism from the pullback of a descent pair to the pair itself: on each arrow of
the pullback sieve it is the identity, presented as a transport. -/
@[implicit_reducible]
def DescentPairData.pullbackHom (A : DescentPair p J) {U₀ : 𝒮} (v : U₀ ⟶ A.pt) :
    DescentPairData (A.pullback v) A where
  base := v
  hom :=
    { sieve := A.sieve.pullback v
      sieve_mem := J.pullback_stable _ A.sieve_mem
      le_dom := le_refl _
      mem_cod := fun _ _ hf ↦ SieveDescentDatum.mem_of_mem_pullback hf
      map := fun _ f hf _ hg h ↦
        show A.datum.obj (f ≫ v) (SieveDescentDatum.mem_of_mem_pullback hf) ⟶ _ from
          eqToHom (by cases h; rfl)
      map_glue := fun _ _ _ _ _ _ _ _ _ h _ _ h' ε ε' _ ↦ by
        obtain rfl := h
        obtain rfl := h'
        exact pullbackFiberHom_id_glue ε ε' _ }

/-- The factorisation, through the canonical morphism from the pullback of `A` along `v`, of a
morphism into `A` lying over `w ≫ v`. It is the same family of morphisms of fibres, read at the
arrows of the pullback sieve. -/
def DescentPairHom.pullbackLift {A' A : DescentPair p J} (Y : DescentPairData A' A) {U₀ : 𝒮}
    (v : U₀ ⟶ A.pt) (w : A'.pt ⟶ U₀) (hbase : Y.base = w ≫ v) :
    DescentPairHom A' (A.pullback v) w where
  sieve := Y.hom.sieve
  sieve_mem := Y.hom.sieve_mem
  le_dom := Y.hom.le_dom
  mem_cod := fun _ f hf ↦ by
    rw [Sieve.pullback_apply]
    rw [assoc, ← hbase]
    exact Y.hom.mem_cod _ hf
  map := fun _ f hf g hg h ↦ Y.hom.map f hf (g := g ≫ v) hg
    ((congrArg (f ≫ ·) hbase).trans ((assoc f w v).symm.trans (congrArg (· ≫ v) h)))
  map_glue := fun _ _ _ f hf f' hf' _ hg _ _ hg' _ ε ε' heq ↦
    Y.hom.map_glue f hf f' hf' hg _ hg' _ ε ε' heq

/-- If `b = w ≫ v` and `g ≫ w = k`, then `g ≫ b = k ≫ v`. -/
private theorem comp_eq_comp_of_eq_comp {C : Type*} [Category C] {X Z W T : C} {b : X ⟶ Z}
    {v : T ⟶ Z} {w : X ⟶ T} (hb : b = w ≫ v) {g : W ⟶ X} {k : W ⟶ T} (h : g ≫ w = k) :
    g ≫ b = k ≫ v := by
  rw [hb, ← assoc, h]

/-- **The canonical morphism from the pullback of a descent pair is strongly cartesian.** The
factorisation of a morphism through it is the same family of morphisms of fibres, and it is unique
because two morphism data agreeing on a covering sieve are identified. -/
theorem isStronglyCartesian_pullbackHom (A : DescentPair p J) {U₀ : 𝒮} (v : U₀ ⟶ A.pt) :
    (p.descentPairProj J).IsStronglyCartesian v
      (DescentMor.mk (DescentPairData.pullbackHom A v) : A.pullback v ⟶ A) := by
  refine { toIsHomLift := DescentMor.isHomLift_mk (DescentPairData.pullbackHom A v),
           universal_property' := ?_ }
  intro A' w Ψ hΨ
  obtain ⟨Y, rfl⟩ := DescentMor.exists_rep Ψ
  have hbase : Y.base = w ≫ v := DescentMor.base_eq_of_isHomLift Y hΨ
  set X : DescentPairData A' (A.pullback v) := ⟨w, DescentPairHom.pullbackLift Y v w hbase⟩
    with hX
  refine ⟨DescentMor.mk X, ⟨?_,
    (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree hbase.symm ?_)⟩, ?_⟩
  · exact DescentMor.isHomLift_mk X
  · intro V f hf hf' g hg h h'
    exact DescentPairHom.map_target_congr Y.hom f hf' (assoc f w v |>.trans h) hf.2 hg
      (comp_eq_comp_of_eq_comp hbase rfl) h'
  · rintro X' ⟨hX'₁, hX'₂⟩
    obtain ⟨Z, rfl⟩ := DescentMor.exists_rep X'
    obtain ⟨_, T, hT, k₁, k₂, kagree⟩ := (DescentMor.mk_eq_iff _ _).mp hX'₂
    refine (DescentMor.mk_eq_iff _ _).mpr ⟨DescentMor.base_eq_of_isHomLift Z hX'₁, T, hT,
      fun _ _ hf ↦ (k₁ _ hf).1, k₂, fun _ f hf g hg h h' ↦ ?_⟩
    have hA : f ≫ (Z.comp (DescentPairData.pullbackHom A v)).base = g ≫ v :=
      (assoc f Z.base v).symm.trans (congrArg (· ≫ v) h)
    refine Eq.trans ?_ (kagree f hf hg hA (comp_eq_comp_of_eq_comp hbase h'))
    exact (DescentPairHom.map_target_congr Z.hom f ((k₁ _ hf).1) h ((k₁ _ hf).2) hg rfl h).symm

/-- **The structure functor of the third stage is fibred.** The cartesian lift of a morphism `v` of
the base at a pair is the pullback of the pair along `v`. -/
instance isFibered_descentPairProj : (p.descentPairProj J).IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun A _ f ↦
    ⟨A.pullback f, DescentMor.mk (DescentPairData.pullbackHom A f),
      isStronglyCartesian_pullbackHom A f⟩

/-! ### A pair and its restriction to a smaller covering sieve -/

/-- The pair obtained from `A` by restricting its descent datum to a smaller covering sieve. -/
@[reducible]
def DescentPair.restrict (A : DescentPair p J) {T : Sieve A.pt} (hT : T ≤ A.sieve)
    (hTmem : T ∈ J A.pt) : DescentPair p J where
  pt := A.pt
  sieve := T
  sieve_mem := hTmem
  datum := A.datum.restrict hT

/-- The canonical morphism from the restriction of `A` to a smaller covering sieve back to `A`: on
each arrow of the smaller sieve it is the identity, presented as a transport. -/
def DescentPairData.ofRestrict (A : DescentPair p J) {T : Sieve A.pt} (hT : T ≤ A.sieve)
    (hTmem : T ∈ J A.pt) : DescentPairData (A.restrict hT hTmem) A where
  base := 𝟙 A.pt
  hom :=
    { sieve := T
      sieve_mem := hTmem
      le_dom := le_refl _
      mem_cod := fun _ _ hf ↦ by rw [comp_id]; exact hT _ hf
      map := fun _ f hf _ hg h ↦
        show A.datum.obj f (hT _ hf) ⟶ A.datum.obj _ hg from
          eqToHom (by obtain rfl := (comp_id f).symm.trans h; rfl)
      map_glue := fun _ _ _ f _ f' _ _ _ h _ _ h' ε ε' _ ↦ by
        obtain rfl := (comp_id f).symm.trans h
        obtain rfl := (comp_id f').symm.trans h'
        exact pullbackFiberHom_id_glue ε ε' _ }

/-- The canonical morphism from `A` to its restriction to a smaller covering sieve. -/
def DescentPairData.toRestrict (A : DescentPair p J) {T : Sieve A.pt} (hT : T ≤ A.sieve)
    (hTmem : T ∈ J A.pt) : DescentPairData A (A.restrict hT hTmem) where
  base := 𝟙 A.pt
  hom :=
    { sieve := T
      sieve_mem := hTmem
      le_dom := hT
      mem_cod := fun _ _ hf ↦ by rwa [comp_id]
      map := fun _ f hf _ hg h ↦
        show A.datum.obj f (hT _ hf) ⟶ A.datum.obj _ (hT _ hg) from
          eqToHom (by obtain rfl := (comp_id f).symm.trans h; rfl)
      map_glue := fun _ _ _ f _ f' _ _ _ h _ _ h' ε ε' _ ↦ by
        obtain rfl := (comp_id f).symm.trans h
        obtain rfl := (comp_id f').symm.trans h'
        exact pullbackFiberHom_id_glue ε ε' _ }

/-- **A pair and its restriction to a smaller covering sieve are isomorphic**, by an isomorphism
lying over the identity of the base (`CategoryTheory.Functor.isHomLift_restrictIso_hom`).

This is the sense in which two pairs `(R, D)` and `(R', D')` over the same object of the base are
*identified*: when their restrictions to a common covering refinement agree, both are isomorphic
over the identity to that common restriction, hence to each other. No quotient is taken on the
objects; the identification is by isomorphism, as it must be for the objects of a category. -/
def DescentPair.restrictIso (A : DescentPair p J) {T : Sieve A.pt} (hT : T ≤ A.sieve)
    (hTmem : T ∈ J A.pt) : A.restrict hT hTmem ≅ A where
  hom := DescentMor.mk (DescentPairData.ofRestrict A hT hTmem)
  inv := DescentMor.mk (DescentPairData.toRestrict A hT hTmem)
  hom_inv_id := by
    refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (Category.id_comp _) ?_)
    intro V f hf hf' g hg h h'
    refine Eq.trans (DescentPairData.comp_hom_map _ _ f hf.1 hf.2 hg
      ((comp_id (f ≫ 𝟙 A.pt)).trans h') _ _) ?_
    simp [DescentPairData.ofRestrict, DescentPairData.toRestrict, DescentPairData.id,
      DescentPairHom.id, eqToHom_trans]
  inv_hom_id := by
    refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (Category.id_comp _) ?_)
    intro V f hf hf' g hg h h'
    refine Eq.trans (DescentPairData.comp_hom_map _ _ f hf.1 hf.2 hg
      ((comp_id (f ≫ 𝟙 A.pt)).trans h') _ _) ?_
    simp [DescentPairData.ofRestrict, DescentPairData.toRestrict, DescentPairData.id,
      DescentPairHom.id, eqToHom_trans]

/-- The isomorphism identifying a pair with its restriction lies over the identity of the base. -/
theorem isHomLift_restrictIso_hom (A : DescentPair p J) {T : Sieve A.pt} (hT : T ≤ A.sieve)
    (hTmem : T ∈ J A.pt) :
    (p.descentPairProj J).IsHomLift (𝟙 A.pt) (A.restrictIso hT hTmem).hom :=
  DescentMor.isHomLift_mk (DescentPairData.ofRestrict A hT hTmem)

/-! ### The 1-morphism from the fibred category into the third stage -/

section OfObj

/- Needed throughout this section, and for the same reason as in `Sites/Descent/IsStack`, whose
chosen-pullback API a descent datum is phrased in: the instance arguments of `IsHomLift` and
`IsCartesian` for a composite of chosen cartesian lifts are only found after unfolding
`CategoryTheory.Functor.pullbackFiber` and `CategoryTheory.Functor.Fiber.mk`, which the default
transparency of instance search does not do. Nothing before this section needs it. -/
set_option backward.isDefEq.respectTransparency false

/-- An object of `𝒳`, viewed as an object of the fibre over its own image. -/
@[reducible]
def fiberSelf (p : 𝒳 ⥤ 𝒮) (x : 𝒳) : p.Fiber (p.obj x) := ⟨x, rfl⟩

namespace SieveDescentDatum

/-- The object the descent datum of `x` attaches to an arrow `f` is the pullback of `x` along
`f`. -/
@[simp]
theorem ofFiber_obj {U : 𝒮} (x : p.Fiber U) (R : Sieve U) {V : 𝒮} (f : V ⟶ U) (hf : R.arrows f) :
    (ofFiber x R).obj f hf = pullbackFiber p x f := rfl

/-- The gluing isomorphisms of the descent datum of `x` are the comparison isomorphisms between
pullbacks of `x`. -/
@[simp]
theorem ofFiber_iso {U : 𝒮} (x : p.Fiber U) (R : Sieve U) {V W Z : 𝒮} {f : V ⟶ U}
    (hf : R.arrows f) {g : W ⟶ U} (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    (ofFiber x R).iso hf hg ε ε' heq = pullbackFiberComparison x ε ε' heq := rfl

end SieveDescentDatum

/-- The descent pair of an object of `𝒳`: the maximal sieve, together with the descent datum formed
by the chosen pullbacks of the object. -/
@[reducible]
noncomputable def DescentPair.ofObj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮)
    (x : 𝒳) : DescentPair p J where
  pt := p.obj x
  sieve := ⊤
  sieve_mem := J.top_mem _
  datum := SieveDescentDatum.ofFiber (fiberSelf p x) ⊤

/-- The morphism of fibres over `V` induced by `f : x ⟶ y`: the unique morphism from the chosen
pullback of `x` along `g` to the chosen pullback of `y` along `k` whose composite with the chosen
cartesian lift of `k` is the chosen cartesian lift of `g` followed by `f`. -/
noncomputable def pullbackFiberOfHom {x y : 𝒳} (f : x ⟶ y) {V : 𝒮} (g : V ⟶ p.obj x)
    (k : V ⟶ p.obj y) (h : g ≫ p.map f = k) :
    pullbackFiber p (fiberSelf p x) g ⟶ pullbackFiber p (fiberSelf p y) k :=
  have : p.IsHomLift k (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f) := by
    have h0 : p.IsHomLift (g ≫ p.map f) (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f) :=
      inferInstance
    rwa [h] at h0
  ⟨IsCartesian.map p k (IsPreFibered.pullbackMap (fiberSelf p y).2 k)
      (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f),
    IsCartesian.map_isHomLift p k _ _⟩

/-- The equation that determines `CategoryTheory.Functor.pullbackFiberOfHom`. -/
@[reassoc (attr := simp)]
theorem pullbackFiberOfHom_fac {x y : 𝒳} (f : x ⟶ y) {V : 𝒮} (g : V ⟶ p.obj x) (k : V ⟶ p.obj y)
    (h : g ≫ p.map f = k) :
    Fiber.fiberInclusion.map (pullbackFiberOfHom f g k h) ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 k =
      IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f :=
  have : p.IsHomLift k (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f) := by
    have h0 : p.IsHomLift (g ≫ p.map f) (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f) :=
      inferInstance
    rwa [h] at h0
  IsCartesian.fac p k (IsPreFibered.pullbackMap (fiberSelf p y).2 k)
    (IsPreFibered.pullbackMap (fiberSelf p x).2 g ≫ f)

/-- A morphism of `𝒳`, viewed as a morphism of the descent pairs of its source and target. -/
@[implicit_reducible]
noncomputable def DescentPairData.ofHom {x y : 𝒳} (f : x ⟶ y) :
    DescentPairData (DescentPair.ofObj p J x) (DescentPair.ofObj p J y) where
  base := p.map f
  hom :=
    { sieve := ⊤
      sieve_mem := J.top_mem _
      le_dom := le_refl _
      mem_cod := fun _ _ _ ↦ trivial
      map := fun _ g _ k _ h ↦ pullbackFiberOfHom f g k h
      map_glue := fun _ _ _ g _ g' _ k hk h k' hk' h' ε ε' heq ↦ by
        have hc : p.IsCartesian (ε' ≫ k')
            (IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p y) k').2 ε' ≫
              IsPreFibered.pullbackMap (fiberSelf p y).2 k') := inferInstance
        refine fiber_hom_ext_of_cartesian (ε' ≫ k') _ hc _ _ ?_
        simp [SieveDescentDatum.ofFiber_iso, Functor.map_comp, Category.assoc,
          pullbackFiberComparison_hom_fac, pullbackFiberComparison_hom_fac_assoc,
          pullbackFiberHom_fac_assoc, pullbackFiberOfHom_fac] }

/-- The morphism datum of a morphism `f` of `𝒳` lies over `p.map f`. -/
@[simp]
theorem DescentPairData.ofHom_base {x y : 𝒳} (f : x ⟶ y) :
    (DescentPairData.ofHom (p := p) (J := J) f).base = p.map f := rfl

/-- The morphism of fibres the datum of `f` attaches to an arrow `g` is the morphism between
pullbacks induced by `f`. -/
@[simp]
theorem DescentPairData.ofHom_map {x y : 𝒳} (f : x ⟶ y) {V : 𝒮} (g : V ⟶ p.obj x)
    (hg : (⊤ : Sieve (p.obj x)).arrows g) (k : V ⟶ p.obj y)
    (hk : (⊤ : Sieve (p.obj y)).arrows k) (h : g ≫ p.map f = k) :
    (DescentPairData.ofHom (J := J) f).hom.map g hg hk h = pullbackFiberOfHom f g k h := rfl

/-- Two morphisms into the chosen pullback of `x` along `g` agree once they agree after composing
with the chosen cartesian lift. -/
private theorem pullbackFiber_hom_ext {x : 𝒳} {V : 𝒮} (g : V ⟶ p.obj x) {a : p.Fiber V}
    {m n : a ⟶ pullbackFiber p (fiberSelf p x) g}
    (h : Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap (fiberSelf p x).2 g =
      Fiber.fiberInclusion.map n ≫ IsPreFibered.pullbackMap (fiberSelf p x).2 g) : m = n :=
  fiber_hom_ext_of_cartesian g _ inferInstance _ _ h

/-- The morphism of fibres induced by an identity is the identity. -/
@[simp]
theorem pullbackFiberOfHom_id (x : 𝒳) {V : 𝒮} (g : V ⟶ p.obj x) (h : g ≫ p.map (𝟙 x) = g) :
    pullbackFiberOfHom (𝟙 x) g g h = 𝟙 _ := by
  refine pullbackFiber_hom_ext g ?_
  simp

/-- The morphisms of fibres induced by a composite compose. -/
theorem pullbackFiberOfHom_comp {x y z : 𝒳} (f : x ⟶ y) (f' : y ⟶ z) {V : 𝒮} (g : V ⟶ p.obj x)
    (k : V ⟶ p.obj z) (h : g ≫ p.map (f ≫ f') = k) (h₂ : (g ≫ p.map f) ≫ p.map f' = k) :
    pullbackFiberOfHom (f ≫ f') g k h =
      pullbackFiberOfHom f g (g ≫ p.map f) rfl ≫ pullbackFiberOfHom f' (g ≫ p.map f) k h₂ := by
  refine pullbackFiber_hom_ext k ?_
  simp

/-- **The 1-morphism from `𝒳` into the third stage**: an object goes to the descent pair formed by
its chosen pullbacks along the maximal sieve, and a morphism to the induced morphisms of fibres. -/
@[simps! obj, implicit_reducible]
noncomputable def toDescentPair (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) :
    𝒳 ⥤ DescentPair p J where
  obj x := DescentPair.ofObj p J x
  map f := DescentMor.mk (DescentPairData.ofHom f)
  map_id x := by
    refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (p.map_id x) ?_)
    intro V g hg hg' k hk h h'
    obtain rfl := (comp_id g).symm.trans h'
    simp [DescentPairData.id, DescentPairHom.id]
  map_comp {x y z} f f' := by
    refine (DescentMor.mk_eq_iff _ _).mpr
      (DescentPairData.rel_of_agree (p.map_comp f f') ?_)
    intro V g hg hg' k hk h h'
    refine Eq.trans ?_ (DescentPairData.comp_hom_map (DescentPairData.ofHom f)
      (DescentPairData.ofHom f') g trivial trivial hk ((assoc _ _ _).trans h') _ _).symm
    exact pullbackFiberOfHom_comp f f' g k h ((assoc _ _ _).trans h')

/-- **The 1-morphism into the third stage is strictly over the base.** -/
theorem toDescentPair_comp_descentPairProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    (J : GrothendieckTopology 𝒮) : toDescentPair p J ⋙ p.descentPairProj J = p :=
  Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-! #### The 1-morphism preserves strongly cartesian morphisms -/

/-- The factorisation, through a strongly cartesian `φ : x ⟶ y`, of a morphism of the fibre over
`V` into the chosen pullback of `y` along `k ≫ p.map φ`. -/
noncomputable def fiberLiftOfCartesian {x y : 𝒳} (φ : x ⟶ y) [p.IsStronglyCartesian (p.map φ) φ]
    {V : 𝒮} {a : p.Fiber V} (k : V ⟶ p.obj x)
    (m : a ⟶ pullbackFiber p (fiberSelf p y) (k ≫ p.map φ)) :
    a ⟶ pullbackFiber p (fiberSelf p x) k :=
  have : p.IsCartesian (k ≫ p.map φ) (IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ) :=
    inferInstance
  have : p.IsHomLift (k ≫ p.map φ) (Fiber.fiberInclusion.map m ≫
      IsPreFibered.pullbackMap (fiberSelf p y).2 (k ≫ p.map φ)) := inferInstance
  ⟨IsCartesian.map p (k ≫ p.map φ) (IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ)
      (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap (fiberSelf p y).2 (k ≫ p.map φ)),
    IsCartesian.map_isHomLift p (k ≫ p.map φ) _ _⟩

/-- The equation that determines `CategoryTheory.Functor.fiberLiftOfCartesian`. -/
@[reassoc (attr := simp)]
theorem fiberLiftOfCartesian_fac {x y : 𝒳} (φ : x ⟶ y) [p.IsStronglyCartesian (p.map φ) φ]
    {V : 𝒮} {a : p.Fiber V} (k : V ⟶ p.obj x)
    (m : a ⟶ pullbackFiber p (fiberSelf p y) (k ≫ p.map φ)) :
    Fiber.fiberInclusion.map (fiberLiftOfCartesian φ k m) ≫
        IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ =
      Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 (k ≫ p.map φ) :=
  have : p.IsCartesian (k ≫ p.map φ) (IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ) :=
    inferInstance
  have : p.IsHomLift (k ≫ p.map φ) (Fiber.fiberInclusion.map m ≫
      IsPreFibered.pullbackMap (fiberSelf p y).2 (k ≫ p.map φ)) := inferInstance
  IsCartesian.fac p (k ≫ p.map φ) (IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ) _

/-- `CategoryTheory.Functor.fiberLiftOfCartesian` is the only morphism of the fibre satisfying
`CategoryTheory.Functor.fiberLiftOfCartesian_fac`. -/
theorem fiberLiftOfCartesian_uniq {x y : 𝒳} (φ : x ⟶ y) [p.IsStronglyCartesian (p.map φ) φ]
    {V : 𝒮} {a : p.Fiber V} (k : V ⟶ p.obj x)
    (m : a ⟶ pullbackFiber p (fiberSelf p y) (k ≫ p.map φ))
    (n : a ⟶ pullbackFiber p (fiberSelf p x) k)
    (hn : Fiber.fiberInclusion.map n ≫ IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ =
      Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 (k ≫ p.map φ)) :
    n = fiberLiftOfCartesian φ k m := by
  have hc : p.IsCartesian (k ≫ p.map φ)
      (IsPreFibered.pullbackMap (fiberSelf p x).2 k ≫ φ) := inferInstance
  refine fiber_hom_ext_of_cartesian (k ≫ p.map φ) _ hc _ _ ?_
  rw [hn, fiberLiftOfCartesian_fac]

/-- The factorisation of a morphism of descent pairs into the pair of `y` through the image of a
strongly cartesian `φ : x ⟶ y`: apply `CategoryTheory.Functor.fiberLiftOfCartesian` to each of the
morphisms of fibres making it up. -/
noncomputable def DescentPairHom.liftOfCartesian {x y : 𝒳} (φ : x ⟶ y)
    [p.IsStronglyCartesian (p.map φ) φ] {A' : DescentPair p J}
    (Y : DescentPairData A' (DescentPair.ofObj p J y)) (w : A'.pt ⟶ p.obj x)
    (hbase : Y.base = w ≫ p.map φ) : DescentPairHom A' (DescentPair.ofObj p J x) w where
  sieve := Y.hom.sieve
  sieve_mem := Y.hom.sieve_mem
  le_dom := Y.hom.le_dom
  mem_cod := fun _ _ _ ↦ trivial
  map := fun _ g hg k _ h ↦
    fiberLiftOfCartesian φ k (Y.hom.map g hg (g := k ≫ p.map φ) trivial
      ((congrArg (g ≫ ·) hbase).trans
        ((assoc g w (p.map φ)).symm.trans (congrArg (· ≫ p.map φ) h))))
  map_glue := fun _ _ _ g hg g' hg' k _ h k' _ h' ε ε' heq ↦ by
    have pfk : g ≫ Y.base = k ≫ p.map φ :=
      (congrArg (g ≫ ·) hbase).trans
        ((assoc g w (p.map φ)).symm.trans (congrArg (· ≫ p.map φ) h))
    have pfk' : g' ≫ Y.base = k' ≫ p.map φ :=
      (congrArg (g' ≫ ·) hbase).trans
        ((assoc g' w (p.map φ)).symm.trans (congrArg (· ≫ p.map φ) h'))
    have hcart : p.IsCartesian ((ε' ≫ k') ≫ p.map φ)
        (IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p x) k').2 ε' ≫
          IsPreFibered.pullbackMap (fiberSelf p x).2 k' ≫ φ) := by
      have h0 : p.IsCartesian (ε' ≫ k' ≫ p.map φ)
          (IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p x) k').2 ε' ≫
            IsPreFibered.pullbackMap (fiberSelf p x).2 k' ≫ φ) := inferInstance
      rwa [← assoc] at h0
    refine fiber_hom_ext_of_cartesian ((ε' ≫ k') ≫ p.map φ) _ hcart _ _ ?_
    have hY := congrArg (fun t ↦ Fiber.fiberInclusion.map t ≫
        IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p y) (k' ≫ p.map φ)).2 ε' ≫
          IsPreFibered.pullbackMap (fiberSelf p y).2 (k' ≫ p.map φ))
      (Y.hom.map_glue g hg g' hg' (g := k ≫ p.map φ) trivial pfk (g' := k' ≫ p.map φ) trivial pfk'
        ε ε' heq)
    simp only [SieveDescentDatum.ofFiber_iso, Functor.map_comp, Category.assoc,
      pullbackFiberComparison_hom_fac, pullbackFiberComparison_hom_fac_assoc,
      pullbackFiberHom_fac_assoc, fiberLiftOfCartesian_fac] at hY ⊢
    exact hY

/-- The factorisation of a morphism of descent pairs through the image of a strongly cartesian
morphism, bundled with the morphism of the base it lies over. -/
@[implicit_reducible]
noncomputable def DescentPairData.liftOfCartesian {x y : 𝒳} (φ : x ⟶ y)
    [p.IsStronglyCartesian (p.map φ) φ] {A' : DescentPair p J}
    (Y : DescentPairData A' (DescentPair.ofObj p J y)) (w : A'.pt ⟶ p.obj x)
    (hbase : Y.base = w ≫ p.map φ) : DescentPairData A' (DescentPair.ofObj p J x) :=
  ⟨w, DescentPairHom.liftOfCartesian φ Y w hbase⟩

/-- The lift of `Y` through the cartesian morphism `φ` lies over `w`. -/
@[simp]
theorem DescentPairData.liftOfCartesian_base {x y : 𝒳} (φ : x ⟶ y)
    [p.IsStronglyCartesian (p.map φ) φ] {A' : DescentPair p J}
    (Y : DescentPairData A' (DescentPair.ofObj p J y)) (w : A'.pt ⟶ p.obj x)
    (hbase : Y.base = w ≫ p.map φ) : (DescentPairData.liftOfCartesian φ Y w hbase).base = w := rfl

/-- The morphism of fibres the lift of `Y` through `φ` attaches to an arrow `g` is the lift through
`φ` of the one `Y` attaches to `g`. -/
theorem DescentPairData.liftOfCartesian_hom_map {x y : 𝒳} (φ : x ⟶ y)
    [p.IsStronglyCartesian (p.map φ) φ] {A' : DescentPair p J}
    (Y : DescentPairData A' (DescentPair.ofObj p J y)) (w : A'.pt ⟶ p.obj x)
    (hbase : Y.base = w ≫ p.map φ) {V : 𝒮} (g : V ⟶ A'.pt) (hg : Y.hom.sieve.arrows g)
    (k : V ⟶ p.obj x) (hk : (⊤ : Sieve (p.obj x)).arrows k) (h : g ≫ w = k)
    (pf : g ≫ Y.base = k ≫ p.map φ) :
    (liftOfCartesian φ Y w hbase).hom.map g hg hk h =
      fiberLiftOfCartesian φ k (Y.hom.map g hg (g := k ≫ p.map φ) trivial pf) := rfl

/-- **`toDescentPair` preserves strongly cartesian morphisms.** The factorisation of a morphism of
descent pairs is obtained by factoring each of the morphisms of fibres making it up through `φ`,
and it is unique because each of those factorisations is. -/
theorem isStronglyCartesian_toDescentPair_map {R S : 𝒮} (f : R ⟶ S) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : p.IsStronglyCartesian f φ) :
    (p.descentPairProj J).IsStronglyCartesian f ((toDescentPair p J).map φ) := by
  have := hφ
  subst_hom_lift p f φ
  have hlift : (p.descentPairProj J).IsHomLift (p.map φ) ((toDescentPair p J).map φ) :=
    DescentMor.isHomLift_mk (DescentPairData.ofHom (p := p) (J := J) φ)
  refine { toIsHomLift := hlift, universal_property' := ?_ }
  intro A' w Ψ hΨ
  obtain ⟨Y, rfl⟩ := DescentMor.exists_rep Ψ
  have hbase : Y.base = w ≫ p.map φ := DescentMor.base_eq_of_isHomLift Y hΨ
  refine ⟨DescentMor.mk (DescentPairData.liftOfCartesian φ Y w hbase),
    ⟨DescentMor.isHomLift_mk (DescentPairData.liftOfCartesian φ Y w hbase), ?_⟩, ?_⟩
  · refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree hbase.symm ?_)
    intro V g hf hf' k hk h h'
    obtain rfl : (g ≫ w) ≫ p.map φ = k := (assoc g w (p.map φ)).trans h
    refine Eq.trans (DescentPairData.comp_hom_map _ (DescentPairData.ofHom φ) g hf.1 trivial hk
      rfl _ _) ?_
    rw [DescentPairData.liftOfCartesian_hom_map φ Y w hbase g hf.1 (g ≫ w) trivial rfl
      (comp_eq_comp_of_eq_comp hbase rfl)]
    refine pullbackFiber_hom_ext ((g ≫ w) ≫ p.map φ) ?_
    simp
  · rintro X' ⟨hX'₁, hX'₂⟩
    obtain ⟨Z, rfl⟩ := DescentMor.exists_rep X'
    obtain ⟨_, T, hT, k₁, k₂, kagree⟩ := (DescentMor.mk_eq_iff _ _).mp hX'₂
    refine (DescentMor.mk_eq_iff _ _).mpr
      ⟨DescentMor.base_eq_of_isHomLift Z hX'₁, T, hT, fun _ _ hf ↦ (k₁ _ hf).1, k₂,
        fun _ g hf k hk h h' ↦ ?_⟩
    obtain rfl : g ≫ Z.base = k := h
    have pf : g ≫ Y.base = (g ≫ Z.base) ≫ p.map φ := comp_eq_comp_of_eq_comp hbase h'
    rw [DescentPairData.liftOfCartesian_hom_map φ Y w hbase g (k₂ _ hf) (g ≫ Z.base) hk h' pf]
    refine fiberLiftOfCartesian_uniq φ (g ≫ Z.base) _ _ ?_
    have hZ := kagree g hf (g := (g ≫ Z.base) ≫ p.map φ) trivial
      (assoc g Z.base (p.map φ)).symm pf
    rw [DescentPairData.comp_hom_map Z (DescentPairData.ofHom φ) g ((k₁ _ hf).1) trivial trivial
      rfl _ _] at hZ
    have hkey := congrArg (fun t ↦ Fiber.fiberInclusion.map t ≫
      IsPreFibered.pullbackMap (fiberSelf p y).2 ((g ≫ Z.base) ≫ p.map φ)) hZ
    simpa using hkey

/-- **The 1-morphism into the third stage is a 1-morphism of fibred categories over `𝒮`**: it is
strictly over the base and preserves strongly cartesian morphisms. -/
theorem isFibredOneMorphism_toDescentPair (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    (J : GrothendieckTopology 𝒮) :
    IsFibredOneMorphism p (p.descentPairProj J) (toDescentPair p J) where
  comp_eq := toDescentPair_comp_descentPairProj p J
  map_isStronglyCartesian := by
    intro R T f a b φ h
    exact isStronglyCartesian_toDescentPair_map f φ h

end OfObj

/-! ### The third stage of the stackification -/

/-- **The third stage of the construction of the stackification of a fibred category**: the objects
that descent data prescribe are adjoined to the second stage.

This is *not* Stacks 02ZN: that the result is a stack — that its morphism presheaves are still
sheaves and that every descent datum in it is effective — is not proved here. See the list of
obligations in the module docstring. -/
abbrev StageThree (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) : Type _ :=
  DescentPair (p.stageTwoProj J) J

/-- The structure functor of the third stage. -/
abbrev stageThreeProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) :
    p.StageThree J ⥤ 𝒮 :=
  descentPairProj (p.stageTwoProj J) J

/-- The 1-morphism from `𝒳` to the third stage: the composite of all three stages. -/
noncomputable def toStageThree (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) :
    𝒳 ⥤ p.StageThree J :=
  p.toStageTwo J ⋙ toDescentPair (p.stageTwoProj J) J

/-- The 1-morphism to the third stage is *strictly* over the base. -/
theorem toStageThree_comp_stageThreeProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    (J : GrothendieckTopology 𝒮) : p.toStageThree J ⋙ p.stageThreeProj J = p := by
  rw [toStageThree, Functor.assoc, toDescentPair_comp_descentPairProj,
    toStageTwo_comp_stageTwoProj]

/-- **The structure functor of the third stage is fibred.** -/
instance isFibered_stageThreeProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) :
    (p.stageThreeProj J).IsFibered :=
  isFibered_descentPairProj

/-- **The 1-morphism to the third stage is a 1-morphism of fibred categories over `𝒮`.** -/
theorem isFibredOneMorphism_toStageThree (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    (J : GrothendieckTopology 𝒮) :
    IsFibredOneMorphism p (p.stageThreeProj J) (p.toStageThree J) :=
  (isFibredOneMorphism_toStageTwo p J).comp
    (isFibredOneMorphism_toDescentPair (p.stageTwoProj J) J)

end CategoryTheory.Functor
