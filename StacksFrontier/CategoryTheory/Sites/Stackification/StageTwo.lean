module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageOne

/-! # Adjoining the locally defined morphisms

Let `p : 𝒳 ⥤ 𝒮` be a category over a site `(𝒮, J)`. A *locally defined morphism* from `x` to `y`
consists of a morphism `u : p.obj x ⟶ p.obj y` of the base, a covering sieve `R` of `p.obj x`, and
a morphism `a(φ) : w ⟶ y` lying over `p.map φ ≫ u` for every morphism `φ : w ⟶ x` of `𝒳` whose
image lies in `R`, compatibly with precomposition. Two such data are identified when they agree on
a common covering sieve. This is the plus construction applied to the presheaves of morphisms of
`𝒳` lying over a fixed morphism of the base: the base morphism `u` is a global datum, while the
morphism above it is given only locally.

The objects of `𝒳` and the locally defined morphisms between them form a category
`CategoryTheory.Functor.MorPlus p J` over `𝒮`, and `𝒳` maps into it by
`CategoryTheory.Functor.toMorPlus`. The construction quantifies over *all* morphisms of `𝒳` into
`x` lying over a member of the covering sieve, exactly as `CategoryTheory.Functor.LocallyEqual`
does; for a fibred category this is no stronger than the formulation in terms of the chosen
restrictions, because every morphism into `x` over a member of the sieve factors through a
strongly cartesian one.

## Main definitions

* `CategoryTheory.Functor.LocalHom`: the datum of a locally defined morphism.
* `CategoryTheory.Functor.LocalMor`: locally defined morphisms modulo agreement on a covering
  sieve; the morphisms of `MorPlus`.
* `CategoryTheory.Functor.MorPlus`: the category of objects of `𝒳` and locally defined morphisms.
* `CategoryTheory.Functor.morPlusProj`: its structure functor to `𝒮`.
* `CategoryTheory.Functor.toMorPlus`: the functor from `𝒳`, sending a morphism to itself viewed
  as a locally defined morphism on the maximal sieve.
* `CategoryTheory.Functor.StageTwo`: the above applied to the separated quotient of `𝒳` by local
  equality of morphisms.

## Main results

* `CategoryTheory.Functor.toMorPlus_comp_morPlusProj`: `toMorPlus` is *strictly* over `𝒮`.
* `CategoryTheory.Functor.isStronglyCartesian_toMorPlus_map`: `toMorPlus` preserves strongly
  cartesian morphisms. This needs no fibredness hypothesis.
* `CategoryTheory.Functor.isFibered_morPlusProj`: if `p` is fibred then so is `morPlusProj`.
* `CategoryTheory.Functor.isFibredOneMorphism_toMorPlus`: the two statements above, packaged as
  the statement that `toMorPlus` is a 1-morphism of fibred categories over `𝒮`.
* `CategoryTheory.Functor.toMorPlus_map_eq_iff`: the morphism map of `toMorPlus` identifies
  exactly the locally equal morphisms.
* `CategoryTheory.Functor.toMorPlus_map_comp_toLocalMor` and
  `CategoryTheory.Functor.exists_covering_toMorPlus_map_comp`: every morphism of `MorPlus p J` is,
  locally on a covering sieve, the image of a morphism of `𝒳`.
* `CategoryTheory.Functor.locallyEqual_morPlusProj_iff`: if locally equal morphisms of `𝒳` are
  equal, then the same holds in `MorPlus p J`. This is the separatedness half of the sheaf
  condition for the morphism presheaves of `MorPlus p J`.
* `CategoryTheory.Functor.exists_amalgamation_morPlusProj`: the gluing half of that sheaf
  condition. A family of morphisms of `MorPlus p J` indexed by the morphisms lying over a covering
  sieve, all lying over a single morphism of the base and compatible with restriction, has an
  amalgamation. Separatedness of the morphism presheaves of `𝒳` is a hypothesis, and
  `CategoryTheory.Functor.exists_amalgamation_stageTwoProj` supplies it from the first stage.
* `CategoryTheory.Functor.faithful_toMorPlus_bot` and
  `CategoryTheory.Functor.full_toMorPlus_bot`: for the trivial topology `toMorPlus` is fully
  faithful, so the construction does nothing when the topology is trivial.
* `CategoryTheory.Functor.toStageTwo_map_eq_iff` and
  `CategoryTheory.Functor.exists_isHomLift_id_iso_toStageTwo_obj`: the two clauses of
  Stacks 02ZN for the composite of the first two stages, in the form available at this point —
  the morphism map identifies exactly the locally equal morphisms, and every object is in the
  essential image by an isomorphism over an identity.

## Obligations that remain before Stacks 02ZN

The following are **not** proved here, and no declaration here should be read as claiming them.

That the morphism presheaves of `MorPlus p J` are *sheaves* is proved, in the formulation in terms
of sieves used throughout this file: `CategoryTheory.Functor.locallyEqual_morPlusProj_iff` is
separatedness and `CategoryTheory.Functor.exists_amalgamation_morPlusProj` is gluing. What remains
is the following.

1. The identification of the morphism sets of `MorPlus p J` with the sheafification of
   `CategoryTheory.Functor.morPresheaf` for `𝒳`, that is, the translation of the sheaf condition
   just mentioned, together with `CategoryTheory.Functor.toStageTwo_map_eq_iff` (local injectivity)
   and `CategoryTheory.Functor.exists_covering_toMorPlus_map_comp` (local surjectivity), into the
   language of presheaves on `Over U` in which `CategoryTheory.Functor.IsMorSheaf` is phrased. Only
   with that translation does clause (1) of Stacks 02ZN follow for the composite of the first two
   stages.
2. Stage three: the category of pairs (covering sieve, descent datum), and that the result is a
   stack in the sense of `CategoryTheory.Functor.IsStack`.
3. The composite 1-morphism `G : 𝒮 ⥤ 𝒮'` and clauses (1) and (2) of Stacks 02ZN for it, and
   uniqueness of the stackification up to unique 2-isomorphism.

## References

This is the second stage of the proof of Stacks 02ZN, applied in
`CategoryTheory.Functor.StageTwo` to the separated quotient produced by the first stage.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- A *locally defined morphism* from `x` to `y` with respect to a topology `J` on the base: a
morphism `base : p.obj x ⟶ p.obj y` of the base, a covering sieve `sieve` of `p.obj x`, and for
each morphism `φ : w ⟶ x` of `𝒳` whose image lies in `sieve` a morphism `map φ : w ⟶ y` lying
over `p.map φ ≫ base`, compatibly with precomposition. -/
structure LocalHom (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x y : 𝒳) where
  /-- The morphism of the base that the locally defined morphism lies over. -/
  base : p.obj x ⟶ p.obj y
  /-- The sieve on which the morphism is defined. -/
  sieve : Sieve (p.obj x)
  /-- The defining sieve is a covering sieve. -/
  sieve_mem : sieve ∈ J (p.obj x)
  /-- The morphism assigned to each restriction of `x` along a member of the defining sieve. -/
  map : ∀ {w : 𝒳} (φ : w ⟶ x), sieve.arrows (p.map φ) → (w ⟶ y)
  /-- Each assigned morphism lies over `base`, precomposed with the restriction. -/
  map_base : ∀ {w : 𝒳} (φ : w ⟶ x) (hφ : sieve.arrows (p.map φ)),
    p.map (map φ hφ) = p.map φ ≫ base
  /-- The assigned morphisms are compatible with further restriction. -/
  map_precomp : ∀ {w w' : 𝒳} (χ : w' ⟶ w) (φ : w ⟶ x) (hφ : sieve.arrows (p.map φ))
    (hχφ : sieve.arrows (p.map (χ ≫ φ))), map (χ ≫ φ) hχφ = χ ≫ map φ hφ

variable {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

namespace LocalHom

/-- The defining sieve of a locally defined morphism is stable under precomposition. -/
theorem mem_sieve_precomp {x y : 𝒳} (a : LocalHom p J x y) {w w' : 𝒳} (χ : w' ⟶ w) (φ : w ⟶ x)
    (hφ : a.sieve.arrows (p.map φ)) : a.sieve.arrows (p.map (χ ≫ φ)) := by
  rw [p.map_comp]
  exact a.sieve.downward_closed hφ _

/-- The morphism assigned to `φ` lies over `p.map φ ≫ base`. -/
theorem isHomLift_map {x y : 𝒳} (a : LocalHom p J x y) {w : 𝒳} (φ : w ⟶ x)
    (hφ : a.sieve.arrows (p.map φ)) : p.IsHomLift (p.map φ ≫ a.base) (a.map φ hφ) := by
  rw [← a.map_base φ hφ]
  infer_instance

/-- The morphism assigned to `φ` depends only on `φ`, not on the proof that its image lies in the
defining sieve. -/
theorem map_congr {x y : 𝒳} (a : LocalHom p J x y) {w : 𝒳} {φ φ' : w ⟶ x}
    (hφ : a.sieve.arrows (p.map φ)) (hφ' : a.sieve.arrows (p.map φ')) (h : φ = φ') :
    a.map φ hφ = a.map φ' hφ' := by
  subst h; rfl

/-- If the image of `φ` lies in the defining sieve of `a`, and `p.map φ ≫ a.base` lies in the
defining sieve of `b`, then the image of `a.map φ` lies in the defining sieve of `b`. -/
theorem mem_sieve_map {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) {w : 𝒳}
    (φ : w ⟶ x) (hφ : a.sieve.arrows (p.map φ)) (hb : b.sieve.arrows (p.map φ ≫ a.base)) :
    b.sieve.arrows (p.map (a.map φ hφ)) := by
  rw [a.map_base]; exact hb

/-! ### Agreement on a sieve -/

/-- Two locally defined morphisms *agree on* a sieve `T` if every morphism into `x` whose image
lies in `T` also lies in both defining sieves and is assigned the same morphism by both. -/
def AgreeOn {x y : 𝒳} (a b : LocalHom p J x y) (T : Sieve (p.obj x)) : Prop :=
  ∀ {w : 𝒳} (φ : w ⟶ x), T.arrows (p.map φ) →
    ∃ (ha : a.sieve.arrows (p.map φ)) (hb : b.sieve.arrows (p.map φ)), a.map φ ha = b.map φ hb

/-- Agreement passes to smaller sieves. -/
theorem AgreeOn.mono {x y : 𝒳} {a b : LocalHom p J x y} {T T' : Sieve (p.obj x)}
    (h : a.AgreeOn b T) (hT : T' ≤ T) : a.AgreeOn b T' :=
  fun φ hφ ↦ h φ (hT _ hφ)

/-- Agreement is symmetric. -/
theorem AgreeOn.symm {x y : 𝒳} {a b : LocalHom p J x y} {T : Sieve (p.obj x)}
    (h : a.AgreeOn b T) : b.AgreeOn a T := by
  intro w φ hφ
  obtain ⟨ha, hb, e⟩ := h φ hφ
  exact ⟨hb, ha, e.symm⟩

/-- Agreement is transitive, on the intersection of the two witnessing sieves. -/
theorem AgreeOn.trans {x y : 𝒳} {a b c : LocalHom p J x y} {T T' : Sieve (p.obj x)}
    (hab : a.AgreeOn b T) (hbc : b.AgreeOn c T') : a.AgreeOn c (T ⊓ T') := by
  intro w φ hφ
  obtain ⟨ha, hb, e₁⟩ := hab φ hφ.1
  obtain ⟨hb', hc, e₂⟩ := hbc φ hφ.2
  exact ⟨ha, hc, e₁.trans e₂⟩

/-- Two locally defined morphisms are identified if they lie over the same morphism of the base
and agree on a covering sieve. -/
def Rel {x y : 𝒳} (a b : LocalHom p J x y) : Prop :=
  a.base = b.base ∧ ∃ T ∈ J (p.obj x), a.AgreeOn b T

/-- Identified locally defined morphisms lie over the same morphism of the base. -/
theorem Rel.base_eq {x y : 𝒳} {a b : LocalHom p J x y} (h : a.Rel b) : a.base = b.base := h.1

/-- To identify two locally defined morphisms it suffices to check that they lie over the same
morphism of the base and agree on the intersection of their defining sieves. -/
theorem rel_of_agreeOn {x y : 𝒳} {a b : LocalHom p J x y} (hbase : a.base = b.base)
    (h : a.AgreeOn b (a.sieve ⊓ b.sieve)) : a.Rel b :=
  ⟨hbase, _, J.intersection_covering a.sieve_mem b.sieve_mem, h⟩

/-- Identification of locally defined morphisms is reflexive. -/
@[refl]
theorem Rel.refl {x y : 𝒳} (a : LocalHom p J x y) : a.Rel a :=
  ⟨rfl, a.sieve, a.sieve_mem, fun _ h ↦ ⟨h, h, rfl⟩⟩

/-- Identification of locally defined morphisms is symmetric. -/
theorem Rel.symm {x y : 𝒳} {a b : LocalHom p J x y} (h : a.Rel b) : b.Rel a := by
  obtain ⟨hbase, T, hT, hagree⟩ := h
  exact ⟨hbase.symm, T, hT, AgreeOn.symm hagree⟩

/-- Identification of locally defined morphisms is transitive. -/
theorem Rel.trans {x y : 𝒳} {a b c : LocalHom p J x y} (hab : a.Rel b) (hbc : b.Rel c) :
    a.Rel c := by
  obtain ⟨h₁, T, hT, h⟩ := hab
  obtain ⟨h₂, T', hT', h'⟩ := hbc
  exact ⟨h₁.trans h₂, T ⊓ T', J.intersection_covering hT hT', AgreeOn.trans h h'⟩

/-- Locally defined morphisms from `x` to `y`, up to agreement on a covering sieve. -/
instance setoid (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x y : 𝒳) :
    _root_.Setoid (LocalHom p J x y) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-! ### Identities, composition, and honest morphisms -/

/-- The identity, viewed as a locally defined morphism on the maximal sieve. -/
def id (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x : 𝒳) : LocalHom p J x x where
  base := 𝟙 (p.obj x)
  sieve := ⊤
  sieve_mem := J.top_mem _
  map φ _ := φ
  map_base φ _ := by simp
  map_precomp _ _ _ _ := rfl

/-- The identity locally defined morphism lies over the identity of `p.obj x`. -/
@[simp]
theorem id_base (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x : 𝒳) :
    (LocalHom.id p J x).base = 𝟙 (p.obj x) := rfl

/-- The identity locally defined morphism is defined on the maximal sieve. -/
@[simp]
theorem id_sieve (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x : 𝒳) :
    (LocalHom.id p J x).sieve = ⊤ := rfl

/-- A morphism of `𝒳`, viewed as a locally defined morphism on the maximal sieve. -/
def ofHom {x y : 𝒳} (f : x ⟶ y) : LocalHom p J x y where
  base := p.map f
  sieve := ⊤
  sieve_mem := J.top_mem _
  map φ _ := φ ≫ f
  map_base φ _ := by rw [p.map_comp]
  map_precomp χ φ _ _ := by rw [assoc]

/-- The locally defined morphism `ofHom f` lies over `p.map f`. -/
@[simp]
theorem ofHom_base {x y : 𝒳} (f : x ⟶ y) : (ofHom f : LocalHom p J x y).base = p.map f := rfl

/-- The locally defined morphism `ofHom f` is defined on the maximal sieve. -/
@[simp]
theorem ofHom_sieve {x y : 𝒳} (f : x ⟶ y) : (ofHom f : LocalHom p J x y).sieve = ⊤ := rfl

/-- The composite of two locally defined morphisms: it is defined on the intersection of the
defining sieve of the first with the pullback, along its base, of the defining sieve of the
second. -/
def comp {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) : LocalHom p J x z where
  base := a.base ≫ b.base
  sieve := a.sieve ⊓ b.sieve.pullback a.base
  sieve_mem := J.intersection_covering a.sieve_mem (J.pullback_stable _ b.sieve_mem)
  map φ hφ := b.map (a.map φ hφ.1) (a.mem_sieve_map b φ hφ.1 hφ.2)
  map_base φ hφ := by rw [b.map_base, a.map_base, assoc]
  map_precomp χ φ hφ hχφ := by
    have hkey : b.sieve.arrows (p.map (χ ≫ a.map φ hφ.1)) := by
      rw [← a.map_precomp χ φ hφ.1 hχφ.1]
      exact a.mem_sieve_map b (χ ≫ φ) hχφ.1 hχφ.2
    exact (b.map_congr _ hkey (a.map_precomp χ φ hφ.1 hχφ.1)).trans
      (b.map_precomp χ (a.map φ hφ.1) (a.mem_sieve_map b φ hφ.1 hφ.2) hkey)

/-- The composite of locally defined morphisms lies over the composite of their bases. -/
@[simp]
theorem comp_base {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) :
    (a.comp b).base = a.base ≫ b.base := rfl

/-- The defining sieve of `a.comp b` is `a.sieve ⊓ b.sieve.pullback a.base`. -/
@[simp]
theorem comp_sieve {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) :
    (a.comp b).sieve = a.sieve ⊓ b.sieve.pullback a.base := rfl

/-- The composite `a.comp b` assigns to `φ` the morphism `b` assigns to `a.map φ`. -/
theorem comp_map {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) {w : 𝒳} (φ : w ⟶ x)
    (h : (a.comp b).sieve.arrows (p.map φ)) (h₁ : a.sieve.arrows (p.map φ))
    (h₂ : b.sieve.arrows (p.map (a.map φ h₁))) :
    (a.comp b).map φ h = b.map (a.map φ h₁) h₂ := rfl

/-- A locally defined morphism whose defining sieve contains the identity is identified with an
honest morphism of `𝒳`, namely with the one it assigns to the identity. -/
theorem rel_ofHom_map_id {x y : 𝒳} (a : LocalHom p J x y)
    (h : a.sieve.arrows (p.map (𝟙 x))) : a.Rel (ofHom (a.map (𝟙 x) h)) :=
  rel_of_agreeOn (by simp [a.map_base (𝟙 x) h]) fun φ hφ ↦
    ⟨hφ.1, hφ.2, (a.map_congr hφ.1 (a.mem_sieve_precomp φ (𝟙 x) h) (comp_id φ).symm).trans
      (a.map_precomp φ (𝟙 x) h (a.mem_sieve_precomp φ (𝟙 x) h))⟩

/-- Composition of locally defined morphisms respects their identification. -/
theorem Rel.comp {x y z : 𝒳} {a a' : LocalHom p J x y} {b b' : LocalHom p J y z}
    (ha : a.Rel a') (hb : b.Rel b') : (a.comp b).Rel (a'.comp b') := by
  obtain ⟨habase, T, hT, hTa⟩ := ha
  obtain ⟨hbbase, U, hU, hUb⟩ := hb
  refine ⟨by rw [comp_base, comp_base, habase, hbbase], T ⊓ U.pullback a.base,
    J.intersection_covering hT (J.pullback_stable _ hU), ?_⟩
  intro w φ hφ
  obtain ⟨h₁, h₂, e⟩ := hTa φ hφ.1
  have hUα : U.arrows (p.map (a.map φ h₁)) := by rw [a.map_base]; exact hφ.2
  obtain ⟨k₁, k₂, f⟩ := hUb (a.map φ h₁) hUα
  have hb₁ : b.sieve.arrows (p.map φ ≫ a.base) := by rw [← a.map_base φ h₁]; exact k₁
  have hb₂ : b'.sieve.arrows (p.map φ ≫ a'.base) := by
    rw [← habase, ← a.map_base φ h₁]; exact k₂
  have k₂' : b'.sieve.arrows (p.map (a'.map φ h₂)) := by rw [← e]; exact k₂
  refine ⟨⟨h₁, hb₁⟩, ⟨h₂, hb₂⟩, ?_⟩
  exact ((comp_map a b φ _ h₁ k₁).trans (f.trans (b'.map_congr k₂ k₂' e))).trans
    (comp_map a' b' φ _ h₂ k₂').symm

end LocalHom

/-! ### The morphisms of the second stage -/

/-- Locally defined morphisms from `x` to `y`, up to agreement on a covering sieve. These are the
morphisms of `CategoryTheory.Functor.MorPlus`. -/
abbrev LocalMor (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x y : 𝒳) : Type _ :=
  _root_.Quotient (LocalHom.setoid p J x y)

/-- The class of a locally defined morphism modulo agreement on a covering sieve. -/
abbrev LocalHom.toLocalMor {x y : 𝒳} (a : LocalHom p J x y) : LocalMor p J x y :=
  _root_.Quotient.mk _ a

/-- Every class of locally defined morphisms is the class of a locally defined morphism. -/
theorem LocalMor.exists_rep {x y : 𝒳} (F : LocalMor p J x y) :
    ∃ a : LocalHom p J x y, a.toLocalMor = F :=
  _root_.Quotient.exists_rep F

/-- Two locally defined morphisms have the same class exactly when they are identified. -/
theorem LocalHom.toLocalMor_eq_iff {x y : 𝒳} (a b : LocalHom p J x y) :
    a.toLocalMor = b.toLocalMor ↔ a.Rel b :=
  _root_.Quotient.eq

/-- Identified locally defined morphisms have the same class. -/
theorem LocalHom.Rel.toLocalMor_eq {x y : 𝒳} {a b : LocalHom p J x y} (h : a.Rel b) :
    a.toLocalMor = b.toLocalMor :=
  _root_.Quotient.sound h

namespace LocalMor

/-- The identity as a class of locally defined morphisms. -/
def id (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (x : 𝒳) : LocalMor p J x x :=
  (LocalHom.id p J x).toLocalMor

/-- Composition of classes of locally defined morphisms. -/
def comp {x y z : 𝒳} : LocalMor p J x y → LocalMor p J y z → LocalMor p J x z :=
  _root_.Quotient.lift₂ (fun a b ↦ (a.comp b).toLocalMor)
    fun _ _ _ _ ha hb ↦ LocalHom.Rel.toLocalMor_eq (LocalHom.Rel.comp ha hb)

/-- The base morphism of a class of locally defined morphisms. -/
def base {x y : 𝒳} (F : LocalMor p J x y) : p.obj x ⟶ p.obj y :=
  _root_.Quotient.liftOn F LocalHom.base fun _ _ h ↦ LocalHom.Rel.base_eq h

/-- The composite of two classes is the class of the composite of representatives. -/
@[simp]
theorem comp_toLocalMor {x y z : 𝒳} (a : LocalHom p J x y) (b : LocalHom p J y z) :
    comp a.toLocalMor b.toLocalMor = (a.comp b).toLocalMor := rfl

/-- The base morphism of the class of `a` is the base morphism of `a`. -/
@[simp]
theorem base_toLocalMor {x y : 𝒳} (a : LocalHom p J x y) : base a.toLocalMor = a.base := rfl

/-- The identity class is a left unit for composition. -/
theorem id_comp {x y : 𝒳} (F : LocalMor p J x y) : comp (LocalMor.id p J x) F = F := by
  obtain ⟨a, rfl⟩ := LocalMor.exists_rep F
  exact LocalHom.Rel.toLocalMor_eq
    (LocalHom.rel_of_agreeOn (by simp) fun _ h ↦ ⟨h.1, h.2, rfl⟩)

/-- The identity class is a right unit for composition. -/
theorem comp_id {x y : 𝒳} (F : LocalMor p J x y) : comp F (LocalMor.id p J y) = F := by
  obtain ⟨a, rfl⟩ := LocalMor.exists_rep F
  exact LocalHom.Rel.toLocalMor_eq
    (LocalHom.rel_of_agreeOn (by simp) fun _ h ↦ ⟨h.1, h.2, rfl⟩)

/-- Composition of classes of locally defined morphisms is associative. -/
theorem assoc {w x y z : 𝒳} (F : LocalMor p J w x) (G : LocalMor p J x y) (H : LocalMor p J y z) :
    comp (comp F G) H = comp F (comp G H) := by
  obtain ⟨a, rfl⟩ := LocalMor.exists_rep F
  obtain ⟨b, rfl⟩ := LocalMor.exists_rep G
  obtain ⟨c, rfl⟩ := LocalMor.exists_rep H
  exact LocalHom.Rel.toLocalMor_eq
    (LocalHom.rel_of_agreeOn (by simp) fun _ h ↦ ⟨h.1, h.2, rfl⟩)

end LocalMor

/-! ### The category of locally defined morphisms -/

/-- The category with the same objects as `𝒳` and the locally defined morphisms as its morphisms.
This is the second stage `𝒮²` of the construction of the stackification, once applied to the
separated quotient produced by the first stage. -/
structure MorPlus (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : Type u₂ where
  /-- The object of `𝒳` underlying an object of `MorPlus p J`. -/
  as : 𝒳

/-- `MorPlus p J` is a category, with the classes of locally defined morphisms as morphisms. -/
instance : Category (p.MorPlus J) where
  Hom A B := LocalMor p J A.as B.as
  id A := LocalMor.id p J A.as
  comp := LocalMor.comp
  id_comp := LocalMor.id_comp
  comp_id := LocalMor.comp_id
  assoc := LocalMor.assoc

namespace MorPlus

/-- Every morphism of `MorPlus p J` is the class of a locally defined morphism. -/
theorem exists_rep {A B : p.MorPlus J} (F : A ⟶ B) :
    ∃ a : LocalHom p J A.as B.as, a.toLocalMor = F :=
  LocalMor.exists_rep F

/-- The identity of `A` is the class of the identity locally defined morphism. -/
@[simp]
theorem id_eq (A : p.MorPlus J) : 𝟙 A = (LocalHom.id p J A.as).toLocalMor := rfl

end MorPlus

/-- The structure functor of `MorPlus p J`: an object goes to the image of the object of `𝒳` it
comes from, and a locally defined morphism to the morphism of the base it lies over. -/
@[implicit_reducible]
def morPlusProj (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : p.MorPlus J ⥤ 𝒮 where
  obj A := p.obj A.as
  map F := LocalMor.base F
  map_id _ := rfl
  map_comp F G := by
    obtain ⟨a, rfl⟩ := MorPlus.exists_rep F
    obtain ⟨b, rfl⟩ := MorPlus.exists_rep G
    rfl

/-- The functor from `𝒳` to `MorPlus p J`: it is the identity on objects and sends a morphism to
itself, viewed as a locally defined morphism on the maximal sieve. -/
@[implicit_reducible]
def toMorPlus (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : 𝒳 ⥤ p.MorPlus J where
  obj x := ⟨x⟩
  map f := (LocalHom.ofHom f).toLocalMor
  map_id x := LocalHom.Rel.toLocalMor_eq
    ⟨by simp, ⊤, J.top_mem _, fun φ _ ↦ ⟨trivial, trivial, comp_id φ⟩⟩
  map_comp f g := LocalHom.Rel.toLocalMor_eq
    (LocalHom.rel_of_agreeOn (by simp) fun φ hφ ↦ ⟨hφ.1, hφ.2, (assoc φ f g).symm⟩)

/-- `toMorPlus` sends an object `x` to `⟨x⟩`. -/
@[simp]
theorem toMorPlus_obj (x : 𝒳) : (p.toMorPlus J).obj x = ⟨x⟩ := rfl

/-- `toMorPlus` sends a morphism `f` to the class of `LocalHom.ofHom f`. -/
@[simp]
theorem toMorPlus_map {x y : 𝒳} (f : x ⟶ y) :
    (p.toMorPlus J).map f = (LocalHom.ofHom f).toLocalMor := rfl

/-- `morPlusProj` sends an object `A` to `p.obj A.as`. -/
@[simp]
theorem morPlusProj_obj (A : p.MorPlus J) : (p.morPlusProj J).obj A = p.obj A.as := rfl

/-- `morPlusProj` sends the class of `a` to the base morphism of `a`. -/
@[simp]
theorem morPlusProj_map_toLocalMor {A B : p.MorPlus J} (a : LocalHom p J A.as B.as) :
    (p.morPlusProj J).map (a.toLocalMor : A ⟶ B) = a.base := rfl

/-- The class of a locally defined morphism lies over the morphism of the base it is declared to
lie over. -/
theorem isHomLift_toLocalMor {A B : p.MorPlus J} (a : LocalHom p J A.as B.as) :
    (p.morPlusProj J).IsHomLift a.base (a.toLocalMor : A ⟶ B) := by
  have h : a.base = (p.morPlusProj J).map (a.toLocalMor : A ⟶ B) := rfl
  rw [h]
  infer_instance

/-- The base morphism of a locally defined morphism is the unique morphism of the base that its
class lies over. -/
theorem base_eq_of_isHomLift {A B : p.MorPlus J} (a : LocalHom p J A.as B.as)
    {f : (p.morPlusProj J).obj A ⟶ (p.morPlusProj J).obj B}
    (hf : (p.morPlusProj J).IsHomLift f (a.toLocalMor : A ⟶ B)) : a.base = f :=
  have := hf
  (IsHomLift.eq_of_isHomLift (p.morPlusProj J) f (a.toLocalMor : A ⟶ B)).symm

/-- `toMorPlus` is *strictly* over the base: no comparison isomorphism is needed. -/
theorem toMorPlus_comp_morPlusProj (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) :
    p.toMorPlus J ⋙ p.morPlusProj J = p :=
  Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-! ### Factoring a locally defined morphism through a strongly cartesian morphism -/

section Lift

variable {a' x y : 𝒳} (b : LocalHom p J a' y) (φ : x ⟶ y) (g : p.obj a' ⟶ p.obj x)
  (hbase : b.base = g ≫ p.map φ)

include hbase in
/-- The morphism assigned by `b` to a restriction lies over `p.map ρ ≫ g ≫ p.map φ`. -/
theorem isHomLift_map_of_base_eq {w : 𝒳} (ρ : w ⟶ a') (hρ : b.sieve.arrows (p.map ρ)) :
    p.IsHomLift (p.map ρ ≫ g ≫ p.map φ) (b.map ρ hρ) := by
  rw [← hbase]
  exact b.isHomLift_map ρ hρ

variable [p.IsStronglyCartesian (p.map φ) φ]

/-- The factorisation through the strongly cartesian morphism `φ` of the morphism assigned by `b`
to a restriction. -/
noncomputable def LocalHom.liftMap {w : 𝒳} (ρ : w ⟶ a') (hρ : b.sieve.arrows (p.map ρ)) :
    w ⟶ x :=
  haveI := isHomLift_map_of_base_eq b φ g hbase ρ hρ
  IsStronglyCartesian.map p (p.map φ) φ (assoc (p.map ρ) g (p.map φ)).symm (b.map ρ hρ)

/-- The factorisation `b.liftMap φ g hbase ρ hρ` lies over `p.map ρ ≫ g`. -/
instance liftMap_isHomLift {w : 𝒳} (ρ : w ⟶ a') (hρ : b.sieve.arrows (p.map ρ)) :
    p.IsHomLift (p.map ρ ≫ g) (b.liftMap φ g hbase ρ hρ) :=
  haveI := isHomLift_map_of_base_eq b φ g hbase ρ hρ
  IsStronglyCartesian.map_isHomLift p (p.map φ) φ (assoc (p.map ρ) g (p.map φ)).symm (b.map ρ hρ)

/-- The factorisation, composed with `φ`, is the morphism assigned by `b` to `ρ`. -/
theorem LocalHom.liftMap_fac {w : 𝒳} (ρ : w ⟶ a') (hρ : b.sieve.arrows (p.map ρ)) :
    b.liftMap φ g hbase ρ hρ ≫ φ = b.map ρ hρ :=
  have := isHomLift_map_of_base_eq b φ g hbase ρ hρ
  IsStronglyCartesian.fac p (p.map φ) φ (assoc (p.map ρ) g (p.map φ)).symm (b.map ρ hρ)

/-- The factorisations of the morphisms assigned by `b` are compatible with restriction. -/
theorem LocalHom.liftMap_precomp {w w' : 𝒳} (χ : w' ⟶ w) (ρ : w ⟶ a')
    (hρ : b.sieve.arrows (p.map ρ)) (hχρ : b.sieve.arrows (p.map (χ ≫ ρ))) :
    b.liftMap φ g hbase (χ ≫ ρ) hχρ = χ ≫ b.liftMap φ g hbase ρ hρ := by
  have h₁ : p.IsHomLift (p.map χ ≫ p.map ρ ≫ g) (b.liftMap φ g hbase (χ ≫ ρ) hχρ) := by
    rw [← assoc, ← p.map_comp]
    infer_instance
  have h₂ : p.IsHomLift (p.map χ ≫ p.map ρ ≫ g) (χ ≫ b.liftMap φ g hbase ρ hρ) := inferInstance
  refine IsStronglyCartesian.ext p (p.map φ) φ (p.map χ ≫ p.map ρ ≫ g) ?_
  rw [assoc, b.liftMap_fac, b.liftMap_fac]
  exact b.map_precomp χ ρ hρ hχρ

/-- Factoring a locally defined morphism `b` into `y` through a strongly cartesian morphism
`φ : x ⟶ y`, given a factorisation through `p.map φ` of the morphism of the base that `b` lies
over. -/
noncomputable def LocalHom.lift : LocalHom p J a' x where
  base := g
  sieve := b.sieve
  sieve_mem := b.sieve_mem
  map ρ hρ := b.liftMap φ g hbase ρ hρ
  map_base ρ hρ := (IsHomLift.eq_of_isHomLift p (p.map ρ ≫ g) (b.liftMap φ g hbase ρ hρ)).symm
  map_precomp χ ρ hρ hχρ := b.liftMap_precomp φ g hbase χ ρ hρ hχρ

/-- The factorisation `b.lift φ g hbase` lies over `g`. -/
@[simp]
theorem LocalHom.lift_base : (b.lift φ g hbase).base = g := rfl

/-- The factorisation `b.lift φ g hbase` is defined on the defining sieve of `b`. -/
@[simp]
theorem LocalHom.lift_sieve : (b.lift φ g hbase).sieve = b.sieve := rfl

/-- The factorisation, composed with `φ`, recovers the locally defined morphism it came from. -/
theorem LocalHom.lift_comp_ofHom : ((b.lift φ g hbase).comp (LocalHom.ofHom φ)).Rel b :=
  LocalHom.rel_of_agreeOn (by simp [hbase])
    fun ρ hρ ↦ ⟨hρ.1, hρ.2, b.liftMap_fac φ g hbase ρ hρ.2⟩

/-- The factorisation is unique: any locally defined morphism into `x` over `g` which composes
with `φ` to give `b` is identified with it. -/
theorem LocalHom.rel_lift_of_comp_rel {c : LocalHom p J a' x} (hc : c.base = g)
    (h : (c.comp (LocalHom.ofHom φ)).Rel b) : c.Rel (b.lift φ g hbase) := by
  obtain ⟨-, T, hT, hagree⟩ := h
  refine ⟨hc, T, hT, ?_⟩
  intro w ρ hρ
  obtain ⟨h₁, h₂, e⟩ := hagree ρ hρ
  have h₁' : c.sieve.arrows (p.map ρ) := h₁.1
  have e' : c.map ρ h₁' ≫ φ = b.map ρ h₂ := e
  refine ⟨h₁', h₂, ?_⟩
  unfold LocalHom.lift
  have hc₁ : p.IsHomLift (p.map ρ ≫ g) (c.map ρ h₁') := by
    rw [← hc]
    exact c.isHomLift_map ρ h₁'
  refine IsStronglyCartesian.ext p (p.map φ) φ (p.map ρ ≫ g) ?_
  rw [b.liftMap_fac]
  exact e'

end Lift

/-! ### `MorPlus` is a fibred category over the base -/

/-- **`toMorPlus` preserves strongly cartesian morphisms.**

Existence of the factorisation is the universal property of `φ` in `𝒳`, applied to each of the
morphisms making up the given locally defined one; the factorisations are compatible with
restriction because the universal property determines them uniquely. Uniqueness of the
factorisation in `MorPlus p J` is the same uniqueness, applied on a covering sieve.

No fibredness hypothesis on `p` is needed. -/
theorem isStronglyCartesian_toMorPlus_map {R S : 𝒮} (f : R ⟶ S) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : p.IsStronglyCartesian f φ) :
    (p.morPlusProj J).IsStronglyCartesian f ((p.toMorPlus J).map φ) := by
  have := hφ
  subst_hom_lift p f φ
  refine
    { toIsHomLift := isHomLift_map_of_comp_eq (toMorPlus_comp_morPlusProj p J) (p.map φ) φ
      universal_property' := ?_ }
  intro A' g Ψ hΨ
  obtain ⟨b, rfl⟩ := MorPlus.exists_rep Ψ
  have hbase : b.base = g ≫ p.map φ := base_eq_of_isHomLift b hΨ
  refine ⟨(b.lift φ g hbase).toLocalMor, ⟨isHomLift_toLocalMor (b.lift φ g hbase), ?_⟩, ?_⟩
  · exact LocalHom.Rel.toLocalMor_eq (b.lift_comp_ofHom φ g hbase)
  · rintro X ⟨hX₁, hX₂⟩
    obtain ⟨c, rfl⟩ := MorPlus.exists_rep X
    exact LocalHom.Rel.toLocalMor_eq (LocalHom.rel_lift_of_comp_rel b φ g hbase
      (base_eq_of_isHomLift c hX₁) ((LocalHom.toLocalMor_eq_iff _ _).mp hX₂))

/-- **The structure functor of `MorPlus p J` is fibred** when `p` is: push a strongly cartesian
lift in `𝒳` forward along `toMorPlus`, which is strongly cartesian by
`CategoryTheory.Functor.isStronglyCartesian_toMorPlus_map`. -/
instance isFibered_morPlusProj [p.IsFibered] : (p.morPlusProj J).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian fun A R f ↦ ?_
  have ha : p.obj A.as = (p.morPlusProj J).obj A := rfl
  have hcart : p.IsStronglyCartesian f (IsPreFibered.pullbackMap ha f) := inferInstance
  exact ⟨(p.toMorPlus J).obj (IsPreFibered.pullbackObj ha f),
    (p.toMorPlus J).map (IsPreFibered.pullbackMap ha f),
    isStronglyCartesian_toMorPlus_map f _ hcart⟩

/-- **`toMorPlus` is a 1-morphism of fibred categories over `𝒮`**: it is strictly over the base
and preserves strongly cartesian morphisms. -/
theorem isFibredOneMorphism_toMorPlus (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) :
    IsFibredOneMorphism p (p.morPlusProj J) (p.toMorPlus J) where
  comp_eq := toMorPlus_comp_morPlusProj p J
  map_isStronglyCartesian := by
    intro R T f a b φ h
    exact isStronglyCartesian_toMorPlus_map f φ h

/-! ### The morphism map of `toMorPlus` -/

/-- **The morphism map of `toMorPlus` identifies exactly the locally equal morphisms.** This is
the local injectivity half of the statement that the morphism presheaves of `MorPlus p J` are the
sheafifications of those of `𝒳`. -/
theorem toMorPlus_map_eq_iff {x y : 𝒳} (a b : x ⟶ y) :
    (p.toMorPlus J).map a = (p.toMorPlus J).map b ↔ p.LocallyEqual J a b := by
  rw [toMorPlus_map, toMorPlus_map, LocalHom.toLocalMor_eq_iff]
  constructor
  · rintro ⟨hbase, T, hT, hagree⟩
    exact ⟨hbase, T, hT, fun _ φ hφ ↦ (hagree φ hφ).2.2⟩
  · rintro ⟨hbase, R, hR, hagree⟩
    exact ⟨hbase, R, hR, fun φ hφ ↦ ⟨trivial, trivial, hagree φ hφ⟩⟩

/-- **A locally defined morphism is, on its defining sieve, the image of an honest morphism.**
This is the local surjectivity half of the statement that the morphism presheaves of
`MorPlus p J` are the sheafifications of those of `𝒳`. -/
theorem toMorPlus_map_comp_toLocalMor {x y w : 𝒳} (a : LocalHom p J x y) (ρ : w ⟶ x)
    (hρ : a.sieve.arrows (p.map ρ)) :
    (p.toMorPlus J).map ρ ≫
        (a.toLocalMor : (p.toMorPlus J).obj x ⟶ (p.toMorPlus J).obj y) =
      (p.toMorPlus J).map (a.map ρ hρ) :=
  LocalHom.Rel.toLocalMor_eq (LocalHom.rel_of_agreeOn (by simp [a.map_base ρ hρ])
    fun φ hφ ↦ ⟨hφ.1, hφ.2, a.map_precomp φ ρ hρ (a.mem_sieve_precomp φ ρ hρ)⟩)

/-- **Every morphism of `MorPlus p J` is locally the image of a morphism of `𝒳`.** -/
theorem exists_covering_toMorPlus_map_comp {A B : p.MorPlus J} (F : A ⟶ B) :
    ∃ S ∈ J ((p.morPlusProj J).obj A), ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) →
      ∃ f : w ⟶ B.as, (p.toMorPlus J).map ρ ≫ F = (p.toMorPlus J).map f := by
  obtain ⟨a, rfl⟩ := MorPlus.exists_rep F
  exact ⟨a.sieve, a.sieve_mem, fun ρ hρ ↦ ⟨a.map ρ hρ, toMorPlus_map_comp_toLocalMor a ρ hρ⟩⟩

/-- `toMorPlus` is essentially surjective, being the identity on objects. -/
instance essSurj_toMorPlus : (p.toMorPlus J).EssSurj where
  mem_essImage A := ⟨A.as, ⟨Iso.refl _⟩⟩

/-- **Clause (2) of Stacks 02ZN for the second stage, with the trivial covering.** Every object of
`MorPlus p J` is in the essential image of `toMorPlus`, by an isomorphism lying over an identity of
the base — indeed `toMorPlus` is the identity on objects, so no covering is needed at all.

This is stated in the shape required by
`CategoryTheory.Functor.IsFibredOneMorphism.of_fullyFaithful`. -/
theorem exists_isHomLift_id_iso_toMorPlus_obj (A : p.MorPlus J) :
    ∃ (x : 𝒳) (e : (p.toMorPlus J).obj x ≅ A),
      (p.morPlusProj J).IsHomLift (𝟙 ((p.morPlusProj J).obj A)) e.hom :=
  ⟨A.as, Iso.refl _, IsHomLift.id rfl⟩

/-- If locally equal morphisms of `𝒳` are equal then `toMorPlus` is faithful: a morphism of `𝒳`
is determined by the locally defined morphism it becomes. -/
theorem faithful_toMorPlus_of_separated
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b) :
    (p.toMorPlus J).Faithful where
  map_injective h := hsep ((toMorPlus_map_eq_iff _ _).mp h)

/-- Two morphisms of `MorPlus p J` that agree after restriction along a covering sieve are equal,
when locally equal morphisms of `𝒳` are equal. -/
private theorem eq_of_forall_toMorPlus_map_comp_eq
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} {F G : A ⟶ B}
    (hbase : (p.morPlusProj J).map F = (p.morPlusProj J).map G)
    {S : Sieve (p.obj A.as)} (hS : S ∈ J (p.obj A.as))
    (h : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) →
      (p.toMorPlus J).map ρ ≫ F = (p.toMorPlus J).map ρ ≫ G) :
    F = G := by
  obtain ⟨a, rfl⟩ := MorPlus.exists_rep F
  obtain ⟨b, rfl⟩ := MorPlus.exists_rep G
  rw [LocalHom.toLocalMor_eq_iff]
  refine ⟨hbase, S ⊓ (a.sieve ⊓ b.sieve),
    J.intersection_covering hS (J.intersection_covering a.sieve_mem b.sieve_mem), ?_⟩
  intro w ρ hρ
  refine ⟨hρ.2.1, hρ.2.2, ?_⟩
  have key := h ρ hρ.1
  rw [toMorPlus_map_comp_toLocalMor a ρ hρ.2.1, toMorPlus_map_comp_toLocalMor b ρ hρ.2.2] at key
  exact hsep ((toMorPlus_map_eq_iff _ _).mp key)

/-- **If locally equal morphisms of `𝒳` are equal, the same holds in `MorPlus p J`.** So the
morphism presheaves of `MorPlus p J` are separated as soon as those of `𝒳` are; combined with the
first stage of the construction of the stackification, which achieves exactly that hypothesis,
this is the separatedness half of the sheaf condition for the morphism presheaves of the second
stage. -/
theorem locallyEqual_morPlusProj_iff
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} (F G : A ⟶ B) :
    (p.morPlusProj J).LocallyEqual J F G ↔ F = G := by
  refine ⟨fun h ↦ ?_, locallyEqual_of_eq⟩
  obtain ⟨hbase, S, hS, hagree⟩ := h
  exact eq_of_forall_toMorPlus_map_comp_eq hsep hbase hS fun ρ hρ ↦
    hagree ((p.toMorPlus J).map ρ) hρ

/-- **The construction is non-degenerate.** For the trivial topology, in which only the maximal
sieve is covering, local equality is equality, so nothing is identified. -/
instance faithful_toMorPlus_bot : (p.toMorPlus (⊥ : GrothendieckTopology 𝒮)).Faithful :=
  faithful_toMorPlus_of_separated fun h ↦ (locallyEqual_bot_iff _ _).mp h

/-- **The construction is non-degenerate.** For the trivial topology, in which only the maximal
sieve is covering, every locally defined morphism is defined on the maximal sieve and is therefore
the image of an honest morphism of `𝒳`. Together with
`CategoryTheory.Functor.faithful_toMorPlus_bot`: adjoining the locally defined morphisms does
nothing when the topology is trivial, as it must not. -/
instance full_toMorPlus_bot : (p.toMorPlus (⊥ : GrothendieckTopology 𝒮)).Full where
  map_surjective {x _} F := by
    obtain ⟨a, rfl⟩ := MorPlus.exists_rep F
    have htop : a.sieve = ⊤ := by
      have h := a.sieve_mem
      rwa [GrothendieckTopology.bot_covering] at h
    have h : a.sieve.arrows (p.map (𝟙 x)) := by rw [htop]; trivial
    exact ⟨a.map (𝟙 x) h, (LocalHom.Rel.toLocalMor_eq (a.rel_ofHom_map_id h)).symm⟩

/-! ### Gluing locally defined morphisms -/

/-- `toMorPlus` followed by `morPlusProj` sends a morphism `f` to `p.map f`. -/
@[simp]
theorem morPlusProj_map_toMorPlus_map {x y : 𝒳} (f : x ⟶ y) :
    (p.morPlusProj J).map ((p.toMorPlus J).map f) = p.map f := rfl

/-- **Two morphisms of `MorPlus p J` that agree after restriction along a covering sieve are
equal**, when locally equal morphisms of `𝒳` are equal. -/
theorem eq_of_toMorPlus_map_comp_eq
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} {F G : A ⟶ B}
    (hbase : (p.morPlusProj J).map F = (p.morPlusProj J).map G)
    {S : Sieve (p.obj A.as)} (hS : S ∈ J (p.obj A.as))
    (h : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) →
      (p.toMorPlus J).map ρ ≫ F = (p.toMorPlus J).map ρ ≫ G) :
    F = G :=
  eq_of_forall_toMorPlus_map_comp_eq hsep hbase hS h

/-- Given a family `H` of morphisms of `MorPlus p J` out of the restrictions of `A` along the
morphisms of `𝒳` lying over a sieve `S`, the *gluing sieve* of `H` consists of those morphisms
`g` of the base such that every morphism `ρ` of `𝒳` into `A.as` whose image factors through `g`
lies over `S` and has `H ρ` in the image of the morphism map of
`CategoryTheory.Functor.toMorPlus`. On this sieve the family is therefore given by honest
morphisms of `𝒳`, which is what makes it possible to amalgamate it.

Phrasing membership with an explicit factorisation `p.map ρ = k ≫ g`, rather than with
`p.map ρ = g` on the nose, is what makes downward closure hold for formal reasons: it is absorbed
into `k`. This is the same device as in `CategoryTheory.Functor.agreementSieve`. -/
def gluingSieve {A B : p.MorPlus J} (S : Sieve (p.obj A.as))
    (H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B)) :
    Sieve (p.obj A.as) where
  arrows V g := ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ A.as) (k : p.obj w ⟶ V), p.map ρ = k ≫ g →
    ∃ (hρ : S.arrows (p.map ρ)) (f : w ⟶ B.as), (p.toMorPlus J).map f = H ρ hρ
  downward_closed := by
    intro V V' g hg k₀ w ρ k hk
    exact hg ρ (k ≫ k₀) (by rw [hk, assoc])

/-- Membership in the gluing sieve of `H`, unfolded. -/
theorem mem_gluingSieve_iff {A B : p.MorPlus J} (S : Sieve (p.obj A.as))
    (H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B))
    {V : 𝒮} (g : V ⟶ p.obj A.as) :
    (gluingSieve S H).arrows g ↔
      ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ A.as) (k : p.obj w ⟶ V), p.map ρ = k ≫ g →
        ∃ (hρ : S.arrows (p.map ρ)) (f : w ⟶ B.as), (p.toMorPlus J).map f = H ρ hρ :=
  Iff.rfl

/-- A morphism whose image lies in the gluing sieve of `H` lies over `S`, and the morphism `H`
assigns to it is the image of a morphism of `𝒳`. -/
theorem exists_hom_of_mem_gluingSieve {A B : p.MorPlus J} {S : Sieve (p.obj A.as)}
    {H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B)}
    {w : 𝒳} {ρ : w ⟶ A.as} (h : (gluingSieve S H).arrows (p.map ρ)) :
    ∃ (hρ : S.arrows (p.map ρ)) (f : w ⟶ B.as), (p.toMorPlus J).map f = H ρ hρ :=
  (mem_gluingSieve_iff S H _).mp h ρ (𝟙 _) (id_comp _).symm

/-- The gluing sieve of `H` is contained in the sieve `H` is indexed by. -/
theorem mem_of_mem_gluingSieve {A B : p.MorPlus J} {S : Sieve (p.obj A.as)}
    {H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B)}
    {w : 𝒳} {ρ : w ⟶ A.as} (h : (gluingSieve S H).arrows (p.map ρ)) : S.arrows (p.map ρ) := by
  obtain ⟨hρ, f, hf⟩ := exists_hom_of_mem_gluingSieve h
  exact hρ

/-- **The gluing sieve of a compatible family is covering.**

For each member `g` of `S` take the chosen strongly cartesian lift `ψ` of `g` — this is where
fibredness of `p` enters. The value `H ψ` of the family at `ψ` is a locally defined morphism, so
by `CategoryTheory.Functor.exists_covering_toMorPlus_map_comp` it is the image of a morphism of
`𝒳` after restriction along a covering sieve `R` of the source of `ψ`. Every morphism of `𝒳` into
`A.as` over a member of `R`, pushed into `V`, factors through `ψ`, and compatibility of the family
identifies the value there with a restriction of `H ψ`. So the pullback of the gluing sieve along
each member of `S` is covering, and the local character of the topology finishes the proof. -/
theorem gluingSieve_mem [p.IsFibered] {A B : p.MorPlus J} {S : Sieve (p.obj A.as)}
    (hS : S ∈ J (p.obj A.as))
    (H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B))
    (Hcomp : ∀ {w w' : 𝒳} (χ : w' ⟶ w) (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ))
      (hχρ : S.arrows (p.map (χ ≫ ρ))), H (χ ≫ ρ) hχρ = (p.toMorPlus J).map χ ≫ H ρ hρ) :
    gluingSieve S H ∈ J (p.obj A.as) := by
  have hHcongr : ∀ {w : 𝒳} {ρ₁ ρ₂ : w ⟶ A.as} (h₁ : S.arrows (p.map ρ₁))
      (h₂ : S.arrows (p.map ρ₂)), ρ₁ = ρ₂ → H ρ₁ h₁ = H ρ₂ h₂ := by
    intro w ρ₁ ρ₂ h₁ h₂ h
    subst h
    rfl
  refine J.transitive hS _ fun V g hg ↦ ?_
  -- The chosen strongly cartesian lift of `g`.
  have ha : p.obj A.as = p.obj A.as := rfl
  have hprj : p.obj (IsPreFibered.pullbackObj ha g) = V := IsPreFibered.pullbackObj_proj ha g
  set ψ := IsPreFibered.pullbackMap ha g with hψdef
  have hcart : p.IsStronglyCartesian g ψ := inferInstance
  have hmapψ : p.map ψ = eqToHom hprj ≫ g := by
    have := IsHomLift.fac' p g ψ
    simpa using this
  have hmemS : S.arrows (p.map ψ) := by
    rw [hmapψ]
    exact S.downward_closed hg _
  -- The value of the family at `ψ` is locally the image of a morphism of `𝒳`.
  obtain ⟨R, hR, hRspec⟩ := exists_covering_toMorPlus_map_comp (H ψ hmemS)
  have hRmem : R ∈ J (p.obj (IsPreFibered.pullbackObj ha g)) := hR
  have hRspec' : ∀ {w : 𝒳} (σ : w ⟶ IsPreFibered.pullbackObj ha g), R.arrows (p.map σ) →
      ∃ f : w ⟶ B.as, (p.toMorPlus J).map σ ≫ H ψ hmemS = (p.toMorPlus J).map f := hRspec
  refine J.superset_covering (S := R.pullback (eqToHom hprj.symm)) ?_
    (J.pullback_stable _ hRmem)
  intro V' k hk
  rw [Sieve.pullback_apply] at hk
  rw [Sieve.pullback_apply, mem_gluingSieve_iff]
  intro w ρ k₁ hk₁
  have hfac : p.map ρ = (k₁ ≫ k) ≫ g := by rw [hk₁, assoc]
  have hρS : S.arrows (p.map ρ) := by
    rw [hfac]
    exact S.downward_closed hg _
  -- Factor `ρ` through `ψ`.
  set σ := IsStronglyCartesian.map p g ψ hfac ρ with hσdef
  have hσfac : σ ≫ ψ = ρ := IsStronglyCartesian.fac ..
  have hσlift : p.IsHomLift (k₁ ≫ k) σ := inferInstance
  have hmapσ : p.map σ = (k₁ ≫ k) ≫ eqToHom hprj.symm := by
    simpa using IsHomLift.fac' p (k₁ ≫ k) σ
  have hmemR : R.arrows (p.map σ) := by
    rw [hmapσ, assoc]
    exact R.downward_closed hk _
  obtain ⟨f, hf⟩ := hRspec' σ hmemR
  have hσρ : S.arrows (p.map (σ ≫ ψ)) := by
    rw [hσfac]
    exact hρS
  refine ⟨hρS, f, ?_⟩
  rw [← hf]
  exact (Hcomp σ ψ hmemS hσρ).symm.trans (hHcongr hσρ hρS hσfac)

/-- The amalgamation constructed in `CategoryTheory.Functor.exists_localHom_amalgamation`
restricts to the given family, not merely on its own defining sieve, but along *every* morphism
of `𝒳` lying over the sieve the family is indexed by.

The two sides are morphisms of `MorPlus p J` which agree after restriction along a covering sieve,
so this is `CategoryTheory.Functor.eq_of_toMorPlus_map_comp_eq`, and it needs the hypothesis that
locally equal morphisms of `𝒳` are equal. -/
theorem toMorPlus_map_comp_toLocalMor_eq
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} (u : p.obj A.as ⟶ p.obj B.as) (S : Sieve (p.obj A.as))
    (H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B))
    (Hbase : ∀ {w : 𝒳} (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ)),
      (p.morPlusProj J).map (H ρ hρ) = p.map ρ ≫ u)
    (Hcomp : ∀ {w w' : 𝒳} (χ : w' ⟶ w) (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ))
      (hχρ : S.arrows (p.map (χ ≫ ρ))), H (χ ≫ ρ) hχρ = (p.toMorPlus J).map χ ≫ H ρ hρ)
    (a : LocalHom p J A.as B.as) (hbase : a.base = u)
    (hmap : ∀ {w : 𝒳} (χ : w ⟶ A.as) (hχ : a.sieve.arrows (p.map χ))
      (hχS : S.arrows (p.map χ)), (p.toMorPlus J).map (a.map χ hχ) = H χ hχS)
    {w : 𝒳} (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ)) :
    (p.toMorPlus J).map ρ ≫ (a.toLocalMor : A ⟶ B) = H ρ hρ := by
  refine eq_of_toMorPlus_map_comp_eq hsep ?_ (J.pullback_stable (p.map ρ) a.sieve_mem) ?_
  · rw [Functor.map_comp, morPlusProj_map_toMorPlus_map, morPlusProj_map_toLocalMor, hbase, Hbase]
  · intro w' σ hσ
    have hmem : a.sieve.arrows (p.map (σ ≫ ρ)) := by
      rw [p.map_comp]
      exact hσ
    have hmemS : S.arrows (p.map (σ ≫ ρ)) := by
      rw [p.map_comp]
      exact S.downward_closed hρ _
    calc (p.toMorPlus J).map σ ≫ (p.toMorPlus J).map ρ ≫ (a.toLocalMor : A ⟶ B)
        = (p.toMorPlus J).map (σ ≫ ρ) ≫ (a.toLocalMor : A ⟶ B) := by
          rw [Functor.map_comp, assoc]
      _ = (p.toMorPlus J).map (a.map (σ ≫ ρ) hmem) :=
          toMorPlus_map_comp_toLocalMor a (σ ≫ ρ) hmem
      _ = H (σ ≫ ρ) hmemS := hmap (σ ≫ ρ) hmem hmemS
      _ = (p.toMorPlus J).map σ ≫ H ρ hρ := Hcomp σ ρ hρ hmemS

/-- **A compatible family of morphisms of `MorPlus p J`, indexed by the morphisms of `𝒳` lying
over a covering sieve and all lying over a single morphism `u` of the base, is the restriction of
a single locally defined morphism over `u`.**

The locally defined morphism is defined on `CategoryTheory.Functor.gluingSieve`, and its value at
a morphism `ρ` of that sieve is *the* morphism of `𝒳` whose image is the value of the family at
`ρ`. The choice of that morphism is where `Classical.choose` enters, and its uniqueness — which is
what makes the assignment compatible with restriction, and hence a locally defined morphism at all
— is exactly the hypothesis that locally equal morphisms of `𝒳` are equal. Nothing weaker will do:
two candidate values are only locally equal a priori. -/
theorem exists_localHom_amalgamation [p.IsFibered]
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} (u : p.obj A.as ⟶ p.obj B.as) {S : Sieve (p.obj A.as)}
    (hS : S ∈ J (p.obj A.as))
    (H : ∀ {w : 𝒳} (ρ : w ⟶ A.as), S.arrows (p.map ρ) → ((p.toMorPlus J).obj w ⟶ B))
    (Hbase : ∀ {w : 𝒳} (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ)),
      (p.morPlusProj J).map (H ρ hρ) = p.map ρ ≫ u)
    (Hcomp : ∀ {w w' : 𝒳} (χ : w' ⟶ w) (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ))
      (hχρ : S.arrows (p.map (χ ≫ ρ))), H (χ ≫ ρ) hχρ = (p.toMorPlus J).map χ ≫ H ρ hρ) :
    ∃ a : LocalHom p J A.as B.as, a.base = u ∧
      ∀ {w : 𝒳} (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ)),
        (p.toMorPlus J).map ρ ≫ (a.toLocalMor : A ⟶ B) = H ρ hρ := by
  have hT : gluingSieve S H ∈ J (p.obj A.as) := gluingSieve_mem hS H Hcomp
  have hex : ∀ (w : 𝒳) (ρ : w ⟶ A.as) (hρT : (gluingSieve S H).arrows (p.map ρ)),
      ∃ f : w ⟶ B.as, (p.toMorPlus J).map f = H ρ (mem_of_mem_gluingSieve hρT) := by
    intro w ρ hρT
    obtain ⟨hρ, f, hf⟩ := exists_hom_of_mem_gluingSieve hρT
    exact ⟨f, hf⟩
  have hval : ∀ (w : 𝒳) (ρ : w ⟶ A.as) (hρT : (gluingSieve S H).arrows (p.map ρ)),
      (p.toMorPlus J).map (hex w ρ hρT).choose = H ρ (mem_of_mem_gluingSieve hρT) :=
    fun w ρ hρT ↦ (hex w ρ hρT).choose_spec
  -- Uniqueness of the chosen morphism: **this is where separatedness of `𝒳` is used.**
  have huniq : ∀ {w : 𝒳} {ρ : w ⟶ A.as} (hρT : (gluingSieve S H).arrows (p.map ρ))
      (f : w ⟶ B.as), (p.toMorPlus J).map f = H ρ (mem_of_mem_gluingSieve hρT) →
      f = (hex w ρ hρT).choose := by
    intro w ρ hρT f hf
    exact hsep ((toMorPlus_map_eq_iff f (hex w ρ hρT).choose).mp (hf.trans (hval w ρ hρT).symm))
  obtain ⟨a, hbase, hmap⟩ : ∃ a : LocalHom p J A.as B.as, a.base = u ∧
      ∀ {w : 𝒳} (χ : w ⟶ A.as) (hχ : a.sieve.arrows (p.map χ)) (hχS : S.arrows (p.map χ)),
        (p.toMorPlus J).map (a.map χ hχ) = H χ hχS := by
    refine ⟨{ base := u
              sieve := gluingSieve S H
              sieve_mem := hT
              map χ hχ := (hex _ χ hχ).choose
              map_base := ?_
              map_precomp := ?_ }, rfl, fun χ hχ _ ↦ hval _ χ hχ⟩
    · intro w χ hχ
      show p.map (hex w χ hχ).choose = p.map χ ≫ u
      rw [← morPlusProj_map_toMorPlus_map (J := J) (hex w χ hχ).choose, hval w χ hχ]
      exact Hbase χ (mem_of_mem_gluingSieve hχ)
    · intro w w' ξ χ hχ hξχ
      show (hex w' (ξ ≫ χ) hξχ).choose = ξ ≫ (hex w χ hχ).choose
      refine (huniq hξχ (ξ ≫ (hex w χ hχ).choose) ?_).symm
      rw [Functor.map_comp, hval w χ hχ]
      exact (Hcomp ξ χ (mem_of_mem_gluingSieve hχ) (mem_of_mem_gluingSieve hξχ)).symm
  exact ⟨a, hbase, fun ρ hρ ↦
    toMorPlus_map_comp_toLocalMor_eq hsep u S H Hbase Hcomp a hbase hmap ρ hρ⟩

/-- **The gluing half of the sheaf condition for the morphism presheaves of `MorPlus p J`**, when
locally equal morphisms of `𝒳` are equal.

A family of morphisms `F Φ : W ⟶ B` of `MorPlus p J`, indexed by the morphisms `Φ : W ⟶ A` lying
over a covering sieve `S` of the base, all lying over the restrictions of a single morphism `u` of
the base and compatible with further restriction, has an amalgamation: a morphism `G : A ⟶ B` over
`u` restricting to `F Φ` along every such `Φ`.

Together with `CategoryTheory.Functor.locallyEqual_morPlusProj_iff`, which is the separatedness
half and gives uniqueness of `G`, this says that the morphism presheaves of `MorPlus p J` are
sheaves. Fibredness of `p` is used to lift the members of `S` to morphisms of `𝒳`; the hypothesis
`hsep` — which the first stage of the construction of the stackification exists to supply — is
used twice, to make the amalgamation well defined and to compare it with the given family. -/
theorem exists_amalgamation_morPlusProj [p.IsFibered]
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : p.MorPlus J} (u : (p.morPlusProj J).obj A ⟶ (p.morPlusProj J).obj B)
    {S : Sieve ((p.morPlusProj J).obj A)} (hS : S ∈ J ((p.morPlusProj J).obj A))
    (F : ∀ {W : p.MorPlus J} (Φ : W ⟶ A), S.arrows ((p.morPlusProj J).map Φ) → (W ⟶ B))
    (hFbase : ∀ {W : p.MorPlus J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.morPlusProj J).map Φ)),
      (p.morPlusProj J).map (F Φ hΦ) = (p.morPlusProj J).map Φ ≫ u)
    (hFcomp : ∀ {W W' : p.MorPlus J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
      (hΦ : S.arrows ((p.morPlusProj J).map Φ))
      (hΨΦ : S.arrows ((p.morPlusProj J).map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) :
    ∃ G : A ⟶ B, (p.morPlusProj J).map G = u ∧
      ∀ {W : p.MorPlus J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.morPlusProj J).map Φ)),
        Φ ≫ G = F Φ hΦ := by
  have hFcongr : ∀ {W : p.MorPlus J} {Φ₁ Φ₂ : W ⟶ A} (h : Φ₁ = Φ₂)
      (h₁ : S.arrows ((p.morPlusProj J).map Φ₁)) (h₂ : S.arrows ((p.morPlusProj J).map Φ₂)),
      F Φ₁ h₁ = F Φ₂ h₂ := by
    intro W Φ₁ Φ₂ h h₁ h₂
    subst h
    rfl
  have Hbase : ∀ {w : 𝒳} (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ)),
      (p.morPlusProj J).map (F ((p.toMorPlus J).map ρ) hρ) = p.map ρ ≫ u :=
    fun ρ hρ ↦ hFbase ((p.toMorPlus J).map ρ) hρ
  have Hcomp : ∀ {w w' : 𝒳} (χ : w' ⟶ w) (ρ : w ⟶ A.as) (hρ : S.arrows (p.map ρ))
      (hχρ : S.arrows (p.map (χ ≫ ρ))),
      F ((p.toMorPlus J).map (χ ≫ ρ)) hχρ =
        (p.toMorPlus J).map χ ≫ F ((p.toMorPlus J).map ρ) hρ := by
    intro w w' χ ρ hρ hχρ
    have h₁ : (p.toMorPlus J).map (χ ≫ ρ) =
        (p.toMorPlus J).map χ ≫ (p.toMorPlus J).map ρ := (p.toMorPlus J).map_comp χ ρ
    have h₂ : S.arrows ((p.morPlusProj J).map
        ((p.toMorPlus J).map χ ≫ (p.toMorPlus J).map ρ)) := by
      rw [← h₁]
      exact hχρ
    exact (hFcongr h₁ hχρ h₂).trans
      (hFcomp ((p.toMorPlus J).map χ) ((p.toMorPlus J).map ρ) hρ h₂)
  obtain ⟨a, hab, ha⟩ := exists_localHom_amalgamation hsep u hS
    (fun ρ hρ ↦ F ((p.toMorPlus J).map ρ) hρ) Hbase Hcomp
  refine ⟨a.toLocalMor, hab, ?_⟩
  intro W Φ hΦ
  obtain ⟨R, hR, hRspec⟩ := exists_covering_toMorPlus_map_comp Φ
  refine eq_of_toMorPlus_map_comp_eq hsep ?_ hR ?_
  · rw [Functor.map_comp, morPlusProj_map_toLocalMor, hab, hFbase]
  · intro w σ hσ
    obtain ⟨f, hf⟩ := hRspec σ hσ
    have hmap : p.map f = p.map σ ≫ (p.morPlusProj J).map Φ := by
      rw [← morPlusProj_map_toMorPlus_map (J := J) f, ← hf, Functor.map_comp,
        morPlusProj_map_toMorPlus_map]
    have hfS : S.arrows (p.map f) := by
      rw [hmap]
      exact S.downward_closed hΦ _
    have h₂ : S.arrows ((p.morPlusProj J).map ((p.toMorPlus J).map σ ≫ Φ)) := by
      rw [hf]
      exact hfS
    calc (p.toMorPlus J).map σ ≫ Φ ≫ (a.toLocalMor : A ⟶ B)
        = (p.toMorPlus J).map f ≫ (a.toLocalMor : A ⟶ B) := by rw [← assoc, hf]
      _ = F ((p.toMorPlus J).map f) hfS := ha f hfS
      _ = F ((p.toMorPlus J).map σ ≫ Φ) h₂ := hFcongr hf.symm hfS h₂
      _ = (p.toMorPlus J).map σ ≫ F Φ hΦ := hFcomp ((p.toMorPlus J).map σ) Φ hΦ h₂

/-! ### The second stage of the stackification -/

/-- **The second stage of the construction of the stackification of a fibred category**: the
locally defined morphisms are adjoined to the separated quotient produced by the first stage. -/
abbrev StageTwo (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : Type u₂ :=
  MorPlus (p.morQuotientProj J) J

/-- The structure functor of the second stage. -/
abbrev stageTwoProj (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : p.StageTwo J ⥤ 𝒮 :=
  morPlusProj (p.morQuotientProj J) J

/-- The 1-morphism from `𝒳` to the second stage: quotient by local equality of morphisms, then
adjoin the locally defined morphisms. -/
def toStageTwo (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : 𝒳 ⥤ p.StageTwo J :=
  p.toMorQuotient J ⋙ toMorPlus (p.morQuotientProj J) J

/-- The 1-morphism to the second stage is *strictly* over the base. -/
theorem toStageTwo_comp_stageTwoProj (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) :
    p.toStageTwo J ⋙ p.stageTwoProj J = p := by
  rw [toStageTwo, Functor.assoc, toMorPlus_comp_morPlusProj]
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- **The structure functor of the second stage is fibred.** -/
instance isFibered_stageTwoProj [p.IsFibered] : (p.stageTwoProj J).IsFibered :=
  isFibered_morPlusProj

/-- **The 1-morphism to the second stage is a 1-morphism of fibred categories over `𝒮`.** -/
theorem isFibredOneMorphism_toStageTwo (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) :
    IsFibredOneMorphism p (p.stageTwoProj J) (p.toStageTwo J) :=
  (isFibredOneMorphism_toMorQuotient p J).comp
    (isFibredOneMorphism_toMorPlus (p.morQuotientProj J) J)

/-- **Adjoining the locally defined morphisms to the separated quotient is faithful.** Since the
first stage has already identified the locally equal morphisms, and its output is separated, no
further identification is made at the second stage. -/
instance faithful_toMorPlus_morQuotientProj [p.IsFibered] :
    (toMorPlus (p.morQuotientProj J) J).Faithful :=
  faithful_toMorPlus_of_separated fun h ↦ (locallyEqual_morQuotientProj_iff _ _).mp h

/-- **The morphism presheaves of the second stage are separated.** -/
theorem locallyEqual_stageTwoProj_iff [p.IsFibered] {A B : p.StageTwo J} (F G : A ⟶ B) :
    (p.stageTwoProj J).LocallyEqual J F G ↔ F = G :=
  locallyEqual_morPlusProj_iff (fun h ↦ (locallyEqual_morQuotientProj_iff _ _).mp h) F G

/-- **The morphism map of the second stage identifies exactly the locally equal morphisms of
`𝒳`.** Both stages contribute: the first identifies locally equal morphisms outright, and the
second makes no further identification because the first is separated. -/
theorem toStageTwo_map_eq_iff [p.IsFibered] {x y : 𝒳} (f g : x ⟶ y) :
    (p.toStageTwo J).map f = (p.toStageTwo J).map g ↔ p.LocallyEqual J f g := by
  rw [toStageTwo, Functor.comp_map, Functor.comp_map, toMorPlus_map_eq_iff]
  exact ⟨locallyEqual_of_locallyEqual_toMorQuotient_map,
    fun h ↦ locallyEqual_of_eq
      ((CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) f g).mpr h)⟩

/-- **Clause (2) of Stacks 02ZN for the second stage, with the trivial covering.** Both stages are
the identity on objects, so every object of the second stage is in the essential image of
`toStageTwo` by an isomorphism lying over an identity of the base. -/
theorem exists_isHomLift_id_iso_toStageTwo_obj (A : p.StageTwo J) :
    ∃ (x : 𝒳) (e : (p.toStageTwo J).obj x ≅ A),
      (p.stageTwoProj J).IsHomLift (𝟙 ((p.stageTwoProj J).obj A)) e.hom :=
  ⟨A.as.as, Iso.refl _, IsHomLift.id rfl⟩

/-- **The gluing half of the sheaf condition for the morphism presheaves of the second stage.**
Both stages contribute: the second stage supplies the amalgamation, and the first supplies the
hypothesis that makes it well defined, namely that its own morphism presheaves are separated
(`CategoryTheory.Functor.locallyEqual_morQuotientProj_iff`).

With `CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`, which is the separatedness half, this
says that the morphism presheaves of the second stage are sheaves. -/
theorem exists_amalgamation_stageTwoProj [p.IsFibered] {A B : p.StageTwo J}
    (u : (p.stageTwoProj J).obj A ⟶ (p.stageTwoProj J).obj B)
    {S : Sieve ((p.stageTwoProj J).obj A)} (hS : S ∈ J ((p.stageTwoProj J).obj A))
    (F : ∀ {W : p.StageTwo J} (Φ : W ⟶ A), S.arrows ((p.stageTwoProj J).map Φ) → (W ⟶ B))
    (hFbase : ∀ {W : p.StageTwo J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.stageTwoProj J).map Φ)),
      (p.stageTwoProj J).map (F Φ hΦ) = (p.stageTwoProj J).map Φ ≫ u)
    (hFcomp : ∀ {W W' : p.StageTwo J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
      (hΦ : S.arrows ((p.stageTwoProj J).map Φ))
      (hΨΦ : S.arrows ((p.stageTwoProj J).map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) :
    ∃ G : A ⟶ B, (p.stageTwoProj J).map G = u ∧
      ∀ {W : p.StageTwo J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.stageTwoProj J).map Φ)),
        Φ ≫ G = F Φ hΦ :=
  exists_amalgamation_morPlusProj (fun h ↦ (locallyEqual_morQuotientProj_iff _ _).mp h) u hS F
    hFbase hFcomp

end CategoryTheory.Functor
