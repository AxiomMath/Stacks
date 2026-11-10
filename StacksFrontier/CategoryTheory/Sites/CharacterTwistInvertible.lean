module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCharacterTwistTorsor

/-!
# The character twist of a torsor is invertible

Let `W` be a torsor under a group `G` over the final object of a site, in the sense of
`CategoryTheory.IsTorsorObject`, and let `χ : G → ℤˣ` be a character. This file proves that the
twist `ℤ(χ)` is invertible for the tensor product of abelian sheaves, its own inverse being `ℤ(χ)`
itself: there is an isomorphism `ℤ ≅ ℤ(χ) ⊗_ℤ ℤ(χ)`.

Over an object carrying a morphism `φ : V ⟶ W` the twist is free of rank one on the class `[φ]`, so
the tensor square is free of rank one on `[φ] ⊗ [φ]`; and that generator does not depend on `φ`,
because two choices differ locally by a group element `g`, which contributes `χ g` to each factor,
and `χ g` is its own inverse since `χ` takes values in `{+1, -1}`. The local generators therefore
glue to a global section of the tensor square, and the morphism out of `ℤ` it determines is locally
bijective.

The class of the identity of `W` is a section of `ℤ(χ)` over `W` transforming according to `χ`, and
the global section of the tensor square attached to it by Stacks 0727,
`CategoryTheory.IsTorsorObject.twistTensorGlobalSection`, is the section described above.

## Main definitions

* `CategoryTheory.IsTorsorObject.twistSelfSection` is the section of `ℤ(χ)` over `W` given by the
  class of the identity of `W`, and `CategoryTheory.IsTorsorObject.twistTensorSelfSection` the
  resulting global section of `ℤ(χ) ⊗_ℤ ℤ(χ)`.
* `CategoryTheory.IsTorsorObject.twistTensorUnit` is the morphism `ℤ ⟶ ℤ(χ) ⊗_ℤ ℤ(χ)` of
  *presheaves* it determines, and `CategoryTheory.IsTorsorObject.constantToTwistTensorSelf` the
  morphism of abelian sheaves.

## Main results

* `CategoryTheory.IsTorsorObject.constantSheafIsoTwistTensorSelf`: **`ℤ ≅ ℤ(χ) ⊗_ℤ ℤ(χ)`**, so that
  `ℤ(χ)` is invertible and tensoring with it is an auto-equivalence of abelian sheaves.
* `CategoryTheory.IsTorsorObject.w_twistTensorUnit`: the same statement in the form the tensor
  product of presheaves consumes, namely that sheafification inverts
  `CategoryTheory.IsTorsorObject.twistTensorUnit`.
* `CategoryTheory.IsTorsorObject.isLocallySurjective_twistTensorUnit` and
  `CategoryTheory.IsTorsorObject.isLocallyInjective_twistTensorUnit`: the two halves, local
  surjectivity and local injectivity.
* `CategoryTheory.IsTorsorObject.mem_characterSections_twistSelfSection`: the class of the identity
  of `W` transforms according to `χ`.

## Implementation notes

The morphism `ℤ ⟶ ℤ(χ) ⊗_ℤ ℤ(χ)` is built from a global section rather than objectwise: over an
object of the site admitting no morphism to `W` the twist presheaf has no distinguished element, so
there is no morphism from the constant presheaf `ℤ` to the *objectwise* tensor square, and the
section exists only after the local pieces are glued. What the construction does produce objectwise
is the restriction of the glued global section, which is
`CategoryTheory.constPresheafOfGlobalSection`, and that is enough: it is a morphism of presheaves,
so `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` applies to it and the two local
statements are checked on the objects lying over `W`, where Stacks 0727 describes both `ℤ(χ)` and
the tensor square.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ u

namespace CategoryTheory

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
  {W : C} {G : Type w} [Group G] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (χ : G →* ℤˣ)

/-- The morphism from the constant presheaf `ℤ` to a presheaf of abelian groups determined by a
section over the final object: over `V` it sends `n` to `n` times the restriction of the
section. -/
def constPresheafOfGlobalSection {M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {T : C} (hT : IsTerminal T)
    (s : M.obj (op T)) :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ M where
  app V := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun n : ULift.{u + 1} ℤ => n.down • M.map (hT.from V.unop).op s)
    (fun a b => add_smul a.down b.down _))
  naturality V V' f := by
    ext n
    have hf : (hT.from V.unop).op ≫ f = (hT.from V'.unop).op :=
      Quiver.Hom.unop_inj (hT.hom_ext _ _)
    change (ULift.down n) • M.map (hT.from V'.unop).op s =
      M.map f ((ULift.down n) • M.map (hT.from V.unop).op s)
    rw [map_zsmul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, hf]

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- Over `V` the morphism determined by a global section sends `n` to `n` times the restriction of
the section. -/
@[simp]
lemma constPresheafOfGlobalSection_app {M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {T : C}
    (hT : IsTerminal T) (s : M.obj (op T)) (V : Cᵒᵖ) (n : ULift.{u + 1} ℤ) :
    (constPresheafOfGlobalSection hT s).app V n = n.down • M.map (hT.from V.unop).op s := rfl

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- Pulling back the image sieve of a section along a morphism gives the image sieve of the
restricted section. -/
private lemma imageSieve_pullback_eq {F M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (α : F ⟶ M)
    {V V' : C} (g : V' ⟶ V) (y : M.obj (op V)) :
    (Presheaf.imageSieve α y).pullback g =
      Presheaf.imageSieve α (M.map g.op y) := by
  have key : ∀ {V'' : C} (k : V'' ⟶ V'),
      M.map (k ≫ g).op y = M.map k.op (M.map g.op y) := by
    intro V'' k
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  ext V'' k
  exact ⟨fun hk => ⟨hk.choose, hk.choose_spec.trans (key k)⟩,
    fun hk => ⟨hk.choose, hk.choose_spec.trans (key k).symm⟩⟩

namespace IsTorsorObject

/-- The section of `ℤ(χ)` over `W` given by the class of the identity of `W`. -/
def twistSelfSection : (characterTwist W act χ J).obj.obj (op W) :=
  (toSheafify J (characterTwistPresheaf W act χ)).app (op W)
    (twistedGenerator W act χ (𝟙 W))

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The class of the identity of `W` transforms according to `χ`.** -/
theorem mem_characterSections_twistSelfSection :
    twistSelfSection (act := act) (J := J) χ ∈
      characterSections W act χ (characterTwist W act χ J).obj := by
  intro g
  have hnat := NatTrans.naturality_apply
    (toSheafify J (characterTwistPresheaf W act χ)) ((act g).asIso.hom).op
    (twistedGenerator W act χ (𝟙 W))
  have hgen : (characterTwistPresheaf W act χ).map ((act g).asIso.hom).op
      (twistedGenerator W act χ (𝟙 W)) = (χ g : ℤ) • twistedGenerator W act χ (𝟙 W) := by
    rw [characterTwistPresheaf_map_twistedGenerator, Category.comp_id]
    have hid := twistedGenerator_act W act χ (𝟙 W) g
    rwa [Category.id_comp] at hid
  have h2 : (characterTwist W act χ J).obj.map ((act g).asIso.hom).op
        ((toSheafify J (characterTwistPresheaf W act χ)).app (op W)
          (twistedGenerator W act χ (𝟙 W))) =
      (toSheafify J (characterTwistPresheaf W act χ)).app (op W)
        ((characterTwistPresheaf W act χ).map ((act g).asIso.hom).op
          (twistedGenerator W act χ (𝟙 W))) := hnat.symm
  rw [twistSelfSection, h2, hgen, map_zsmul]
  rfl

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The section of `F ⊗_ℤ ℤ(χ)` built from a section of `F` and a morphism to `W` is `ℤ`-linear in
the section of `F`. -/
theorem twistTensorGenSection_zsmul {F : Sheaf J AddCommGrpCat.{u + 1}} (act : G →* Aut W)
    (χ : G →* ℤˣ) {V : C} (n : ℤ) (t : F.obj.obj (op V)) (f : V ⟶ W) :
    twistTensorGenSection (J := J) act χ (n • t) f =
      n • twistTensorGenSection (J := J) act χ t f := by
  unfold twistTensorGenSection
  have key : characterTwistTensorGen act χ (n • t) (twistedGenerator W act χ f) =
      n • characterTwistTensorGen act χ t (twistedGenerator W act χ f) :=
    TensorProduct.smul_tmul' n t _
  rw [key]
  exact map_zsmul _ _ _

section Tensor

variable {T : C} (hT : IsTerminal T) (h : IsTorsorObject act J)

include hT h

/-- The canonical global section of `ℤ(χ) ⊗_ℤ ℤ(χ)`: over an object carrying a morphism `φ : V ⟶ W`
it is `[φ] ⊗ [φ]`. It is the global section attached by Stacks 0727 to the class of the identity of
`W`. -/
def twistTensorSelfSection :
    (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.obj (op T) :=
  h.twistTensorGlobalSection (T := T) χ
    ⟨twistSelfSection χ, mem_characterSections_twistSelfSection χ⟩


omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The restriction of the canonical global section of the tensor square to an object lying over
`W`.** Over an object carrying `φ : V ⟶ W` the global section is `[φ] ⊗ [φ]`. -/
theorem twistTensorSelfSection_map {V : C} (φ : V ⟶ W) :
    (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.map (hT.from V).op
        (h.twistTensorSelfSection (T := T) χ) =
      twistTensorGenSection act χ
        ((toSheafify J (characterTwistPresheaf W act χ)).app (op V)
          (twistedGenerator W act χ φ)) φ := by
  have hmap := h.twistTensorGlobalSection_map χ hT
    ⟨twistSelfSection χ, mem_characterSections_twistSelfSection χ⟩ φ
  refine hmap.trans ?_
  rw [twistTensorLocalSection_eq_genSection]
  congr 1
  have hnat := NatTrans.naturality_apply
    (toSheafify J (characterTwistPresheaf W act χ)) φ.op
    (twistedGenerator W act χ (𝟙 W))
  have h2 : (characterTwist W act χ J).obj.map φ.op (twistSelfSection χ) =
      (toSheafify J (characterTwistPresheaf W act χ)).app (op V)
        ((characterTwistPresheaf W act χ).map φ.op
          (twistedGenerator W act χ (𝟙 W))) := hnat.symm
  rw [h2, characterTwistPresheaf_map_twistedGenerator, Category.comp_id]

/-- The morphism `ℤ ⟶ ℤ(χ) ⊗_ℤ ℤ(χ)` of presheaves determined by the canonical global section of
the tensor square: over `V` it sends `n` to `n` times the restriction of that section. -/
def twistTensorUnit :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj :=
  constPresheafOfGlobalSection hT (h.twistTensorSelfSection (T := T) χ)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- Over an object carrying a morphism `φ : V ⟶ W` the unit sends `n` to `n • ([φ] ⊗ [φ])`. -/
theorem twistTensorUnit_app {V : C} (φ : V ⟶ W) (n : ULift.{u + 1} ℤ) :
    (h.twistTensorUnit χ hT).app (op V) n =
      n.down • twistTensorGenSection act χ
        ((toSheafify J (characterTwistPresheaf W act χ)).app (op V)
          (twistedGenerator W act χ φ)) φ := by
  rw [twistTensorUnit, constPresheafOfGlobalSection_app,
    h.twistTensorSelfSection_map χ hT φ]
  rfl

/-- **Locally on an object lying over `W`, every section of `ℤ(χ) ⊗_ℤ ℤ(χ)` is an integer multiple
of the canonical global section.** -/
theorem imageSieve_twistTensorUnit_mem {V : C} (φ : V ⟶ W)
    (y : (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.obj (op V)) :
    Presheaf.imageSieve (h.twistTensorUnit χ hT) y ∈ J V := by
  have := (J.W_toSheafify
    (characterTwistTensorPresheaf (characterTwist W act χ J).obj act χ)).isLocallySurjective
  have := (J.W_toSheafify (characterTwistPresheaf W act χ)).isLocallySurjective
  refine J.transitive (Presheaf.imageSieve_mem J
    (toSheafify J (characterTwistTensorPresheaf (characterTwist W act χ J).obj act χ)) y) _ ?_
  rintro V₁ f ⟨x, hx⟩
  rw [imageSieve_pullback_eq]
  have hx' : (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.map f.op y =
      (toSheafify J
        (characterTwistTensorPresheaf (characterTwist W act χ J).obj act χ)).app (op V₁) x :=
    hx.symm
  obtain ⟨S', hS', hfam⟩ := h.exists_sieve_twistTensorGen χ (f ≫ φ) x
  refine J.transitive hS' _ ?_
  intro V₂ k hk
  obtain ⟨t, ht⟩ := hfam k hk
  rw [imageSieve_pullback_eq, hx', ← NatTrans.naturality_apply
    (toSheafify J (characterTwistTensorPresheaf (characterTwist W act χ J).obj act χ)) k.op, ht]
  refine J.transitive (Presheaf.imageSieve_mem J
    (toSheafify J (characterTwistPresheaf W act χ)) t) _ ?_
  rintro V₃ m ⟨x₂, hx₂⟩
  have hx₂' : (characterTwist W act χ J).obj.map m.op t =
      (toSheafify J (characterTwistPresheaf W act χ)).app (op V₃) x₂ := hx₂.symm
  rw [imageSieve_pullback_eq, show (toSheafify J
      (characterTwistTensorPresheaf (characterTwist W act χ J).obj act χ)).app (op V₂)
      (characterTwistTensorGen act χ t (twistedGenerator W act χ (k ≫ f ≫ φ))) =
      twistTensorGenSection act χ t (k ≫ f ≫ φ) from rfl,
    twistTensorGenSection_map, hx₂']
  obtain ⟨S'', hS'', hfam''⟩ :=
    h.exists_sieve_twistedGenerator_zsmul χ (m ≫ k ≫ f ≫ φ) x₂
  refine J.superset_covering ?_ hS''
  intro V₄ r hr
  obtain ⟨n, hn⟩ := hfam'' r hr
  refine ⟨ULift.up n, ?_⟩
  have e1 : (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.map r.op
        (twistTensorGenSection act χ
          ((toSheafify J (characterTwistPresheaf W act χ)).app (op V₃) x₂)
          (m ≫ k ≫ f ≫ φ)) =
      twistTensorGenSection act χ
        ((characterTwist W act χ J).obj.map r.op
          ((toSheafify J (characterTwistPresheaf W act χ)).app (op V₃) x₂))
        (r ≫ m ≫ k ≫ f ≫ φ) :=
    twistTensorGenSection_map (F := characterTwist W act χ J) act χ _ _ _
  have e2 : (characterTwist W act χ J).obj.map r.op
        ((toSheafify J (characterTwistPresheaf W act χ)).app (op V₃) x₂) =
      (toSheafify J (characterTwistPresheaf W act χ)).app (op V₄)
        ((characterTwistPresheaf W act χ).map r.op x₂) :=
    (NatTrans.naturality_apply
      (toSheafify J (characterTwistPresheaf W act χ)) r.op x₂).symm
  refine (h.twistTensorUnit_app χ hT (r ≫ m ≫ k ≫ f ≫ φ) (ULift.up n)).trans ?_
  rw [e1, e2, hn, map_zsmul]
  exact (twistTensorGenSection_zsmul (F := characterTwist W act χ J) act χ n _ _).symm

/-- **The unit of the tensor square is locally surjective.** -/
theorem isLocallySurjective_twistTensorUnit :
    Presheaf.IsLocallySurjective J (h.twistTensorUnit χ hT) := by
  constructor
  intro V y
  refine J.transitive (h.splittingSieve_mem V) _ ?_
  rintro V₁ f ⟨φ⟩
  refine J.superset_covering ?_
    (h.imageSieve_twistTensorUnit_mem χ hT φ
      ((characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.map f.op y))
  intro V₂ k hk
  obtain ⟨z, hz⟩ := hk
  refine ⟨z, ?_⟩
  show (h.twistTensorUnit χ hT).app (op V₂) z =
    (characterTwistTensor (characterTwist W act χ J).obj act χ J).obj.map (k ≫ f).op y
  rw [hz, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **The unit of the tensor square is locally injective.** -/
theorem isLocallyInjective_twistTensorUnit :
    Presheaf.IsLocallyInjective J (h.twistTensorUnit χ hT) := by
  constructor
  intro V n₁ n₂ heq
  by_cases hne : n₁ = n₂
  · rw [hne, Presheaf.equalizerSieve_self_eq_top]
    exact J.top_mem _
  refine J.superset_covering bot_le ?_
  have hmne : n₁.down - n₂.down ≠ 0 := sub_ne_zero.mpr fun hm => hne (ULift.ext hm)
  have hrestrict : ∀ {V₁ : C} (f : V₁ ⟶ V.unop),
      (h.twistTensorUnit χ hT).app (op V₁) n₁ =
        (h.twistTensorUnit χ hT).app (op V₁) n₂ := by
    intro V₁ f
    have h1 := NatTrans.naturality_apply (h.twistTensorUnit χ hT) f.op n₁
    have h2 := NatTrans.naturality_apply (h.twistTensorUnit χ hT) f.op n₂
    change (h.twistTensorUnit χ hT).app (op V₁) n₁ = _ at h1
    change (h.twistTensorUnit χ hT).app (op V₁) n₂ = _ at h2
    rw [h1, h2, heq]
  have hbotW : ∀ {V₁ : C} (f : V₁ ⟶ V.unop) (φ : V₁ ⟶ W), (⊥ : Sieve V₁) ∈ J V₁ := by
    intro V₁ f φ
    have := (J.W_toSheafify (characterTwistPresheaf W act χ)).isLocallyInjective
    have hgs : (n₁.down - n₂.down) • twistTensorGenSection act χ
        ((toSheafify J (characterTwistPresheaf W act χ)).app (op V₁)
          (twistedGenerator W act χ φ)) φ = 0 := by
      have e := hrestrict f
      rw [h.twistTensorUnit_app χ hT φ, h.twistTensorUnit_app χ hT φ] at e
      rw [sub_smul, e, sub_self]
    have hzero : twistTensorGenSection (F := characterTwist W act χ J) act χ 0 φ = 0 := by
      unfold twistTensorGenSection
      rw [characterTwistTensorGen_zero_left]
      exact map_zero _
    have hvan : (n₁.down - n₂.down) •
        (toSheafify J (characterTwistPresheaf W act χ)).app (op V₁)
          (twistedGenerator W act χ φ) = 0 := by
      refine h.twistTensorGenSection_injective χ φ ?_
      dsimp only
      exact (twistTensorGenSection_zsmul (F := characterTwist W act χ J) act χ
        (n₁.down - n₂.down) _ φ).trans (hgs.trans hzero.symm)
    have hpre : (toSheafify J (characterTwistPresheaf W act χ)).app (op V₁)
          ((n₁.down - n₂.down) • twistedGenerator W act χ φ) =
        (toSheafify J (characterTwistPresheaf W act χ)).app (op V₁) 0 := by
      rw [map_zsmul, hvan, map_zero]
    refine J.transitive (Presheaf.equalizerSieve_mem J
      (toSheafify J (characterTwistPresheaf W act χ)) _ _ hpre) _ ?_
    intro V₂ k hk
    refine J.superset_covering bot_le ?_
    by_contra hbot
    have hk' : (characterTwistPresheaf W act χ).map k.op
          ((n₁.down - n₂.down) • twistedGenerator W act χ φ) =
        (characterTwistPresheaf W act χ).map k.op 0 := hk
    rw [map_zsmul, map_zero, characterTwistPresheaf_map_twistedGenerator] at hk'
    have hz : (0 : ℤ) • twistedGenerator W act χ (k ≫ φ) = 0 := zero_smul _ _
    exact hmne (h.zsmul_twistedGenerator_injective χ (k ≫ φ) hbot (hk'.trans hz.symm))
  refine J.transitive (h.splittingSieve_mem V.unop) _ ?_
  rintro V₁ f ⟨φ⟩
  exact J.superset_covering bot_le (hbotW f φ)

/-- **`ℤ(χ)` is invertible: the unit of its tensor square is inverted by sheafification.** -/
theorem w_twistTensorUnit : J.W (h.twistTensorUnit χ hT) :=
  (GrothendieckTopology.WEqualsLocallyBijective.iff _).2
    ⟨h.isLocallyInjective_twistTensorUnit χ hT, h.isLocallySurjective_twistTensorUnit χ hT⟩

/-- **`ℤ ≅ ℤ(χ) ⊗_ℤ ℤ(χ)`.** The character twist of a torsor is its own inverse for the tensor
product of abelian sheaves. -/
noncomputable def constantSheafIsoTwistTensorSelf :
    (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      characterTwistTensor (characterTwist W act χ J).obj act χ J :=
  letI h1 : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (h.twistTensorUnit χ hT)) := (J.W_iff _).1 (h.w_twistTensorUnit χ hT)
  (@asIso _ _ _ _ _ h1) ≪≫
    asIso ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app
      (characterTwistTensor (characterTwist W act χ J).obj act χ J))

/-- The morphism `ℤ ⟶ ℤ(χ) ⊗_ℤ ℤ(χ)` of abelian sheaves determined by the canonical global section
of the tensor square. -/
def constantToTwistTensorSelf :
    (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      characterTwistTensor (characterTwist W act χ J).obj act χ J :=
  (h.constantSheafIsoTwistTensorSelf χ hT).hom

/-- The morphism `ℤ ⟶ ℤ(χ) ⊗_ℤ ℤ(χ)` of abelian sheaves is an isomorphism. -/
instance isIso_constantToTwistTensorSelf :
    IsIso (h.constantToTwistTensorSelf χ hT) :=
  (h.constantSheafIsoTwistTensorSelf χ hT).isIso_hom

end Tensor

end IsTorsorObject

end CategoryTheory

end
