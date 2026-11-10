module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistTorsor

/-!
# Sections of a sheaf twisted by a character of a group acting on a torsor

Let `W` be a torsor under a group `G` over the final object of a site, in the sense of
`CategoryTheory.IsTorsorObject`, and let `χ : G → ℤˣ` be a character. Tensoring an abelian sheaf
`F` with the twisted free abelian sheaf `ℤ(χ)` and taking global sections recovers the sections
of `F` over `W` that transform according to `χ`.

The comparison is built by descent along the covering of the final object by `W`: a section `s`
of `F` over `W` transforming according to `χ` determines, over an object `V` carrying a morphism
`φ : V ⟶ W`, the local section `s|_φ ⊗ [φ]` of `F ⊗_ℤ ℤ(χ)`, and that local section does not
depend on `φ`, because two choices differ locally by a group element `g` which contributes
`χ g` twice, and `χ g` is its own inverse. The local sections therefore glue, and the resulting
global section determines `s` back because the class of `φ` generates a direct summand of the
twist presheaf.

## Main definitions

* `CategoryTheory.characterTwistTensorPresheaf` is the objectwise tensor product of an abelian
  presheaf with the twist presheaf, and `CategoryTheory.characterTwistTensor` its
  sheafification, which is `F ⊗_ℤ ℤ(χ)`.
* `CategoryTheory.IsTorsorObject.twistTensorLocalSection` is the local section described above.

## Main results

* `AddCommGrpCat.W_presheafTensorMap_id`: tensoring with a fixed presheaf of abelian groups
  preserves the morphisms inverted by sheafification, so `F ⊗_ℤ ℤ(χ)` may equally be computed
  from the twist presheaf or from the twisted sheaf.
* `CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv`: **Stacks 0727**, the sections of `F`
  over `W` transforming according to `χ` are the global sections of `F ⊗_ℤ ℤ(χ)`. The other
  half of that tag, the local freeness of rank one of `ℤ(χ)`, is
  `CategoryTheory.characterTwistOverIso`.

## Implementation notes

The tensor product of presheaves of abelian groups used here is
`AddCommGrpCat.presheafTensor`, which is defined for an arbitrary category; the results of the
first two sections are therefore statements about an arbitrary site, even though they are
recorded in this directory, where that tensor product lives.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0722](https://stacks.math.columbia.edu/tag/0722)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Enriched.FunctorCategory

universe w v₁ u₁ u

namespace AddCommGrpCat

/-- **Tensoring with a fixed presheaf of abelian groups preserves the morphisms inverted by
sheafification.** This is the monoidality of the class of local isomorphisms, read through the
identification of the objectwise tensor product with the transported monoidal structure. -/
theorem W_presheafTensorMap_id {C : Type u₁} [Category.{v₁} C] [UnivLE.{max u₁ v₁, u + 1}]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {g : G₁ ⟶ G₂} (hg : J.W g) :
    J.W (presheafTensorMap (𝟙 F) g) := by
  let : MonoidalCategory AddCommGrpCat.{u + 1} := monoidalCategory.{u + 1}
  let : (uliftIntEquivalence.{u + 1}).inverse.Monoidal := by
    change (Monoidal.equivalenceTransported (uliftIntEquivalence.{u + 1})).inverse.Monoidal
    infer_instance
  let : MonoidalClosed AddCommGrpCat.{u + 1} :=
    MonoidalClosed.ofEquiv (uliftIntEquivalence.{u + 1}).inverse
      (uliftIntEquivalence.{u + 1}).symm.toAdjunction
  let : HasLimitsOfSize.{max u₁ v₁, max u₁ v₁} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasLimitsOfSize
  let : BraidedCategory AddCommGrpCat.{u + 1} := by
    change BraidedCategory (Monoidal.Transported (uliftIntEquivalence.{u + 1}))
    infer_instance
  let : EnrichedOrdinaryCategory AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := inferInstance
  let : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, HasFunctorEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ :=
    by
      intro F₁ F₂ V
      infer_instance
  let : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, HasEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ := by
    intro F₁ F₂
    infer_instance
  have hw : J.W (F ◁ g) := hg.whiskerLeft F
  refine (J.W.arrow_mk_iso_iff (Arrow.isoMk (presheafTensorIso F G₁) (presheafTensorIso F G₂)
    ?_)).2 hw
  change (presheafTensorIso F G₁).hom ≫ (F ◁ g) =
    presheafTensorMap (𝟙 F) g ≫ (presheafTensorIso F G₂).hom
  rw [presheafTensorMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    MonoidalCategory.id_tensorHom]

/-- The objectwise tensor product of presheaves of abelian groups acts on a pure tensor
componentwise. -/
theorem presheafTensor_map_tmul {C : Type u₁} [Category.{v₁} C]
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V V' : Cᵒᵖ} (f : V ⟶ V') (a : F.obj V) (x : G.obj V) :
    (presheafTensor F G).map f (a ⊗ₜ[ℤ] x) = F.map f a ⊗ₜ[ℤ] G.map f x :=
  rfl

end AddCommGrpCat

namespace CategoryTheory

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
  {W : C} {G : Type w} [Group G] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (χ : G →* ℤˣ)

/-- The objectwise tensor product over `ℤ` of an abelian presheaf with the presheaf whose
sheafification is the twist `ℤ(χ)`. -/
abbrev characterTwistTensorPresheaf (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (act : G →* Aut W)
    (χ : G →* ℤˣ) : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ)

/-- The tensor product `F ⊗_ℤ ℤ(χ)` of an abelian sheaf with the twist. -/
abbrev characterTwistTensor (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (act : G →* Aut W) (χ : G →* ℤˣ)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u + 1}] :
    Sheaf J AddCommGrpCat.{u + 1} :=
  (presheafToSheaf J AddCommGrpCat.{u + 1}).obj (characterTwistTensorPresheaf F act χ)

/-- A pure tensor in the objectwise tensor product of an abelian presheaf with the twist
presheaf. -/
def characterTwistTensorGen {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (act : G →* Aut W) (χ : G →* ℤˣ)
    {V : C} (a : F.obj (op V)) (x : (characterTwistPresheaf W act χ).obj (op V)) :
    (characterTwistTensorPresheaf F act χ).obj (op V) :=
  a ⊗ₜ[ℤ] x

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- Scaling both factors of a pure tensor by the same integer scales the tensor by its
square. -/
theorem characterTwistTensorGen_smul_smul {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (act : G →* Aut W)
    (χ : G →* ℤˣ) {V : C} (n : ℤ) (a : F.obj (op V))
    (x : (characterTwistPresheaf W act χ).obj (op V)) :
    characterTwistTensorGen act χ (n • a) (n • x) =
      (n * n) • characterTwistTensorGen act χ a x := by
  have key : (n • a) ⊗ₜ[ℤ] (n • x) = (n * n) • (a ⊗ₜ[ℤ] x) := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
      TensorProduct.smul_tmul']
  exact key

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- A pure tensor with zero first factor vanishes. -/
theorem characterTwistTensorGen_zero_left {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (act : G →* Aut W)
    (χ : G →* ℤˣ) {V : C} (x : (characterTwistPresheaf W act χ).obj (op V)) :
    characterTwistTensorGen (F := F) act χ 0 x = 0 :=
  TensorProduct.zero_tmul _ _

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- A pure tensor is additive in its first factor. -/
theorem characterTwistTensorGen_add_left {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (act : G →* Aut W)
    (χ : G →* ℤˣ) {V : C} (a a' : F.obj (op V))
    (x : (characterTwistPresheaf W act χ).obj (op V)) :
    characterTwistTensorGen act χ (a + a') x =
      characterTwistTensorGen act χ a x + characterTwistTensorGen act χ a' x :=
  TensorProduct.add_tmul _ _ _

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- An integer scalar may be moved from the second factor of a pure tensor to the first. -/
theorem characterTwistTensorGen_smul_left {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (act : G →* Aut W)
    (χ : G →* ℤˣ) {V : C} (n : ℤ) (a : F.obj (op V))
    (x : (characterTwistPresheaf W act χ).obj (op V)) :
    characterTwistTensorGen act χ a (n • x) = characterTwistTensorGen act χ (n • a) x := by
  have key : a ⊗ₜ[ℤ] (n • x) = (n • a) ⊗ₜ[ℤ] x := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact key

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- Restricting a pure tensor along `f` restricts each of its factors along `f`. -/
theorem characterTwistTensorPresheaf_map_gen {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (act : G →* Aut W) (χ : G →* ℤˣ) {V V' : C} (f : V' ⟶ V) (a : F.obj (op V))
    (x : (characterTwistPresheaf W act χ).obj (op V)) :
    (characterTwistTensorPresheaf F act χ).map f.op (characterTwistTensorGen act χ a x) =
      characterTwistTensorGen act χ (F.map f.op a) ((characterTwistPresheaf W act χ).map f.op x) :=
  rfl

/-- **The tensor product with the twist may be formed before or after sheafifying the twist.**
Tensoring with `F` carries the sheafification map of the twist presheaf to a local
isomorphism. -/
def characterTwistTensorIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (act : G →* Aut W) :
    characterTwistTensor F act χ J ≅
      (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.presheafTensor F (characterTwist W act χ J).obj) := by
  have hiso := (J.W_iff (AddCommGrpCat.presheafTensorMap (𝟙 F)
      (toSheafify J (characterTwistPresheaf W act χ)))).mp
    (AddCommGrpCat.W_presheafTensorMap_id J F (J.W_toSheafify _))
  exact @asIso _ _ _ _ _ hiso

namespace IsTorsorObject

variable {F : Sheaf J AddCommGrpCat.{u + 1}} (h : IsTorsorObject act J)

/-- The local section of `F ⊗_ℤ ℤ(χ)` over `V` attached to a section `s` of `F` over `W` and a
morphism `φ : V ⟶ W`: the restriction of `s` along `φ`, tensored with the class of `φ`. -/
def twistTensorLocalSection (act : G →* Aut W) (χ : G →* ℤˣ) (s : F.obj.obj (op W)) {V : C}
    (φ : V ⟶ W) : (characterTwistTensor F.obj act χ J).obj.obj (op V) :=
  (toSheafify J (characterTwistTensorPresheaf F.obj act χ)).app (op V)
    (characterTwistTensorGen act χ (F.obj.map φ.op s) (twistedGenerator W act χ φ))

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- Restricting the local section attached to `φ` along `f` gives the local section attached to
`f ≫ φ`. -/
theorem twistTensorLocalSection_map (act : G →* Aut W) (χ : G →* ℤˣ) (s : F.obj.obj (op W))
    {V V' : C} (f : V' ⟶ V) (φ : V ⟶ W) :
    (characterTwistTensor F.obj act χ J).obj.map f.op
        (twistTensorLocalSection (J := J) act χ s φ) =
      twistTensorLocalSection (J := J) act χ s (f ≫ φ) := by
  rw [twistTensorLocalSection, ← NatTrans.naturality_apply
    (toSheafify J (characterTwistTensorPresheaf F.obj act χ)) f.op,
    characterTwistTensorPresheaf_map_gen, characterTwistPresheaf_map_twistedGenerator,
    twistTensorLocalSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The local section attached to a morphism to the torsor is additive in the section. -/
theorem twistTensorLocalSection_add (act : G →* Aut W) (χ : G →* ℤˣ) (s s' : F.obj.obj (op W))
    {V : C} (φ : V ⟶ W) :
    twistTensorLocalSection (J := J) act χ (s + s') φ =
      twistTensorLocalSection (J := J) act χ s φ + twistTensorLocalSection (J := J) act χ s' φ := by
  rw [twistTensorLocalSection, twistTensorLocalSection, twistTensorLocalSection, ← map_add,
    map_add]
  congr 1
  exact TensorProduct.add_tmul _ _ _

/-- The local section of `F ⊗_ℤ ℤ(χ)` over `V` built from a section of `F` over `V` and a
morphism `V ⟶ W`. -/
def twistTensorGenSection (act : G →* Aut W) (χ : G →* ℤˣ) {V : C} (t : F.obj.obj (op V))
    (f : V ⟶ W) : (characterTwistTensor F.obj act χ J).obj.obj (op V) :=
  (toSheafify J (characterTwistTensorPresheaf F.obj act χ)).app (op V)
    (characterTwistTensorGen act χ t (twistedGenerator W act χ f))

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The local section attached to `s` and `φ` is the section built from the restriction of `s`
along `φ` and from `φ`. -/
theorem twistTensorLocalSection_eq_genSection (act : G →* Aut W) (χ : G →* ℤˣ)
    (s : F.obj.obj (op W)) {V : C} (φ : V ⟶ W) :
    twistTensorLocalSection (J := J) act χ s φ =
      twistTensorGenSection (J := J) act χ (F.obj.map φ.op s) φ :=
  rfl

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- Restricting the section built from `t` and `f` along `k` gives the section built from the
restriction of `t` and from `k ≫ f`. -/
theorem twistTensorGenSection_map (act : G →* Aut W) (χ : G →* ℤˣ) {V V' : C}
    (t : F.obj.obj (op V)) (f : V ⟶ W) (k : V' ⟶ V) :
    (characterTwistTensor F.obj act χ J).obj.map k.op (twistTensorGenSection (J := J) act χ t f) =
      twistTensorGenSection (J := J) act χ (F.obj.map k.op t) (k ≫ f) := by
  rw [twistTensorGenSection, ← NatTrans.naturality_apply
    (toSheafify J (characterTwistTensorPresheaf F.obj act χ)) k.op,
    characterTwistTensorPresheaf_map_gen, characterTwistPresheaf_map_twistedGenerator,
    twistTensorGenSection]

omit [UnivLE.{max u₁ (u + 1), u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The section built from `t` and `f` is additive in `t`. -/
theorem twistTensorGenSection_sub (act : G →* Aut W) (χ : G →* ℤˣ) {V : C}
    (t t' : F.obj.obj (op V)) (f : V ⟶ W) :
    twistTensorGenSection (J := J) act χ (t - t') f =
      twistTensorGenSection (J := J) act χ t f - twistTensorGenSection (J := J) act χ t' f := by
  rw [twistTensorGenSection, twistTensorGenSection, twistTensorGenSection, ← map_sub]
  congr 1
  exact TensorProduct.sub_tmul _ _ _

include h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The local section does not depend on the chosen morphism to `W`.** Two morphisms
`φ ψ : V ⟶ W` differ locally by a group element `g`, which multiplies both tensor factors by
`χ g`; since `χ g` is its own inverse the two local sections agree. -/
theorem twistTensorLocalSection_eq (s : characterSections W act χ F.obj) {V : C}
    (φ ψ : V ⟶ W) :
    twistTensorLocalSection (J := J) act χ s.1 φ =
      twistTensorLocalSection (J := J) act χ s.1 ψ := by
  refine (characterTwistTensor F.obj act χ J).isSeparated V (translationSieve act φ ψ)
    (h.translationSieve_mem φ ψ) _ _ ?_
  rintro V' f ⟨g, hg⟩
  have hcomp : f ≫ ψ = (f ≫ φ) ≫ (act g).asIso.hom := by rw [hg, Category.assoc]
  have hgen : twistedGenerator W act χ (f ≫ ψ) =
      (χ g : ℤ) • twistedGenerator W act χ (f ≫ φ) := by
    rw [hcomp, twistedGenerator_act]
  have hsec : F.obj.map (f ≫ ψ).op s.1 = (χ g : ℤ) • F.obj.map (f ≫ φ).op s.1 := by
    rw [hcomp, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, s.2 g, map_zsmul]
  have key : characterTwistTensorGen act χ (F.obj.map (f ≫ φ).op s.1)
        (twistedGenerator W act χ (f ≫ φ)) =
      characterTwistTensorGen act χ (F.obj.map (f ≫ ψ).op s.1)
        (twistedGenerator W act χ (f ≫ ψ)) := by
    rw [hgen, hsec, characterTwistTensorGen_smul_smul, Int.units_coe_mul_self, one_smul]
  rw [twistTensorLocalSection_map, twistTensorLocalSection_map, twistTensorLocalSection,
    twistTensorLocalSection, key]

/-- **A section of `F` is determined by the local section of `F ⊗_ℤ ℤ(χ)` it builds.** If the
local section attached to `t` and a morphism `p : V ⟶ W` vanishes, then `t` vanishes. -/
theorem eq_zero_of_toSheafify_tensorGen_eq_zero {V : C} (p : V ⟶ W) (t : F.obj.obj (op V))
    (ht : (toSheafify J (characterTwistTensorPresheaf F.obj act χ)).app (op V)
        (characterTwistTensorGen act χ t (twistedGenerator W act χ p)) = 0) :
    t = 0 := by
  have := (J.W_toSheafify (characterTwistTensorPresheaf F.obj act χ)).isLocallyInjective
  have hzero : (toSheafify J (characterTwistTensorPresheaf F.obj act χ)).app (op V)
      (characterTwistTensorGen act χ t (twistedGenerator W act χ p)) =
      (toSheafify J (characterTwistTensorPresheaf F.obj act χ)).app (op V) 0 := by
    rw [ht, map_zero]
  have hmem := Presheaf.equalizerSieve_mem J
    (toSheafify J (characterTwistTensorPresheaf F.obj act χ))
    (characterTwistTensorGen act χ t (twistedGenerator W act χ p)) 0 hzero
  refine F.isSeparated V _ hmem t 0 ?_
  intro V' f hf
  have hf' : (characterTwistTensorPresheaf F.obj act χ).map f.op
      (characterTwistTensorGen act χ t (twistedGenerator W act χ p)) =
      (characterTwistTensorPresheaf F.obj act χ).map f.op 0 := hf
  rw [map_zero] at hf'
  rw [characterTwistTensorPresheaf_map_gen, characterTwistPresheaf_map_twistedGenerator] at hf'
  rw [map_zero]
  by_cases hbot : (⊥ : Sieve V') ∈ J V'
  · exact F.isSeparated V' ⊥ hbot _ 0 (fun _ _ hg => hg.elim)
  · refine h.injective_tmul_twistedGenerator χ (f ≫ p) hbot ?_
    change characterTwistTensorGen act χ (F.obj.map f.op t) (twistedGenerator W act χ (f ≫ p)) =
      characterTwistTensorGen act χ 0 (twistedGenerator W act χ (f ≫ p))
    rw [hf', characterTwistTensorGen]
    exact (TensorProduct.zero_tmul _ _).symm

/-- The section built from `t` and `f` determines `t`. -/
private theorem eq_of_twistTensorGenSection_eq {V : C} (f : V ⟶ W) {t t' : F.obj.obj (op V)}
    (htt : twistTensorGenSection (J := J) act χ t f = twistTensorGenSection (J := J) act χ t' f) :
    t = t' := by
  refine sub_eq_zero.mp (h.eq_zero_of_toSheafify_tensorGen_eq_zero χ f (t - t') ?_)
  have hsub := twistTensorGenSection_sub (J := J) act χ t t' f
  rwa [htt, sub_self] at hsub

/-! ### The global section attached to a section over the torsor -/

section Global

variable {T : C} (hT : IsTerminal T)

include hT

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] hT in
/-- The covering of the final object by the torsor is a sheaf covering for `F ⊗_ℤ ℤ(χ)`. -/
theorem isSheafFor_splittingSieve :
    Presieve.IsSheafFor ((characterTwistTensor F.obj act χ J).obj ⋙ forget AddCommGrpCat.{u + 1})
      ((splittingSieve W T : Sieve T) : Presieve T) :=
  ((isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj
      (characterTwistTensor F.obj act χ J)).2) _ (h.splittingSieve_mem T)

/-- The family of local sections of `F ⊗_ℤ ℤ(χ)` indexed by the covering of the final object by
the torsor. -/
def twistTensorFamily (s : characterSections W act χ F.obj) :
    Presieve.FamilyOfElements
      ((characterTwistTensor F.obj act χ J).obj ⋙ forget AddCommGrpCat.{u + 1})
      ((splittingSieve W T : Sieve T) : Presieve T) :=
  fun _ _ hk => twistTensorLocalSection (J := J) act χ s.1 (Classical.choice hk)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] hT in
/-- The family of local sections attached to a section transforming according to `χ` is
compatible. -/
theorem twistTensorFamily_compatible (s : characterSections W act χ F.obj) :
    (twistTensorFamily (J := J) (T := T) χ s).Compatible := by
  intro V₁ V₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ _
  change (characterTwistTensor F.obj act χ J).obj.map g₁.op
      (twistTensorLocalSection (J := J) act χ s.1 (Classical.choice hk₁)) =
    (characterTwistTensor F.obj act χ J).obj.map g₂.op
      (twistTensorLocalSection (J := J) act χ s.1 (Classical.choice hk₂))
  rw [twistTensorLocalSection_map, twistTensorLocalSection_map]
  exact h.twistTensorLocalSection_eq χ s _ _

/-- **The global section of `F ⊗_ℤ ℤ(χ)` attached to a section of `F` over the torsor that
transforms according to `χ`**, obtained by glueing the local sections. -/
def twistTensorGlobalSection (s : characterSections W act χ F.obj) :
    (characterTwistTensor F.obj act χ J).obj.obj (op T) :=
  (h.isSheafFor_splittingSieve χ).amalgamate _ (h.twistTensorFamily_compatible χ s)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The global section restricts, over an object carrying a morphism `φ` to the torsor, to the
local section attached to `φ`. -/
theorem twistTensorGlobalSection_map (s : characterSections W act χ F.obj) {V : C}
    (φ : V ⟶ W) :
    (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op
        (h.twistTensorGlobalSection (T := T) χ s) =
      twistTensorLocalSection (J := J) act χ s.1 φ := by
  have hk : (splittingSieve W T : Sieve T).arrows (hT.from V) := ⟨φ⟩
  have hglue := (h.isSheafFor_splittingSieve χ).valid_glue
    (h.twistTensorFamily_compatible χ s) (hT.from V) hk
  refine hglue.trans ?_
  exact h.twistTensorLocalSection_eq χ s _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The global section is additive in the section over the torsor.** -/
theorem twistTensorGlobalSection_add {F : Sheaf J AddCommGrpCat.{u + 1}}
    (s s' : characterSections W act χ F.obj) :
    h.twistTensorGlobalSection (T := T) χ (s + s') =
      h.twistTensorGlobalSection (T := T) χ s + h.twistTensorGlobalSection (T := T) χ s' := by
  refine (characterTwistTensor F.obj act χ J).isSeparated T _ (h.splittingSieve_mem T) _ _ ?_
  rintro V k ⟨φ⟩
  obtain rfl : k = hT.from V := hT.hom_ext k _
  rw [map_add, h.twistTensorGlobalSection_map χ hT (s + s') φ,
    h.twistTensorGlobalSection_map χ hT s φ, h.twistTensorGlobalSection_map χ hT s' φ]
  exact twistTensorLocalSection_add act χ s.1 s'.1 φ

/-- **A section over the torsor is recovered from its global section.** -/
theorem twistTensorGlobalSection_injective (F : Sheaf J AddCommGrpCat.{u + 1}) :
    Function.Injective fun s : characterSections W act χ F.obj =>
      h.twistTensorGlobalSection (T := T) χ s := by
  intro s s' hss
  have hW := (h.twistTensorGlobalSection_map χ hT s (𝟙 W)).symm.trans
    ((congrArg (fun z => (characterTwistTensor F.obj act χ J).obj.map (hT.from W).op z) hss).trans
      (h.twistTensorGlobalSection_map χ hT s' (𝟙 W)))
  simp only [twistTensorLocalSection_eq_genSection, op_id, F.obj.map_id,
    ConcreteCategory.id_apply] at hW
  exact Subtype.ext (h.eq_of_twistTensorGenSection_eq χ (𝟙 W) hW)

omit hT in
/-- **The section of `F` built from a section of `F ⊗_ℤ ℤ(χ)` is unique.** -/
theorem twistTensorGenSection_injective {V : C} (f : V ⟶ W) :
    Function.Injective fun t : F.obj.obj (op V) => twistTensorGenSection (J := J) act χ t f := by
  intro t t' htt
  exact h.eq_of_twistTensorGenSection_eq χ f htt

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] hT in
/-- **Locally on an object lying over `W`, every section of the presheaf underlying
`F ⊗_ℤ ℤ(χ)` is a section of `F` tensored with the class of the structure morphism.** -/
theorem exists_sieve_twistTensorGen {V : C} (p : V ⟶ W)
    (y : (characterTwistTensorPresheaf F.obj act χ).obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f →
      ∃ t : F.obj.obj (op V'), (characterTwistTensorPresheaf F.obj act χ).map f.op y =
        characterTwistTensorGen act χ t (twistedGenerator W act χ (f ≫ p)) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨S, hS, hfam⟩ := h.exists_sieve_twistedGenerator_zsmul χ p x
    refine ⟨S, hS, fun V' f hf => ?_⟩
    obtain ⟨n, hn⟩ := hfam f hf
    refine ⟨n • F.obj.map f.op a, ?_⟩
    have hy : (characterTwistTensorPresheaf F.obj act χ).map f.op
        (characterTwistTensorGen act χ a x) =
        characterTwistTensorGen act χ (F.obj.map f.op a)
          ((characterTwistPresheaf W act χ).map f.op x) :=
      characterTwistTensorPresheaf_map_gen act χ f a x
    refine hy.trans ?_
    rw [hn, characterTwistTensorGen_smul_left]
  | add y y' hy hy' =>
    obtain ⟨S, hS, hfam⟩ := hy
    obtain ⟨S', hS', hfam'⟩ := hy'
    refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V' f hf => ?_⟩
    obtain ⟨t, ht⟩ := hfam f hf.1
    obtain ⟨t', ht'⟩ := hfam' f hf.2
    refine ⟨t + t', ?_⟩
    have hadd : (characterTwistTensorPresheaf F.obj act χ).map f.op (y + y') =
        (characterTwistTensorPresheaf F.obj act χ).map f.op y +
          (characterTwistTensorPresheaf F.obj act χ).map f.op y' := map_add _ _ _
    rw [hadd, ht, ht', characterTwistTensorGen_add_left]

/-- **Every global section of `F ⊗_ℤ ℤ(χ)` comes from a section of `F` over the torsor
transforming according to `χ`.** -/
theorem twistTensorGlobalSection_surjective (F : Sheaf J AddCommGrpCat.{u + 1}) :
    Function.Surjective fun s : characterSections W act χ F.obj =>
      h.twistTensorGlobalSection (T := T) χ s := by
  intro τ
  have hres : ∀ {V V' : C} (k : V' ⟶ V),
      (characterTwistTensor F.obj act χ J).obj.map k.op
          ((characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ) =
        (characterTwistTensor F.obj act χ J).obj.map (hT.from V').op τ := by
    intro V V' k
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congrArg (fun m => (characterTwistTensor F.obj act χ J).obj.map
      (Opposite.op m) τ) (hT.hom_ext _ _)
  let S : Sieve W :=
    { arrows := fun V f => ∃ t : F.obj.obj (op V),
        twistTensorGenSection (J := J) act χ t f =
          (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ
      downward_closed := by
        rintro V V' f ⟨t, ht⟩ k
        exact ⟨F.obj.map k.op t, by
          rw [← twistTensorGenSection_map, ht, hres]⟩ }
  have hScov : S ∈ J W := by
    have := (J.W_toSheafify (characterTwistTensorPresheaf F.obj act χ)).isLocallySurjective
    refine J.transitive (Presheaf.imageSieve_mem J
      (toSheafify J (characterTwistTensorPresheaf F.obj act χ))
      ((characterTwistTensor F.obj act χ J).obj.map (hT.from W).op τ)) S ?_
    rintro V f ⟨y, hy⟩
    obtain ⟨S', hS', hfam⟩ := h.exists_sieve_twistTensorGen χ f y
    refine J.superset_covering ?_ hS'
    intro V' k hk
    obtain ⟨t, ht⟩ := hfam k hk
    refine ⟨t, ?_⟩
    rw [twistTensorGenSection, ← ht, NatTrans.naturality_apply
      (toSheafify J (characterTwistTensorPresheaf F.obj act χ)) k.op, hy]
    exact (congrArg (fun z => (characterTwistTensor F.obj act χ J).obj.map k.op z)
      (hres f)).trans (hres k)
  have hFsheaf : Presieve.IsSheafFor (F.obj ⋙ forget AddCommGrpCat.{u + 1})
      ((S : Sieve W) : Presieve W) :=
    ((isSheaf_iff_isSheaf_of_type J _).1
      ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj F).2) _ hScov
  let fam : Presieve.FamilyOfElements (F.obj ⋙ forget AddCommGrpCat.{u + 1})
      ((S : Sieve W) : Presieve W) := fun _ _ hf => hf.choose
  have hfamspec : ∀ ⦃V : C⦄ (f : V ⟶ W) (hf : (S : Sieve W).arrows f),
      twistTensorGenSection (J := J) act χ (fam f hf) f =
        (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ :=
    fun _ _ hf => hf.choose_spec
  have hcompat : fam.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    refine h.twistTensorGenSection_injective χ (g₁ ≫ f₁) ?_
    have e : ∀ {Y Y' : C} (g : Y ⟶ Y') (f : Y' ⟶ W) (hf : (S : Sieve W).arrows f),
        twistTensorGenSection (J := J) act χ (F.obj.map g.op (fam f hf)) (g ≫ f) =
          (characterTwistTensor F.obj act χ J).obj.map (hT.from Y).op τ := by
      intro Y Y' g f hf
      rw [← twistTensorGenSection_map, hfamspec, hres]
    have e₂ := e g₂ f₂ hf₂
    rw [← heq] at e₂
    exact (e g₁ f₁ hf₁).trans e₂.symm
  obtain ⟨s, hs⟩ : ∃ s : F.obj.obj (op W), ∀ {V : C} (f : V ⟶ W)
      (hf : (S : Sieve W).arrows f), F.obj.map f.op s = fam f hf :=
    ⟨hFsheaf.amalgamate fam hcompat, fun f hf => hFsheaf.valid_glue hcompat f hf⟩
  have hgen : ∀ {V : C} (f : V ⟶ W), (S : Sieve W).arrows f →
      twistTensorGenSection (J := J) act χ (F.obj.map f.op s) f =
        (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ := by
    intro V f hf
    rw [hs f hf, hfamspec]
  have hchar : s ∈ characterSections W act χ F.obj := by
    intro g
    refine F.isSeparated W S hScov _ _ ?_
    intro V f hf
    have ht : twistTensorGenSection (J := J) act χ (F.obj.map f.op s) f =
      (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ := hgen f hf
    have hfgwit : twistTensorGenSection (J := J) act χ ((χ g : ℤ) • F.obj.map f.op s)
        (f ≫ (act g).asIso.hom) =
        (characterTwistTensor F.obj act χ J).obj.map (hT.from V).op τ := by
      rw [twistTensorGenSection, twistedGenerator_act, characterTwistTensorGen_smul_smul,
        Int.units_coe_mul_self, one_smul]
      exact ht
    have key := h.twistTensorGenSection_injective χ (f ≫ (act g).asIso.hom)
      ((hgen (f ≫ (act g).asIso.hom) ⟨_, hfgwit⟩).trans hfgwit.symm)
    rw [map_zsmul, ← key, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]
  refine ⟨⟨s, hchar⟩, ?_⟩
  refine (characterTwistTensor F.obj act χ J).isSeparated T _ (h.splittingSieve_mem T) _ _ ?_
  rintro V k ⟨φ⟩
  obtain rfl : k = hT.from V := hT.hom_ext k _
  rw [h.twistTensorGlobalSection_map χ hT ⟨s, hchar⟩ φ, twistTensorLocalSection_eq_genSection]
  refine (characterTwistTensor F.obj act χ J).isSeparated V _
    (J.pullback_stable φ hScov) _ _ ?_
  intro V' m hm
  have hmφ : F.obj.map m.op (F.obj.map φ.op s) = F.obj.map (m ≫ φ).op s := by
    rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]
  rw [twistTensorGenSection_map, hres, hmφ]
  exact hgen (m ≫ φ) hm

/-- For a torsor `W` under a group `G` over the final object of a site and a character
`χ : G → ℤˣ`, the sections of an abelian sheaf `F` over `W` that transform according to `χ` are
the global sections of `F ⊗_ℤ ℤ(χ)`, where `ℤ(χ)` is the twisted free abelian sheaf on `W`. -/
@[stacks 0727 "the sections transforming according to the character"]
def twistTensorSectionsEquiv (F : Sheaf J AddCommGrpCat.{u + 1}) :
    characterSections W act χ F.obj ≃+ (characterTwistTensor F.obj act χ J).obj.obj (op T) :=
  { Equiv.ofBijective (fun s : characterSections W act χ F.obj =>
      h.twistTensorGlobalSection (T := T) χ s)
      ⟨h.twistTensorGlobalSection_injective χ hT F,
        h.twistTensorGlobalSection_surjective χ hT F⟩ with
    map_add' := h.twistTensorGlobalSection_add χ hT }

/-- The equivalence sends a section over the torsor to its global section. -/
@[simp]
theorem twistTensorSectionsEquiv_apply (F : Sheaf J AddCommGrpCat.{u + 1})
    (s : characterSections W act χ F.obj) :
    h.twistTensorSectionsEquiv χ hT F s = h.twistTensorGlobalSection (T := T) χ s :=
  rfl

end Global

end IsTorsorObject

end CategoryTheory

end
