module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invariant opens of a descent datum, and the restricted datum

Let `f i : X i ⟶ S` be a family of morphisms of schemes with common target and let `D` be a
descent datum for that family, with components `V i` over `X i` and gluing isomorphisms
`φ i j : V i ×_S X j ≅ X i ×_S V j`. A family of open subschemes `W i ⊆ V i` is *invariant*
when each gluing isomorphism carries `W i ×_S X j` onto `X i ×_S W j`.

An invariant family carries a descent datum of its own: its component at `i` is the open
subscheme `W i`, and its gluing isomorphism is the restriction of `φ i j`. The inclusions
assemble into a morphism of descent data whose components are open immersions; conversely the
images of a morphism of descent data with open-immersion components form an invariant family.

## Main definitions

* `AlgebraicGeometry.DescentData.IsInvariantOpens` is invariance of a family of open
  subschemes of the components of a descent datum.
* `AlgebraicGeometry.DescentData.openInclusion` is the inclusion of `W i` into the `i`-th
  component; `AlgebraicGeometry.DescentData.sourceInclusion` and
  `AlgebraicGeometry.DescentData.targetInclusion` are its base changes to the source and the
  target of a gluing isomorphism.
* `AlgebraicGeometry.DescentData.restrictGluing` is the restriction of a gluing isomorphism to
  an invariant family, and `AlgebraicGeometry.DescentData.restrictGluingIso` is it as an
  isomorphism.
* `AlgebraicGeometry.DescentData.restrict` is the descent datum carried by an invariant family
  of opens, and `AlgebraicGeometry.DescentData.restrictHom` its inclusion into the original
  datum.
* `AlgebraicGeometry.DescentData.mkIso` builds an isomorphism of descent data from a family of
  isomorphisms of the components.
* `AlgebraicGeometry.DescentData.openImmersionComponentIso` identifies a component of an
  open-immersion morphism of descent data with the open subscheme which is its image.

## Main results

* `AlgebraicGeometry.DescentData.isInvariantOpens_iff_gluing` restates invariance in terms of
  the products over `S` which carry the gluing isomorphisms; this is the form the construction
  uses.
* `AlgebraicGeometry.DescentData.isOpenImmersion_restrictHom` and
  `AlgebraicGeometry.DescentData.opensRange_restrictHom`: the inclusion of the restricted datum
  has open immersions for components, with images the given opens.
* `AlgebraicGeometry.DescentData.isInvariantOpens_opensRange`: the images of a morphism of
  descent data whose components are open immersions form an invariant family of opens.
* `AlgebraicGeometry.DescentData.openImmersionIsoRestrict` and
  `AlgebraicGeometry.DescentData.openImmersionIsoRestrict_hom_comp_restrictHom`: a morphism of
  descent data with open-immersion components *is* the inclusion of the restriction to the
  invariant family of its images. So the restricted data of invariant families are, up to
  isomorphism, exactly the descent data mapping to `D` by open immersions.
* `CategoryTheory.Limits.isPullback_prodMap_id` and
  `CategoryTheory.Limits.isPullback_id_prodMap`: applying a map to one factor of a binary
  product is a base change of that map.
* `AlgebraicGeometry.range_prodMap_map_left` and
  `AlgebraicGeometry.range_id_prodMap_map_left`: the image of an open immersion of schemes over
  `X`, multiplied over `S` by a fixed object, is the inverse image of its image.

## Implementation notes

Invariance is stated on the literal fibre products, through
`AlgebraicGeometry.DescentData.gluingPullbackIso`, so that it reads as the condition
`φ(W ×_S X) = X ×_S W` of the source. The construction works instead with the products in
`Over S` that carry the gluing isomorphism itself; the two forms are matched by
`AlgebraicGeometry.DescentData.isInvariantOpens_iff_gluing`.

The two inclusions `W i ×_S X j ⟶ V i ×_S X j` and `X i ×_S W j ⟶ X i ×_S V j` are base
changes of the inclusion `W i ⟶ V i`: applying a map to one factor of a binary product is a
base change of that map, and the forgetful functor `Over S ⥤ Scheme` preserves pullbacks,
being a projection out of an over category and pullbacks being connected limits. Hence they are
open immersions with the expected images, and the restricted gluing isomorphism is obtained by
lifting `φ i j` through the second of them. Its inverse comes the same way from the inverse of
`φ i j`, and the two composites are identities because the inclusions are monomorphisms. The
cocycle condition for the restricted datum follows from the one for `D` by cancelling the
monomorphism `X i ×_S X j ×_S W k ⟶ X i ×_S X j ×_S V k`, using the naturality of
`CategoryTheory.Limits.prodMapLastTwo` and `CategoryTheory.Limits.prodMapFirstThird`.

The invariance hypothesis is used through its consequence on points: the gluing isomorphism
carries the image of `W i ×_S X j` into the image of `X i ×_S W j`, and its inverse carries the
second image into the first. Both inclusions of images are in fact equalities, but only the
inclusions are needed, each being what lifting through an open immersion asks for.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasBinaryProducts C]

/-- Applying a map to the first factor of a binary product is a base change of that map. -/
@[ega "I 3.3.2" "partial"]
lemma isPullback_prodMap_id {A B : C} (h : A ⟶ B) (Z : C) :
    IsPullback (prod.map h (𝟙 Z)) prod.fst prod.fst h := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ prod.lift s.snd (s.fst ≫ prod.snd)) ?_ ?_ ?_
  · intro s
    apply prod.hom_ext
    · simpa using s.condition.symm
    · simp
  · intro s; simp
  · intro s m h₁ h₂
    apply prod.hom_ext
    · simpa using h₂
    · simpa using congrArg (fun t ↦ t ≫ prod.snd) h₁

/-- Applying a map to the second factor of a binary product is a base change of that map. -/
@[ega "I 3.3.2" "partial"]
lemma isPullback_id_prodMap {A B : C} (h : A ⟶ B) (Z : C) :
    IsPullback (prod.map (𝟙 Z) h) prod.snd prod.snd h := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ prod.lift (s.fst ≫ prod.fst) s.snd) ?_ ?_ ?_
  · intro s
    apply prod.hom_ext
    · simp
    · simpa using s.condition.symm
  · intro s; simp
  · intro s m h₁ h₂
    apply prod.hom_ext
    · simpa using congrArg (fun t ↦ t ≫ prod.fst) h₁
    · simpa using h₂

end CategoryTheory.Limits

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- A morphism of schemes over `S` whose underlying morphism of schemes is an open immersion is
a monomorphism. -/
lemma mono_of_isOpenImmersion_left {A B : Over S} (m : A ⟶ B) [IsOpenImmersion m.left] :
    Mono m :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono m.left))

/-- In a pullback square whose top map and right map are open immersions, the image of the top
map is the inverse image of the image of the right map. -/
private lemma range_eq_preimage_range_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} [IsOpenImmersion fst] [IsOpenImmersion g]
    (h : IsPullback fst snd f g) : Set.range ⇑fst = ⇑f ⁻¹' Set.range ⇑g := by
  simpa using congr(($(IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip ⊤)).1)

/-- Base-changing a morphism of schemes over `X` to `S` and multiplying it by a fixed scheme
over `S` on the right is, on underlying schemes, a base change of that morphism. -/
lemma isPullback_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S) :
    IsPullback (prod.map ((Over.map f).map u) (𝟙 Z)).left
      (prod.fst : (Over.map f).obj V' ⨯ Z ⟶ _).left
      (prod.fst : (Over.map f).obj V ⨯ Z ⟶ _).left u.left :=
  (isPullback_prodMap_id ((Over.map f).map u) Z).map (Over.forget S)

/-- Base-changing a morphism of schemes over `X` to `S` and multiplying it by a fixed scheme
over `S` on the left is, on underlying schemes, a base change of that morphism. -/
lemma isPullback_id_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S) :
    IsPullback (prod.map (𝟙 Z) ((Over.map f).map u)).left
      (prod.snd : Z ⨯ (Over.map f).obj V' ⟶ _).left
      (prod.snd : Z ⨯ (Over.map f).obj V ⟶ _).left u.left :=
  (isPullback_id_prodMap ((Over.map f).map u) Z).map (Over.forget S)

/-- If `u` is an open immersion, then so is `u ×_S 𝟙 Z` on underlying schemes. -/
instance isOpenImmersion_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S)
    [IsOpenImmersion u.left] :
    IsOpenImmersion (prod.map ((Over.map f).map u) (𝟙 Z)).left := by
  rw [← (isPullback_prodMap_map_left f u Z).isoPullback_hom_fst]
  infer_instance

/-- If `u` is an open immersion, then so is `𝟙 Z ×_S u` on underlying schemes. -/
instance isOpenImmersion_id_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S)
    [IsOpenImmersion u.left] :
    IsOpenImmersion (prod.map (𝟙 Z) ((Over.map f).map u)).left := by
  rw [← (isPullback_id_prodMap_map_left f u Z).isoPullback_hom_fst]
  infer_instance

/-- The image of `V' ×_S Z` in `V ×_S Z` is the inverse image of the image of `V'` in `V`. -/
lemma range_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S)
    [IsOpenImmersion u.left] :
    Set.range ⇑(prod.map ((Over.map f).map u) (𝟙 Z)).left =
      ⇑(prod.fst : (Over.map f).obj V ⨯ Z ⟶ _).left ⁻¹' Set.range ⇑u.left := by
  exact range_eq_preimage_range_of_isPullback (isPullback_prodMap_map_left f u Z)

/-- The image of `Z ×_S V'` in `Z ×_S V` is the inverse image of the image of `V'` in `V`. -/
lemma range_id_prodMap_map_left {V V' : Over X} (u : V' ⟶ V) (Z : Over S)
    [IsOpenImmersion u.left] :
    Set.range ⇑(prod.map (𝟙 Z) ((Over.map f).map u)).left =
      ⇑(prod.snd : Z ⨯ (Over.map f).obj V ⟶ _).left ⁻¹' Set.range ⇑u.left := by
  exact range_eq_preimage_range_of_isPullback (isPullback_id_prodMap_map_left f u Z)

end AlgebraicGeometry

namespace AlgebraicGeometry.DescentData

open CategoryTheory CategoryTheory.Limits

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

section Gluing

variable (D : DescentData f) (i j : ι)

/-- A gluing isomorphism composed with its inverse is the identity, as a map of schemes over
`S`. -/
@[reassoc]
lemma gluing_hom_left_comp_inv_left :
    (D.gluing i j).hom.left ≫ (D.gluing i j).inv.left =
      𝟙 ((Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j)) := by
  rw [← Over.comp_left, (D.gluing i j).hom_inv_id]
  rfl

/-- The inverse of a gluing isomorphism composed with it is the identity, as a map of schemes
over `S`. -/
@[reassoc]
lemma gluing_inv_left_comp_hom_left :
    (D.gluing i j).inv.left ≫ (D.gluing i j).hom.left =
      𝟙 (Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j)) := by
  rw [← Over.comp_left, (D.gluing i j).inv_hom_id]
  rfl

/-- On points, the inverse of a gluing isomorphism undoes the gluing isomorphism. -/
lemma gluing_inv_apply_hom_apply
    (x : ((Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j)).left) :
    (D.gluing i j).inv.left.left ((D.gluing i j).hom.left.left x) = x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, D.gluing_hom_left_comp_inv_left i j]
  simp

/-- On points, a gluing isomorphism undoes its inverse. -/
lemma gluing_hom_apply_inv_apply
    (x : (Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j)).left) :
    (D.gluing i j).hom.left.left ((D.gluing i j).inv.left.left x) = x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, D.gluing_inv_left_comp_hom_left i j]
  simp

/-- A gluing isomorphism is injective on points. -/
lemma gluing_hom_injective : Function.Injective ⇑(D.gluing i j).hom.left.left :=
  Function.LeftInverse.injective (D.gluing_inv_apply_hom_apply i j)

end Gluing

variable (D : DescentData f) (W : ∀ i, (D.obj i).left.Opens)

/-- A family of open subschemes of the components of a descent datum is *invariant* when each
gluing isomorphism `V i ×_S X j ≅ X i ×_S V j` carries `W i ×_S X j` onto `X i ×_S W j`.

**Stacks Project, Tag 023W.** -/
def IsInvariantOpens : Prop :=
  ∀ i j, (D.gluingPullbackIso i j).hom ⁻¹ᵁ
      (pullback.snd (f i) ((D.obj j).hom ≫ f j) ⁻¹ᵁ W j) =
    pullback.fst ((D.obj i).hom ≫ f i) (f j) ⁻¹ᵁ W i

/-- Invariance, read on the products in `Over S` which carry the gluing isomorphisms. -/
lemma isInvariantOpens_iff_gluing :
    D.IsInvariantOpens W ↔ ∀ i j, (D.gluing i j).hom.left.left ⁻¹ᵁ
        ((prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left ⁻¹ᵁ W j) =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left ⁻¹ᵁ W i := by
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  have e₂ : ((Over.mk (f i)).prodLeftIsoPullback ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) =
      (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have e₁ : (((Over.map (f i)).obj (D.obj i)).prodLeftIsoPullback (Over.mk (f j))).inv ≫
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← e₁]
  simp only [gluingPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc, e₂]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have h₂ := congrArg (fun T ↦ (((Over.map (f i)).obj (D.obj i)).prodLeftIsoPullback
    (Over.mk (f j))).hom ⁻¹ᵁ T) h
  simpa only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id_assoc] using h₂

/-- The inclusion of the open subscheme `W i` into the `i`-th component of `D`, as a morphism
of schemes over `X i`. -/
def openInclusion (i : ι) :
    (Over.mk ((W i).ι ≫ (D.obj i).hom) : Over (X i)) ⟶ D.obj i :=
  Over.homMk (W i).ι

/-- The underlying morphism of `openInclusion` is the inclusion `(W i).ι`. -/
@[simp]
lemma openInclusion_left (i : ι) : (D.openInclusion W i).left = (W i).ι := rfl

/-- The inclusion of `W i` into the `i`-th component is an open immersion. -/
instance isOpenImmersion_openInclusion (i : ι) :
    IsOpenImmersion (D.openInclusion W i).left :=
  inferInstanceAs (IsOpenImmersion (W i).ι)

/-- The inclusion `W i ×_S X j ⟶ V i ×_S X j` of the source of a gluing isomorphism, as a
morphism of schemes over `S`. -/
abbrev sourceInclusion (i j : ι) :
    (Over.map (f i)).obj (Over.mk ((W i).ι ≫ (D.obj i).hom)) ⨯ Over.mk (f j) ⟶
      (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) :=
  prod.map ((Over.map (f i)).map (D.openInclusion W i)) (𝟙 (Over.mk (f j)))

/-- The inclusion `X i ×_S W j ⟶ X i ×_S V j` of the target of a gluing isomorphism, as a
morphism of schemes over `S`. -/
abbrev targetInclusion (i j : ι) :
    Over.mk (f i) ⨯ (Over.map (f j)).obj (Over.mk ((W j).ι ≫ (D.obj j).hom)) ⟶
      Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) :=
  prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (D.openInclusion W j))

/-- The inclusion of `W i` is compatible with the structure maps to `X i`. -/
lemma openInclusion_comp_structureMap (i : ι) :
    (Over.map (f i)).map (D.openInclusion W i) ≫ structureMap (f i) (D.obj i) =
      structureMap (f i) (Over.mk ((W i).ι ≫ (D.obj i).hom)) :=
  Over.OverMorphism.ext rfl

/-- The source inclusion is compatible with the structure maps to `X i ×_S X j`. -/
lemma sourceInclusion_comp_structureMap (i j : ι) :
    D.sourceInclusion W i j ≫ prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))) =
      prod.map (structureMap (f i) (Over.mk ((W i).ι ≫ (D.obj i).hom)))
        (𝟙 (Over.mk (f j))) := by
  simp [D.openInclusion_comp_structureMap W i]

/-- The target inclusion is compatible with the structure maps to `X i ×_S X j`. -/
lemma targetInclusion_comp_structureMap (i j : ι) :
    D.targetInclusion W i j ≫ prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)) =
      prod.map (𝟙 (Over.mk (f i)))
        (structureMap (f j) (Over.mk ((W j).ι ≫ (D.obj j).hom))) := by
  simp [D.openInclusion_comp_structureMap W j]

/-- The image of a composite is the image under the second map of the image of the first. -/
private lemma range_comp_eq_image {A B T : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ T) :
    Set.range ⇑(a ≫ b) = ⇑b '' Set.range ⇑a := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun x ↦ Scheme.Hom.comp_apply a b x)

/-- Invariance says exactly that the gluing isomorphism identifies the image of `W i ×_S X j`
with the image of `X i ×_S W j`. -/
lemma preimage_range_targetInclusion (hW : D.IsInvariantOpens W) (i j : ι) :
    ⇑(D.gluing i j).hom.left.left ⁻¹' Set.range ⇑(D.targetInclusion W i j).left =
      Set.range ⇑(D.sourceInclusion W i j).left := by
  have e : ∀ m : ι, Set.range ⇑(D.openInclusion W m).left = (W m : Set (D.obj m).left) :=
    fun m ↦ (W m).range_ι
  rw [range_prodMap_map_left (f i) (D.openInclusion W i) (Over.mk (f j)),
    range_id_prodMap_map_left (f j) (D.openInclusion W j) (Over.mk (f i)), e i, e j]
  exact TopologicalSpace.Opens.ext_iff.mp ((D.isInvariantOpens_iff_gluing W).mp hW i j)

/-- The gluing isomorphism carries `W i ×_S X j` into `X i ×_S W j`. -/
lemma range_sourceInclusion_comp_le (hW : D.IsInvariantOpens W) (i j : ι) :
    Set.range ⇑((D.sourceInclusion W i j).left ≫ (D.gluing i j).hom.left.left) ⊆
      Set.range ⇑(D.targetInclusion W i j).left := by
  rw [range_comp_eq_image, ← D.preimage_range_targetInclusion W hW i j]
  exact Set.image_preimage_subset _ _

/-- The inverse gluing isomorphism carries `X i ×_S W j` into `W i ×_S X j`. -/
lemma range_targetInclusion_comp_le (hW : D.IsInvariantOpens W) (i j : ι) :
    Set.range ⇑((D.targetInclusion W i j).left ≫ (D.gluing i j).inv.left.left) ⊆
      Set.range ⇑(D.sourceInclusion W i j).left := by
  rw [range_comp_eq_image, ← D.preimage_range_targetInclusion W hW i j, Set.image_subset_iff,
    Set.preimage_preimage]
  simp only [D.gluing_hom_apply_inv_apply i j]
  exact fun x hx ↦ hx

/-- The restriction of the gluing isomorphism `V i ×_S X j ≅ X i ×_S V j` to an invariant
family of opens, as a morphism `W i ×_S X j ⟶ X i ×_S W j` of schemes over `S`. -/
def restrictGluing (hW : D.IsInvariantOpens W) (i j : ι) :
    (Over.map (f i)).obj (Over.mk ((W i).ι ≫ (D.obj i).hom)) ⨯ Over.mk (f j) ⟶
      Over.mk (f i) ⨯ (Over.map (f j)).obj (Over.mk ((W j).ι ≫ (D.obj j).hom)) :=
  Over.homMk (IsOpenImmersion.lift (D.targetInclusion W i j).left
      ((D.sourceInclusion W i j).left ≫ (D.gluing i j).hom.left.left)
      (D.range_sourceInclusion_comp_le W hW i j))
    (by
      have hg : (D.gluing i j).hom.left.left ≫
          (Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j)).hom =
          ((Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j)).hom :=
        Over.w ((D.gluing i j).hom.left)
      rw [← Over.w (D.targetInclusion W i j), ← Category.assoc, IsOpenImmersion.lift_fac,
        Category.assoc, hg, Over.w (D.sourceInclusion W i j)])

/-- The restriction of the inverse gluing isomorphism to an invariant family of opens. -/
def restrictGluingInv (hW : D.IsInvariantOpens W) (i j : ι) :
    Over.mk (f i) ⨯ (Over.map (f j)).obj (Over.mk ((W j).ι ≫ (D.obj j).hom)) ⟶
      (Over.map (f i)).obj (Over.mk ((W i).ι ≫ (D.obj i).hom)) ⨯ Over.mk (f j) :=
  Over.homMk (IsOpenImmersion.lift (D.sourceInclusion W i j).left
      ((D.targetInclusion W i j).left ≫ (D.gluing i j).inv.left.left)
      (D.range_targetInclusion_comp_le W hW i j))
    (by
      have hg : (D.gluing i j).inv.left.left ≫
          ((Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j)).hom =
          (Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j)).hom :=
        Over.w ((D.gluing i j).inv.left)
      rw [← Over.w (D.sourceInclusion W i j), ← Category.assoc, IsOpenImmersion.lift_fac,
        Category.assoc, hg, Over.w (D.targetInclusion W i j)])

/-- The restricted gluing map followed by the target inclusion equals the source inclusion
followed by the gluing isomorphism. -/
@[reassoc]
lemma restrictGluing_comp_targetInclusion (hW : D.IsInvariantOpens W) (i j : ι) :
    D.restrictGluing W hW i j ≫ D.targetInclusion W i j =
      D.sourceInclusion W i j ≫ (D.gluing i j).hom.left :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The inverse restricted gluing map followed by the source inclusion equals the target
inclusion followed by the inverse gluing isomorphism. -/
@[reassoc]
lemma restrictGluingInv_comp_sourceInclusion (hW : D.IsInvariantOpens W) (i j : ι) :
    D.restrictGluingInv W hW i j ≫ D.sourceInclusion W i j =
      D.targetInclusion W i j ≫ (D.gluing i j).inv.left :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The restricted gluing map is an isomorphism `W i ×_S X j ≅ X i ×_S W j`. -/
def restrictGluingIso (hW : D.IsInvariantOpens W) (i j : ι) :
    (Over.map (f i)).obj (Over.mk ((W i).ι ≫ (D.obj i).hom)) ⨯ Over.mk (f j) ≅
      Over.mk (f i) ⨯ (Over.map (f j)).obj (Over.mk ((W j).ι ≫ (D.obj j).hom)) where
  hom := D.restrictGluing W hW i j
  inv := D.restrictGluingInv W hW i j
  hom_inv_id := by
    have := mono_of_isOpenImmersion_left (D.sourceInclusion W i j)
    rw [← cancel_mono (D.sourceInclusion W i j), Category.assoc,
      D.restrictGluingInv_comp_sourceInclusion W hW i j,
      D.restrictGluing_comp_targetInclusion_assoc W hW i j,
      D.gluing_hom_left_comp_inv_left i j, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    have := mono_of_isOpenImmersion_left (D.targetInclusion W i j)
    rw [← cancel_mono (D.targetInclusion W i j), Category.assoc,
      D.restrictGluing_comp_targetInclusion W hW i j,
      D.restrictGluingInv_comp_sourceInclusion_assoc W hW i j,
      D.gluing_inv_left_comp_hom_left i j, Category.comp_id, Category.id_comp]

/-- The cocycle condition for the restricted gluing isomorphisms. -/
lemma restrictGluing_cocycle (hW : D.IsInvariantOpens W) (i j k : ι) :
    prod.map (D.restrictGluing W hW i j) (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (D.restrictGluing W hW j k) =
      prodMapFirstThird (D.restrictGluing W hW i k) := by
  have hmono : Mono (prod.map (prod.map (𝟙 (Over.mk (f i))) (𝟙 (Over.mk (f j))))
      ((Over.map (f k)).map (D.openInclusion W k))) := by
    rw [prod.map_id_id]
    exact mono_of_isOpenImmersion_left _
  have hLT := prodMapLastTwo_naturality (𝟙 (Over.mk (f i)))
    ((Over.map (f j)).map (D.openInclusion W j)) (𝟙 (Over.mk (f k)))
    (𝟙 (Over.mk (f j))) ((Over.map (f k)).map (D.openInclusion W k))
    (D.restrictGluing W hW j k) (D.gluing j k).hom.left
    (D.restrictGluing_comp_targetInclusion W hW j k).symm
  have hFT := prodMapFirstThird_naturality ((Over.map (f i)).map (D.openInclusion W i))
    (𝟙 (Over.mk (f j))) (𝟙 (Over.mk (f k))) (𝟙 (Over.mk (f i)))
    ((Over.map (f k)).map (D.openInclusion W k))
    (D.restrictGluing W hW i k) (D.gluing i k).hom.left
    (D.restrictGluing_comp_targetInclusion W hW i k).symm
  rw [← cancel_mono (prod.map (prod.map (𝟙 (Over.mk (f i))) (𝟙 (Over.mk (f j))))
    ((Over.map (f k)).map (D.openInclusion W k)))]
  calc (prod.map (D.restrictGluing W hW i j) (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (D.restrictGluing W hW j k)) ≫
        prod.map (prod.map (𝟙 (Over.mk (f i))) (𝟙 (Over.mk (f j))))
          ((Over.map (f k)).map (D.openInclusion W k))
      = prod.map (D.restrictGluing W hW i j) (𝟙 (Over.mk (f k))) ≫
          (prod.map (D.targetInclusion W i j) (𝟙 (Over.mk (f k))) ≫
            prodMapLastTwo (D.gluing j k).hom.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t ↦ prod.map (D.restrictGluing W hW i j) (𝟙 (Over.mk (f k))) ≫ t)
            hLT.symm)
    _ = prod.map (D.restrictGluing W hW i j ≫ D.targetInclusion W i j)
          (𝟙 (Over.mk (f k))) ≫ prodMapLastTwo (D.gluing j k).hom.left := by
        rw [← Category.assoc, prod.map_map, Category.comp_id]
    _ = prod.map (D.sourceInclusion W i j ≫ (D.gluing i j).hom.left)
          (𝟙 (Over.mk (f k))) ≫ prodMapLastTwo (D.gluing j k).hom.left :=
        congrArg
          (fun t ↦ prod.map t (𝟙 (Over.mk (f k))) ≫ prodMapLastTwo (D.gluing j k).hom.left)
          (D.restrictGluing_comp_targetInclusion W hW i j)
    _ = prod.map (D.sourceInclusion W i j) (𝟙 (Over.mk (f k))) ≫
          (prod.map (D.gluing i j).hom.left (𝟙 (Over.mk (f k))) ≫
            prodMapLastTwo (D.gluing j k).hom.left) := by
        rw [prod.map_comp_id, Category.assoc]
    _ = prod.map (D.sourceInclusion W i j) (𝟙 (Over.mk (f k))) ≫
          prodMapFirstThird (D.gluing i k).hom.left :=
        congrArg (fun t ↦ prod.map (D.sourceInclusion W i j) (𝟙 (Over.mk (f k))) ≫ t)
          (D.cocycle i j k)
    _ = prodMapFirstThird (D.restrictGluing W hW i k) ≫
          prod.map (prod.map (𝟙 (Over.mk (f i))) (𝟙 (Over.mk (f j))))
            ((Over.map (f k)).map (D.openInclusion W k)) := hFT

/-- The descent datum carried by an invariant family of open subschemes: its component at `i`
is the open subscheme `W i`, and its gluing isomorphisms are the restrictions of those of `D`.

**Stacks Project, Tag 023W.** -/
def restrict (hW : D.IsInvariantOpens W) : DescentData f where
  obj i := Over.mk ((W i).ι ≫ (D.obj i).hom)
  gluing i j := Over.isoMk (D.restrictGluingIso W hW i j)
    (by
      have hw : (D.gluing i j).hom.left ≫
          prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)) =
          prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))) :=
        Over.w (D.gluing i j).hom
      change D.restrictGluing W hW i j ≫
          prod.map (𝟙 (Over.mk (f i)))
            (structureMap (f j) (Over.mk ((W j).ι ≫ (D.obj j).hom))) =
        prod.map (structureMap (f i) (Over.mk ((W i).ι ≫ (D.obj i).hom))) (𝟙 (Over.mk (f j)))
      rw [← D.targetInclusion_comp_structureMap W i j,
        D.restrictGluing_comp_targetInclusion_assoc W hW i j, hw,
        D.sourceInclusion_comp_structureMap W i j])
  cocycle i j k := D.restrictGluing_cocycle W hW i j k

/-- The `i`-th component of the restricted descent datum is the open subscheme `W i` over
`X i`. -/
@[simp]
lemma restrict_obj (hW : D.IsInvariantOpens W) (i : ι) :
    (D.restrict W hW).obj i = Over.mk ((W i).ι ≫ (D.obj i).hom) := rfl

/-- The inclusion of the restricted descent datum into the original one. -/
def restrictHom (hW : D.IsInvariantOpens W) : D.restrict W hW ⟶ D where
  hom i := D.openInclusion W i
  comm i j := (D.restrictGluing_comp_targetInclusion W hW i j).symm

/-- The `i`-th component of `restrictHom` is `openInclusion W i`. -/
@[simp]
lemma restrictHom_hom (hW : D.IsInvariantOpens W) (i : ι) :
    (D.restrictHom W hW).hom i = D.openInclusion W i := rfl

/-- The components of the inclusion of the restricted descent datum are open immersions. -/
instance isOpenImmersion_restrictHom (hW : D.IsInvariantOpens W) (i : ι) :
    IsOpenImmersion ((D.restrictHom W hW).hom i).left :=
  inferInstanceAs (IsOpenImmersion (W i).ι)

/-- The components of the inclusion of the restricted datum have the given opens as images. -/
@[simp]
lemma opensRange_restrictHom (hW : D.IsInvariantOpens W) (i : ι) :
    ((D.restrictHom W hW).hom i).left.opensRange = W i :=
  (W i).opensRange_ι

end AlgebraicGeometry.DescentData

namespace AlgebraicGeometry.DescentData

open CategoryTheory CategoryTheory.Limits

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  {D E : DescentData f} (φ : E ⟶ D)

/-- A morphism of descent data carries the image of its source at `i`, times `X j`, onto the
image of its source at `j`, times `X i`, along the gluing isomorphism. -/
lemma preimage_range_prodMap_hom (i j : ι) [IsOpenImmersion (φ.hom i).left]
    [IsOpenImmersion (φ.hom j).left] :
    ⇑(D.gluing i j).hom.left.left ⁻¹'
        Set.range ⇑(prod.map (𝟙 (Over.mk (f i)))
          ((Over.map (f j)).map (φ.hom j))).left =
      Set.range ⇑(prod.map ((Over.map (f i)).map (φ.hom i))
        (𝟙 (Over.mk (f j)))).left := by
  have hpt : ∀ w, (D.gluing i j).hom.left.left
      ((prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j)))).left w) =
      (prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (φ.hom j))).left
        ((E.gluing i j).hom.left.left w) := by
    intro w
    have h := congrArg (fun m : (Over.map (f i)).obj (E.obj i) ⨯ Over.mk (f j) ⟶
      Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ↦ m.left w) (φ.comm i j)
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h
  refine Set.ext fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hx
    refine ⟨(E.gluing i j).inv.left.left z, D.gluing_hom_injective i j ?_⟩
    rw [hpt, E.gluing_hom_apply_inv_apply i j z]
    exact hz
  · rintro ⟨y, rfl⟩
    exact ⟨(E.gluing i j).hom.left.left y, (hpt y).symm⟩

/-- An isomorphism of descent data built from a family of isomorphisms of the components. -/
def mkIso (e : ∀ i, D.obj i ≅ E.obj i)
    (hcomm : ∀ i j, prod.map ((Over.map (f i)).map (e i).hom) (𝟙 (Over.mk (f j))) ≫
        (E.gluing i j).hom.left =
      (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).hom)) :
    D ≅ E where
  hom := { hom i := (e i).hom, comm := hcomm }
  inv :=
    { hom i := (e i).inv
      comm i j := by
        have ha : prod.map ((Over.map (f i)).map (e i).inv) (𝟙 (Over.mk (f j))) =
            (prod.mapIso ((Over.map (f i)).mapIso (e i)) (Iso.refl (Over.mk (f j)))).inv := by
          simp
        have hb : prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).inv) =
            (prod.mapIso (Iso.refl (Over.mk (f i))) ((Over.map (f j)).mapIso (e j))).inv := by
          simp
        rw [ha, hb, Iso.inv_comp_eq, ← Category.assoc]
        have hc : (prod.mapIso ((Over.map (f i)).mapIso (e i))
              (Iso.refl (Over.mk (f j)))).hom ≫ (E.gluing i j).hom.left =
            (D.gluing i j).hom.left ≫
              (prod.mapIso (Iso.refl (Over.mk (f i)))
                ((Over.map (f j)).mapIso (e j))).hom := by
          simpa using hcomm i j
        rw [hc, Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  hom_inv_id := DescentData.hom_ext fun i ↦ by simp
  inv_hom_id := DescentData.hom_ext fun i ↦ by simp

/-- The images of a morphism of descent data whose components are open immersions form an
invariant family of opens.

**Stacks Project, Tag 023W.** -/
lemma isInvariantOpens_opensRange [∀ i, IsOpenImmersion (φ.hom i).left] :
    D.IsInvariantOpens fun i ↦ (φ.hom i).left.opensRange := by
  rw [isInvariantOpens_iff_gluing]
  intro i j
  apply TopologicalSpace.Opens.ext
  show ⇑(D.gluing i j).hom.left.left ⁻¹'
      (⇑(prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left ⁻¹'
        Set.range ⇑(φ.hom j).left) =
    ⇑(prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left ⁻¹'
      Set.range ⇑(φ.hom i).left
  rw [← range_id_prodMap_map_left (f j) (φ.hom j) (Over.mk (f i)),
    ← range_prodMap_map_left (f i) (φ.hom i) (Over.mk (f j))]
  exact preimage_range_prodMap_hom φ i j

/-- The component of an open-immersion morphism of descent data, as an isomorphism onto the
open subscheme which is its image. -/
def openImmersionComponentIso [∀ i, IsOpenImmersion (φ.hom i).left] (i : ι) :
    E.obj i ≅ Over.mk (((φ.hom i).left.opensRange).ι ≫ (D.obj i).hom) :=
  Over.isoMk (φ.hom i).left.isoOpensRange (by
    change (φ.hom i).left.isoOpensRange.hom ≫
      ((φ.hom i).left.opensRange).ι ≫ (D.obj i).hom = (E.obj i).hom
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact Over.w (φ.hom i))

/-- The isomorphism `openImmersionComponentIso φ i` followed by the inclusion of the image of
`φ.hom i` is `φ.hom i`. -/
@[reassoc]
lemma openImmersionComponentIso_hom_comp [∀ i, IsOpenImmersion (φ.hom i).left] (i : ι) :
    (openImmersionComponentIso φ i).hom ≫
        D.openInclusion (fun i ↦ (φ.hom i).left.opensRange) i = φ.hom i :=
  Over.OverMorphism.ext (Scheme.Hom.isoOpensRange_hom_ι _)

/-- **A morphism of descent data with open-immersion components is the inclusion of the
restriction to the invariant family of its images.**

**Stacks Project, Tag 023W.** -/
def openImmersionIsoRestrict [∀ i, IsOpenImmersion (φ.hom i).left] :
    E ≅ D.restrict (fun i ↦ (φ.hom i).left.opensRange) (isInvariantOpens_opensRange φ) :=
  mkIso (openImmersionComponentIso φ) (by
    intro i j
    have hW := isInvariantOpens_opensRange φ
    have hm := mono_of_isOpenImmersion_left
      (D.targetInclusion (fun i ↦ (φ.hom i).left.opensRange) i j)
    change prod.map ((Over.map (f i)).map (openImmersionComponentIso φ i).hom)
        (𝟙 (Over.mk (f j))) ≫
        D.restrictGluing (fun i ↦ (φ.hom i).left.opensRange) hW i j =
      (E.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i)))
          ((Over.map (f j)).map (openImmersionComponentIso φ j).hom)
    rw [← cancel_mono (D.targetInclusion (fun i ↦ (φ.hom i).left.opensRange) i j),
      Category.assoc, D.restrictGluing_comp_targetInclusion _ hW i j]
    simp only [DescentData.sourceInclusion, DescentData.targetInclusion]
    rw [← Category.assoc, prod.map_map, Category.comp_id, ← Functor.map_comp,
      openImmersionComponentIso_hom_comp φ i, φ.comm i j, Category.assoc, prod.map_map,
      Category.id_comp, ← Functor.map_comp, openImmersionComponentIso_hom_comp φ j])

/-- The `i`-th component of `openImmersionIsoRestrict φ` is `openImmersionComponentIso φ i`. -/
@[simp]
lemma openImmersionIsoRestrict_hom_hom [∀ i, IsOpenImmersion (φ.hom i).left] (i : ι) :
    (openImmersionIsoRestrict φ).hom.hom i = (openImmersionComponentIso φ i).hom := rfl

/-- The inclusion of the restriction recovers the original morphism. -/
lemma openImmersionIsoRestrict_hom_comp_restrictHom
    [∀ i, IsOpenImmersion (φ.hom i).left] :
    (openImmersionIsoRestrict φ).hom ≫
        D.restrictHom (fun i ↦ (φ.hom i).left.opensRange) (isInvariantOpens_opensRange φ) =
      φ :=
  DescentData.hom_ext fun i ↦ openImmersionComponentIso_hom_comp φ i

end AlgebraicGeometry.DescentData

end

end
