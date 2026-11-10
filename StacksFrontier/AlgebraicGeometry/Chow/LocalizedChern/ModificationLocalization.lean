module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedClosedCover
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CompositeCommuting

/-!
# Localizations at infinity of classes on a modification of the projective line

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with
fibre at infinity `i_∞ : W_∞ ⟶ W` and class `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J. For a closed
subscheme `Y ⊆ X`, with `E = W_∞ ×_X Y`, a class `a ∈ A^m(E ⟶ W_∞)` has the *localization*

  `(E ⟶ Y)_* ∘ a ∘ C ∈ A^m(Y ⟶ X)`;

the class `c'_p(Q)` of Stacks 0F9K is the localization of the class `c'_p(Q|_E)` of
Stacks 0F9H. This file proves the induction step of Stacks 0FE7: the product of two
localizations is the localization of the product, provided the second class preserves the image
of the Gysin map at infinity,

  `res((E_Z ⟶ Z)_* ∘ e ∘ C) ∘ ((E_Y ⟶ Y)_* ∘ a ∘ C) =
    (E_{Z ×_X Y} ⟶ Z ×_X Y)_* ∘ (res(e) ∘ a) ∘ C`.

The proof is the source's, on every test scheme `V ⟶ X`. For a lift `β ∈ A_{k+1}(W ×_X V)` of
`α`, `C ∩ α = i_∞^* β`, and `a ∩ i_∞^* β = i_∞^* β'` for some `β'` on `W ×_X (Y ×_X V)`; so the
second localization caps `α` as the pushforward of `i_∞^* β'` to `Y ×_X V`, on which `C` is
`i_∞^* β'` again (Stacks 0FAR). Both sides are then pushforwards of `e ∩ i_∞^* β'`.

A class preserves the image of the Gysin map at infinity when it is the restriction to `W_∞` of
a bivariant class `κ` for `W ×_X Y ⟶ W`, because `κ` commutes with the Gysin map of the divisor
at infinity (Stacks 0B76 (3)); and products of classes preserving the image preserve it.

## Main definitions

* `Stacks.Chow.modificationLocalization` — the localization `(E ⟶ Y)_* ∘ a ∘ C`.
* `Stacks.Chow.PreservesInfinityGysinImage` — `a` maps the image of `i_∞^*` into the image of
  `i_∞^*`.
* `Stacks.Chow.IsModificationInfinityRestriction` — `a` is the restriction of `κ` to `W_∞`.
* `Stacks.Chow.modificationInfinityMul` — the product `res(e) ∘ a` over `W_∞`, supported on
  `W_∞ ×_X (Z ×_X Y)`.

## Main results

* `Stacks.Chow.localizedModificationClass_eq_modificationLocalization` — the class of
  Stacks 0F9K is a localization.
* `Stacks.Chow.modificationLocalization_cap_eq_of_isModificationLift` — the cap operation of a
  localization at a lift.
* `Stacks.Chow.supportedIntersectionMul_modificationLocalization` — the product of two
  localizations.
* `Stacks.Chow.PreservesInfinityGysinImage.modificationInfinityMul` — products preserve the image
  of the Gysin map at infinity.
* `Stacks.Chow.IsModificationInfinityRestriction.preservesInfinityGysinImage` — so do
  restrictions.
* `Stacks.Chow.isModificationInfinityRestriction_bivariantProperPushforward` — the restriction of
  Remark 0F9Z, pushed forward along `(W ×_X Y) ×_W W_∞ ≅ W_∞ ×_X Y`, is a restriction in this
  sense.

## Implementation notes

The intersection `W_{Z,∞} ∩ W_{Y,∞}` of the source is presented as `W_∞ ×_X (Z ×_X Y)`, the
scheme over which the localization along `Z ×_X Y` is formed; the product over `W_∞` is the
product of Stacks 0FE5 for the pullback square `Stacks.Chow.isPullback_pullbackFstTestIso`. The
image of the Gysin map at infinity is recorded on every test scheme, `a ∩ i_∞^* β` being read on
`W_∞ ×_X (Y ×_X V)` through `Stacks.Chow.pullbackFstTestIso`.

## References

* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Bookkeeping

variable {C : ChowSituation.{u}}

/-- The cap operation of a bivariant class commutes with the transport along an equality of
degrees. -/
theorem BivariantClass.cap_chowGroupDegreeEquiv {G : GysinSystem C} {A Y T : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {F : A ⟶ Y} [LocallyOfFiniteType F] {hF : F ≫ sY = sA} {p : ℤ}
    (c : BivariantClass C G sA sY F hF p) (t : T ⟶ Y) [LocallyOfFiniteType t] {k l : ℤ}
    (hkl : k = l) (x : chowGroup C (t ≫ sY) k) :
    c.cap t l (chowGroupDegreeEquiv C _ hkl x) =
      chowGroupDegreeEquiv C _ (by rw [hkl]) (c.cap t k x) := by
  subst hkl
  rfl

/-- The cap operation of a class read for an equal morphism and an equal degree
(`Stacks.Chow.BivariantClass.copy`) is that of the class, carried along the comparison of the two
base changes and the equality of degrees. -/
theorem BivariantClass.copy_cap_eq {G : GysinSystem C} {A Y T : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {F F' : A ⟶ Y}
    [LocallyOfFiniteType F] [LocallyOfFiniteType F'] (hFF' : F = F') (hF : F ≫ sY = sA)
    (hF' : F' ≫ sY = sA) {p p' : ℤ} (hpp' : p = p') (c : BivariantClass C G sA sY F hF p)
    (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (BivariantClass.copy C G sA sY hFF' hF hF' hpp' c).cap t k α =
      chowPushforwardOfIso C (pullback.fst F t ≫ sA) (pullback.fst F' t ≫ sA)
        (pullback.congrHom hFF' rfl).hom (pullback_congrHom_hom_comp_fst_comp hFF' t) (k - p')
        (chowGroupDegreeEquiv C _ (by rw [hpp']) (c.cap t k α)) := by
  subst hFF' hpp'
  rw [chowPushforwardOfIso_congr_apply C (pullback.fst F t ≫ sA) (pullback.fst F t ≫ sA)
    (pullback.congrHom rfl rfl).hom (𝟙 _) (by simp) _ (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]
  rfl

/-- Proper pushforward along three composable morphisms is proper pushforward along the
composite. -/
theorem chowPush_comp_comp {A B D E : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
    (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsProper v]
    (w : D ⟶ E) [IsProper w] (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sE = sD)
    (huvw : (u ≫ v ≫ w) ≫ sE = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowPush C sD sE w hw k (chowPush C sB sD v hv k (chowPush C sA sB u hu k x)) =
      chowPush C sA sE (u ≫ v ≫ w) huvw k x := by
  rw [chowPush_comp C sA sB sD u v (u ≫ v) rfl hu hv (by rw [Category.assoc, hv, hu]),
    chowPush_comp C sA sD sE (u ≫ v) w (u ≫ v ≫ w) (Category.assoc _ _ _)]

end Bookkeeping

/-! ### Iterated base changes -/

section IteratedBaseChange

variable {A X Y V : Scheme.{u}} (w : A ⟶ X) (y : Y ⟶ X) (g : V ⟶ X)

/-- The morphism `(A ×_X Y) ×_A (A ×_X V) ⟶ Y ×_X V` of base changes. -/
def pullbackFstTestMap : pullback (pullback.fst w y) (pullback.fst w g) ⟶ pullback y g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd w y) (pullback.snd _ _ ≫ pullback.snd w g) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, pullback.condition, Category.assoc])

/-- `Stacks.Chow.pullbackFstTestMap` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestMap_fst :
    pullbackFstTestMap w y g ≫ pullback.fst y g = pullback.fst _ _ ≫ pullback.snd w y :=
  pullback.lift_fst _ _ _

/-- `Stacks.Chow.pullbackFstTestMap` lies over the test scheme `V`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestMap_snd :
    pullbackFstTestMap w y g ≫ pullback.snd y g = pullback.snd _ _ ≫ pullback.snd w g :=
  pullback.lift_snd _ _ _

/-- The morphism of `Stacks.Chow.pullbackFstTestMap` is the composite of the comparison
isomorphisms of iterated base changes with the base change of `A ×_X Y ⟶ Y`. -/
theorem pullbackFstTestMap_eq :
    pullbackFstTestMap w y g =
      (pullbackRightPullbackFstIso w g (pullback.fst w y)).hom ≫
        (pullback.congrHom pullback.condition rfl).hom ≫
        bivariantPushforwardBaseChange (pullback.snd w y) y g := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackFstTestMap_fst]
    simp [bivariantPushforwardBaseChange]
  · rw [pullbackFstTestMap_snd]
    simp [bivariantPushforwardBaseChange]

/-- `Stacks.Chow.pullbackFstTestMap` is proper when `A ⟶ X` is: it is a base change of
`A ×_X Y ⟶ Y`. -/
instance [IsProper w] : IsProper (pullbackFstTestMap w y g) := by
  rw [pullbackFstTestMap_eq]
  infer_instance

/-- The identification `(A ×_X Y) ×_A (A ×_X V) ≅ A ×_X (Y ×_X V)`, the second scheme being the
base change of `A` along the test scheme `Y ×_X V ⟶ Y ⟶ X`. -/
def pullbackFstTestIso :
    pullback (pullback.fst w y) (pullback.fst w g) ≅ pullback w (pullback.fst y g ≫ y) where
  hom := pullback.lift (pullback.snd _ _ ≫ pullback.fst w g) (pullbackFstTestMap w y g) (by
    simp only [pullbackFstTestMap_fst_assoc, Category.assoc]
    rw [← pullback.condition (f := w) (g := y), pullback.condition_assoc])
  inv := pullback.lift
    (pullback.lift (pullback.fst w (pullback.fst y g ≫ y))
      (pullback.snd w (pullback.fst y g ≫ y) ≫ pullback.fst y g) (by
        rw [Category.assoc]; exact pullback.condition))
    (pullback.lift (pullback.fst w (pullback.fst y g ≫ y))
      (pullback.snd w (pullback.fst y g ≫ y) ≫ pullback.snd y g) (by
        rw [Category.assoc, ← pullback.condition (f := y) (g := g)]; exact pullback.condition))
    (by rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp, pullbackFstTestMap_fst]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp, pullbackFstTestMap_snd]
  inv_hom_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst,
        pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp, pullbackFstTestMap_fst,
        ]
    · simp only [Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp, pullbackFstTestMap_snd,
        ]

/-- `Stacks.Chow.pullbackFstTestIso` lies over `A`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestIso_hom_fst :
    (pullbackFstTestIso w y g).hom ≫ pullback.fst w (pullback.fst y g ≫ y) =
      pullback.snd _ _ ≫ pullback.fst w g := by
  dsimp only [pullbackFstTestIso]
  exact pullback.lift_fst _ _ _

/-- `Stacks.Chow.pullbackFstTestIso` lies over `Y ×_X V`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestIso_hom_snd :
    (pullbackFstTestIso w y g).hom ≫ pullback.snd w (pullback.fst y g ≫ y) =
      pullbackFstTestMap w y g := by
  dsimp only [pullbackFstTestIso]
  exact pullback.lift_snd _ _ _

/-- The inverse of `Stacks.Chow.pullbackFstTestIso` on the first factor `A ×_X Y`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestIso_inv_fst :
    (pullbackFstTestIso w y g).inv ≫ pullback.fst (pullback.fst w y) (pullback.fst w g) =
      pullback.lift (pullback.fst w (pullback.fst y g ≫ y))
        (pullback.snd w (pullback.fst y g ≫ y) ≫ pullback.fst y g) (by
          rw [Category.assoc]; exact pullback.condition) := by
  dsimp only [pullbackFstTestIso]
  exact pullback.lift_fst _ _ _

/-- The inverse of `Stacks.Chow.pullbackFstTestIso` on the second factor `A ×_X V`. -/
@[reassoc (attr := simp)]
theorem pullbackFstTestIso_inv_snd :
    (pullbackFstTestIso w y g).inv ≫ pullback.snd (pullback.fst w y) (pullback.fst w g) =
      pullback.lift (pullback.fst w (pullback.fst y g ≫ y))
        (pullback.snd w (pullback.fst y g ≫ y) ≫ pullback.snd y g) (by
          rw [Category.assoc, ← pullback.condition (f := y) (g := g)]
          exact pullback.condition) := by
  dsimp only [pullbackFstTestIso]
  exact pullback.lift_snd _ _ _

/-- The square presenting `A ×_X (Z ×_X Y)` as the fibre product of `A ×_X Z` and `A ×_X Y` over
`A`, through `Stacks.Chow.pullbackFstTestIso`. -/
theorem isPullback_pullbackFstTestIso {Z : Scheme.{u}} (z : Z ⟶ X) :
    IsPullback ((pullbackFstTestIso w z y).inv ≫ pullback.fst _ _)
      ((pullbackFstTestIso w z y).inv ≫ pullback.snd _ _) (pullback.fst w z) (pullback.fst w y) :=
  IsPullback.of_iso_pullback ⟨by
    simp only [Category.assoc]
    exact (pullbackFstTestIso w z y).inv ≫= pullback.condition⟩
    (pullbackFstTestIso w z y).symm rfl rfl

/-- The second leg of `Stacks.Chow.isPullback_pullbackFstTestIso`, followed by `A ×_X Y ⟶ A`, is
`A ×_X (Z ×_X Y) ⟶ A`. -/
theorem pullbackFstTestIso_inv_snd_fst {Z : Scheme.{u}} (z : Z ⟶ X) :
    ((pullbackFstTestIso w z y).inv ≫ pullback.snd _ _) ≫ pullback.fst w y =
      pullback.fst w (pullback.fst z y ≫ z) := by
  rw [Category.assoc, ← pullbackFstTestIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The projection `A ×_X (Z ×_X Y) ⟶ Z`, through the first factor of
`Stacks.Chow.isPullback_pullbackFstTestIso`. -/
theorem snd_fst_eq_pullbackFstTestIso_inv_fst_snd {Z : Scheme.{u}} (z : Z ⟶ X) :
    pullback.snd w (pullback.fst z y ≫ z) ≫ pullback.fst z y =
      ((pullbackFstTestIso w z y).inv ≫ pullback.fst _ _) ≫ pullback.snd w z := by
  conv_lhs => rw [← Iso.inv_hom_id_assoc (pullbackFstTestIso w z y)
    (pullback.snd w (pullback.fst z y ≫ z))]
  simp

/-- The projection `A ×_X (Z ×_X Y) ⟶ Y`, through the second factor of
`Stacks.Chow.isPullback_pullbackFstTestIso`. -/
theorem snd_snd_eq_pullbackFstTestIso_inv_snd_snd {Z : Scheme.{u}} (z : Z ⟶ X) :
    pullback.snd w (pullback.fst z y ≫ z) ≫ pullback.snd z y =
      ((pullbackFstTestIso w z y).inv ≫ pullback.snd _ _) ≫ pullback.snd w y := by
  conv_lhs => rw [← Iso.inv_hom_id_assoc (pullbackFstTestIso w z y)
    (pullback.snd w (pullback.fst z y ≫ z))]
  simp

/-- `A ×_X (Y ×_X V) ⟶ (A ×_X Y) ×_A (A ×_X V) ⟶ A ×_X Y ⟶ A` is the projection. -/
theorem pullbackFstTestIso_inv_fst_fst :
    (pullbackFstTestIso w y g).inv ≫ (pullback.fst (pullback.fst w y) (pullback.fst w g) ≫
      pullback.fst w y) = pullback.fst w (pullback.fst y g ≫ y) := by
  rw [← Category.assoc, pullbackFstTestIso_inv_fst, pullback.lift_fst]

end IteratedBaseChange

section Localization

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **The localization `(E ⟶ Y)_* ∘ a ∘ C ∈ A^m(Y ⟶ X)` of a class `a ∈ A^m(E ⟶ W_∞)`**, for a
closed subscheme `Y ⊆ X` and `E = W_∞ ×_X Y`, where `C ∈ A⁰(W_∞ ⟶ X)` is the class of
Stacks 0F9J, `∘` is the composition of Stacks 0B75 and `(E ⟶ Y)_*` is the pushforward of
Stacks 0EPK. The composite `a ∘ C`, a class of degree `m + 0` for `E ⟶ W_∞ ⟶ X`, is read as a
class of degree `m` for `E ⟶ Y ⟶ X`. For the class `a = c'_p(Q|_E)` of Stacks 0F9H this is the
class `c'_p(Q)` of Stacks 0F9K
(`Stacks.Chow.localizedModificationClass_eq_modificationLocalization`). -/
def modificationLocalization (y : Y ⟶ X) [IsClosedImmersion y] {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) :
    BivariantClass C (gysinSystemOfInvertible C) (y ≫ f) f y rfl m :=
  bivariantProperPushforwardOfInvertible C _ (y ≫ f) f
    (pullback.snd (modificationProjectionAtInfinity f b) y)
    y (pullbackSnd_comp_structureMorphism rfl y) rfl m
    (BivariantClass.copy C _ _ f pullback.condition _ _ (add_zero m)
      (bivariantCompositeOfInvertible C _ _ f
        (pullback.fst (modificationProjectionAtInfinity f b) y)
        (modificationProjectionAtInfinity f b) rfl rfl m 0 a (gysinAtInfinityClass C f b hA)))

/-- The class `c'_p(Q)` of Stacks 0F9K, and more generally the localized class `q'` of a class
`q ∈ A^p(W)` vanishing over `T`, is the localization of the extension `(q|_E)'` of Stacks 0F9H. -/
theorem localizedModificationClass_eq_modificationLocalization {Z T : Scheme.{u}} (z : Z ⟶ X)
    [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    {p : ℤ}
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq =
      modificationLocalization C f b hA z (modificationExtension z t hT hq) :=
  rfl

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The structure morphisms are compatible with `Stacks.Chow.pullbackFstTestMap`. -/
theorem pullbackFstTestMap_comp_over (y : Y ⟶ X) {V : Scheme.{u}} (g : V ⟶ X) :
    pullbackFstTestMap (modificationProjectionAtInfinity f b) y g ≫ (pullback.fst y g ≫ y ≫ f) =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y)
          (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
        pullback.fst (modificationProjectionAtInfinity f b) y ≫
          modificationProjectionAtInfinity f b ≫ f := by
  rw [pullbackFstTestMap, pullback.lift_fst_assoc, Category.assoc, ← pullback.condition_assoc]

/-- **The cap operation of a localization.** On a test scheme `g : V ⟶ X`, the localization
`(E ⟶ Y)_* ∘ a ∘ C` caps `α` as `a ∩ (C ∩ α)`, pushed forward along
`E ×_{W_∞} (W_∞ ×_X V) ⟶ Y ×_X V`; the degree `(k - 0) - m` is read as `k - m`. -/
theorem modificationLocalization_cap (y : Y ⟶ X) [IsClosedImmersion y] {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    (modificationLocalization C f b hA y a).cap g k α =
      chowPush C _ (pullback.fst y g ≫ y ≫ f)
        (pullbackFstTestMap (modificationProjectionAtInfinity f b) y g)
        (pullbackFstTestMap_comp_over y g) (k - m)
        (chowGroupDegreeEquiv C _ (by ring)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
            ((gysinAtInfinityClass C f b hA).cap g k α))) := by
  rw [modificationLocalization, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply, BivariantClass.copy_cap_eq]
  have hcomp : (bivariantCompositeOfInvertible C _ _ f
      (pullback.fst (modificationProjectionAtInfinity f b) y)
      (modificationProjectionAtInfinity f b) rfl rfl m 0 a (gysinAtInfinityClass C f b hA)).cap
        g k α = chowGroupDegreeEquiv C _ (by ring : (k - 0) - m = k - (m + 0))
          (bivariantCompositeCap C _ _ _ _ _ _ rfl rfl (properPushforwardDescends C) m 0 a
            (gysinAtInfinityClass C f b hA) g k α) := rfl
  rw [hcomp, bivariantCompositeCap_apply, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  change chowPush C _ _ (bivariantPushforwardBaseChange
      (pullback.snd (modificationProjectionAtInfinity f b) y) y g) _ (k - m)
    (chowPush C _ _ (pullback.congrHom
      (pullback.condition (f := modificationProjectionAtInfinity f b) (g := y))
        (rfl : g = g)).hom _ (k - m)
      (chowGroupDegreeEquiv C _ _ (chowPush C _ _ (pullbackRightPullbackFstIso
        (modificationProjectionAtInfinity f b) g
        (pullback.fst (modificationProjectionAtInfinity f b) y)).hom _ ((k - 0) - m)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
            ((gysinAtInfinityClass C f b hA).cap g k α))))) = _
  rw [chowGroupDegreeEquiv_properChowPushforward_comp _ _ _ _ _ _ _
      (properPushforwardDescends C _ _ _ _ _), chowPush_comp C _ _ _ _ _ _ rfl _ _
      (by rw [Category.assoc, bivariantPushforwardBaseChange_comp_structure
        (pullbackSnd_comp_structureMorphism rfl y), pullback_congrHom_hom_comp_fst_comp]),
    chowPush_comp C _ _ _ _ _ _ rfl _ _ (by
      rw [← pullbackFstTestMap_eq]; exact pullbackFstTestMap_comp_over y g)]
  exact chowPush_congr C _ _ (by simp only [pullbackFstTestMap_eq]) _ _ _ _

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The identification of `Stacks.Chow.pullbackFstTestIso` lies over the base. -/
theorem pullbackFstTestIso_hom_comp_over (y : Y ⟶ X) {V : Scheme.{u}}
    (g : V ⟶ X) :
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom ≫
        modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y) =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y)
          (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
        pullback.fst (modificationProjectionAtInfinity f b) y ≫
          modificationProjectionAtInfinity f b ≫ f := by
  rw [modificationInfinityBaseChangeOver, pullbackFstTestIso_hom_fst_assoc,
    ← pullback.condition_assoc]

/-- **Classes preserving the image of the Gysin map at infinity.** A class `a ∈ A^m(E ⟶ W_∞)`,
`E = W_∞ ×_X Y`, maps the classes in the image of `i_∞^* : A_{k+1}(W ×_X V) ⟶ A_k(W_∞ ×_X V)`
to classes in the image of `i_∞^*` on `W ×_X (Y ×_X V)`, for every test scheme `V ⟶ X`: the
class `a ∩ i_∞^* β`, read on `W_∞ ×_X (Y ×_X V)`, is `i_∞^* β'`. This holds for the restriction
to `W_∞` of every bivariant class for `W ×_X Y ⟶ W`. -/
def PreservesInfinityGysinImage (y : Y ⟶ X) [IsClosedImmersion y] {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) : Prop :=
  ∀ {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)),
    ∃ β' : chowGroup C (modificationBaseChangeOver f b (pullback.fst y g ≫ y)) (k - m + 1),
      chowPushforwardOfIso C _ (modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y))
          (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom
          (pullbackFstTestIso_hom_comp_over y g) (k - m)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) k
            (modificationInfinityGysin C f b g k β)) =
        modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β'

/-- **The cap operation of a localization, at a lift.** If `a` preserves the image of the Gysin
map at infinity and `β` lifts `α`, then `(E ⟶ Y)_* ∘ a ∘ C` caps `α` as the pushforward along
`W_∞ ×_X (Y ×_X V) ⟶ Y ×_X V` of `i_∞^* β'`, where `a ∩ i_∞^* β = i_∞^* β'`. -/
theorem modificationLocalization_cap_eq_of_isModificationLift (y : Y ⟶ X) [IsClosedImmersion y]
    {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (hβ : IsModificationLift C f b hA g k α β)
    (β' : chowGroup C (modificationBaseChangeOver f b (pullback.fst y g ≫ y)) (k - m + 1))
    (hβ' : chowPushforwardOfIso C _ (modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y))
          (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom
          (pullbackFstTestIso_hom_comp_over y g) (k - m)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) k
            (modificationInfinityGysin C f b g k β)) =
        modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β') :
    (modificationLocalization C f b hA y a).cap g k α =
      chowPush C (modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y))
        (pullback.fst y g ≫ y ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) (pullback.fst y g ≫ y))
        (by rw [← modificationInfinityBaseChange_snd_over f b (pullback.fst y g ≫ y),
          Category.assoc]) (k - m)
        (modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β') := by
  rw [modificationLocalization_cap, gysinAtInfinityClass_cap,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k α β hβ,
    BivariantClass.cap_chowGroupDegreeEquiv, chowGroupDegreeEquiv_chowGroupDegreeEquiv, ← hβ',
    chowPush_chowPushforwardOfIso C _ _ _ _ _ _ _ (by
      rw [pullbackFstTestIso_hom_snd]; exact pullbackFstTestMap_comp_over y g)]
  exact chowPush_congr C _ _ (pullbackFstTestIso_hom_snd _ y g).symm _ _ _ _

end Localization

/-! ### Restrictions of classes on the modification -/

section InfinityRestriction

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The square presenting `(W_∞ ×_X Y) ×_{W_∞} T ⟶ Y` over `X`. -/
theorem modificationInfinityRestriction_condition (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    (pullback.snd (pullback.fst (modificationProjection f b) y)
        (t ≫ modificationInclusionAtInfinity f b) ≫ t) ≫ modificationProjectionAtInfinity f b =
      (pullback.fst (pullback.fst (modificationProjection f b) y)
        (t ≫ modificationInclusionAtInfinity f b) ≫ pullback.snd (modificationProjection f b) y) ≫
        y := by
  have h := pullback.condition (f := pullback.fst (modificationProjection f b) y)
    (g := t ≫ modificationInclusionAtInfinity f b)
  have h' := pullback.condition (f := modificationProjection f b) (g := y)
  simp only [Category.assoc] at h ⊢
  rw [← h', ← reassoc_of% h]

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The square presenting `(W ×_X Y) ×_W T ⟶ Y` over `X`, for `T ⟶ W_∞ ⟶ W`. -/
theorem modificationInfinityRestriction_condition_inclusion (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    (pullback.snd (pullback.fst (modificationProjectionAtInfinity f b) y) t ≫ t ≫
        modificationInclusionAtInfinity f b) ≫ modificationProjection f b =
      (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y) t ≫
        pullback.snd (modificationProjectionAtInfinity f b) y) ≫ y := by
  have h := pullback.condition (f := pullback.fst (modificationProjectionAtInfinity f b) y) (g := t)
  have h' := pullback.condition (f := modificationProjectionAtInfinity f b) (g := y)
  simp only [Category.assoc] at h h' ⊢
  rw [← h', ← reassoc_of% h]

variable {C f b} in
/-- The identification `(W ×_X Y) ×_W T ≅ (W_∞ ×_X Y) ×_{W_∞} T` for a test scheme `T ⟶ W_∞`,
`T` lying over `W` through `i_∞ : W_∞ ⟶ W`. -/
def modificationInfinityRestrictionIso (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    pullback (pullback.fst (modificationProjection f b) y) (t ≫ modificationInclusionAtInfinity f b)
      ≅ pullback (pullback.fst (modificationProjectionAtInfinity f b) y) t where
  hom := pullback.lift
    (pullback.lift (pullback.snd _ _ ≫ t) (pullback.fst _ _ ≫ pullback.snd _ y)
      (modificationInfinityRestriction_condition y t))
    (pullback.snd _ _) (by rw [pullback.lift_fst])
  inv := pullback.lift
    (pullback.lift (pullback.snd _ _ ≫ t ≫ modificationInclusionAtInfinity f b)
      (pullback.fst _ _ ≫ pullback.snd _ y)
      (modificationInfinityRestriction_condition_inclusion y t))
    (pullback.snd _ _) (by rw [pullback.lift_fst])
  hom_inv_id := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [Category.assoc, pullback.lift_fst,
        pullback.lift_snd_assoc, Category.id_comp]
      exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd,
        Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [Category.assoc, pullback.lift_fst,
        pullback.lift_snd_assoc, Category.id_comp]
      exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd,
        Category.id_comp]

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- `Stacks.Chow.modificationInfinityRestrictionIso` on the first factor. -/
@[reassoc (attr := simp)]
theorem modificationInfinityRestrictionIso_hom_fst (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    (modificationInfinityRestrictionIso y t).hom ≫
        pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y) t =
      pullback.lift (pullback.snd (pullback.fst (modificationProjection f b) y)
          (t ≫ modificationInclusionAtInfinity f b) ≫ t)
        (pullback.fst (pullback.fst (modificationProjection f b) y)
          (t ≫ modificationInclusionAtInfinity f b) ≫ pullback.snd _ y)
        (modificationInfinityRestriction_condition y t) := by
  dsimp only [modificationInfinityRestrictionIso]
  exact pullback.lift_fst _ _ _

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- `Stacks.Chow.modificationInfinityRestrictionIso` lies over `T`. -/
@[reassoc (attr := simp)]
theorem modificationInfinityRestrictionIso_hom_snd (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    (modificationInfinityRestrictionIso y t).hom ≫
        pullback.snd (pullback.fst (modificationProjectionAtInfinity f b) y) t =
      pullback.snd (pullback.fst (modificationProjection f b) y)
        (t ≫ modificationInclusionAtInfinity f b) := by
  dsimp only [modificationInfinityRestrictionIso]
  exact pullback.lift_snd _ _ _

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The identification of `Stacks.Chow.modificationInfinityRestrictionIso` lies over the base. -/
theorem modificationInfinityRestrictionIso_hom_comp_structure (y : Y ⟶ X) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) :
    (modificationInfinityRestrictionIso y t).hom ≫
        (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y) t ≫
          pullback.fst (modificationProjectionAtInfinity f b) y ≫
            modificationProjectionAtInfinity f b ≫ f) =
      pullback.fst (pullback.fst (modificationProjection f b) y)
          (t ≫ modificationInclusionAtInfinity f b) ≫
        pullback.fst (modificationProjection f b) y ≫ modificationProjection f b ≫ f := by
  rw [modificationInfinityRestrictionIso_hom_fst_assoc, pullback.lift_fst_assoc]
  have h := pullback.condition (f := pullback.fst (modificationProjection f b) y)
    (g := t ≫ modificationInclusionAtInfinity f b)
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% h]

/-- **A class over `W_∞` restricted from `W`.** The class `a ∈ A^m(W_∞ ×_X Y ⟶ W_∞)` caps every
test scheme `T ⟶ W_∞` as the class `κ ∈ A^m(W ×_X Y ⟶ W)` caps `T ⟶ W_∞ ⟶ W`, read on
`(W_∞ ×_X Y) ×_{W_∞} T` through `Stacks.Chow.modificationInfinityRestrictionIso`: `a` is the
restriction of `κ` to `W_∞` (Remark 0F9Z), transported to `W_∞ ×_X Y`. -/
def IsModificationInfinityRestriction (y : Y ⟶ X) [IsClosedImmersion y] {m : ℤ}
    (κ : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) y ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) y) rfl m)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType t] (k : ℤ)
    (x : chowGroup C (t ≫ modificationProjectionAtInfinity f b ≫ f) k),
    a.cap t k x = chowPushforwardOfIso C _ _ (modificationInfinityRestrictionIso y t).hom
      (modificationInfinityRestrictionIso_hom_comp_structure y t) (k - m)
      (κ.cap (t ≫ modificationInclusionAtInfinity f b) k (chowGroupCongr C rfl k x))

/-- **Restrictions preserve the image of the Gysin map at infinity.** If `a` is the restriction
to `W_∞` of a class `κ ∈ A^m(W ×_X Y ⟶ W)`, then `a ∩ i_∞^* β = i_∞^*(κ ∩ β)`, with `κ ∩ β` read on
`W ×_X (Y ×_X V)`: this is the Gysin axiom of `κ` (Stacks 0B76 (3)) at the divisor at infinity of
`W ×_X V`, whose pullback to `(W ×_X Y) ×_W (W ×_X V) ≅ W ×_X (Y ×_X V)` is the divisor at
infinity there. This is the last step of the proof of Stacks 0FE7. -/
theorem IsModificationInfinityRestriction.preservesInfinityGysinImage (y : Y ⟶ X)
    [IsClosedImmersion y] {m : ℤ}
    {κ : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) y ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) y) rfl m}
    {a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m}
    (h : IsModificationInfinityRestriction C f b y κ a) :
    PreservesInfinityGysinImage C f b y a := by
  have := lineInfinityDivisor_isEffectiveCartierDivisor C.S
  intro V g _ k β
  have hφ : (pullbackFstTestIso (modificationProjection f b) y g).hom ≫
      modificationBaseChangeOver f b (pullback.fst y g ≫ y) =
      pullback.fst (pullback.fst (modificationProjection f b) y)
          (pullback.fst (modificationProjection f b) g) ≫
        pullback.fst (modificationProjection f b) y ≫ modificationProjection f b ≫ f := by
    rw [modificationBaseChangeOver, pullbackFstTestIso_hom_fst_assoc, ← pullback.condition_assoc]
  refine ⟨chowGroupDegreeEquiv C _ (by ring : k + 1 - m = k - m + 1)
    (chowPushforwardOfIso C _ (modificationBaseChangeOver f b (pullback.fst y g ≫ y))
      (pullbackFstTestIso (modificationProjection f b) y g).hom hφ _
      (κ.cap (pullback.fst (modificationProjection f b) g) (k + 1)
        (chowGroupCongr C rfl (k + 1) β))), ?_⟩
  have hZ : (modificationInfinityZeroSchemeIso f b g).hom ≫
      (pullback.fst (modificationProjectionAtInfinity f b) g ≫
        modificationInclusionAtInfinity f b) =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
        pullback.fst (modificationProjection f b) g := by
    rw [← modificationInfinityBaseChange_comp_fst, ← Category.assoc,
      modificationInfinityZeroSchemeIso_hom_comp]
  have hgys := κ.cap_chowPushforwardOfIso_gysin (pullback.fst (modificationProjection f b) g)
    (modificationInfinityModule f b g) (modificationInfinitySection f b g)
    (pullback.fst (modificationProjectionAtInfinity f b) g ≫ modificationInclusionAtInfinity f b)
    (modificationInfinityZeroSchemeIso f b g).hom hZ (qA := modificationBaseChangeOver f b g) rfl
    (qV := modificationInfinityBaseChangeOver f b g) rfl
    (modificationInfinityZeroSchemeIso_over C f b g) k β
  have e2 := (congrArg (κ.cap (pullback.fst (modificationProjectionAtInfinity f b) g ≫
      modificationInclusionAtInfinity f b) k) (eq_of_heq ((chowGroupCongr_heq C rfl k
        (modificationInfinityGysin C f b g k β)).trans
      (chowGroupCongr_heq C rfl k _).symm))).trans hgys
  rw [h]
  refine (congrArg (fun z ↦ chowPushforwardOfIso C _ _
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom
    (pullbackFstTestIso_hom_comp_over y g) (k - m)
    (chowPushforwardOfIso C _ _ (modificationInfinityRestrictionIso y _).hom
      (modificationInfinityRestrictionIso_hom_comp_structure y _) (k - m) z)) e2).trans ?_
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  have hZ' : (modificationInfinityZeroSchemeIso f b g).hom ≫
      pullback.snd (modificationProjectionAtInfinity f b) g =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
        pullback.snd (modificationProjection f b) g := by
    rw [← modificationInfinityBaseChange_comp_snd, ← Category.assoc,
      modificationInfinityZeroSchemeIso_hom_comp]
  have key : (testBaseChangeIso (pullback.fst (modificationProjection f b) y)
      (pullback.fst (modificationProjectionAtInfinity f b) g ≫ modificationInclusionAtInfinity f b)
      (modificationInfinityZeroSchemeIso f b g).hom
      ((Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
        pullback.fst (modificationProjection f b) g) hZ).hom ≫
      (modificationInfinityRestrictionIso y
        (pullback.fst (modificationProjectionAtInfinity f b) g)).hom ≫
      (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom ≫
      modificationInfinityBaseChange f b (pullback.fst y g ≫ y) =
      bivariantBaseChangeMap (pullback.fst (modificationProjection f b) y)
        (pullback.fst (modificationProjection f b) g)
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
          (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
      (pullbackFstTestIso (modificationProjection f b) y g).hom := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc]
      rw [modificationInfinityBaseChange_comp_fst, pullbackFstTestIso_hom_fst_assoc,
        modificationInfinityRestrictionIso_hom_snd_assoc, testBaseChangeIso_hom_snd_assoc, hZ,
        pullbackFstTestIso_hom_fst]
      simp [bivariantBaseChangeMap]
    · simp only [Category.assoc]
      rw [← Category.assoc (modificationInfinityBaseChange f b _),
        modificationInfinityBaseChange_comp_snd, pullbackFstTestIso_hom_snd_assoc,
        pullbackFstTestMap_fst, modificationInfinityRestrictionIso_hom_fst_assoc,
        pullback.lift_snd, testBaseChangeIso_hom_fst_assoc, pullbackFstTestIso_hom_snd_assoc,
        pullbackFstTestMap_fst]
      simp [bivariantBaseChangeMap]
    · simp only [Category.assoc]
      rw [← Category.assoc (modificationInfinityBaseChange f b _),
        modificationInfinityBaseChange_comp_snd, pullbackFstTestIso_hom_snd_assoc,
        pullbackFstTestMap_snd, modificationInfinityRestrictionIso_hom_snd_assoc,
        testBaseChangeIso_hom_snd_assoc, hZ', pullbackFstTestIso_hom_snd_assoc,
        pullbackFstTestMap_snd]
      simp [bivariantBaseChangeMap]
  have hMb : (((bivariantDivisorBaseChangeIso (pullback.fst (modificationProjection f b) y)
      (pullback.fst (modificationProjection f b) g) (modificationInfinityModule f b g)
      (modificationInfinitySection f b g)).inv ≫ (testBaseChangeIso
        (pullback.fst (modificationProjection f b) y)
        (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          modificationInclusionAtInfinity f b)
        (modificationInfinityZeroSchemeIso f b g).hom
        ((Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
          (modificationInfinityModule f b g) (modificationInfinitySection f b g)).subschemeι ≫
          pullback.fst (modificationProjection f b) g) hZ).hom) ≫
      ((modificationInfinityRestrictionIso y
        (pullback.fst (modificationProjectionAtInfinity f b) g)).hom ≫
      (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom)) ≫
      modificationInfinityBaseChange f b (pullback.fst y g ≫ y) =
      (Stacks.Divisors.zeroScheme (pullback (pullback.fst (modificationProjection f b) y)
          (pullback.fst (modificationProjection f b) g))
        ((Scheme.Modules.pullback (pullback.snd (pullback.fst (modificationProjection f b) y)
          (pullback.fst (modificationProjection f b) g))).obj (modificationInfinityModule f b g))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd
          (pullback.fst (modificationProjection f b) y)
          (pullback.fst (modificationProjection f b) g))
          (modificationInfinityModule f b g) (modificationInfinitySection f b g))).subschemeι ≫
      (pullbackFstTestIso (modificationProjection f b) y g).hom := by
    simp only [Category.assoc]
    rw [Iso.inv_comp_eq, reassoc_of% bivariantDivisorBaseChangeIso_hom_subschemeι]
    simpa only [Category.assoc] using key
  refine Eq.trans ?_ (modificationInfinityGysin_apply C f b (pullback.fst y g ≫ y) (k - m) _).symm
  have hzB : inv (modificationInfinityZeroSchemeIso f b (pullback.fst y g ≫ y)).hom ≫
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b (pullback.fst y g ≫ y))
        (modificationInfinityModule f b (pullback.fst y g ≫ y))
        (modificationInfinitySection f b (pullback.fst y g ≫ y))).subschemeι =
      modificationInfinityBaseChange f b (pullback.fst y g ≫ y) := by
    rw [IsIso.inv_comp_eq, modificationInfinityZeroSchemeIso_hom_comp]
  have hur : (pullbackFstTestIso (modificationProjection f b) y g).hom ≫
      modificationBaseChangeToRelativeLine f b (pullback.fst y g ≫ y) =
      pullback.snd (pullback.fst (modificationProjection f b) y)
        (pullback.fst (modificationProjection f b) g) ≫
          modificationBaseChangeToRelativeLine f b g := by
    simp [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine]
  refine (gysinSystemOfInvertible_onChow_chowPushforwardOfIso_comparison C _
    (modificationBaseChangeOver f b (pullback.fst y g ≫ y))
    (modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y))
    (pullback.snd (pullback.fst (modificationProjection f b) y)
      (pullback.fst (modificationProjection f b) g))
    (modificationBaseChangeToRelativeLine f b g)
    (modificationBaseChangeToRelativeLine f b (pullback.fst y g ≫ y)) _ hφ hur
    (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S))
    (by ring : k + 1 - m = k - m + 1) _
    (modificationInfinityZeroSchemeIso_over C f b (pullback.fst y g ≫ y)) _ _ ?_
    (κ.cap (pullback.fst (modificationProjection f b) g) (k + 1)
      (chowGroupCongr C rfl (k + 1) β))).symm
  rw [hzB, hMb]

variable {C f b} in
/-- The identification `(W ×_X Y) ×_W W_∞ ≅ W_∞ ×_X Y` of the restriction of `W ×_X Y` to the
fibre at infinity, as a morphism over `W_∞`. -/
def modificationInfinityRestrictionMap (y : Y ⟶ X) :
    pullback (pullback.fst (modificationProjection f b) y) (modificationInclusionAtInfinity f b) ⟶
      pullback (modificationProjectionAtInfinity f b) y :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd _ y) (by
    have h := pullback.condition (f := pullback.fst (modificationProjection f b) y)
      (g := modificationInclusionAtInfinity f b)
    rw [Category.assoc, ← pullback.condition, ← reassoc_of% h])

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- `Stacks.Chow.modificationInfinityRestrictionMap` lies over `W_∞`. -/
@[reassoc (attr := simp)]
theorem modificationInfinityRestrictionMap_fst (y : Y ⟶ X) :
    modificationInfinityRestrictionMap (f := f) (b := b) y ≫
      pullback.fst (modificationProjectionAtInfinity f b) y = pullback.snd _ _ :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- `Stacks.Chow.modificationInfinityRestrictionMap` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem modificationInfinityRestrictionMap_snd (y : Y ⟶ X) :
    modificationInfinityRestrictionMap (f := f) (b := b) y ≫
      pullback.snd (modificationProjectionAtInfinity f b) y =
        pullback.fst _ _ ≫ pullback.snd _ y :=
  pullback.lift_snd _ _ _

variable {C f b} in
/-- The inverse of `Stacks.Chow.modificationInfinityRestrictionMap`. -/
def modificationInfinityRestrictionMapInv (y : Y ⟶ X) :
    pullback (modificationProjectionAtInfinity f b) y ⟶
      pullback (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b) :=
  pullback.lift (pullback.lift (pullback.fst _ _ ≫ modificationInclusionAtInfinity f b)
    (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)) (pullback.fst _ _)
    (by rw [pullback.lift_fst])

/-- `Stacks.Chow.modificationInfinityRestrictionMap` is an isomorphism. -/
instance (y : Y ⟶ X) : IsIso (modificationInfinityRestrictionMap (f := f) (b := b) y) :=
  ⟨modificationInfinityRestrictionMapInv y, by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [modificationInfinityRestrictionMapInv, Category.assoc, pullback.lift_fst,
        modificationInfinityRestrictionMap_fst_assoc, Category.id_comp]
      exact pullback.condition.symm
    · simp only [modificationInfinityRestrictionMapInv, Category.assoc, pullback.lift_fst,
        pullback.lift_snd, modificationInfinityRestrictionMap_snd, Category.id_comp]
    · simp only [modificationInfinityRestrictionMapInv, Category.assoc, pullback.lift_snd,
        modificationInfinityRestrictionMap_fst, Category.id_comp], by
    refine pullback.hom_ext ?_ ?_
    · simp only [modificationInfinityRestrictionMapInv, Category.assoc, pullback.lift_snd,
        modificationInfinityRestrictionMap_fst, Category.id_comp]
    · simp only [modificationInfinityRestrictionMapInv, Category.assoc, pullback.lift_snd,
        pullback.lift_fst_assoc, modificationInfinityRestrictionMap_snd, Category.id_comp]⟩

/-- **The pushforward of a restriction to the fibre at infinity is a restriction.** For a class
`κ ∈ A^m(W ×_X Y ⟶ W)`, the restriction of `κ` to `W_∞` (Remark 0F9Z), a class for
`(W ×_X Y) ×_W W_∞ ⟶ W_∞`, pushed forward along the identification
`(W ×_X Y) ×_W W_∞ ≅ W_∞ ×_X Y` (Stacks 0EPK), is the restriction of `κ` to `W_∞` in the sense
of `Stacks.Chow.IsModificationInfinityRestriction`. -/
theorem isModificationInfinityRestriction_bivariantProperPushforward (y : Y ⟶ X)
    [IsClosedImmersion y] {m : ℤ}
    (κ : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjection f b) y ≫ modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) y) rfl m) :
    IsModificationInfinityRestriction C f b y κ
      (bivariantProperPushforwardOfInvertible C _ _ _ (modificationInfinityRestrictionMap y)
        (pullback.fst (modificationProjectionAtInfinity f b) y)
        (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst]; rfl) rfl m
        ((bivariantClassCongrBase C (gysinSystemOfInvertible C)
          (pullback.snd (pullback.fst (modificationProjection f b) y)
            (modificationInclusionAtInfinity f b))
          (pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _) (hv' := rfl) m
          (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ rfl
            (modificationInclusionAtInfinity f b) m
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)).congrHom
          (modificationInfinityRestrictionMap_fst y).symm
          (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst, Category.assoc]))) := by
  intro T t _ k x
  change chowPush C _ _ (bivariantPushforwardBaseChange (modificationInfinityRestrictionMap y)
    (pullback.fst (modificationProjectionAtInfinity f b) y) t) _ (k - m)
    (BivariantClass.cap _ t k x) = _
  have hres := bivariantClassCongrBase_cap C (gysinSystemOfInvertible C)
    (pullback.snd (pullback.fst (modificationProjection f b) y)
      (modificationInclusionAtInfinity f b))
    (pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _).symm rfl
    (hv := pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _) (hv' := rfl) m
    (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ rfl
      (modificationInclusionAtInfinity f b) m
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ) t k x x HEq.rfl
  have h1 := BivariantClass.congrHom_cap (modificationInfinityRestrictionMap_fst y).symm
    (by rw [← Category.assoc, modificationInfinityRestrictionMap_fst, Category.assoc])
    (bivariantClassCongrBase C (gysinSystemOfInvertible C)
      (pullback.snd (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b))
      (pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _).symm rfl
      (hv := pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _) (hv' := rfl) m
      (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ rfl
        (modificationInclusionAtInfinity f b) m
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)) t k x
  refine (congrArg _ h1).trans ?_
  have hA := hres.trans (heq_of_eq (bivariantRestrictionCap_apply C (gysinSystemOfInvertible C) _ _
    _ rfl (modificationInclusionAtInfinity f b) m κ t k x))
  have hsA : pullback.fst (pullback.snd (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b)) t ≫
      (pullback.snd (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b) ≫ modificationInclusionAtInfinity f b ≫
          modificationProjection f b ≫ f) =
      pullback.fst (pullback.snd (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b)) t ≫
      (pullback.fst (pullback.fst (modificationProjection f b) y)
        (modificationInclusionAtInfinity f b) ≫ pullback.fst (modificationProjection f b) y ≫
          modificationProjection f b ≫ f) := by
    rw [pullbackSnd_comp_structureMorphism_eq C _ _ _ rfl _]
  refine (congrArg _ (eq_of_heq (chowPush_heq C _ _
    (by rw [pullback_congrHom_hom_comp_fst_comp, ← hsA]) hsA rfl rfl hA))).trans ?_
  have key : (pullbackLeftPullbackSndIso (pullback.fst (modificationProjection f b) y)
      (modificationInclusionAtInfinity f b) t).inv ≫ (pullback.congrHom
        (modificationInfinityRestrictionMap_fst y).symm rfl).hom ≫
      bivariantPushforwardBaseChange (modificationInfinityRestrictionMap y)
        (pullback.fst (modificationProjectionAtInfinity f b) y) t =
      (modificationInfinityRestrictionIso y t).hom := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [pullback.congrHom, asIso_hom, bivariantPushforwardBaseChange, Category.assoc,
        pullback.map_fst, pullback.map_fst_assoc, Category.id_comp,
        modificationInfinityRestrictionMap_fst, pullbackLeftPullbackSndIso_inv_fst_snd,
        modificationInfinityRestrictionIso_hom_fst]
      rw [pullback.lift_fst]
    · simp only [pullback.congrHom, asIso_hom, bivariantPushforwardBaseChange, Category.assoc,
        pullback.map_fst, pullback.map_fst_assoc, Category.id_comp,
        modificationInfinityRestrictionMap_snd, pullbackLeftPullbackSndIso_inv_fst_assoc,
        modificationInfinityRestrictionIso_hom_fst]
      rw [pullback.lift_snd]
    · simp [bivariantPushforwardBaseChange, pullback.congrHom]
  exact (chowPush_comp_comp _ _ _ _ _ _ _ _ _ _
    (by rw [key]; exact modificationInfinityRestrictionIso_hom_comp_structure y t) _ _).trans
    (chowPush_congr C _ _ key _ _ _ _)


end InfinityRestriction

section Product

variable (C : ChowSituation.{u}) {X W Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The product `res(e) ∘ a` of two classes over `W_∞`, supported on `W_∞ ×_X Z` and `W_∞ ×_X Y`,
as a class supported on `W_∞ ×_X (Z ×_X Y)`. -/
abbrev modificationInfinityMul (z : Z ⟶ X) [IsClosedImmersion z] (y : Y ⟶ X)
    [IsClosedImmersion y] {p m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z) ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z)) rfl (p + m) :=
  supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z)
    (pullback.fst (modificationProjectionAtInfinity f b) y)
    (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z))
    (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z) e a

/-- **The product over `W_∞` on the image of the Gysin map at infinity.** If
`a ∩ i_∞^* β = i_∞^* β'` on `W_∞ ×_X (Y ×_X V)`, then `res(e) ∘ a` caps `i_∞^* β` as
`e ∩ i_∞^* β'`, pushed forward to `(W_∞ ×_X (Z ×_X Y)) ×_{W_∞} (W_∞ ×_X V)`; the two sides lie
in the degrees `k - (p + m)` and `(k - m) - p`. -/
theorem modificationInfinityMul_cap_modificationInfinityGysin (z : Z ⟶ X) [IsClosedImmersion z]
    (y : Y ⟶ X) [IsClosedImmersion y] {p m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (β' : chowGroup C (modificationBaseChangeOver f b (pullback.fst y g ≫ y)) (k - m + 1))
    (hβ' : chowPushforwardOfIso C _ (modificationInfinityBaseChangeOver f b (pullback.fst y g ≫ y))
          (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).hom
          (pullbackFstTestIso_hom_comp_over y g) (k - m)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) k
            (modificationInfinityGysin C f b g k β)) =
        modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β') :
    (modificationInfinityMul C f b z y e a).cap
        (pullback.fst (modificationProjectionAtInfinity f b) g) k
        (modificationInfinityGysin C f b g k β) ≍
      chowPush C _ _ (supportedIntersectionTestIso
          (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (modificationProjectionAtInfinity f b) y)
          (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
          (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z))
          (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z)
          (pullback.fst (modificationProjectionAtInfinity f b) g)).hom
        (supportedIntersectionTestIso_hom_comp_base C _ _ _ _ _ _ _) (k - m - p)
        (chowPush C
          (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
              (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y g ≫ y)) ≫
            pullback.fst (modificationProjectionAtInfinity f b) z ≫
              modificationProjectionAtInfinity f b ≫ f)
          (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
              (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y)
                (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
                  pullback.fst (modificationProjectionAtInfinity f b) y) ≫
            pullback.fst (modificationProjectionAtInfinity f b) z ≫
              modificationProjectionAtInfinity f b ≫ f)
          (testBaseChangeMapOfEq _ _ _ _
            (pullbackFstTestIso_inv_fst_fst (modificationProjectionAtInfinity f b) y g))
          (by rw [← Category.assoc, testBaseChangeMapOfEq_fst]) (k - m - p)
          (e.cap (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y g ≫ y))
            (k - m) (modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β'))) := by
  have h1 := eq_chowPushforwardOfIso_inv_of_eq _ _
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g)
    (pullbackFstTestIso_hom_comp_over y g)
    (by rw [Iso.inv_comp_eq, pullbackFstTestIso_hom_comp_over]) (k - m) hβ'
  have hm := pullbackFstTestIso_inv_fst_fst (modificationProjectionAtInfinity f b) y g
  have h2 := e.cap_properChowPushforward (properPushforwardDescends C)
    (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) y)
        (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
          pullback.fst (modificationProjectionAtInfinity f b) y)
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) y g).inv
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y g ≫ y)) hm
    (testBaseChangeMapOfEq _ _ _ _ hm) (testBaseChangeMapOfEq_fst _ _ _ _ hm)
    (testBaseChangeMapOfEq_snd _ _ _ _ hm) (k - m)
    (modificationInfinityGysin C f b (pullback.fst y g ≫ y) (k - m) β')
  have hR := supportedIntersectionMul_cap C (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z)
    (pullback.fst (modificationProjectionAtInfinity f b) y)
    (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z))
    (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z) e a
    (pullback.fst (modificationProjectionAtInfinity f b) g) k
    (modificationInfinityGysin C f b g k β)
  rw [h1, chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _
    (by rw [modificationInfinityBaseChangeOver, ← hm]; simp only [Category.assoc])] at hR
  exact hR.trans (heq_of_eq (congrArg _ h2))

/-- **The product of two localizations** (the step of the induction in Stacks 0FE7). Let
`Z, Y ⊆ X` be closed, and let `e ∈ A^p(W_∞ ×_X Z ⟶ W_∞)` and `a ∈ A^m(W_∞ ×_X Y ⟶ W_∞)`, where
`a` preserves the image of the Gysin map at infinity. Then the product
`res((E_Z ⟶ Z)_* ∘ e ∘ C) ∘ ((E_Y ⟶ Y)_* ∘ a ∘ C)` of the two localizations, a class
supported on `Z ×_X Y`, is the localization of the product `res(e) ∘ a` over `W_∞`. On a test
scheme, with `β` a lift of `α` and `a ∩ i_∞^* β = i_∞^* β'`, the second localization caps `α` as
the pushforward of `i_∞^* β'`, on which the class at infinity is `i_∞^* β'` again by Stacks 0FAR;
so both sides are pushforwards of `e ∩ i_∞^* β'`. -/
theorem supportedIntersectionMul_modificationLocalization (z : Z ⟶ X) [IsClosedImmersion z]
    (y : Y ⟶ X) [IsClosedImmersion y] {p m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    (ha : PreservesInfinityGysinImage C f b y a) :
    supportedIntersectionMul C f z y (IsPullback.of_hasPullback z y) (pullback.fst z y ≫ z)
        pullback.condition.symm (modificationLocalization C f b hA z e)
        (modificationLocalization C f b hA y a) =
      modificationLocalization C f b hA (pullback.fst z y ≫ z)
        (modificationInfinityMul C f b z y e a) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {V} g _ k α ↦ ?_
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g k α
  obtain ⟨β', hβ'⟩ := ha g k β
  -- the left side
  have hL := supportedIntersectionMul_cap C f z y (IsPullback.of_hasPullback z y)
    (pullback.fst z y ≫ z) pullback.condition.symm (modificationLocalization C f b hA z e)
    (modificationLocalization C f b hA y a) g k α
  rw [modificationLocalization_cap_eq_of_isModificationLift C f b hA y a g k α β hβ β' hβ',
    chowGroupCongr_chowPush _ _ _ _ _ (modificationInfinityBaseChange_snd_over f b _),
    modificationLocalization_cap, gysinAtInfinityClass_cap,
    gysinCapOfLift_chowPush_modificationInfinityGysin, BivariantClass.cap_chowGroupDegreeEquiv,
    chowGroupDegreeEquiv_chowGroupDegreeEquiv] at hL
  -- the right side
  have hR := modificationInfinityMul_cap_modificationInfinityGysin C f b z y e a g k β β' hβ'
  rw [modificationLocalization_cap, gysinAtInfinityClass_cap,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k α β hβ,
    BivariantClass.cap_chowGroupDegreeEquiv, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  refine eq_of_heq (hL.trans (HEq.trans ?_ (chowPush_heq C _ _
    (pullbackFstTestMap_comp_over _ g) rfl rfl (by ring)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans hR)).symm))
  refine heq_of_eq ?_
  rw [chowGroupDegreeEquiv_self]
  have key : pullbackFstTestMap (modificationProjectionAtInfinity f b) z (pullback.fst y g ≫ y) ≫
      (supportedIntersectionTestIso z y
      (IsPullback.of_hasPullback z y) (pullback.fst z y ≫ z) pullback.condition.symm g).hom =
      testBaseChangeMapOfEq _ _ _ _
        (pullbackFstTestIso_inv_fst_fst (modificationProjectionAtInfinity f b) y g) ≫
        (supportedIntersectionTestIso
        (pullback.fst (modificationProjectionAtInfinity f b) z)
        (pullback.fst (modificationProjectionAtInfinity f b) y)
        (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
        (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z))
        (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z)
        (pullback.fst (modificationProjectionAtInfinity f b) g)).hom ≫
        pullbackFstTestMap (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z) g := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp only [Category.assoc]
      rw [pullbackFstTestMap_fst_assoc, snd_fst_eq_pullbackFstTestIso_inv_fst_snd,
        supportedIntersectionTestIso_hom_fst_w₁_assoc, testBaseChangeMapOfEq_fst_assoc,
        supportedIntersectionTestIso_hom_fst_w₁, pullbackFstTestMap_fst]
    · simp only [Category.assoc]
      rw [pullbackFstTestMap_fst_assoc, snd_snd_eq_pullbackFstTestIso_inv_snd_snd,
        supportedIntersectionTestIso_hom_fst_w₂_assoc, testBaseChangeMapOfEq_snd_assoc,
        pullbackFstTestIso_inv_fst_assoc, pullback.lift_snd,
        supportedIntersectionTestIso_hom_fst_w₂, pullbackFstTestMap_snd_assoc]
    · simp only [Category.assoc]
      rw [pullbackFstTestMap_snd, supportedIntersectionTestIso_hom_snd_assoc,
        testBaseChangeMapOfEq_snd_assoc, pullbackFstTestIso_inv_snd_assoc,
        pullback.lift_snd, supportedIntersectionTestIso_hom_snd, pullbackFstTestMap_snd_assoc]
  refine (chowPush_comp C _ _ _ _ _ _ rfl _ _ ?_ _ _).trans ?_
  · rw [Category.assoc, supportedIntersectionTestIso_hom_comp_base,
      pullbackFstTestMap_comp_over]
  refine (chowPush_congr C _ _ key _ ?_ _ _).trans ?_
  · rw [← key, Category.assoc, supportedIntersectionTestIso_hom_comp_base,
      pullbackFstTestMap_comp_over]
  exact (chowPush_comp_comp _ _ _ _ _ _ _ _ _ _ _ _ _).symm

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The base change of a morphism of test schemes to the modification lies over the base. -/
theorem testBaseChangeMapOfEq_modificationBaseChangeOver {T T' : Scheme.{u}} (g : T ⟶ X)
    (h : T' ⟶ T) (n : T' ⟶ X) (hn : h ≫ g = n) :
    testBaseChangeMapOfEq (modificationProjection f b) g h n hn ≫
        modificationBaseChangeOver f b g = modificationBaseChangeOver f b n := by
  rw [modificationBaseChangeOver, testBaseChangeMapOfEq_fst_assoc]

omit [LocallyOfFiniteType f] [IsProper b] in
variable {C f b} in
/-- The base change of a morphism of test schemes to the fibre at infinity lies over the base. -/
theorem testBaseChangeMapOfEq_modificationInfinityBaseChangeOver {T T' : Scheme.{u}}
    (g : T ⟶ X) (h : T' ⟶ T) (n : T' ⟶ X) (hn : h ≫ g = n) :
    testBaseChangeMapOfEq (modificationProjectionAtInfinity f b) g h n hn ≫
        modificationInfinityBaseChangeOver f b g = modificationInfinityBaseChangeOver f b n := by
  rw [modificationInfinityBaseChangeOver, testBaseChangeMapOfEq_fst_assoc]

/-- **The Gysin map at infinity commutes with proper pushforward** (Stacks 02TA), along a proper
morphism `h : T' ⟶ T` of test schemes, the test morphism of `T'` being presented as equal to
`h ≫ g`. -/
theorem modificationInfinityGysin_chowPush_testBaseChangeMapOfEq {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (n : T' ⟶ X) [LocallyOfFiniteType n]
    (hn : h ≫ g = n) (k : ℤ) (β : chowGroup C (modificationBaseChangeOver f b n) (k + 1)) :
    modificationInfinityGysin C f b g k
        (chowPush C _ _ (testBaseChangeMapOfEq (modificationProjection f b) g h n hn)
          (testBaseChangeMapOfEq_modificationBaseChangeOver g h n hn) (k + 1) β) =
      chowPush C _ _ (testBaseChangeMapOfEq (modificationProjectionAtInfinity f b) g h n hn)
        (testBaseChangeMapOfEq_modificationInfinityBaseChangeOver g h n hn) k
        (modificationInfinityGysin C f b n k β) := by
  subst hn
  have hW : testBaseChangeMapOfEq (modificationProjection f b) g h (h ≫ g) rfl =
      bivariantBaseChangeMap (modificationProjection f b) g h := by
    refine pullback.hom_ext ?_ ?_ <;> simp [bivariantBaseChangeMap]
  rw [chowPush_congr C _ _ hW _ (modificationBaseChangeMap_over f b g h)]
  exact modificationInfinityGysin_properChowPushforward C f b g h k _
    (testBaseChangeMapOfEq_snd _ _ _ _ rfl) (testBaseChangeMapOfEq_fst _ _ _ _ rfl) β

/-- The Gysin map at infinity commutes with the transport along an equality of degrees. -/
theorem modificationInfinityGysin_chowGroupDegreeEquiv {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] {k l : ℤ} (hkl : k = l)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    modificationInfinityGysin C f b g l
        (chowGroupDegreeEquiv C _ (by rw [hkl] : k + 1 = l + 1) β) =
      chowGroupDegreeEquiv C _ hkl (modificationInfinityGysin C f b g k β) := by
  subst hkl
  rfl

/-- The comparison `Z ×_X (Y ×_X V) ≅ (Z ×_X Y) ×_X V` of Stacks 0FE5 is a morphism of test
schemes over `X`. -/
theorem supportedIntersectionTestIso_hom_comp_test (z : Z ⟶ X) (y : Y ⟶ X) {V : Scheme.{u}}
    (g : V ⟶ X) :
    (supportedIntersectionTestIso z y (IsPullback.of_hasPullback z y) (pullback.fst z y ≫ z)
        pullback.condition.symm g).hom ≫ (pullback.fst (pullback.fst z y ≫ z) g ≫
          pullback.fst z y ≫ z) =
      pullback.fst z (pullback.fst y g ≫ y) ≫ z := by
  rw [supportedIntersectionTestIso_hom_fst_w₁_assoc]

/-- **Products preserve the image of the Gysin map at infinity.** If `e` and `a` preserve the
image of `i_∞^*`, so does `res(e) ∘ a`: `a ∩ i_∞^* β = i_∞^* β'` and `e ∩ i_∞^* β' = i_∞^* β''`,
and `β''` is carried to `W ×_X ((Z ×_X Y) ×_X V)` along the identification of the test schemes,
with which `i_∞^*` commutes (Stacks 02TA). -/
theorem PreservesInfinityGysinImage.modificationInfinityMul {z : Z ⟶ X} [IsClosedImmersion z]
    {y : Y ⟶ X} [IsClosedImmersion y] {p m : ℤ}
    {e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p}
    {a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m}
    (he : PreservesInfinityGysinImage C f b z e) (ha : PreservesInfinityGysinImage C f b y a) :
    PreservesInfinityGysinImage C f b (pullback.fst z y ≫ z)
      (modificationInfinityMul C f b z y e a) := by
  intro V g _ k β
  obtain ⟨β', hβ'⟩ := ha g k β
  obtain ⟨β'', hβ''⟩ := he (pullback.fst y g ≫ y) (k - m) β'
  have hθ := supportedIntersectionTestIso_hom_comp_test z y g
  refine ⟨chowGroupDegreeEquiv C _ (by ring)
    (chowPush C _ _ (testBaseChangeMapOfEq (modificationProjection f b) _ _ _ hθ)
      (testBaseChangeMapOfEq_modificationBaseChangeOver _ _ _ hθ) _ β''), ?_⟩
  rw [modificationInfinityGysin_chowGroupDegreeEquiv C f b _ (by ring : k - m - p = k - (p + m)),
    modificationInfinityGysin_chowPush_testBaseChangeMapOfEq]
  have hR := modificationInfinityMul_cap_modificationInfinityGysin C f b z y e a g k β β' hβ'
  rw [eq_chowPushforwardOfIso_inv_of_eq _ _
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) z _)
    (pullbackFstTestIso_hom_comp_over z _)
    (by rw [Iso.inv_comp_eq, pullbackFstTestIso_hom_comp_over]) (k - m - p)
      hβ''] at hR
  refine eq_of_heq ((chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : k - (p + m) = k - m - p)
    _ _ hR).trans (HEq.trans (heq_of_eq ?_) (chowGroupDegreeEquiv_heq C _ _ _).symm))
  rw [chowPush_chowPushforwardOfIso C _ _ _ _ _ _ _ (by
      rw [Category.assoc, testBaseChangeMapOfEq_fst_assoc, ← Category.assoc,
        pullbackFstTestIso_inv_fst, pullback.lift_fst_assoc]),
    chowPush_comp C _ _ _ _ _ _ rfl _ _ (by
      rw [Category.assoc, supportedIntersectionTestIso_hom_comp_base, Category.assoc,
        testBaseChangeMapOfEq_fst_assoc, ← Category.assoc,
        pullbackFstTestIso_inv_fst, pullback.lift_fst_assoc]),
    chowPushforwardOfIso_chowPush C _ _ _ _ _ _ _ (by
      rw [Category.assoc, pullbackFstTestIso_hom_comp_over, Category.assoc,
        supportedIntersectionTestIso_hom_comp_base, Category.assoc,
        testBaseChangeMapOfEq_fst_assoc, ← Category.assoc,
        pullbackFstTestIso_inv_fst, pullback.lift_fst_assoc])]
  refine chowPush_congr C _ _ ?_ _ _ _ _
  refine pullback.hom_ext ?_ (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
  · simp only [Category.assoc, pullbackFstTestIso_hom_fst,
      supportedIntersectionTestIso_hom_snd_assoc, testBaseChangeMapOfEq_snd_assoc,
      pullbackFstTestIso_inv_snd_assoc, pullback.lift_fst,
      testBaseChangeMapOfEq_fst]
  · simp only [Category.assoc]
    rw [pullbackFstTestIso_hom_snd_assoc, pullbackFstTestMap_fst_assoc,
      snd_fst_eq_pullbackFstTestIso_inv_fst_snd, supportedIntersectionTestIso_hom_fst_w₁_assoc,
      testBaseChangeMapOfEq_fst_assoc, testBaseChangeMapOfEq_snd_assoc,
      supportedIntersectionTestIso_hom_fst_w₁]
    simp only [pullbackFstTestIso_inv_fst_assoc, pullback.lift_snd]
  · simp only [Category.assoc]
    rw [pullbackFstTestIso_hom_snd_assoc, pullbackFstTestMap_fst_assoc,
      snd_snd_eq_pullbackFstTestIso_inv_snd_snd, supportedIntersectionTestIso_hom_fst_w₂_assoc,
      testBaseChangeMapOfEq_snd_assoc, testBaseChangeMapOfEq_snd_assoc,
      supportedIntersectionTestIso_hom_fst_w₂]
    simp only [pullbackFstTestIso_inv_fst_assoc, pullback.lift_snd,
      pullbackFstTestIso_inv_snd_assoc, pullback.lift_snd_assoc, Category.assoc]
  · simp only [Category.assoc, pullbackFstTestIso_hom_snd_assoc,
      pullbackFstTestMap_snd, supportedIntersectionTestIso_hom_snd_assoc,
      testBaseChangeMapOfEq_snd_assoc, pullbackFstTestIso_inv_snd_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, supportedIntersectionTestIso_hom_snd]

end Product

end Stacks.Chow

end
