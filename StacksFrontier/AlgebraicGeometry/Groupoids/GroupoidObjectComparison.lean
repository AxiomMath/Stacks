module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.Deformation.Groupoid.Internal

/-!
# Groupoid objects and groupoid schemes

A groupoid scheme over `S` (Stacks 0231) is a groupoid object in the category of schemes over
`S`, presented with the object of composable pairs *chosen* to be
`CategoryTheory.Limits.pullback source target` and with the laws involving the composition read
on generalized points over every `T : Over S`. `Deformation.GroupoidObject` is the same notion
for an arbitrary category, presented with an arbitrary object of composable pairs together with
the cartesian square exhibiting it, and with an object of composable triples carried as data.
This file relates the two presentations.

## Main definitions

* `Deformation.GroupoidObject.ofUniversal`: the groupoid object with given structure morphisms
  whose four unit and inverse laws hold at every composable pair with domain the object of
  arrows, and whose associativity holds at every pair of composable pairs with domain the object
  of triples.
* `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject`: the groupoid scheme underlying a groupoid
  object of `CategoryTheory.Over S`, whose composition is that of the groupoid object transported
  along the identification of its object of composable pairs with the chosen fibre product.

## Main results

* `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_objects`,
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_arrows`,
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_source`,
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_target`,
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_identity`,
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_inverse` and
  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject_comp`: the structure spaces and structure
  morphisms of `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject H` are those of `H`, the
  composition read on the chosen fibre product.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.GroupoidObject

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- The groupoid object with the given structure morphisms, whose two unit laws and two inverse
laws are asked for only at composable pairs with domain the object of arrows, and whose
associativity is asked for only at pairs of composable pairs with domain the object of composable
triples. -/
noncomputable def ofUniversal {objects arrows pairs triples : C}
    {source target : arrows ⟶ objects} (identity : objects ⟶ arrows)
    (inverse : arrows ⟶ arrows) {fst snd : pairs ⟶ arrows}
    (hp : IsPullback fst snd source target) (comp : pairs ⟶ arrows)
    {fst₃ snd₃ : triples ⟶ pairs} (ht : IsPullback fst₃ snd₃ snd fst)
    (hsi : identity ≫ source = 𝟙 objects) (hti : identity ≫ target = 𝟙 objects)
    (hsv : inverse ≫ source = target) (htv : inverse ≫ target = source)
    (hcs : comp ≫ source = snd ≫ source) (hct : comp ≫ target = fst ≫ target)
    (hul : ∀ k : arrows ⟶ pairs, k ≫ fst = target ≫ identity → k ≫ snd = 𝟙 arrows →
      k ≫ comp = 𝟙 arrows)
    (hur : ∀ k : arrows ⟶ pairs, k ≫ fst = 𝟙 arrows → k ≫ snd = source ≫ identity →
      k ≫ comp = 𝟙 arrows)
    (hil : ∀ k : arrows ⟶ pairs, k ≫ fst = inverse → k ≫ snd = 𝟙 arrows →
      k ≫ comp = source ≫ identity)
    (hir : ∀ k : arrows ⟶ pairs, k ≫ fst = 𝟙 arrows → k ≫ snd = inverse →
      k ≫ comp = target ≫ identity)
    (ha : ∀ m n : triples ⟶ pairs, m ≫ fst = fst₃ ≫ comp → m ≫ snd = snd₃ ≫ snd →
      n ≫ fst = fst₃ ≫ fst → n ≫ snd = snd₃ ≫ comp → m ≫ comp = n ≫ comp) :
    GroupoidObject C where
  objects := objects
  arrows := arrows
  pairs := pairs
  triples := triples
  source := source
  target := target
  identity := identity
  inverse := inverse
  fst := fst
  snd := snd
  isPullback_pairs := hp
  comp := comp
  fst₃ := fst₃
  snd₃ := snd₃
  isPullback_triples := ht
  identity_source := hsi
  identity_target := hti
  inverse_source := hsv
  inverse_target := htv
  comp_source := hcs
  comp_target := hct
  comp_identity_left := by
    intro X a k h₁ h₂
    have w₀ : (target ≫ identity) ≫ source = 𝟙 arrows ≫ target := by
      rw [Category.assoc, hsi, Category.comp_id, Category.id_comp]
    have hk : k = a ≫ hp.lift (target ≫ identity) (𝟙 arrows) w₀ := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst]
      · rwa [Category.assoc, hp.lift_snd, Category.comp_id]
    rw [hk, Category.assoc, hul _ (hp.lift_fst _ _ _) (hp.lift_snd _ _ _), Category.comp_id]
  comp_identity_right := by
    intro X a k h₁ h₂
    have w₀ : 𝟙 arrows ≫ source = (source ≫ identity) ≫ target := by
      rw [Category.id_comp, Category.assoc, hti, Category.comp_id]
    have hk : k = a ≫ hp.lift (𝟙 arrows) (source ≫ identity) w₀ := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst, Category.comp_id]
      · rwa [Category.assoc, hp.lift_snd]
    rw [hk, Category.assoc, hur _ (hp.lift_fst _ _ _) (hp.lift_snd _ _ _), Category.comp_id]
  comp_inverse_left := by
    intro X a k h₁ h₂
    have w₀ : inverse ≫ source = 𝟙 arrows ≫ target := by rw [hsv, Category.id_comp]
    have hk : k = a ≫ hp.lift inverse (𝟙 arrows) w₀ := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst]
      · rwa [Category.assoc, hp.lift_snd, Category.comp_id]
    rw [hk, Category.assoc, hil _ (hp.lift_fst _ _ _) (hp.lift_snd _ _ _)]
  comp_inverse_right := by
    intro X a k h₁ h₂
    have w₀ : 𝟙 arrows ≫ source = inverse ≫ target := by rw [htv, Category.id_comp]
    have hk : k = a ≫ hp.lift (𝟙 arrows) inverse w₀ := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst, Category.comp_id]
      · rwa [Category.assoc, hp.lift_snd]
    rw [hk, Category.assoc, hir _ (hp.lift_fst _ _ _) (hp.lift_snd _ _ _)]
  comp_assoc := by
    intro X k l m n hkl hm₁ hm₂ hn₁ hn₂
    have wm : (fst₃ ≫ comp) ≫ source = (snd₃ ≫ snd) ≫ target := by
      rw [Category.assoc, hcs, ← Category.assoc, ht.w, Category.assoc, Category.assoc, hp.w]
    have wn : (fst₃ ≫ fst) ≫ source = (snd₃ ≫ comp) ≫ target := by
      rw [Category.assoc, hp.w, ← Category.assoc, ht.w, Category.assoc, Category.assoc, hct]
    have hmn := ha (hp.lift (fst₃ ≫ comp) (snd₃ ≫ snd) wm)
      (hp.lift (fst₃ ≫ fst) (snd₃ ≫ comp) wn)
      (hp.lift_fst _ _ _) (hp.lift_snd _ _ _) (hp.lift_fst _ _ _) (hp.lift_snd _ _ _)
    have hjf := ht.lift_fst k l hkl
    have hjs := ht.lift_snd k l hkl
    have hm : m = ht.lift k l hkl ≫ hp.lift (fst₃ ≫ comp) (snd₃ ≫ snd) wm := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst, ← Category.assoc, hjf]
      · rwa [Category.assoc, hp.lift_snd, ← Category.assoc, hjs]
    have hn : n = ht.lift k l hkl ≫ hp.lift (fst₃ ≫ fst) (snd₃ ≫ comp) wn := by
      refine hp.hom_ext ?_ ?_
      · rwa [Category.assoc, hp.lift_fst, ← Category.assoc, hjf]
      · rwa [Category.assoc, hp.lift_snd, ← Category.assoc, hjs]
    rw [hm, hn, Category.assoc, Category.assoc, hmn]

end Deformation.GroupoidObject

namespace Stacks.Groupoids.GroupoidScheme

universe u

variable {S : Scheme.{u}} (H : Deformation.GroupoidObject (Over S))

/-- The identification of the object of composable pairs of a groupoid object of schemes over
`S` with the chosen fibre product of its source and target. -/
noncomputable abbrev groupoidObjectPairsIso :
    H.pairs ≅ pullback H.source H.target :=
  H.isPullback_pairs.isoPullback

/-- The composable pair of generalized arrows underlying a generalized point of the chosen
fibre product of the source and target of a groupoid object of schemes over `S`. -/
noncomputable abbrev groupoidObjectPair {T : Over S} (k : T ⟶ pullback H.source H.target) :
    T ⟶ H.pairs :=
  k ≫ (groupoidObjectPairsIso H).inv

/-- The first arrow of `groupoidObjectPair H k` is the first projection of `k`. -/
theorem groupoidObjectPair_comp_fst {T : Over S} (k : T ⟶ pullback H.source H.target) :
    groupoidObjectPair H k ≫ H.fst = k ≫ pullback.fst H.source H.target := by
  rw [Category.assoc, H.isPullback_pairs.isoPullback_inv_fst]

/-- The second arrow of `groupoidObjectPair H k` is the second projection of `k`. -/
theorem groupoidObjectPair_comp_snd {T : Over S} (k : T ⟶ pullback H.source H.target) :
    groupoidObjectPair H k ≫ H.snd = k ≫ pullback.snd H.source H.target := by
  rw [Category.assoc, H.isPullback_pairs.isoPullback_inv_snd]

/-- **The groupoid scheme underlying a groupoid object of schemes over `S`.**  Its object and
arrow schemes, its source, target, identity and inverse are those of the groupoid object, and
its composition is the composition of the groupoid object read on the chosen fibre product of
the source and the target. -/
noncomputable def ofGroupoidObject : GroupoidScheme S where
  objects := H.objects
  arrows := H.arrows
  source := H.source
  target := H.target
  comp := (groupoidObjectPairsIso H).inv ≫ H.comp
  identity := H.identity
  inverse := H.inverse
  source_identity := H.identity_source
  target_identity := H.identity_target
  source_inverse := H.inverse_source
  target_inverse := H.inverse_target
  source_comp := by
    rw [Category.assoc, H.comp_source, ← Category.assoc,
      H.isPullback_pairs.isoPullback_inv_snd]
  target_comp := by
    rw [Category.assoc, H.comp_target, ← Category.assoc,
      H.isPullback_pairs.isoPullback_inv_fst]
  left_identity := by
    intro T f w
    rw [← Category.assoc]
    refine H.comp_identity_left f _ ?_ ?_
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd]
  right_identity := by
    intro T f w
    rw [← Category.assoc]
    refine H.comp_identity_right f _ ?_ ?_
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd]
  left_inverse := by
    intro T f w
    rw [← Category.assoc]
    refine H.comp_inverse_left f _ ?_ ?_
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd]
  right_inverse := by
    intro T f w
    rw [← Category.assoc]
    refine H.comp_inverse_right f _ ?_ ?_
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd]
  assoc := by
    intro T f g h wfg wgh w₁ w₂
    refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm ?_) (Category.assoc _ _ _)
    refine H.comp_assoc (groupoidObjectPair H (pullback.lift f g wfg))
      (groupoidObjectPair H (pullback.lift g h wgh)) _ _ ?_ ?_ ?_ ?_ ?_
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd, groupoidObjectPair_comp_fst,
        pullback.lift_fst]
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst, Category.assoc]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd, groupoidObjectPair_comp_snd,
        pullback.lift_snd]
    · rw [groupoidObjectPair_comp_fst, pullback.lift_fst, groupoidObjectPair_comp_fst,
        pullback.lift_fst]
    · rw [groupoidObjectPair_comp_snd, pullback.lift_snd, Category.assoc]

/-- The object scheme of the groupoid scheme underlying a groupoid object is the object of
objects of the groupoid object. -/
@[simp] theorem ofGroupoidObject_objects : (ofGroupoidObject H).objects = H.objects := rfl

/-- The arrow scheme of the groupoid scheme underlying a groupoid object is the object of
arrows of the groupoid object. -/
@[simp] theorem ofGroupoidObject_arrows : (ofGroupoidObject H).arrows = H.arrows := rfl

/-- The source of the groupoid scheme underlying a groupoid object is the source of the
groupoid object. -/
@[simp] theorem ofGroupoidObject_source : (ofGroupoidObject H).source = H.source := rfl

/-- The target of the groupoid scheme underlying a groupoid object is the target of the
groupoid object. -/
@[simp] theorem ofGroupoidObject_target : (ofGroupoidObject H).target = H.target := rfl

/-- The identity of the groupoid scheme underlying a groupoid object is the identity of the
groupoid object. -/
@[simp] theorem ofGroupoidObject_identity : (ofGroupoidObject H).identity = H.identity := rfl

/-- The inverse of the groupoid scheme underlying a groupoid object is the inverse of the
groupoid object. -/
@[simp] theorem ofGroupoidObject_inverse : (ofGroupoidObject H).inverse = H.inverse := rfl

/-- The composition of the groupoid scheme underlying a groupoid object is the composition of
the groupoid object, read on the chosen fibre product of the source and the target. -/
theorem ofGroupoidObject_comp :
    (ofGroupoidObject H).comp = (groupoidObjectPairsIso H).inv ≫ H.comp := rfl

end Stacks.Groupoids.GroupoidScheme

end
