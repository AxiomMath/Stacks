module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.FormalObject.AdicQuotient
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# Completion and restriction of cofibered sets

A cofibered set over the category of Artinian local `Λ`-algebras with residue field `k`
is a covariant set-valued functor on that category. Restricting such a functor along the
inclusion of Artinian local algebras into complete local algebras has a right adjoint,
the completion: its value on a complete local algebra `S` is the set of compatible
families of values on the Artinian truncations `S / m_S ^ (n + 1)`. The counit of this
adjunction is an isomorphism, so restricting a completion recovers the original functor.

## Main definitions

* `Deformation.completedSections`: the compatible families of values on the Artinian
  truncations of a complete local algebra.
* `Deformation.cofiberedCompletion`: the completion functor.

## Main results

* `Deformation.cofiberedCompletionAdjunction`: completion is right adjoint to restriction.
* `Deformation.cofiberedCompletion_isRightKanExtension`: completion is the right Kan
  extension along the inclusion of Artinian local algebras, with comparison the counit.
* `Deformation.cofiberedCompletion_obj_equiv_formalObject`: the sections of a completion
  over `S` are the formal objects of the category of elements with base `S`.
* `Deformation.cofiberedCompletion_restriction_isIso`: the counit is an isomorphism.

## Implementation notes

The value universe of the functors is independent of the universe of the algebras:
everything is stated for functors into `Type (max v z)`, with `v` the hom-set universe
of the categories of algebras. Specialising `z` to `v` recovers the setting of
`Deformation.adicCompletion`, which is pinned to `Type v`.

Levels use the positive power `m_S ^ (n + 1)`, as for formal objects. An Artinian local
algebra has a vanishing power of its maximal ideal, so from some level on its truncations
are canonically isomorphic to it; `Deformation.vanishingIndex` is the least such level,
and the counit is evaluation at it.

## References

* [Stacks Project, Tag 06HB](https://stacks.math.columbia.edu/tag/06HB)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w z uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The compatible families of values of a cofibered set `F` on the Artinian
truncations of a complete local algebra `S`. -/
public noncomputable def completedSections
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :=
  {x : (n : ℕ) → F.obj ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj S) //
    ∀ n, F.map ((AdicTruncation.transitionNat (Λ := Λ) (k := k) n).app S)
      (x (n + 1)) = x n}

/-- Completion of a cofibered set, viewed as a covariant set-valued functor.
Its sections over a complete local algebra are the compatible families of values
on the Artinian truncations. -/
@[stacks 06HB "completion functor"]
public noncomputable def cofiberedCompletion :
    (ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) ⥤
      (CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) where
  obj F := {
    obj := fun S => completedSections F S
    map := fun {S T} f => ↾fun x : completedSections F S =>
      ⟨fun n => F.map ((AdicTruncation.functor (Λ := Λ) (k := k) n).map f) (x.1 n), by
        intro n
        rw [← Functor.map_comp_apply,
          (AdicTruncation.transitionNat (Λ := Λ) (k := k) n).naturality f,
          Functor.map_comp_apply, x.2 n]⟩
    map_id := by
      intro S
      ext x
      apply Subtype.ext
      funext n
      change F.map ((AdicTruncation.functor (Λ := Λ) (k := k) n).map (𝟙 S)) (x.1 n) = x.1 n
      simp
    map_comp := by
      intro S T U f g
      ext x
      apply Subtype.ext
      funext n
      change F.map ((AdicTruncation.functor (Λ := Λ) (k := k) n).map (f ≫ g)) (x.1 n) =
        F.map ((AdicTruncation.functor (Λ := Λ) (k := k) n).map g)
          (F.map ((AdicTruncation.functor (Λ := Λ) (k := k) n).map f) (x.1 n))
      rw [(AdicTruncation.functor (Λ := Λ) (k := k) n).map_comp]
      exact Functor.map_comp_apply F _ _ (x.1 n)
  }
  map := fun {F G} α => {
    app := fun S => ↾fun x : completedSections F S =>
      ⟨fun n => α.app ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj S) (x.1 n), by
        intro n
        rw [← NatTrans.naturality_apply, x.2 n]⟩
    naturality := by
      intro S T f
      ext x
      apply Subtype.ext
      funext n
      exact NatTrans.naturality_apply α
        ((AdicTruncation.functor (Λ := Λ) (k := k) n).map f) (x.1 n)
  }
  map_id := by
    intro F
    ext S x
    apply Subtype.ext
    funext n
    rfl

  map_comp := by
    intro F G H α β
    ext S x
    apply Subtype.ext
    funext n
    rfl

/-- Once a truncation ideal of an Artinian local algebra vanishes, it vanishes at
every higher level. -/
public theorem artinianTruncation_stable_of_le
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {n m : ℕ}
    (hn : AdicTruncation.ideal (artinianToComplete.obj A) n = ⊥)
    (hm : n ≤ m) :
    AdicTruncation.ideal (artinianToComplete.obj A) m = ⊥ := by
  change maximalIdeal A ^ (n + 1) = ⊥ at hn
  exact le_antisymm ((Ideal.pow_le_pow_right (Nat.add_le_add_right hm 1)).trans_eq hn) bot_le

/-- Pulling a compatible family back along the identification with a truncation gives
the same element at two adjacent stable levels. -/
public theorem artinianSequence_eval_adjacent
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (x : completedSections F (artinianToComplete.obj A))
    (n : ℕ)
    (hn : AdicTruncation.ideal (artinianToComplete.obj A) n = ⊥)
    (hn1 : AdicTruncation.ideal (artinianToComplete.obj A) (n + 1) = ⊥) :
    F.map (artinianTruncationIso (Λ := Λ) (k := k) A n hn).inv (x.1 n) =
      F.map (artinianTruncationIso (Λ := Λ) (k := k) A (n + 1) hn1).inv
        (x.1 (n + 1)) := by
  let e0 := artinianTruncationIso (Λ := Λ) (k := k) A n hn
  let e1 := artinianTruncationIso (Λ := Λ) (k := k) A (n + 1) hn1
  have hq : e1.hom ≫ AdicTruncation.transition
      (artinianToComplete.obj A) n = e0.hom :=
    artinianAdicQuotient_transition (Λ := Λ) (k := k) A n
  have ht : AdicTruncation.transition
      (artinianToComplete.obj A) n ≫ e0.inv = e1.inv := by
    calc
      AdicTruncation.transition (artinianToComplete.obj A) n ≫ e0.inv =
          e1.inv ≫ (e1.hom ≫ AdicTruncation.transition
            (artinianToComplete.obj A) n) ≫ e0.inv := by simp
      _ = e1.inv := by
        rw [hq]
        simp
  calc
    F.map e0.inv (x.1 n) = F.map e0.inv
        (F.map (AdicTruncation.transition (artinianToComplete.obj A) n)
          (x.1 (n + 1))) := by
            congr 1
            simpa [AdicTruncation.transitionNat, AdicTruncation.transition] using
              (x.2 n).symm
    _ = F.map (AdicTruncation.transition
        (artinianToComplete.obj A) n ≫ e0.inv) (x.1 (n + 1)) := by
          rw [← Functor.map_comp_apply]
    _ = F.map e1.inv (x.1 (n + 1)) := by rw [ht]

/-- Pulling a compatible family back along the identification with a truncation is
independent of the stable level used. -/
public theorem artinianSequence_eval_eq_of_le
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (x : completedSections F (artinianToComplete.obj A))
    {n m : ℕ} (hn : AdicTruncation.ideal
      (artinianToComplete.obj A) n = ⊥)
    (hm : AdicTruncation.ideal
      (artinianToComplete.obj A) m = ⊥) (h : n ≤ m) :
    F.map (artinianTruncationIso (Λ := Λ) (k := k) A n hn).inv (x.1 n) =
      F.map (artinianTruncationIso (Λ := Λ) (k := k) A m hm).inv (x.1 m) := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      have hm0 : AdicTruncation.ideal
          (artinianToComplete.obj A) m = ⊥ :=
        artinianTruncation_stable_of_le (Λ := Λ) (k := k) A hn h
      rw [ih]
      exact artinianSequence_eval_adjacent (Λ := Λ) (k := k) F A x m hm0 hm

/-- The truncation comparison to a lower level factors through the adjacent
transition map. -/
theorem truncationMapLE_transition
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (h : n ≤ m) :
    truncationMapLE S (h.trans (Nat.le_succ m)) =
      AdicTruncation.transition S m ≫ truncationMapLE S h := by
  rw [← truncationMapLE_succ S m, truncationMapLE_comp]

/-- The inverse identification at a stable level, followed by a lower quotient map, is
the comparison between the two truncations. -/
public theorem artinianTruncationIso_inv_comp_map
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (h : n ≤ m)
    (hm : AdicTruncation.ideal (artinianToComplete.obj A) m = ⊥) :
    (artinianTruncationIso (Λ := Λ) (k := k) A m hm).inv ≫
        artinianAdicQuotient (Λ := Λ) (k := k) A n =
      truncationMapLE (artinianToComplete.obj A) h := by
  let e := artinianTruncationIso (Λ := Λ) (k := k) A m hm
  let I := AdicTruncation.ideal (artinianToComplete.obj A) m
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : e.inv.hom (Ideal.Quotient.mk I r) = r := by
    calc
      e.inv.hom (Ideal.Quotient.mk I r) = e.inv.hom (e.hom.hom r) := rfl
      _ = r := congrArg (fun f : A ⟶ A => f.hom r) e.hom_inv_id
  show (artinianAdicQuotient (Λ := Λ) (k := k) A n).hom
      (e.inv.hom (Ideal.Quotient.mk I r)) =
    (truncationMapLE (artinianToComplete.obj A) h).hom
      (Ideal.Quotient.mk I r)
  rw [he]
  rfl

/-- A compatible family is compatible with the comparison between any two truncation
levels, not only adjacent ones. -/
public theorem completedSections_eval_truncationMapLE
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : completedSections F S)
    {n m : ℕ} (h : n ≤ m) :
    F.map (truncationMapLE S h) (x.1 m) = x.1 n := by
  induction h with
  | refl =>
      rw [truncationMapLE_refl]
      simp
  | @step m h ih =>
      rw [truncationMapLE_transition (S := S) h, Functor.map_comp_apply, ← ih]
      exact congrArg (F.map _) (x.2 m)

/-- The quotient maps of a complete local algebra are compatible with the adjacent
transition maps of its truncations. -/
public theorem quotientProjection_transition
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    quotientProjection S (n + 1) ≫
      artinianToComplete.map (AdicTruncation.transition S n) =
        quotientProjection S n := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro x
  rfl

/-- The quotient maps of a complete local algebra are compatible with the comparison
between any two truncation levels. -/
public theorem quotientProjection_truncationMapLE
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (h : n ≤ m) :
    quotientProjection S m ≫
      artinianToComplete.map (truncationMapLE S h) =
    quotientProjection S n := by
  induction h with
  | refl =>
      rw [truncationMapLE_refl]
      simp
  | @step m h ih =>
      rw [truncationMapLE_transition (S := S) h, Functor.map_comp, ← Category.assoc]
      rw [quotientProjection_transition S m, ih]

/-- At a stable level, the quotient map of an Artinian local algebra viewed as a
complete local algebra is the identification with its truncation. -/
public theorem quotientProjection_artinianTruncationIso
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : AdicTruncation.ideal (artinianToComplete.obj A) n = ⊥) :
    quotientProjection (artinianToComplete.obj A) n =
      artinianToComplete.map
        (artinianTruncationIso (Λ := Λ) (k := k) A n hn).hom := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  rfl

/-- The formal object of the category of elements of `F` determined by a compatible
family of values. -/
public noncomputable def sectionsToFormalObject
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : completedSections F S) :
    FormalObject (CategoryOfElements.π F) where
  base := S
  level n := CategoryTheory.Functor.elementsMk F
    ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj S) (x.1 n)
  level_eq n := rfl
  transition n := Functor.Elements.homMk
    ((AdicTruncation.transitionNat (Λ := Λ) (k := k) n).app S) (x.2 n)
  transition_lift n := by
    apply IsHomLift.of_fac (CategoryOfElements.π F) _ _ rfl rfl
    rfl

/-- The compatible family of values determined by a formal object of the category of
elements of `F`. -/
public noncomputable def formalObjectToSections
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (X : FormalObject (CategoryOfElements.π F)) :
    completedSections F X.base := by
  let θ (n : ℕ) := eqToHom (X.level_eq n)
  refine ⟨fun n => F.map (θ n) (X.level n).2, ?_⟩
  intro n
  let := X.transition_lift n
  let p := CategoryOfElements.π F
  let tr := (AdicTruncation.transitionNat (Λ := Λ) (k := k) n).app X.base
  have htheta : θ (n + 1) ≫ tr = p.map (X.transition n) ≫ θ n := by
    have hcomm := IsHomLift.commSq p tr (X.transition n)
    simpa [θ, tr, X.level_eq] using hcomm.w.symm
  calc
    F.map tr (F.map (θ (n + 1)) (X.level (n + 1)).2) =
        F.map (θ (n + 1) ≫ tr) (X.level (n + 1)).2 := by
          exact (F.map_comp_apply _ _ _).symm
    _ = F.map (p.map (X.transition n) ≫ θ n) (X.level (n + 1)).2 := by
          rw [htheta]
    _ = F.map (θ n) (F.map (p.map (X.transition n)) (X.level (n + 1)).2) := by
          exact F.map_comp_apply _ _ _
    _ = F.map (θ n) (F.map (X.transition n).hom (X.level (n + 1)).2) := rfl
    _ = F.map (θ n) (X.level n).2 :=
          congrArg (F.map (θ n)) (X.transition n).map_val

/-- Two formal objects of a category of elements with the same base and the same
levels are equal. -/
public theorem formalObject_ext
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    {X Y : FormalObject (CategoryOfElements.π F)}
    (hbase : X.base = Y.base) (hlevel : ∀ n, X.level n = Y.level n) : X = Y := by
  cases X with
  | mk baseX levelX levelEqX transitionX transitionLiftX =>
    cases Y with
    | mk baseY levelY levelEqY transitionY transitionLiftY =>
      dsimp at hbase hlevel
      subst baseY
      have hlevel' : levelX = levelY := funext hlevel
      subst levelY
      have htransition : transitionX = transitionY := by
        funext n
        apply Functor.Elements.hom_ext
        let q := AdicTruncation.transitionNat (Λ := Λ) (k := k) n
        let p := CategoryOfElements.π F
        let : p.IsHomLift (q.app baseX) (transitionX n) := transitionLiftX n
        let : p.IsHomLift (q.app baseX) (transitionY n) := transitionLiftY n
        have h₁ := IsHomLift.commSq p (q.app baseX) (transitionX n)
        have h₂ := IsHomLift.commSq p (q.app baseX) (transitionY n)
        have hmap : p.map (transitionX n) = p.map (transitionY n) := by
          apply (cancel_mono (eqToHom (levelEqX n))).1
          simpa [q, Category.assoc, levelEqX, levelEqY] using h₁.w.trans h₂.w.symm
        simpa [p, CategoryOfElements.π] using hmap
      subst transitionY
      congr 1

/-- Turning a compatible family into a formal object and back recovers the family. -/
public theorem sectionsFormalObjectRoundTrip
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : completedSections F S) :
    formalObjectToSections F (sectionsToFormalObject F S x) = x := by
  apply Subtype.ext
  funext n
  show F.map (𝟙 ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj S)) (x.1 n) = x.1 n
  simp

/-- Compatible families of values over `S` correspond to formal objects of the
category of elements of `F` with base `S`. -/
public noncomputable def sectionsFormalObjectEquiv
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    completedSections F S ≃
      {X : FormalObject (CategoryOfElements.π F) // X.base = S} where
  toFun x := ⟨sectionsToFormalObject F S x, rfl⟩
  invFun X := (congrArg (completedSections F) X.2).mp
    (formalObjectToSections F X.1)
  left_inv x := by
    change (formalObjectToSections F (sectionsToFormalObject F S x)) = x
    exact sectionsFormalObjectRoundTrip F S x
  right_inv X := by
    rcases X with ⟨X, hX⟩
    cases hX
    apply Subtype.ext
    change sectionsToFormalObject F X.base (formalObjectToSections F X) = X
    refine formalObject_ext (F := F) (hbase := rfl) ?_
    intro n
    dsimp [sectionsToFormalObject, formalObjectToSections]
    change CategoryTheory.Functor.elementsMk F
      ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj X.base)
      (F.map (eqToHom (X.level_eq n)) (X.level n).2) = X.level n
    refine Functor.Elements.ext _ _
      (by simpa [CategoryOfElements.π] using (X.level_eq n).symm) ?_
    exact (F.map_comp_apply _ _ _).symm.trans (by
      simp only [eqToHom_trans, eqToHom_refl]; exact F.map_id_apply _ _)

/-- The compatible family of images of an element under the quotient maps of its
base. -/
public noncomputable def cofiberedCompletionUnitValue
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : G.obj S) :
    (cofiberedCompletion.obj (artinianToComplete ⋙ G)).obj S := by
  refine ⟨fun n => G.map (quotientProjection S n) x, ?_⟩
  intro n
  calc
    G.map ((artinianToComplete.map
        ((AdicTruncation.transitionNat (Λ := Λ) (k := k) n).app S)))
        (G.map (quotientProjection S (n + 1)) x) =
        G.map (quotientProjection S (n + 1) ≫
          artinianToComplete.map
            ((AdicTruncation.transitionNat (Λ := Λ) (k := k) n).app S)) x := by
              rw [← Functor.map_comp_apply]
    _ = G.map (quotientProjection S n) x := by
          simpa [AdicTruncation.transitionNat] using
            congrArg (fun q => G.map q x) (quotientProjection_transition S n)

/-- The component of the restriction--completion unit at a functor on complete local
algebras. -/
public noncomputable def cofiberedCompletionUnitApp
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) :
    G ⟶ cofiberedCompletion.obj ((artinianToComplete (Λ := Λ) (k := k)) ⋙ G) := by
  refine
    { app := fun S => TypeCat.ofHom (cofiberedCompletionUnitValue G S)
      naturality := ?_ }
  intro S T f
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  funext n
  change G.map (quotientProjection T n) (G.map f x) =
    G.map (artinianToComplete.map
      ((AdicTruncation.functor (Λ := Λ) (k := k) n).map f))
      (G.map (quotientProjection S n) x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun q => G.map q x)
    (quotientProjection_naturality S T f n).symm

/-- The unit of the restriction--completion adjunction. -/
public noncomputable def cofiberedCompletionUnit :
    𝟭 (CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) ⟶
      (Functor.whiskeringLeft
        (ArtinianLocalAlgCat.{u, v, w} Λ k)
        (CompleteLocalAlgCat.{u, v, w} Λ k)
        (Type (max v z))).obj
        (artinianToComplete (Λ := Λ) (k := k)) ⋙
          cofiberedCompletion (Λ := Λ) (k := k) := by
  refine { app := cofiberedCompletionUnitApp, naturality := ?_ }
  intro G H η
  change NatTrans G H at η
  let ηI : artinianToComplete ⋙ G ⟶
      artinianToComplete ⋙ H := {
    app := fun A => η.app (artinianToComplete.obj A)
    naturality := by
      intro A B f
      exact η.naturality (artinianToComplete.map f)
  }
  ext S x
  change G.obj S at x
  change cofiberedCompletionUnitValue H S (η.app S x) =
    ((cofiberedCompletion.map ηI).app S) (cofiberedCompletionUnitValue G S x)
  apply Subtype.ext
  funext n
  change H.map (quotientProjection S n) (η.app S x) =
    ηI.app ((AdicTruncation.functor (Λ := Λ) (k := k) n).obj S)
      (G.map (quotientProjection S n) x)
  dsimp [ηI]
  exact (NatTrans.naturality_apply η
    (quotientProjection S n) x).symm

/-- The value of a compatible family at a stable level, pulled back along the
identification of the algebra with that truncation. -/
public noncomputable def cofiberedCompletionCounitValue
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (x : completedSections F (artinianToComplete.obj A)) : F.obj A :=
  F.map (artinianTruncationIso (Λ := Λ) (k := k) A
    (vanishingIndex (Λ := Λ) (k := k) A)
    (vanishingIndex_spec (Λ := Λ) (k := k) A)).inv
    (x.1 (vanishingIndex (Λ := Λ) (k := k) A))

/-- The compatible family of images of a value of `F` at `A` under the quotient maps
of `A`. -/
public noncomputable def cofiberedCompletionCounitInverseValue
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (y : F.obj A) :
    completedSections F (artinianToComplete.obj A) := by
  refine ⟨fun n => F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n) y, ?_⟩
  intro n
  change F.map (AdicTruncation.transition (artinianToComplete.obj A) n)
    (F.map (artinianAdicQuotient (Λ := Λ) (k := k) A (n + 1)) y) = _
  rw [← Functor.map_comp_apply, artinianAdicQuotient_transition]

/-- The component of the restriction--completion counit at a cofibered set. -/
public noncomputable def cofiberedCompletionCounitApp
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) :
    artinianToComplete (Λ := Λ) (k := k) ⋙ (cofiberedCompletion.obj F) ⟶ F := by
  classical
  refine {
    app := fun A => TypeCat.ofHom (cofiberedCompletionCounitValue F A)
    naturality := ?_ }
  intro A B f
  apply ConcreteCategory.hom_ext
  intro x
  let nA := vanishingIndex (Λ := Λ) (k := k) A
  let nB := vanishingIndex (Λ := Λ) (k := k) B
  let m := max nA nB
  have hmA : nA ≤ m := le_max_left _ _
  have hmB : nB ≤ m := le_max_right _ _
  have hA : AdicTruncation.ideal (artinianToComplete.obj A) m = ⊥ :=
    artinianTruncation_stable_of_le (Λ := Λ) (k := k) A
      (vanishingIndex_spec (Λ := Λ) (k := k) A) hmA
  have hB : AdicTruncation.ideal (artinianToComplete.obj B) m = ⊥ :=
    artinianTruncation_stable_of_le (Λ := Λ) (k := k) B
      (vanishingIndex_spec (Λ := Λ) (k := k) B) hmB
  let eA := artinianTruncationIso (Λ := Λ) (k := k) A m hA
  let eB := artinianTruncationIso (Λ := Λ) (k := k) B m hB
  have he : eA.hom ≫ (AdicTruncation.functor (Λ := Λ) (k := k) m).map
      (artinianToComplete.map f) = f ≫ eB.hom :=
    artinianAdicQuotient_naturality (Λ := Λ) (k := k) f m
  have he' : eA.inv ≫ f =
      (AdicTruncation.functor (Λ := Λ) (k := k) m).map
        (artinianToComplete.map f) ≫ eB.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, Iso.inv_comp_eq, he]
  change cofiberedCompletionCounitValue F B
      ((cofiberedCompletion.obj F).map (artinianToComplete.map f) x) =
    F.map f (cofiberedCompletionCounitValue F A x)
  unfold cofiberedCompletionCounitValue
  rw [artinianSequence_eval_eq_of_le (Λ := Λ) (k := k) F B
    ((cofiberedCompletion.obj F).map (artinianToComplete.map f) x)
    (vanishingIndex_spec (Λ := Λ) (k := k) B) hB hmB]
  rw [artinianSequence_eval_eq_of_le (Λ := Λ) (k := k) F A x
    (vanishingIndex_spec (Λ := Λ) (k := k) A) hA hmA]
  change F.map eB.inv
      (F.map ((AdicTruncation.functor (Λ := Λ) (k := k) m).map
        (artinianToComplete.map f)) (x.1 m)) =
    F.map f (F.map eA.inv (x.1 m))
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, he']

/-- The counit of the restriction--completion adjunction. -/
public noncomputable def cofiberedCompletionCounit :
    (cofiberedCompletion (Λ := Λ) (k := k)).comp
        ((Functor.whiskeringLeft (ArtinianLocalAlgCat.{u, v, w} Λ k)
          (CompleteLocalAlgCat.{u, v, w} Λ k) (Type (max v z))).obj
          (artinianToComplete (Λ := Λ) (k := k))) ⟶
      𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) := by
  refine { app := cofiberedCompletionCounitApp, naturality := ?_ }
  intro F G α
  ext A x
  change cofiberedCompletionCounitValue G A
      (((cofiberedCompletion.map α).app (artinianToComplete.obj A)) x) =
    α.app A (cofiberedCompletionCounitValue F A x)
  unfold cofiberedCompletionCounitValue
  exact (NatTrans.naturality_apply α
    (artinianTruncationIso (Λ := Λ) (k := k) A
      (vanishingIndex (Λ := Λ) (k := k) A)
      (vanishingIndex_spec (Λ := Λ) (k := k) A)).inv
    (x.1 (vanishingIndex (Λ := Λ) (k := k) A))).symm

/-- The truncation of a quotient map, followed by the inverse identification at a
stable level, is the comparison between the two truncations. -/
public theorem quotientProjection_map_artinianTruncationIso_inv
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (h : n ≤ m)
    (hm : AdicTruncation.ideal
      (artinianToComplete.obj ((AdicTruncation.functor n).obj S)) m = ⊥) :
    (AdicTruncation.functor m).map (quotientProjection S n) ≫
        (artinianTruncationIso (Λ := Λ) (k := k)
          ((AdicTruncation.functor n).obj S) m hm).inv =
      truncationMapLE S h := by
  let A := (AdicTruncation.functor n).obj S
  let e := artinianTruncationIso (Λ := Λ) (k := k) A m hm
  let qM := quotientProjection S m
  let q := quotientProjection S n
  let τ := (AdicTruncation.functor m).map q
  let t := truncationMapLE S h
  let qA := quotientProjection (artinianToComplete.obj A) m
  have hFactor : qM ≫ artinianToComplete.map t = q :=
    quotientProjection_truncationMapLE S h
  have hA : qA = artinianToComplete.map e.hom :=
    quotientProjection_artinianTruncationIso A m hm
  have hNat := quotientProjection_naturality S
    (artinianToComplete.obj A) q m
  have hEq : qM ≫ artinianToComplete.map τ =
      qM ≫ artinianToComplete.map (t ≫ e.hom) := by
    calc
      qM ≫ artinianToComplete.map τ = q ≫ qA := hNat
      _ = (qM ≫ artinianToComplete.map t) ≫
          artinianToComplete.map e.hom := by rw [hFactor, hA]
      _ = qM ≫ artinianToComplete.map (t ≫ e.hom) := by
          simp [Functor.map_comp, Category.assoc]
  have ht : τ = t ≫ e.hom := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hpt := congrArg (fun f : S ⟶ artinianToComplete.obj
      ((AdicTruncation.functor (Λ := Λ) (k := k) m).obj
        (artinianToComplete.obj A)) => f.hom r) hEq
    change τ.hom (Ideal.Quotient.mk
        (AdicTruncation.ideal S m) r) =
      e.hom.hom (t.hom (Ideal.Quotient.mk (AdicTruncation.ideal S m) r)) at hpt
    exact hpt
  show τ ≫ e.inv = t
  rw [ht]
  simp

/-- Completion is right adjoint to restriction; its hom equivalence is the
functorial bijection from maps out of a restriction to maps into a completion. -/
@[stacks 06HB "functorial hom bijection"]
public noncomputable def cofiberedCompletionAdjunction :
    (Functor.whiskeringLeft
      (ArtinianLocalAlgCat.{u, v, w} Λ k)
      (CompleteLocalAlgCat.{u, v, w} Λ k)
      (Type (max v z))).obj
      (artinianToComplete (Λ := Λ) (k := k)) ⊣
      cofiberedCompletion (Λ := Λ) (k := k) := by
  classical
  exact Adjunction.mkOfUnitCounit {
    unit := cofiberedCompletionUnit (Λ := Λ) (k := k)
    counit := cofiberedCompletionCounit (Λ := Λ) (k := k)
    left_triangle := by
      ext G S x
      change cofiberedCompletionCounitValue
          ((artinianToComplete (Λ := Λ) (k := k)) ⋙ G) S
          (cofiberedCompletionUnitValue G (artinianToComplete.obj S) x) = x
      unfold cofiberedCompletionCounitValue cofiberedCompletionUnitValue
      let n := vanishingIndex (Λ := Λ) (k := k) S
      let hn := vanishingIndex_spec (Λ := Λ) (k := k) S
      let e := artinianTruncationIso (Λ := Λ) (k := k) S n hn
      have hq : quotientProjection (Λ := Λ) (k := k)
          (artinianToComplete.obj S) n =
          artinianToComplete.map e.hom :=
        quotientProjection_artinianTruncationIso S n hn
      change G.map (artinianToComplete.map e.inv)
        (G.map (quotientProjection (Λ := Λ) (k := k)
          (artinianToComplete.obj S) n) x) = x
      rw [← Functor.map_comp_apply, hq]
      simp [e]
    right_triangle := by
      ext F S x
      apply Subtype.ext
      funext n
      let A := (AdicTruncation.functor (Λ := Λ) (k := k) n).obj S
      let q := quotientProjection S n
      let y := (cofiberedCompletion.obj F).map q x
      let kA := vanishingIndex (Λ := Λ) (k := k) A
      let hkA := vanishingIndex_spec (Λ := Λ) (k := k) A
      let m := max n kA
      have hnm : n ≤ m := le_max_left _ _
      have hkAm : kA ≤ m := le_max_right _ _
      have hmA : AdicTruncation.ideal
          (artinianToComplete.obj A) m = ⊥ :=
        artinianTruncation_stable_of_le (Λ := Λ) (k := k) A hkA hkAm
      change cofiberedCompletionCounitValue F A y = x.1 n
      unfold cofiberedCompletionCounitValue
      calc
        F.map (artinianTruncationIso (Λ := Λ) (k := k) A kA hkA).inv
            (y.1 kA) =
          F.map (artinianTruncationIso (Λ := Λ) (k := k) A m hmA).inv
            (y.1 m) :=
              artinianSequence_eval_eq_of_le (Λ := Λ) (k := k) F A y
                hkA hmA hkAm
        _ = F.map (truncationMapLE S hnm) (x.1 m) := by
              dsimp [y, cofiberedCompletion]
              change F.map
                  (artinianTruncationIso (Λ := Λ) (k := k) A m hmA).inv
                  (F.map ((AdicTruncation.functor (Λ := Λ) (k := k) m).map q)
                    (x.1 m)) = _
              rw [← Functor.map_comp_apply,
                quotientProjection_map_artinianTruncationIso_inv S hnm hmA]
        _ = x.1 n :=
              completedSections_eval_truncationMapLE (Λ := Λ) (k := k)
                F S x hnm
  }

/-- Completion is the right Kan extension of a set-valued functor along the
inclusion of Artinian local algebras, with the comparison supplied by the
adjunction counit. -/
@[stacks 06HB "canonical completion"]
public theorem cofiberedCompletion_isRightKanExtension
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) :
    (cofiberedCompletion (Λ := Λ) (k := k) |>.obj F).IsRightKanExtension
      ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F) := by
  classical
  let L := (Functor.whiskeringLeft
    (ArtinianLocalAlgCat.{u, v, w} Λ k)
    (CompleteLocalAlgCat.{u, v, w} Λ k)
    (Type (max v z))).obj (artinianToComplete (Λ := Λ) (k := k))
  let R := cofiberedCompletion (Λ := Λ) (k := k)
  let adj := cofiberedCompletionAdjunction (Λ := Λ) (k := k)
  let α := adj.counit.app F
  refine ⟨⟨Limits.IsTerminal.ofUniqueHom ?_ ?_⟩⟩
  · intro X
    let γ : X.left ⟶ R.obj F := (adj.homEquiv X.left F) X.hom
    refine CostructuredArrow.homMk γ ?_
    simpa [γ, α, adj] using
      (Adjunction.homEquiv_counit (adj := adj) (X := X.left) (Y := F) (g := γ)).symm
  · intro X f
    apply CostructuredArrow.hom_ext
    let γ : X.left ⟶ R.obj F := (adj.homEquiv X.left F) X.hom
    show f.left = γ
    apply (adj.homEquiv X.left F).symm.injective
    calc
      (adj.homEquiv X.left F).symm f.left =
          L.map f.left ≫ adj.counit.app F :=
            Adjunction.homEquiv_counit (adj := adj) (X := X.left)
              (Y := F) (g := f.left)
      _ = X.hom := CostructuredArrow.w f
      _ = (adj.homEquiv X.left F).symm γ := by simp [γ]

/-- A section of the completed cofibered set at `S` is a formal object of the
category of elements of `F` whose base is `S`. -/
@[stacks 06HB "formal-object description",
  stacks 06H8 "the completion of a set-valued functor is the limit over the adic truncations"]
public noncomputable def cofiberedCompletion_obj_equiv_formalObject
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (cofiberedCompletion.obj F).obj S ≃
      {X : FormalObject (CategoryOfElements.π F) // X.base = S} :=
  sectionsFormalObjectEquiv F S

/-- The canonical map from the restriction of a completion to the original
cofibered set is an isomorphism. -/
@[stacks 06HB "counit isomorphism"]
public theorem cofiberedCompletion_restriction_isIso
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) :
    IsIso ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  rw [CategoryTheory.isIso_iff_bijective]
  show Function.Bijective (cofiberedCompletionCounitValue F A)
  let inv := cofiberedCompletionCounitInverseValue (Λ := Λ) (k := k) F A
  have hleft : ∀ y, cofiberedCompletionCounitValue F A (inv y) = y := by
    intro y
    let n := vanishingIndex (Λ := Λ) (k := k) A
    let hn := vanishingIndex_spec (Λ := Λ) (k := k) A
    let e := artinianTruncationIso (Λ := Λ) (k := k) A n hn
    show F.map e.inv (F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n) y) = y
    rw [← Functor.map_comp_apply]
    have he : artinianAdicQuotient (Λ := Λ) (k := k) A n = e.hom := rfl
    rw [he]
    simp [e]
  have hright : ∀ x,
      inv (cofiberedCompletionCounitValue F A x) = x := by
    intro x
    apply Subtype.ext
    funext n
    let s := vanishingIndex (Λ := Λ) (k := k) A
    let hs := vanishingIndex_spec (Λ := Λ) (k := k) A
    let m := max n s
    have hnm : n ≤ m := le_max_left _ _
    have hsm : s ≤ m := le_max_right _ _
    have hm : AdicTruncation.ideal
        (artinianToComplete.obj A) m = ⊥ :=
      artinianTruncation_stable_of_le (Λ := Λ) (k := k) A hs hsm
    show F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n)
        (cofiberedCompletionCounitValue F A x) = x.1 n
    unfold cofiberedCompletionCounitValue
    calc
      F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n)
          (F.map (artinianTruncationIso (Λ := Λ) (k := k) A s hs).inv
            (x.1 s)) =
        F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n)
          (F.map (artinianTruncationIso (Λ := Λ) (k := k) A m hm).inv
            (x.1 m)) :=
              congrArg (F.map (artinianAdicQuotient (Λ := Λ) (k := k) A n))
                (artinianSequence_eval_eq_of_le (Λ := Λ) (k := k) F A x hs hm hsm)
      _ = F.map ((artinianTruncationIso (Λ := Λ) (k := k) A m hm).inv ≫
            artinianAdicQuotient (Λ := Λ) (k := k) A n) (x.1 m) := by
              rw [← Functor.map_comp_apply]
      _ = F.map (truncationMapLE (artinianToComplete.obj A) hnm) (x.1 m) := by
              rw [artinianTruncationIso_inv_comp_map (Λ := Λ) (k := k)
                A hnm hm]
      _ = x.1 n :=
            completedSections_eval_truncationMapLE (Λ := Λ) (k := k)
              F (artinianToComplete.obj A) x hnm
  exact ⟨Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩

end Deformation
