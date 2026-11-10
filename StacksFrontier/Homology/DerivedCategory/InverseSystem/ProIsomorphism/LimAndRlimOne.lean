module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProMorphisms
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLeffler
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimHom
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimTriangle
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Pro-morphisms of inverse systems, inverse limits and derived limits

An inverse system of abelian groups indexed by the natural numbers determines a pro-object, and a
morphism of pro-objects is represented, as in Stacks 0G2X, by a natural transformation between
the covariant functors the two systems corepresent. This file makes the inverse limit and the
first derived inverse limit into functors of the pro-object: a pro-morphism induces maps on
`lim` and on `R¹lim`, compatibly with identities and composition, and a pro-isomorphism induces
isomorphisms on both.

The computation runs through *sequential representatives*: a pro-morphism `A ⟶ B` is realized by
a strictly increasing reindexing together with maps `A_{index n} ⟶ B_n`, and such a
representative gives two maps on the products of the terms — the reindexing map, which computes
the map on `lim`, and a telescoping map, which computes the map on `R¹lim`. Two representatives
of the same pro-morphism have a common refinement, which is why the induced maps do not depend on
the choice.

As a consequence, derived limits of pro-isomorphic inverse systems in a pretriangulated category
are isomorphic, although not canonically: the isomorphism is produced from a morphism of the two
defining triangles, and is seen to be an isomorphism by comparing the Milnor sequences of the two
systems for maps out of every object.

## Main definitions

* `Rlim.Pro.proYoneda`: the covariant functor corepresented by a pro-system.
* `Rlim.Pro.SequentialRep`: a strictly increasing representative of a pro-morphism, with
  `SequentialRep.productFirst` and `SequentialRep.productSecond` its two induced maps on the
  products of the terms, `SequentialRep.mapLim` and `SequentialRep.mapR1lim` the induced maps on
  `lim` and on `R¹lim`, `SequentialRep.Represents` the assertion that it represents a given
  pro-morphism, and `SequentialRep.Refines` the refinement relation.
* `Rlim.Pro.proIsoRepresents`: the assertion that a transformation is the one a pro-isomorphism
  induces on identity classes.
* `Rlim.Pro.IsProIsomorphismOnDerivedEvaluationSystems`: the assertion that the morphism between
  the evaluated systems of a morphism of `D(Ab(N))` is an isomorphism of pro-objects.
* `Rlim.Pro.MapsHomologyProIsomorphismsToIsomorphisms`: the degreewise-homology criterion for a
  functor on `D(Ab(N))` to invert a morphism.

## Main results

* `Rlim.Pro.exists_map_lim_and_cokernel_delta`: pro-morphisms act functorially on inverse limits
  and on the cokernels computing first derived inverse limits, the action is computed by any
  sequential representative, it is compatible with the Milnor diagram of Tag 0919, and a
  pro-isomorphism induces isomorphisms (Tag 0H9K).
* `Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism`: derived limits of pro-isomorphic
  inverse systems in a pretriangulated category are non-canonically isomorphic (Tag 0H9L).
* `Rlim.Pro.lim_hasRightDerivedFunctor_and_maps_proIsomorphisms_to_isomorphisms`: the
  right-derived inverse limit inverts a morphism of `D(Ab(N))` whose evaluated systems are
  pro-isomorphic (Tag 091B).
* `Rlim.Pro.isProZero_iff_isZero_lim_and_rightDerivedLim_one_and_countable_coproduct`: an inverse
  system is zero as a pro-object exactly when `lim` and `R¹lim` vanish on it and on the countable
  direct sum of copies of it (Tag 091C).

## Implementation notes

The first derived inverse limit is the cokernel of `Rlim.delta`, the presentation of
`StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic`. A pro-isomorphism of inverse
systems is `ProIso`, given by explicit compatible maps in both directions after cofinal
reindexings; it is universe-polymorphic in the morphisms of the ambient category. Since the
source of Tag 0H9L asserts a non-canonical isomorphism, its conclusion is `Nonempty`.

## References

* [Stacks Project, Tag 0H9K](https://stacks.math.columbia.edu/tag/0H9K)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
* [Stacks Project, Tag 091B](https://stacks.math.columbia.edu/tag/091B)
* [Stacks Project, Tag 091C](https://stacks.math.columbia.edu/tag/091C)
* [Stacks Project, Tag 0G2W](https://stacks.math.columbia.edu/tag/0G2W)
-/


section

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace Rlim.Pro

universe w u
/-- The covariant functor represented by a pro-system. -/
public noncomputable abbrev proYoneda (A : Rlim.InvSystemAb.{w}) : Ab.{w} ⥤ Type w :=
  colimit (A.op ⋙ coyoneda)
/-- A sequential representative of a pro-morphism `A ⟶ B`. The value at level `n` is a
map from level `index n` of `A` to level `n` of `B`. -/
public structure SequentialRep (A B : Rlim.InvSystemAb.{w}) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  index_le : ∀ n, n ≤ index n
  component : ∀ n, A.obj (op (index n)) ⟶ B.obj (op n)
  naturality : ∀ {n m : ℕ} (h : n ≤ m),
    A.map (homOfLE (index_strict.monotone h)).op ≫ component n =
      component m ≫ B.map (homOfLE h).op

/-- The map on products used for the ordinary inverse limit. -/
public noncomputable def SequentialRep.productFirst {A B : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) : Rlim.product A ⟶ Rlim.product B :=
  Pi.map' r.index r.component

/-- The telescoping map on products used for the first derived inverse limit. -/
public noncomputable def SequentialRep.productSecond {A B : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) : Rlim.product A ⟶ Rlim.product B :=
  Pi.lift fun n => ∑ k ∈ Finset.Ico (r.index n) (r.index (n + 1)),
    if h : r.index n ≤ k then
      Pi.π (fun j : ℕ ↦ A.obj (op j)) k ≫
        A.map (homOfLE h).op ≫ r.component n
    else 0

/-- The identity sequential representative. -/
public def SequentialRep.id (A : Rlim.InvSystemAb.{w}) : SequentialRep A A where
  index := fun n => n
  index_strict := strictMono_id
  index_le := fun _ => le_refl _
  component := fun _ => 𝟙 _
  naturality := by intros; simp

/-- Composition of sequential representatives, with the expected composite reindexing. -/
public def SequentialRep.comp {A B C : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) (s : SequentialRep B C) : SequentialRep A C where
  index := r.index ∘ s.index
  index_strict := r.index_strict.comp s.index_strict
  index_le := fun n => le_trans (s.index_le n) (r.index_le (s.index n))
  component := fun n => r.component (s.index n) ≫ s.component n
  naturality := by
    intro n m h
    dsimp
    have hr := r.naturality (s.index_strict.monotone h)
    have hs := s.naturality h
    calc
      _ = (r.component (s.index m) ≫ B.map (homOfLE (s.index_strict.monotone h)).op) ≫
          s.component n := congrArg (fun f => f ≫ s.component n) hr
      _ = r.component (s.index m) ≫ (s.component m ≫ C.map (homOfLE h).op) := by
        rw [Category.assoc]
        exact congrArg (fun f => r.component (s.index m) ≫ f) hs
      _ = _ := by simp only [Category.assoc]

/-- A direct refinement changes a representative by moving its source index farther out. -/
public def SequentialRep.Refines {A B : Rlim.InvSystemAb.{w}}
    (r s : SequentialRep A B) : Prop :=
  ∀ n, ∃ h : r.index n ≤ s.index n,
    s.component n = A.map (homOfLE h).op ≫ r.component n

/-- The cone map on ordinary inverse limits determined by a sequential representative. -/
public noncomputable def SequentialRep.mapLim {A B : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) : limit A ⟶ limit B :=
  limit.lift B {
    pt := limit A
    π := {
      app := fun n => limit.π A (op (r.index n.unop)) ≫ r.component n.unop
      naturality := by
        intro n m f
        obtain ⟨n⟩ := n
        obtain ⟨m⟩ := m
        have h : m ≤ n := leOfHom f.unop
        obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
        dsimp
        rw [Category.assoc, ← r.naturality h, ← Category.assoc]
        simp only [Category.id_comp] at *
        exact (congrArg (fun g => g ≫ r.component m)
          (limit.w A (homOfLE (r.index_strict.monotone h)).op)).symm
    }
  }
/-- A sequential representative realizes a pro-morphism when the latter takes each identity
class of the target system to the class of its specified level map. -/
public def SequentialRep.Represents {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B)
    (φ : proYoneda B ⟶ proYoneda A) : Prop :=
  ∀ n : ℕ,
    φ.app (B.obj (op n))
      ((colimit.ι (B.op ⋙ coyoneda) (op (op n))).app (B.obj (op n)) (𝟙 _)) =
    (colimit.ι (A.op ⋙ coyoneda) (op (op (r.index n)))).app (B.obj (op n))
      (r.component n)

/-- The cokernel map induced by a commuting pair of representative product maps. -/
public noncomputable def SequentialRep.mapR1lim {A B : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B)
    (hδ : Rlim.delta A ≫ r.productSecond = r.productFirst ≫ Rlim.delta B) :
    cokernel (Rlim.delta A) ⟶ cokernel (Rlim.delta B) :=
  cokernel.map (Rlim.delta A) (Rlim.delta B) r.productFirst r.productSecond hδ

/-- A pro-isomorphism realizes this transformation on identity classes through its forward
representative. -/
public def proIsoRepresents {A B : Rlim.InvSystemAb.{w}} (a : InverseSequence.ProIso A B)
    (φ : proYoneda B ⟶ proYoneda A) : Prop :=
  ∀ n : ℕ,
    φ.app (B.obj (op n))
      ((colimit.ι (B.op ⋙ coyoneda) (op (op n))).app (B.obj (op n)) (𝟙 _)) =
    (colimit.ι (A.op ⋙ coyoneda) (op (op (a.α n)))).app (B.obj (op n))
      (a.φ n)

end Rlim.Pro
end

end


section

noncomputable section

open CategoryTheory Limits Opposite
open InverseSequence.ProIso (tr_refl tr_trans)

namespace Rlim.Pro

universe w u

private abbrev projection (A : Rlim.InvSystemAb.{w}) (n : ℕ) :=
  Pi.π (fun n : ℕ => A.obj (op n)) n

/-- Maps into the product of an inverse system are determined by their projections. -/
private lemma product_hom_ext {A : Rlim.InvSystemAb.{w}} {X : Ab.{w}} {f g : X ⟶ Rlim.product A}
    (h : ∀ n, f ≫ projection A n = g ≫ projection A n) : f = g :=
  Pi.hom_ext _ _ h

private def intervalSum (A : Rlim.InvSystemAb.{w}) (i j : ℕ) : Rlim.product A ⟶ A.obj (op i) :=
  ∑ k ∈ Finset.Ico i j, if h : i ≤ k then projection A k ≫ InverseSequence.tr A h else 0

private lemma intervalSum_self (A : Rlim.InvSystemAb.{w}) (i : ℕ) : intervalSum A i i = 0 := by
  simp [intervalSum]

private lemma intervalSum_succ (A : Rlim.InvSystemAb.{w}) {i j : ℕ} (h : i ≤ j) :
    intervalSum A i (j + 1) = intervalSum A i j + projection A j ≫ InverseSequence.tr A h := by
  simp [intervalSum, Finset.sum_Ico_succ_top h, h]

private lemma intervalSum_add (A : Rlim.InvSystemAb.{w}) {i j k : ℕ}
    (h : i ≤ j) (h' : j ≤ k) :
    intervalSum A i j + intervalSum A j k ≫ InverseSequence.tr A h = intervalSum A i k := by
  unfold intervalSum
  rw [Preadditive.sum_comp]
  have he : (∑ x ∈ Finset.Ico j k,
      (if hx : j ≤ x then projection A x ≫ InverseSequence.tr A hx else 0) ≫
        InverseSequence.tr A h) =
      ∑ x ∈ Finset.Ico j k, if hx : i ≤ x then projection A x ≫ InverseSequence.tr A hx else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hjx := (Finset.mem_Ico.mp hx).1
    simp only [dite_eq_left hjx, dite_eq_left (h.trans hjx), Category.assoc, tr_trans]
  rw [he, Finset.sum_Ico_consecutive _ h h']

private lemma delta_projection (A : Rlim.InvSystemAb.{w}) (i : ℕ) :
    Rlim.delta A ≫ projection A i =
      projection A i - projection A (i + 1) ≫ InverseSequence.tr A (Nat.le_succ i) := by
  simp [Rlim.delta, Rlim.shift, projection, InverseSequence.tr, Preadditive.sub_comp]

private lemma delta_intervalSum (A : Rlim.InvSystemAb.{w}) {i j : ℕ} (h : i ≤ j) :
    Rlim.delta A ≫ intervalSum A i j =
      projection A i - projection A j ≫ InverseSequence.tr A h := by
  induction j, h using Nat.le_induction with
  | base => simp [intervalSum_self, tr_refl]
  | succ j h ih =>
    rw [intervalSum_succ A h, Preadditive.comp_add, ih, ← Category.assoc,
      delta_projection, Preadditive.sub_comp, Category.assoc, tr_trans]
    abel

private lemma first_projection {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B) (n : ℕ) :
    r.productFirst ≫ projection B n = projection A (r.index n) ≫ r.component n := by
  simp [SequentialRep.productFirst, projection]

private lemma second_projection {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B) (n : ℕ) :
    r.productSecond ≫ projection B n =
      intervalSum A (r.index n) (r.index (n + 1)) ≫ r.component n := by
  simp only [SequentialRep.productSecond, projection, Pi.lift_comp_π, intervalSum,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [dite_eq_left (Finset.mem_Ico.mp hk).1, Category.assoc, InverseSequence.tr]

private lemma representative_naturality {A B : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) {i j : ℕ} (h : i ≤ j) :
    InverseSequence.tr A (r.index_strict.monotone h) ≫ r.component i =
      r.component j ≫ InverseSequence.tr B h :=
  r.naturality h

private lemma representative_chain_map {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B) :
    Rlim.delta A ≫ r.productSecond = r.productFirst ≫ Rlim.delta B := by
  apply product_hom_ext
  intro n
  rw [Category.assoc, second_projection, ← Category.assoc,
    delta_intervalSum A (r.index_strict.monotone (Nat.le_succ n)),
    Preadditive.sub_comp, Category.assoc, representative_naturality r (Nat.le_succ n),
    Category.assoc, delta_projection, Preadditive.comp_sub,
    first_projection]
  simp only [← Category.assoc, first_projection]

private lemma representative_id_products (A : Rlim.InvSystemAb.{w}) :
    (SequentialRep.id A).productFirst = 𝟙 _ ∧
    (SequentialRep.id A).productSecond = 𝟙 _ := by
  constructor
  · apply product_hom_ext
    intro n
    simp [SequentialRep.productFirst, SequentialRep.id]
  · apply product_hom_ext
    intro n
    rw [second_projection]
    simp [SequentialRep.id, intervalSum_succ, intervalSum_self, tr_refl]

private lemma second_intervalSum {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B)
    {i j : ℕ} (h : i ≤ j) :
    r.productSecond ≫ intervalSum B i j =
      intervalSum A (r.index i) (r.index j) ≫ r.component i := by
  induction j, h using Nat.le_induction with
  | base => simp [intervalSum_self]
  | succ j h ih =>
    rw [intervalSum_succ B h, Preadditive.comp_add, ih, ← Category.assoc,
      second_projection, Category.assoc, ← representative_naturality r h, ← Category.assoc,
      ← Preadditive.add_comp, intervalSum_add A (r.index_strict.monotone h)
        (r.index_strict.monotone (Nat.le_succ j))]

private lemma representative_comp_products {A B C : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) (s : SequentialRep B C) :
    (r.comp s).productFirst = r.productFirst ≫ s.productFirst ∧
    (r.comp s).productSecond = r.productSecond ≫ s.productSecond := by
  constructor
  · apply product_hom_ext
    intro n
    simp only [Category.assoc, first_projection, SequentialRep.comp, Function.comp_apply]
    simp only [← Category.assoc, first_projection]
  · apply product_hom_ext
    intro n
    simp only [Category.assoc, second_projection]
    rw [← Category.assoc, second_intervalSum r (s.index_strict.monotone (Nat.le_succ n))]
    rfl

private lemma mapLim_projection {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B) (n : ℕ) :
    r.mapLim ≫ limit.π B (op n) = limit.π A (op (r.index n)) ≫ r.component n := by
  simp [SequentialRep.mapLim]

private lemma representative_refines_lim {A B : Rlim.InvSystemAb.{w}}
    (r s : SequentialRep A B) (h : r.Refines s) : r.mapLim = s.mapLim := by
  apply limit.hom_ext
  rintro ⟨n⟩
  rw [mapLim_projection, mapLim_projection]
  obtain ⟨hn, he⟩ := h n
  rw [he, ← Category.assoc]
  exact (congrArg (fun f => f ≫ r.component n) (limit.w A (homOfLE hn).op)).symm

private lemma representative_refines_cokernel {A B : Rlim.InvSystemAb.{w}}
    (r s : SequentialRep A B) (h : r.Refines s) :
    r.productSecond ≫ cokernel.π (Rlim.delta B) =
      s.productSecond ≫ cokernel.π (Rlim.delta B) := by
  let H : Rlim.product A ⟶ Rlim.product B := Pi.lift fun n =>
    intervalSum A (r.index n) (s.index n) ≫ r.component n
  have hH : H ≫ Rlim.delta B = r.productSecond - s.productSecond := by
    apply product_hom_ext
    intro n
    obtain ⟨hn, en⟩ := h n
    obtain ⟨hn', en'⟩ := h (n + 1)
    have hr := r.index_strict.monotone (Nat.le_succ n)
    have hs := s.index_strict.monotone (Nat.le_succ n)
    have h1 := intervalSum_add A hr hn'
    have h2 := intervalSum_add A hn hs
    rw [Category.assoc, delta_projection, Preadditive.comp_sub,
      Preadditive.sub_comp, second_projection, second_projection, en]
    simp only [H, projection, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    change _ = _ - intervalSum A (s.index n) (s.index (n + 1)) ≫ InverseSequence.tr A hn ≫
      r.component n
    rw [Category.assoc, ← representative_naturality r (Nat.le_succ n)]
    simp only [← Category.assoc, ← Preadditive.sub_comp]
    congr 1
    exact sub_eq_sub_iff_add_eq_add.mpr (h2.trans h1.symm)
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp, ← hH, Category.assoc, cokernel.condition, comp_zero]

private abbrev stageClass (A : Rlim.InvSystemAb.{w}) {X : Ab.{w}} {n : ℕ}
    (f : A.obj (op n) ⟶ X) : (proYoneda A).obj X :=
  (colimit.ι (A.op ⋙ coyoneda) (op (op n))).app X f

private lemma stageClass_postcomp (A : Rlim.InvSystemAb.{w}) {X Y : Ab.{w}} {n : ℕ}
    (f : A.obj (op n) ⟶ X) (g : X ⟶ Y) :
    (proYoneda A).map g (stageClass A f) = stageClass A (f ≫ g) :=
  (ConcreteCategory.congr_hom
    ((colimit.ι (A.op ⋙ coyoneda) (op (op n))).naturality g) f).symm

private lemma stageClass_transition (A : Rlim.InvSystemAb.{w}) {X : Ab.{w}} {n m : ℕ}
    (h : n ≤ m) (f : A.obj (op n) ⟶ X) :
    stageClass A (InverseSequence.tr A h ≫ f) = stageClass A f := by
  have he := congrArg (fun t => t.app X)
    (colimit.w (A.op ⋙ coyoneda) (homOfLE h).op.op)
  exact ConcreteCategory.congr_hom he f

private lemma stageClass_surjective (A : Rlim.InvSystemAb.{w}) (X : Ab.{w})
    (x : (proYoneda A).obj X) : ∃ (n : ℕ) (f : A.obj (op n) ⟶ X), x = stageClass A f := by
  obtain ⟨⟨⟨n⟩⟩, f, h⟩ := FunctorToTypes.jointly_surjective' (A.op ⋙ coyoneda) X x
  exact ⟨n, f, h⟩

private lemma stageClass_eq (A : Rlim.InvSystemAb.{w}) {X : Ab.{w}} {n m : ℕ}
    (f : A.obj (op n) ⟶ X) (g : A.obj (op m) ⟶ X)
    (h : stageClass A f = stageClass A g) :
    ∃ (k : ℕ) (hn : n ≤ k) (hm : m ≤ k),
      InverseSequence.tr A hn ≫ f = InverseSequence.tr A hm ≫ g := by
  let E := colimitObjIsoColimitCompEvaluation (A.op ⋙ coyoneda) X
  have he : (((colimit.ι (A.op ⋙ coyoneda) (op (op n))).app X) ≫ E.hom) f =
      (((colimit.ι (A.op ⋙ coyoneda) (op (op m))).app X) ≫ E.hom) g :=
    congrArg E.hom h
  simp only [E, colimitObjIsoColimitCompEvaluation_ι_app_hom] at he
  obtain ⟨⟨⟨k⟩⟩, a, b, hab⟩ := Types.FilteredColimit.colimit_eq_iff _ |>.mp he
  exact ⟨k, leOfHom a.unop.unop, leOfHom b.unop.unop, hab⟩

private lemma transformation_stage {A B : Rlim.InvSystemAb.{w}}
    (φ : proYoneda B ⟶ proYoneda A) {X : Ab.{w}} {n m : ℕ}
    (f : A.obj (op m) ⟶ B.obj (op n))
    (h : φ.app _ (stageClass B (𝟙 (B.obj (op n)))) = stageClass A f)
    (g : B.obj (op n) ⟶ X) :
    φ.app X (stageClass B g) = stageClass A (f ≫ g) := by
  have hn := ConcreteCategory.congr_hom (φ.naturality g) (stageClass B (𝟙 _))
  dsimp at hn
  rwa [stageClass_postcomp, Category.id_comp, h, stageClass_postcomp] at hn

private lemma successor_naturality {A B : Rlim.InvSystemAb.{w}} (m : ℕ → ℕ)
    (hm : Monotone m) (f : ∀ n, A.obj (op (m n)) ⟶ B.obj (op n))
    (hf : ∀ n, InverseSequence.tr A (hm (Nat.le_succ n)) ≫ f n =
      f (n + 1) ≫ InverseSequence.tr B (Nat.le_succ n)) {i j : ℕ} (h : i ≤ j) :
    InverseSequence.tr A (hm h) ≫ f i = f j ≫ InverseSequence.tr B h := by
  induction j, h using Nat.le_induction with
  | base => simp [tr_refl]
  | succ j h ih =>
    rw [← tr_trans A (hm h) (hm (Nat.le_succ j)), Category.assoc, ih,
      ← Category.assoc, hf j, Category.assoc, tr_trans]

private lemma exists_representative {A B : Rlim.InvSystemAb.{w}}
    (φ : proYoneda B ⟶ proYoneda A) : ∃ r : SequentialRep A B, r.Represents φ := by
  classical
  have he (n : ℕ) := stageClass_surjective A (B.obj (op n))
    (φ.app _ (stageClass B (𝟙 _)))
  choose p f hf using he
  have hc (n : ℕ) : stageClass A (f n) =
      stageClass A (f (n + 1) ≫ InverseSequence.tr B (Nat.le_succ n)) := by
    rw [← hf n, ← transformation_stage φ (f (n + 1)) (hf (n + 1))]
    congr 1
    simpa only [Category.comp_id] using
      (stageClass_transition B (Nat.le_succ n) (𝟙 _)).symm
  choose k hk hk' heq using fun n => stageClass_eq A _ _ (hc n)
  obtain ⟨m, hm, hb⟩ := StacksDraft.InverseSystem.exists_strict_majorant (fun n => max (p n) (k n))
  have hp (n : ℕ) : p n ≤ m n := (le_max_left _ _).trans (hb n)
  have hkn (n : ℕ) : k n ≤ m n := (le_max_right _ _).trans (hb n)
  let g (n : ℕ) := InverseSequence.tr A (hp n) ≫ f n
  have hg (n : ℕ) : InverseSequence.tr A (hm.monotone (Nat.le_succ n)) ≫ g n =
      g (n + 1) ≫ InverseSequence.tr B (Nat.le_succ n) := by
    have hn : k n ≤ m (n + 1) := (hkn n).trans (hm.monotone (Nat.le_succ n))
    have hh := congrArg (fun z => InverseSequence.tr A hn ≫ z) (heq n)
    simpa only [g, ← Category.assoc, tr_trans] using hh
  refine ⟨⟨m, hm, fun n => hm.id_le n, g, fun h => successor_naturality m hm.monotone g hg h⟩, ?_⟩
  intro n
  exact (hf n).trans (stageClass_transition A (hp n) (f n)).symm

private lemma exists_common_refinement {A B : Rlim.InvSystemAb.{w}}
    (r s : SequentialRep A B) (φ : proYoneda B ⟶ proYoneda A)
    (hr : r.Represents φ) (hs : s.Represents φ) :
    ∃ t : SequentialRep A B, r.Refines t ∧ s.Refines t := by
  classical
  choose k hk hk' he using fun n => stageClass_eq A (r.component n) (s.component n)
    ((hr n).symm.trans (hs n))
  obtain ⟨m, hm, hkm⟩ := StacksDraft.InverseSystem.exists_strict_majorant k
  have h₁ (n : ℕ) : r.index n ≤ m n := (hk n).trans (hkm n)
  have h₂ (n : ℕ) : s.index n ≤ m n := (hk' n).trans (hkm n)
  let t : SequentialRep A B := {
    index := m
    index_strict := hm
    index_le := fun n => hm.id_le n
    component := fun n => InverseSequence.tr A (h₁ n) ≫ r.component n
    naturality := by
      intro i j h
      change InverseSequence.tr A (hm.monotone h) ≫ (InverseSequence.tr A (h₁ i) ≫ r.component i) =
        (InverseSequence.tr A (h₁ j) ≫ r.component j) ≫ InverseSequence.tr B h
      rw [← Category.assoc, tr_trans, Category.assoc,
        ← representative_naturality r h, ← Category.assoc, tr_trans] }
  refine ⟨t, fun n => ⟨h₁ n, rfl⟩, fun n => ⟨h₂ n, ?_⟩⟩
  have hh := congrArg (fun z => InverseSequence.tr A (hkm n) ≫ z) (he n)
  change InverseSequence.tr A (h₁ n) ≫ r.component n = InverseSequence.tr A (h₂ n) ≫ s.component n
  simpa only [← Category.assoc, tr_trans] using hh

private def chosenRepresentative {A B : Rlim.InvSystemAb.{w}}
    (φ : proYoneda B ⟶ proYoneda A) : SequentialRep A B :=
  Classical.choose (exists_representative φ)

private lemma chosenRepresentative_represents {A B : Rlim.InvSystemAb.{w}}
    (φ : proYoneda B ⟶ proYoneda A) : (chosenRepresentative φ).Represents φ :=
  Classical.choose_spec (exists_representative φ)

private abbrev limAction (A B : Rlim.InvSystemAb.{w}) (φ : proYoneda B ⟶ proYoneda A) :=
  (chosenRepresentative φ).mapLim

private abbrev cokernelAction (A B : Rlim.InvSystemAb.{w}) (φ : proYoneda B ⟶ proYoneda A) :=
  (chosenRepresentative φ).mapR1lim (representative_chain_map _)

private lemma action_eq_representative {A B : Rlim.InvSystemAb.{w}}
    (φ : proYoneda B ⟶ proYoneda A) (r : SequentialRep A B) (hr : r.Represents φ) :
    limAction A B φ = r.mapLim ∧
      cokernelAction A B φ = r.mapR1lim (representative_chain_map r) := by
  obtain ⟨t, ht, ht'⟩ := exists_common_refinement (chosenRepresentative φ) r φ
    (chosenRepresentative_represents φ) hr
  constructor
  · exact (representative_refines_lim _ t ht).trans (representative_refines_lim r t ht').symm
  · apply (cancel_epi (cokernel.π _)).1
    simp only [cokernelAction, SequentialRep.mapR1lim, cokernel.π_desc]
    exact (representative_refines_cokernel _ t ht).trans
      (representative_refines_cokernel r t ht').symm

private lemma representative_id_represents (A : Rlim.InvSystemAb.{w}) :
    (SequentialRep.id A).Represents (𝟙 _) := by
  intro n
  rfl

private lemma representative_comp_represents {A B C : Rlim.InvSystemAb.{w}}
    (r : SequentialRep A B) (s : SequentialRep B C)
    (φ : proYoneda B ⟶ proYoneda A) (ψ : proYoneda C ⟶ proYoneda B)
    (hr : r.Represents φ) (hs : s.Represents ψ) : (r.comp s).Represents (ψ ≫ φ) := by
  intro n
  change φ.app _ (ψ.app _ (stageClass C (𝟙 _))) = _
  have hs' : ψ.app _ (stageClass C (𝟙 _)) = stageClass B (s.component n) := hs n
  rw [hs']
  exact transformation_stage φ (r.component (s.index n)) (hr (s.index n)) (s.component n)

private lemma limAction_id (A : Rlim.InvSystemAb.{w}) : limAction A A (𝟙 _) = 𝟙 _ := by
  rw [(action_eq_representative _ _ (representative_id_represents A)).1]
  apply limit.hom_ext
  rintro ⟨n⟩
  simp [mapLim_projection, SequentialRep.id]

private lemma cokernelAction_id (A : Rlim.InvSystemAb.{w}) : cokernelAction A A (𝟙 _) = 𝟙 _ := by
  rw [(action_eq_representative _ _ (representative_id_represents A)).2]
  apply (cancel_epi (cokernel.π _)).1
  simp [SequentialRep.mapR1lim, (representative_id_products A).2]

private lemma limAction_comp (A B C : Rlim.InvSystemAb.{w})
    (φ : proYoneda B ⟶ proYoneda A) (ψ : proYoneda C ⟶ proYoneda B) :
    limAction A C (ψ ≫ φ) = limAction A B φ ≫ limAction B C ψ := by
  let r := chosenRepresentative φ
  let s := chosenRepresentative ψ
  rw [(action_eq_representative _ (r.comp s) (representative_comp_represents r s φ ψ
    (chosenRepresentative_represents φ) (chosenRepresentative_represents ψ))).1]
  apply limit.hom_ext
  rintro ⟨n⟩
  change _ = (r.mapLim ≫ s.mapLim) ≫ _
  simp only [Category.assoc, mapLim_projection, SequentialRep.comp, Function.comp_apply]
  simp only [← Category.assoc, mapLim_projection]

private lemma cokernelAction_comp (A B C : Rlim.InvSystemAb.{w})
    (φ : proYoneda B ⟶ proYoneda A) (ψ : proYoneda C ⟶ proYoneda B) :
    cokernelAction A C (ψ ≫ φ) = cokernelAction A B φ ≫ cokernelAction B C ψ := by
  let r := chosenRepresentative φ
  let s := chosenRepresentative ψ
  rw [(action_eq_representative _ (r.comp s) (representative_comp_represents r s φ ψ
    (chosenRepresentative_represents φ) (chosenRepresentative_represents ψ))).2]
  apply (cancel_epi (cokernel.π _)).1
  simp only [cokernelAction, SequentialRep.mapR1lim, cokernel.π_desc_assoc,
    cokernel.π_desc, (representative_comp_products r s).2, Category.assoc]
  rfl

private lemma actions_isIso (A B : Rlim.InvSystemAb.{w})
    (φ : proYoneda B ⟶ proYoneda A) [IsIso φ] :
    IsIso (limAction A B φ) ∧ IsIso (cokernelAction A B φ) := by
  constructor
  · exact ⟨⟨limAction B A (inv φ), by rw [← limAction_comp, IsIso.inv_hom_id, limAction_id],
      by rw [← limAction_comp, IsIso.hom_inv_id, limAction_id]⟩⟩
  · exact ⟨⟨cokernelAction B A (inv φ),
      by rw [← cokernelAction_comp, IsIso.inv_hom_id, cokernelAction_id],
      by rw [← cokernelAction_comp, IsIso.hom_inv_id, cokernelAction_id]⟩⟩

private lemma representative_limit_square {A B : Rlim.InvSystemAb.{w}} (r : SequentialRep A B) :
    Rlim.limitToProduct A ≫ r.productFirst = r.mapLim ≫ Rlim.limitToProduct B := by
  apply product_hom_ext
  intro n
  simp only [Category.assoc, first_projection, Rlim.limitToProduct, projection, Pi.lift_comp_π]
  rw [← Category.assoc, Pi.lift_comp_π, mapLim_projection]

private def stagesTransformation {A B : Rlim.InvSystemAb.{w}} (m : ℕ → ℕ)
    (hm : Monotone m) (f : ∀ n, A.obj (op (m n)) ⟶ B.obj (op n))
    (hf : ∀ {i j : ℕ} (h : i ≤ j),
      InverseSequence.tr A (hm h) ≫ f i = f j ≫ InverseSequence.tr B h) :
    proYoneda B ⟶ proYoneda A :=
  colimit.desc (B.op ⋙ coyoneda) {
    pt := proYoneda A
    ι := {
      app := fun n => coyoneda.map (f n.unop.unop).op ≫
        colimit.ι (A.op ⋙ coyoneda) (op (op (m n.unop.unop)))
      naturality := by
        rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ v
        have h : i ≤ j := leOfHom v.unop.unop
        have hv : v = (homOfLE h).op.op := Subsingleton.elim _ _
        subst v
        ext X g
        change stageClass A (f j ≫ (InverseSequence.tr B h ≫ g)) = stageClass A (f i ≫ g)
        rw [← Category.assoc, ← hf h, Category.assoc, stageClass_transition]
    }
  }

private lemma stagesTransformation_apply {A B : Rlim.InvSystemAb.{w}} (m : ℕ → ℕ)
    (hm : Monotone m) (f : ∀ n, A.obj (op (m n)) ⟶ B.obj (op n))
    (hf : ∀ {i j : ℕ} (h : i ≤ j), InverseSequence.tr A (hm h) ≫ f i = f j ≫ InverseSequence.tr B h)
    {X : Ab.{w}} {n : ℕ} (g : B.obj (op n) ⟶ X) :
    (stagesTransformation m hm f hf).app X (stageClass B g) =
      stageClass A (f n ≫ g) := by
  change (((colimit.ι (B.op ⋙ coyoneda) (op (op n))) ≫
    stagesTransformation m hm f hf).app X) g = _
  simp only [stagesTransformation, colimit.ι_desc]
  rfl

private lemma transformation_ext {A B : Rlim.InvSystemAb.{w}}
    (φ ψ : proYoneda B ⟶ proYoneda A)
    (h : ∀ n, φ.app _ (stageClass B (𝟙 (B.obj (op n)))) =
      ψ.app _ (stageClass B (𝟙 (B.obj (op n))))) : φ = ψ := by
  apply colimit.hom_ext
  rintro ⟨⟨n⟩⟩
  apply coyonedaEquiv.injective
  exact h n

/-- Two stage transformations whose stage maps compose to transition maps compose to the
identity. -/
private lemma stagesTransformation_comp_eq_id {A B : Rlim.InvSystemAb.{w}} (m : ℕ → ℕ)
    (hm : Monotone m) (f : ∀ n, A.obj (op (m n)) ⟶ B.obj (op n))
    (hf : ∀ {i j : ℕ} (h : i ≤ j), InverseSequence.tr A (hm h) ≫ f i = f j ≫ InverseSequence.tr B h)
    (m' : ℕ → ℕ) (hm' : Monotone m') (f' : ∀ n, B.obj (op (m' n)) ⟶ A.obj (op n))
    (hf' : ∀ {i j : ℕ} (h : i ≤ j),
      InverseSequence.tr B (hm' h) ≫ f' i = f' j ≫ InverseSequence.tr A h)
    (hle : ∀ n, n ≤ m' (m n)) (hc : ∀ n, f' (m n) ≫ f n = InverseSequence.tr B (hle n)) :
    stagesTransformation m hm f hf ≫ stagesTransformation m' hm' f' hf' = 𝟙 _ := by
  apply transformation_ext
  intro n
  change (stagesTransformation m' hm' f' hf').app _
    ((stagesTransformation m hm f hf).app _ (stageClass B (𝟙 _))) = stageClass B (𝟙 _)
  simp only [stagesTransformation_apply, Category.comp_id]
  rw [hc]
  simpa only [Category.comp_id] using stageClass_transition B (hle n) (𝟙 _)

private lemma proIso_transformation {A B : Rlim.InvSystemAb.{w}} (a : InverseSequence.ProIso A B) :
    ∃ φ : proYoneda B ⟶ proYoneda A, proIsoRepresents a φ ∧ IsIso φ := by
  let φ := stagesTransformation a.α a.αmono a.φ a.φnat
  let ψ := stagesTransformation a.β a.βmono a.ψ a.ψnat
  have hφψ := stagesTransformation_comp_eq_id a.α a.αmono a.φ a.φnat a.β a.βmono a.ψ a.ψnat
    (fun n => (a.αle n).trans (a.βle (a.α n))) a.φψ
  have hψφ := stagesTransformation_comp_eq_id a.β a.βmono a.ψ a.ψnat a.α a.αmono a.φ a.φnat
    (fun n => (a.βle n).trans (a.αle (a.β n))) a.ψφ
  refine ⟨φ, ?_, ⟨⟨ψ, hφψ, hψφ⟩⟩⟩
  intro n
  change φ.app _ (stageClass B (𝟙 (B.obj (op n)))) = stageClass A (a.φ n)
  simpa only [φ, Category.comp_id] using
    stagesTransformation_apply a.α a.αmono a.φ a.φnat (𝟙 (B.obj (op n)))

/-- **Stacks 0H9K.** Morphisms of pro-systems of abelian groups induce maps on inverse limits
and first derived inverse limits. The maps are functorial in the pro-morphism, and both are
isomorphisms when the pro-morphism is an isomorphism. -/
@[stacks 0H9K]
public theorem exists_map_lim_and_cokernel_delta :
    let Rlim.InvSystemAb := ℕᵒᵖ ⥤ Ab.{w}
    let proYoneda (A : Rlim.InvSystemAb) : Ab.{w} ⥤ Type w := colimit (A.op ⋙ coyoneda)
    let P (A : Rlim.InvSystemAb) : Ab.{w} := ∏ᶜ fun n : ℕ ↦ A.obj (op n)
    let shift (A : Rlim.InvSystemAb) : P A ⟶ P A := Pi.lift fun n ↦
      Pi.π (fun n : ℕ ↦ A.obj (op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op
    let δ (A : Rlim.InvSystemAb) : P A ⟶ P A := 𝟙 (P A) - shift A
    ∃ (mapLim : ∀ A B : Rlim.InvSystemAb,
          (proYoneda B ⟶ proYoneda A) → (limit A ⟶ limit B))
      (mapR1lim : ∀ A B : Rlim.InvSystemAb,
          (proYoneda B ⟶ proYoneda A) →
            (cokernel (δ A) ⟶ cokernel (δ B))),
      (∀ A : Rlim.InvSystemAb, mapLim A A (𝟙 _) = 𝟙 _) ∧
      (∀ A : Rlim.InvSystemAb, mapR1lim A A (𝟙 _) = 𝟙 _) ∧
      (∀ (A B C : Rlim.InvSystemAb) (φ : proYoneda B ⟶ proYoneda A)
          (ψ : proYoneda C ⟶ proYoneda B),
        mapLim A C (ψ ≫ φ) = mapLim A B φ ≫ mapLim B C ψ) ∧
      (∀ (A B C : Rlim.InvSystemAb) (φ : proYoneda B ⟶ proYoneda A)
          (ψ : proYoneda C ⟶ proYoneda B),
        mapR1lim A C (ψ ≫ φ) = mapR1lim A B φ ≫ mapR1lim B C ψ) ∧
      (∀ (A B : Rlim.InvSystemAb) (φ : proYoneda B ⟶ proYoneda A),
        IsIso φ → IsIso (mapLim A B φ) ∧ IsIso (mapR1lim A B φ)) ∧
      (∀ (A B : Rlim.InvSystemAb) (r : SequentialRep A B),
        Rlim.delta A ≫ r.productSecond = r.productFirst ≫ Rlim.delta B) ∧
      (∀ (A : Rlim.InvSystemAb),
        (SequentialRep.id A).productFirst = 𝟙 _ ∧
        (SequentialRep.id A).productSecond = 𝟙 _) ∧
      (∀ (A B C : Rlim.InvSystemAb) (r : SequentialRep A B) (s : SequentialRep B C),
        (r.comp s).productFirst = r.productFirst ≫ s.productFirst ∧
        (r.comp s).productSecond = r.productSecond ≫ s.productSecond) ∧
      (∀ (A B : Rlim.InvSystemAb) (r s : SequentialRep A B),
        r.Refines s → r.mapLim = s.mapLim ∧
          r.productSecond ≫ cokernel.π (Rlim.delta B) =
            s.productSecond ≫ cokernel.π (Rlim.delta B)) ∧
      (∀ (A B : Rlim.InvSystemAb) (φ : proYoneda B ⟶ proYoneda A),
        ∃ r : SequentialRep A B, r.Represents φ) ∧
      (∀ (A B : Rlim.InvSystemAb) (φ : proYoneda B ⟶ proYoneda A)
        (r : SequentialRep A B), r.Represents φ →
        ∃ hδ : Rlim.delta A ≫ r.productSecond =
            r.productFirst ≫ Rlim.delta B,
          mapLim A B φ = r.mapLim ∧
          mapR1lim A B φ = r.mapR1lim hδ ∧
          Rlim.limitToProduct A ≫ r.productFirst =
            mapLim A B φ ≫ Rlim.limitToProduct B ∧
          cokernel.π (Rlim.delta A) ≫ mapR1lim A B φ =
            r.productSecond ≫ cokernel.π (Rlim.delta B)) ∧
      (∀ (A B : Rlim.InvSystemAb) (a : InverseSequence.ProIso A B),
        ∃ (φ : proYoneda B ⟶ proYoneda A),
          proIsoRepresents a φ ∧ IsIso φ ∧
          IsIso (mapLim A B φ) ∧ IsIso (mapR1lim A B φ)) ∧
      (∀ {D : Type u} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ]
          [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
          [Pretriangulated D]
          (F G : ℕᵒᵖ ⥤ D)
          [HasProduct fun n : ℕ => F.obj (op n)]
          [HasProduct fun n : ℕ => G.obj (op n)] (L : D)
          (f₁ f₂ : Rlim.Hom.systemProduct F ⟶ Rlim.Hom.systemProduct G)
          (φ₀ : proYoneda (Rlim.Hom.homSystem L G) ⟶
            proYoneda (Rlim.Hom.homSystem L F))
          (φ₁ : proYoneda (Rlim.Hom.shiftedHomSystem L G) ⟶
            proYoneda (Rlim.Hom.shiftedHomSystem L F))
          (r₀ : SequentialRep (Rlim.Hom.homSystem L F)
            (Rlim.Hom.homSystem L G))
          (r₁ : SequentialRep (Rlim.Hom.shiftedHomSystem L F)
            (Rlim.Hom.shiftedHomSystem L G)),
          r₀.Represents φ₀ → r₁.Represents φ₁ →
          r₀.productFirst = Rlim.Hom.homProductMap L F G f₁ →
          r₁.productFirst = Rlim.Hom.shiftedHomProductMap L F G f₁ →
          r₁.productSecond = Rlim.Hom.shiftedHomProductMap L F G f₂ →
          ∃ hδ : Rlim.delta (Rlim.Hom.shiftedHomSystem L F) ≫
              Rlim.Hom.shiftedHomProductMap L F G f₂ =
            Rlim.Hom.shiftedHomProductMap L F G f₁ ≫
              Rlim.delta (Rlim.Hom.shiftedHomSystem L G),
            Rlim.limitToProduct (Rlim.Hom.homSystem L F) ≫
                Rlim.Hom.homProductMap L F G f₁ =
              mapLim _ _ φ₀ ≫
                Rlim.limitToProduct (Rlim.Hom.homSystem L G) ∧
            mapR1lim _ _ φ₁ =
              cokernel.map (Rlim.delta (Rlim.Hom.shiftedHomSystem L F))
                (Rlim.delta (Rlim.Hom.shiftedHomSystem L G))
                (Rlim.Hom.shiftedHomProductMap L F G f₁)
                (Rlim.Hom.shiftedHomProductMap L F G f₂) hδ) := by
  refine ⟨limAction, cokernelAction, limAction_id, cokernelAction_id,
    limAction_comp, cokernelAction_comp, ?_, ?_, representative_id_products,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B φ hφ
    let := hφ
    exact actions_isIso A B φ
  · exact fun _ _ r => representative_chain_map r
  · exact fun _ _ _ r s => representative_comp_products r s
  · exact fun _ _ r s h =>
      ⟨representative_refines_lim r s h, representative_refines_cokernel r s h⟩
  · exact fun _ _ φ => exists_representative φ
  · intro A B φ r hr
    obtain ⟨hl, hc⟩ := action_eq_representative φ r hr
    refine ⟨representative_chain_map r, hl, hc, ?_, ?_⟩
    · rw [hl]
      exact representative_limit_square r
    · rw [hc]
      exact cokernel.π_desc _ _ _
  · intro A B a
    obtain ⟨φ, hφ, hi⟩ := proIso_transformation a
    let := hi
    exact ⟨φ, hφ, hi, actions_isIso A B φ⟩
  · intro D _ _ _ _ _ _ F G _ _ L f₁ f₂ φ₀ φ₁ r₀ r₁ hr₀ hr₁ h₀ h₁ h₂
    have hδ := representative_chain_map r₁
    rw [h₁, h₂] at hδ
    refine ⟨hδ, ?_, ?_⟩
    · have hs := representative_limit_square r₀
      rwa [← (action_eq_representative φ₀ r₀ hr₀).1, h₀] at hs
    · have hs := (action_eq_representative φ₁ r₁ hr₁).2
      unfold SequentialRep.mapR1lim at hs
      simp only [h₁, h₂] at hs
      exact hs

end Rlim.Pro

end

end
