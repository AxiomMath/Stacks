module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Transporting the three clauses of a colimit of categories of modules

Stacks 07V7 and Stacks 01ZR both assert that a category of modules of finite presentation over
a limit `X = lim X_i` is the colimit of the corresponding categories over the stages `X_i`.  The
assertion has three clauses — faithfulness, fullness and essential surjectivity of the comparison
— and each is a statement about the inverse-image functors along the transition morphisms and
along the projections of the limit, together with the comparisons of iterated inverse images.

This file isolates that shape as `Stacks.ModuleColimit.PullbackSystem` and proves that the three
clauses pass from one such system to another along a family of comparison functors which are
fully faithful on the relevant objects, essentially surjective onto the objects of finite
presentation, and *pseudonatural*: they commute with the inverse images up to isomorphisms which
paste correctly against the comparisons of iterated inverse images.  It is the formal step by
which the scheme-level Stacks 01ZR is read on the small étale sites of affine schemes, and then on
the algebraic spaces these represent, in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineSystemModuleColimit.lean`.

## Main definitions

* `Stacks.ModuleColimit.PullbackSystem`: categories `C j` over the objects of an index category,
  a category `L` over the limit, inverse images along the morphisms of the index category and
  along the projections, and the comparison of the inverse image along a projection with the
  inverse image along a transition morphism followed by the projection.
* `Stacks.ModuleColimit.PullbackSystem.Faithfulness`, `.Fullness` and `.EssSurj`: the three
  clauses of the colimit assertion.
* `Stacks.ModuleColimit.PullbackSystem.Transfer` and `.TransferUp`: comparison functors from one
  system to another, in the two directions.

## Main results

* `Stacks.ModuleColimit.PullbackSystem.Transfer.faithfulness`, `.fullness`, `.essSurj` and their
  `TransferUp` counterparts: the clauses pass along a comparison.

## Implementation notes

Full faithfulness of the comparison is asked only on the objects of a property `Q` (in the
application: quasi-coherence), stable under the inverse images, and essential surjectivity only
onto the objects of a property `P ⊆ Q` (in the application: finite presentation).  The clauses
themselves only quantify over objects of `P`.
-/

@[expose] public section

open CategoryTheory

universe w w' v₁ u₁ v₂ u₂

namespace Stacks.ModuleColimit

/-- **A system of categories over the stages of an index category and over its limit**, with
inverse images along the transition morphisms and along the projections, the comparison of the
inverse image along a projection with an iterated inverse image, and a property of objects (in the
application: finite presentation) at each stage and at the limit. -/
structure PullbackSystem (J : Type w) [Category.{w'} J] where
  /-- The category at a stage. -/
  C : J → Type u₁
  /-- Its category structure. -/
  [cat : ∀ j, Category.{v₁} (C j)]
  /-- The category over the limit. -/
  L : Type u₁
  /-- Its category structure. -/
  [catL : Category.{v₁} L]
  /-- The inverse image along a transition morphism. -/
  pb : ∀ {j k : J}, (j ⟶ k) → (C k ⥤ C j)
  /-- The inverse image along a projection of the limit. -/
  pbL : ∀ j, C j ⥤ L
  /-- The comparison of the inverse image along a projection with the inverse image along a
  transition morphism followed by the projection. -/
  comp : ∀ {j k : J} (e : j ⟶ k), pbL k ≅ pb e ⋙ pbL j
  /-- The property of objects at a stage. -/
  P : ∀ j, ObjectProperty (C j)
  /-- The property of objects over the limit. -/
  PL : ObjectProperty L

attribute [instance] PullbackSystem.cat PullbackSystem.catL

namespace PullbackSystem

/-- Cancelling the image of an inverse followed by the image of the morphism of a natural
isomorphism component. -/
theorem map_inv_hom_app_assoc {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (α : F ≅ G) (H : D ⥤ E) (X : C) {Z : E} (f : H.obj (G.obj X) ⟶ Z) :
    H.map (α.inv.app X) ≫ H.map (α.hom.app X) ≫ f = f := by
  rw [← H.map_comp_assoc, Iso.inv_hom_id_app, H.map_id, Category.id_comp]

/-- Cancelling the image of an inverse followed by the image of the morphism of a natural
isomorphism component, at the end of a composite. -/
theorem map_inv_hom_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (α : F ≅ G) (H : D ⥤ E) (X : C) :
    H.map (α.inv.app X) ≫ H.map (α.hom.app X) = 𝟙 _ := by
  rw [← H.map_comp, Iso.inv_hom_id_app, H.map_id]

/-- Cancelling the image under a composite of an inverse followed by the morphism of an
isomorphism, at the end of a composite. -/
theorem map_map_inv_hom {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : C ⥤ D) (H : D ⥤ E) {X Y : C} (i : X ≅ Y) :
    H.map (G.map i.inv) ≫ H.map (G.map i.hom) = 𝟙 _ := by
  rw [← H.map_comp, ← G.map_comp, Iso.inv_hom_id, G.map_id, H.map_id]

variable {J : Type w} [Category.{w'} J]

/-- Equality of two images under a composite of functors transfers along a natural isomorphism
of composites. -/
private theorem map_map_eq_of_iso {C D D' E : Type*} [Category* C] [Category* D] [Category* D']
    [Category* E] {F₁ : C ⥤ D} {F₂ : D ⥤ E} {G₁ : C ⥤ D'} {G₂ : D' ⥤ E} (α : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    {M N : C} {φ ψ : M ⟶ N} (h : F₂.map (F₁.map φ) = F₂.map (F₁.map ψ)) :
    G₂.map (G₁.map φ) = G₂.map (G₁.map ψ) := by
  have hφ := α.hom.naturality φ
  have hψ := α.hom.naturality ψ
  simp only [Functor.comp_map] at hφ hψ
  rw [← cancel_epi (α.hom.app M), ← hφ, ← hψ, h]

/-- **The faithfulness clause**: two morphisms between objects of `P` at a stage whose inverse
images to the limit agree have equal inverse images along a transition morphism from some later
stage. -/
def Faithfulness (A : PullbackSystem.{w, w', v₁, u₁} J) : Prop :=
  ∀ (k : J) (M N : A.C k), A.P k M → A.P k N → ∀ φ ψ : M ⟶ N,
    (A.pbL k).map φ = (A.pbL k).map ψ →
      ∃ (j : J) (e : j ⟶ k), (A.pb e).map φ = (A.pb e).map ψ

/-- **The fullness clause**: a morphism between the inverse images to the limit of two objects of
`P` at a stage comes, through the comparisons, from a morphism between their inverse images at
some later stage. -/
def Fullness (A : PullbackSystem.{w, w', v₁, u₁} J) : Prop :=
  ∀ (k : J) (M N : A.C k), A.P k M → A.P k N → ∀ φ : (A.pbL k).obj M ⟶ (A.pbL k).obj N,
    ∃ (j : J) (e : j ⟶ k) (φ' : (A.pb e).obj M ⟶ (A.pb e).obj N),
      (A.pbL j).map φ' = (A.comp e).inv.app M ≫ φ ≫ (A.comp e).hom.app N

/-- **The essential surjectivity clause**: an object of `PL` over the limit is the inverse image
of an object of `P` at some stage. -/
def EssSurj (A : PullbackSystem.{w, w', v₁, u₁} J) : Prop :=
  ∀ M : A.L, A.PL M → ∃ (k : J) (Mk : A.C k), A.P k Mk ∧ Nonempty ((A.pbL k).obj Mk ≅ M)

/-- **A comparison from a system `Bs` down to a system `A`**: functors at the stages and at the
limit, commuting with the inverse images up to isomorphisms which paste against the comparisons
of iterated inverse images, fully faithful on the objects of a property `Q` stable under the
inverse images, preserving `P`, and essentially surjective onto the objects of `P`. -/
structure Transfer (A : PullbackSystem.{w, w', v₁, u₁} J)
    (Bs : PullbackSystem.{w, w', v₂, u₂} J) where
  /-- The comparison at a stage. -/
  F : ∀ j, Bs.C j ⥤ A.C j
  /-- The comparison over the limit. -/
  FL : Bs.L ⥤ A.L
  /-- The comparison commutes with the inverse images along transition morphisms. -/
  β : ∀ {j k : J} (e : j ⟶ k), Bs.pb e ⋙ F j ≅ F k ⋙ A.pb e
  /-- The comparison commutes with the inverse images along projections. -/
  βL : ∀ j, Bs.pbL j ⋙ FL ≅ F j ⋙ A.pbL j
  /-- The pasting coherence. -/
  coherence : ∀ {j k : J} (e : j ⟶ k) (M : Bs.C k),
    FL.map ((Bs.comp e).hom.app M) =
      (βL k).hom.app M ≫ (A.comp e).hom.app ((F k).obj M) ≫
        (A.pbL j).map ((β e).inv.app M) ≫ (βL j).inv.app ((Bs.pb e).obj M)
  /-- The property on which the comparison is fully faithful, at a stage. -/
  Q : ∀ j, ObjectProperty (Bs.C j)
  /-- The same over the limit. -/
  QL : ObjectProperty Bs.L
  /-- `P` implies `Q`. -/
  Q_of_P : ∀ j (M : Bs.C j), Bs.P j M → Q j M
  /-- `Q` is stable under the inverse images along transition morphisms. -/
  Q_pb : ∀ {j k : J} (e : j ⟶ k) (M : Bs.C k), Q k M → Q j ((Bs.pb e).obj M)
  /-- `Q` is carried to `QL` by the inverse images along projections. -/
  QL_pbL : ∀ j (M : Bs.C j), Q j M → QL ((Bs.pbL j).obj M)
  /-- The comparison at a stage is faithful on `Q`. -/
  faithful : ∀ j {M N : Bs.C j}, Q j M → Q j N → ∀ f g : M ⟶ N,
    (F j).map f = (F j).map g → f = g
  /-- The comparison at a stage is full on `Q`. -/
  full : ∀ j {M N : Bs.C j}, Q j M → Q j N → ∀ f : (F j).obj M ⟶ (F j).obj N,
    ∃ g : M ⟶ N, (F j).map g = f
  /-- The comparison over the limit is faithful on `QL`. -/
  faithfulL : ∀ {M N : Bs.L}, QL M → QL N → ∀ f g : M ⟶ N, FL.map f = FL.map g → f = g
  /-- The comparison over the limit is full on `QL`. -/
  fullL : ∀ {M N : Bs.L}, QL M → QL N → ∀ f : FL.obj M ⟶ FL.obj N,
    ∃ g : M ⟶ N, FL.map g = f
  /-- The comparison at a stage preserves `P`. -/
  P_map : ∀ j (M : Bs.C j), Bs.P j M → A.P j ((F j).obj M)
  /-- The comparison over the limit preserves `PL`. -/
  PL_map : ∀ M : Bs.L, Bs.PL M → A.PL (FL.obj M)
  /-- The comparison at a stage is essentially surjective onto `P`. -/
  essSurjP : ∀ j (X : A.C j), A.P j X → ∃ M : Bs.C j, Bs.P j M ∧ Nonempty ((F j).obj M ≅ X)

namespace Transfer

variable {A : PullbackSystem.{w, w', v₁, u₁} J} {Bs : PullbackSystem.{w, w', v₂, u₂} J}
  (T : Transfer A Bs)

include T in
/-- **The faithfulness clause passes down a comparison.** -/
theorem faithfulness (hA : A.Faithfulness) : Bs.Faithfulness := by
  intro k M N hM hN φ ψ h
  obtain ⟨j, e, he⟩ := hA k _ _ (T.P_map k M hM) (T.P_map k N hN) _ _
    (map_map_eq_of_iso (T.βL k) (congrArg T.FL.map h))
  exact ⟨j, e, T.faithful j (T.Q_pb e M (T.Q_of_P k M hM)) (T.Q_pb e N (T.Q_of_P k N hN)) _ _
    (map_map_eq_of_iso (T.β e).symm he)⟩

/-- The coherence of a comparison, inverted. -/
theorem coherence_inv {j k : J} (e : j ⟶ k) (M : Bs.C k) :
    T.FL.map ((Bs.comp e).inv.app M) =
      (T.βL j).hom.app ((Bs.pb e).obj M) ≫ (A.pbL j).map ((T.β e).hom.app M) ≫
        (A.comp e).inv.app ((T.F k).obj M) ≫ (T.βL k).inv.app M := by
  rw [← cancel_epi (T.FL.map ((Bs.comp e).hom.app M)), ← T.FL.map_comp, Iso.hom_inv_id_app,
    T.FL.map_id, T.coherence e M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

include T in
/-- **The fullness clause passes down a comparison.** -/
theorem fullness (hA : A.Fullness) : Bs.Fullness := by
  intro k M N hM hN φ
  have hQM := T.Q_of_P k M hM
  have hQN := T.Q_of_P k N hN
  obtain ⟨j, e, φA, hφA⟩ := hA k _ _ (T.P_map k M hM) (T.P_map k N hN)
    ((T.βL k).inv.app M ≫ T.FL.map φ ≫ (T.βL k).hom.app N)
  obtain ⟨φ', hφ'⟩ := T.full j (T.Q_pb e M hQM) (T.Q_pb e N hQN)
    ((T.β e).hom.app M ≫ φA ≫ (T.β e).inv.app N)
  refine ⟨j, e, φ', T.faithfulL (T.QL_pbL j _ (T.Q_pb e M hQM))
    (T.QL_pbL j _ (T.Q_pb e N hQN)) _ _ ?_⟩
  have hnat := (T.βL j).hom.naturality φ'
  simp only [Functor.comp_map] at hnat
  rw [← cancel_mono ((T.βL j).hom.app ((Bs.pb e).obj N)), hnat, hφ', Functor.map_comp,
    Functor.map_comp, hφA, T.FL.map_comp, T.FL.map_comp, T.coherence_inv, T.coherence]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]

include T in
/-- **The essential surjectivity clause passes down a comparison.** -/
theorem essSurj (hA : A.EssSurj) (hQL : ∀ M : Bs.L, Bs.PL M → T.QL M) : Bs.EssSurj := by
  intro M hM
  obtain ⟨k, X, hX, ⟨eX⟩⟩ := hA _ (T.PL_map M hM)
  obtain ⟨Mk, hMk, ⟨eM⟩⟩ := T.essSurjP k X hX
  refine ⟨k, Mk, hMk, ?_⟩
  let i : T.FL.obj ((Bs.pbL k).obj Mk) ≅ T.FL.obj M :=
    (T.βL k).app Mk ≪≫ (A.pbL k).mapIso eM ≪≫ eX
  have hQ₁ := T.QL_pbL k Mk (T.Q_of_P k Mk hMk)
  have hQ₂ := hQL M hM
  obtain ⟨f, hf⟩ := T.fullL hQ₁ hQ₂ i.hom
  obtain ⟨g, hg⟩ := T.fullL hQ₂ hQ₁ i.inv
  refine ⟨⟨f, g, T.faithfulL hQ₁ hQ₁ _ _ ?_, T.faithfulL hQ₂ hQ₂ _ _ ?_⟩⟩
  · rw [T.FL.map_comp, hf, hg, Iso.hom_inv_id, T.FL.map_id]
  · rw [T.FL.map_comp, hf, hg, Iso.inv_hom_id, T.FL.map_id]

end Transfer

/-- **A comparison from a system `A` up to a system `Bs`**: functors at the stages and at the
limit, commuting with the inverse images up to isomorphisms which paste against the comparisons
of iterated inverse images, fully faithful on the objects of a property `Q` of `A` stable under
the inverse images, and essentially surjective onto the objects of `P` of `Bs` with preimages in
`P`. -/
structure TransferUp (A : PullbackSystem.{w, w', v₁, u₁} J)
    (Bs : PullbackSystem.{w, w', v₂, u₂} J) where
  /-- The comparison at a stage. -/
  F : ∀ j, A.C j ⥤ Bs.C j
  /-- The comparison over the limit. -/
  FL : A.L ⥤ Bs.L
  /-- The comparison commutes with the inverse images along transition morphisms. -/
  β : ∀ {j k : J} (e : j ⟶ k), A.pb e ⋙ F j ≅ F k ⋙ Bs.pb e
  /-- The comparison commutes with the inverse images along projections. -/
  βL : ∀ j, A.pbL j ⋙ FL ≅ F j ⋙ Bs.pbL j
  /-- The pasting coherence. -/
  coherence : ∀ {j k : J} (e : j ⟶ k) (M : A.C k),
    FL.map ((A.comp e).hom.app M) =
      (βL k).hom.app M ≫ (Bs.comp e).hom.app ((F k).obj M) ≫
        (Bs.pbL j).map ((β e).inv.app M) ≫ (βL j).inv.app ((A.pb e).obj M)
  /-- The property on which the comparison is fully faithful, at a stage. -/
  Q : ∀ j, ObjectProperty (A.C j)
  /-- The same over the limit. -/
  QL : ObjectProperty A.L
  /-- `P` implies `Q`. -/
  Q_of_P : ∀ j (M : A.C j), A.P j M → Q j M
  /-- `Q` is stable under the inverse images along transition morphisms. -/
  Q_pb : ∀ {j k : J} (e : j ⟶ k) (M : A.C k), Q k M → Q j ((A.pb e).obj M)
  /-- `Q` is carried to `QL` by the inverse images along projections. -/
  QL_pbL : ∀ j (M : A.C j), Q j M → QL ((A.pbL j).obj M)
  /-- The comparison at a stage is faithful on `Q`. -/
  faithful : ∀ j {M N : A.C j}, Q j M → Q j N → ∀ f g : M ⟶ N,
    (F j).map f = (F j).map g → f = g
  /-- The comparison at a stage is full on `Q`. -/
  full : ∀ j {M N : A.C j}, Q j M → Q j N → ∀ f : (F j).obj M ⟶ (F j).obj N,
    ∃ g : M ⟶ N, (F j).map g = f
  /-- The comparison over the limit is faithful on `QL`. -/
  faithfulL : ∀ {M N : A.L}, QL M → QL N → ∀ f g : M ⟶ N, FL.map f = FL.map g → f = g
  /-- The comparison over the limit is full on `QL`. -/
  fullL : ∀ {M N : A.L}, QL M → QL N → ∀ f : FL.obj M ⟶ FL.obj N,
    ∃ g : M ⟶ N, FL.map g = f
  /-- The comparison at a stage carries `P` to `P`. -/
  P_map : ∀ j (M : A.C j), A.P j M → Bs.P j ((F j).obj M)
  /-- The comparison at a stage is essentially surjective onto `P`, with preimages in `P`. -/
  essSurjP : ∀ j (X : Bs.C j), Bs.P j X → ∃ M : A.C j, A.P j M ∧ Nonempty ((F j).obj M ≅ X)
  /-- The comparison over the limit is essentially surjective onto `PL`, with preimages in
  `PL`. -/
  essSurjL : ∀ X : Bs.L, Bs.PL X → ∃ M : A.L, A.PL M ∧ Nonempty (FL.obj M ≅ X)

namespace TransferUp

variable {A : PullbackSystem.{w, w', v₁, u₁} J} {Bs : PullbackSystem.{w, w', v₂, u₂} J}
  (T : TransferUp A Bs)

/-- The coherence of a comparison, inverted. -/
theorem coherence_inv {j k : J} (e : j ⟶ k) (M : A.C k) :
    T.FL.map ((A.comp e).inv.app M) =
      (T.βL j).hom.app ((A.pb e).obj M) ≫ (Bs.pbL j).map ((T.β e).hom.app M) ≫
        (Bs.comp e).inv.app ((T.F k).obj M) ≫ (T.βL k).inv.app M := by
  rw [← cancel_epi (T.FL.map ((A.comp e).hom.app M)), ← T.FL.map_comp, Iso.hom_inv_id_app,
    T.FL.map_id, T.coherence e M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- Transport of a morphism between images of the comparison along chosen isomorphisms. -/
theorem exists_preimage_conj {j : J} {M₁ M₂ : A.C j} (hM₁ : T.Q j M₁) (hM₂ : T.Q j M₂)
    {X₁ X₂ : Bs.C j} (e₁ : (T.F j).obj M₁ ≅ X₁) (e₂ : (T.F j).obj M₂ ≅ X₂) (φ : X₁ ⟶ X₂) :
    ∃ φ' : M₁ ⟶ M₂, φ = e₁.inv ≫ (T.F j).map φ' ≫ e₂.hom := by
  obtain ⟨φ', h⟩ := T.full j hM₁ hM₂ (e₁.hom ≫ φ ≫ e₂.inv)
  exact ⟨φ', by rw [h]; simp⟩

include T in
/-- **The faithfulness clause passes up a comparison.** -/
theorem faithfulness (hA : A.Faithfulness) : Bs.Faithfulness := by
  intro k X Y hX hY φ ψ h
  obtain ⟨M, hM, ⟨eM⟩⟩ := T.essSurjP k X hX
  obtain ⟨N, hN, ⟨eN⟩⟩ := T.essSurjP k Y hY
  have hQM := T.Q_of_P k M hM
  have hQN := T.Q_of_P k N hN
  obtain ⟨φ', rfl⟩ := T.exists_preimage_conj hQM hQN eM eN φ
  obtain ⟨ψ', rfl⟩ := T.exists_preimage_conj hQM hQN eM eN ψ
  have h₁ : (Bs.pbL k).map ((T.F k).map φ') = (Bs.pbL k).map ((T.F k).map ψ') := by
    simp only [Functor.map_comp] at h
    rw [← cancel_epi ((Bs.pbL k).map eM.inv), ← cancel_mono ((Bs.pbL k).map eN.hom)]
    simpa only [Category.assoc] using h
  have h₂ : (A.pbL k).map φ' = (A.pbL k).map ψ' := by
    exact T.faithfulL (T.QL_pbL k M hQM) (T.QL_pbL k N hQN) _ _
      (map_map_eq_of_iso (T.βL k).symm h₁)
  obtain ⟨j, e, he⟩ := hA k M N hM hN φ' ψ' h₂
  exact ⟨j, e, by simp only [Functor.map_comp, map_map_eq_of_iso (T.β e) (congrArg (T.F j).map he)]⟩

include T in
/-- **The fullness clause passes up a comparison.** -/
theorem fullness (hA : A.Fullness) : Bs.Fullness := by
  intro k X Y hX hY φ
  obtain ⟨M, hM, ⟨eM⟩⟩ := T.essSurjP k X hX
  obtain ⟨N, hN, ⟨eN⟩⟩ := T.essSurjP k Y hY
  have hQM := T.Q_of_P k M hM
  have hQN := T.Q_of_P k N hN
  -- The morphism read on the images of `M` and `N`.
  let φB : (Bs.pbL k).obj ((T.F k).obj M) ⟶ (Bs.pbL k).obj ((T.F k).obj N) :=
    (Bs.pbL k).map eM.hom ≫ φ ≫ (Bs.pbL k).map eN.inv
  obtain ⟨φA, hφA⟩ := T.fullL (T.QL_pbL k M hQM) (T.QL_pbL k N hQN)
    ((T.βL k).hom.app M ≫ φB ≫ (T.βL k).inv.app N)
  obtain ⟨j, e, φ'A, hφ'A⟩ := hA k M N hM hN φA
  refine ⟨j, e, (Bs.pb e).map eM.inv ≫ (T.β e).inv.app M ≫ (T.F j).map φ'A ≫
    (T.β e).hom.app N ≫ (Bs.pb e).map eN.hom, ?_⟩
  -- Both sides, read through the images of `M` and `N`.
  have key : (Bs.pbL j).map ((T.β e).inv.app M ≫ (T.F j).map φ'A ≫ (T.β e).hom.app N) =
      (Bs.comp e).inv.app ((T.F k).obj M) ≫ φB ≫ (Bs.comp e).hom.app ((T.F k).obj N) := by
    have hnat := (T.βL j).hom.naturality φ'A
    simp only [Functor.comp_map] at hnat
    have h₁ : (Bs.pbL j).map ((T.F j).map φ'A) =
        (T.βL j).inv.app ((A.pb e).obj M) ≫ T.FL.map ((A.pbL j).map φ'A) ≫
          (T.βL j).hom.app ((A.pb e).obj N) := by
      rw [hnat, Iso.inv_hom_id_app_assoc]
    rw [Functor.map_comp, Functor.map_comp, h₁, hφ'A, T.FL.map_comp, T.FL.map_comp,
      T.coherence_inv, T.coherence, hφA]
    simp only [φB, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      map_inv_hom_app_assoc]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp, map_inv_hom_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  have hM' := (Bs.comp e).inv.naturality eM.inv
  have hN' := (Bs.comp e).hom.naturality eN.hom
  simp only [Functor.comp_map] at hM' hN'
  have key' := key
  rw [Functor.map_comp, Functor.map_comp] at key'
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% key',
    reassoc_of% hM']
  simp only [φB, Category.assoc]
  rw [← hN']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

include T in
/-- **The essential surjectivity clause passes up a comparison.** -/
theorem essSurj (hA : A.EssSurj) : Bs.EssSurj := by
  intro X hX
  obtain ⟨M, hM, ⟨eX⟩⟩ := T.essSurjL X hX
  obtain ⟨k, Mk, hMk, ⟨e⟩⟩ := hA M hM
  exact ⟨k, (T.F k).obj Mk, T.P_map k Mk hMk,
    ⟨((T.βL k).app Mk).symm ≪≫ T.FL.mapIso e ≪≫ eX⟩⟩

end TransferUp

end PullbackSystem

end Stacks.ModuleColimit

end
