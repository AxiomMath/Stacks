module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitClauseTransfer

/-!
# The descent clauses of a colimit of module categories, into a weaker target

`Stacks.ModuleColimit.PullbackSystem.Faithfulness` and `.Fullness` quantify over pairs of objects
which both satisfy the property `P` of the system — for Stacks 01ZR and 07V7, two modules of
finite presentation.  The proofs of the affine cases ask finiteness only of the *source*: the
target of the morphisms may be any quasi-coherent module, which is what the relative Hom functor
of Stacks 08K4 needs, its target module being only quasi-coherent.

This file states the two clauses with a separate property `R` for the target, and proves that they
pass along the comparisons `Stacks.ModuleColimit.PullbackSystem.Transfer` and
`Stacks.ModuleColimit.PullbackSystem.TransferUp` exactly as the clauses with target in `P` do.

## Main definitions

* `Stacks.ModuleColimit.PullbackSystem.FaithfulnessInto` and
  `Stacks.ModuleColimit.PullbackSystem.FullnessInto`: the faithfulness and fullness clauses for
  morphisms from an object of `P` to an object of `R`.

## Main results

* `Stacks.ModuleColimit.PullbackSystem.Transfer.faithfulnessInto`,
  `Stacks.ModuleColimit.PullbackSystem.Transfer.fullnessInto`: the clauses pass down a comparison.
* `Stacks.ModuleColimit.PullbackSystem.TransferUp.faithfulnessInto`,
  `Stacks.ModuleColimit.PullbackSystem.TransferUp.fullnessInto`: the clauses pass up a comparison.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
-/

@[expose] public section

open CategoryTheory

universe w w' v₁ u₁ v₂ u₂

namespace Stacks.ModuleColimit.PullbackSystem

variable {J : Type w} [Category.{w'} J]

/-- **The faithfulness clause into a target property `R`**: two morphisms from an object of `P` to
an object of `R` at a stage whose inverse images to the limit agree have equal inverse images
along a transition morphism from some later stage. -/
def FaithfulnessInto (A : PullbackSystem.{w, w', v₁, u₁} J) (R : ∀ j, ObjectProperty (A.C j)) :
    Prop :=
  ∀ (k : J) (M N : A.C k), A.P k M → R k N → ∀ φ ψ : M ⟶ N,
    (A.pbL k).map φ = (A.pbL k).map ψ →
      ∃ (j : J) (e : j ⟶ k), (A.pb e).map φ = (A.pb e).map ψ

/-- **The fullness clause into a target property `R`**: a morphism between the inverse images to
the limit of an object of `P` and an object of `R` at a stage comes, through the comparisons, from
a morphism between their inverse images at some later stage. -/
def FullnessInto (A : PullbackSystem.{w, w', v₁, u₁} J) (R : ∀ j, ObjectProperty (A.C j)) :
    Prop :=
  ∀ (k : J) (M N : A.C k), A.P k M → R k N → ∀ φ : (A.pbL k).obj M ⟶ (A.pbL k).obj N,
    ∃ (j : J) (e : j ⟶ k) (φ' : (A.pb e).obj M ⟶ (A.pb e).obj N),
      (A.pbL j).map φ' = (A.comp e).inv.app M ≫ φ ≫ (A.comp e).hom.app N

/-- Two morphisms have equal images under a functor iff they do under an isomorphic functor. -/
private theorem map_eq_map_iff_of_iso {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (α : F ≅ G) {X Y : C} (φ ψ : X ⟶ Y) :
    F.map φ = F.map ψ ↔ G.map φ = G.map ψ := by
  constructor <;> intro h
  · rw [← cancel_epi (α.hom.app X), ← α.hom.naturality φ, ← α.hom.naturality ψ, h]
  · rw [← cancel_mono (α.hom.app Y), α.hom.naturality φ, α.hom.naturality ψ, h]

namespace Transfer

variable {A : PullbackSystem.{w, w', v₁, u₁} J} {Bs : PullbackSystem.{w, w', v₂, u₂} J}
  (T : Transfer A Bs) {RA : ∀ j, ObjectProperty (A.C j)} {RB : ∀ j, ObjectProperty (Bs.C j)}

include T in
/-- **The faithfulness clause into a target property passes down a comparison**, provided the
comparison carries the target property of `Bs` to that of `A` and the former lies in `Q`. -/
theorem faithfulnessInto (hR : ∀ j N, RB j N → RA j ((T.F j).obj N))
    (hRQ : ∀ j N, RB j N → T.Q j N) (hA : A.FaithfulnessInto RA) : Bs.FaithfulnessInto RB := by
  intro k M N hM hN φ ψ h
  have h' : (A.pbL k).map ((T.F k).map φ) = (A.pbL k).map ((T.F k).map ψ) :=
    (map_eq_map_iff_of_iso (T.βL k) φ ψ).1 (congrArg T.FL.map h)
  obtain ⟨j, e, he⟩ := hA k _ _ (T.P_map k M hM) (hR k N hN) _ _ h'
  exact ⟨j, e, T.faithful j (T.Q_pb e M (T.Q_of_P k M hM)) (T.Q_pb e N (hRQ k N hN)) _ _
    ((map_eq_map_iff_of_iso (T.β e) φ ψ).2 he)⟩

include T in
/-- **The fullness clause into a target property passes down a comparison**, provided the
comparison carries the target property of `Bs` to that of `A` and the former lies in `Q`. -/
theorem fullnessInto (hR : ∀ j N, RB j N → RA j ((T.F j).obj N))
    (hRQ : ∀ j N, RB j N → T.Q j N) (hA : A.FullnessInto RA) : Bs.FullnessInto RB := by
  intro k M N hM hN φ
  have hQM := T.Q_of_P k M hM
  have hQN := hRQ k N hN
  obtain ⟨j, e, φA, hφA⟩ := hA k _ _ (T.P_map k M hM) (hR k N hN)
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

end Transfer

namespace TransferUp

variable {A : PullbackSystem.{w, w', v₁, u₁} J} {Bs : PullbackSystem.{w, w', v₂, u₂} J}
  (T : TransferUp A Bs) {RA : ∀ j, ObjectProperty (A.C j)} {RB : ∀ j, ObjectProperty (Bs.C j)}

include T in
/-- **The faithfulness clause into a target property passes up a comparison**, provided every
object of the target property of `Bs` is the image of an object of the target property of `A`,
and the latter lies in `Q`. -/
theorem faithfulnessInto (hRQ : ∀ j M, RA j M → T.Q j M)
    (hess : ∀ j X, RB j X → ∃ M, RA j M ∧ Nonempty ((T.F j).obj M ≅ X))
    (hA : A.FaithfulnessInto RA) : Bs.FaithfulnessInto RB := by
  intro k X Y hX hY φ ψ h
  obtain ⟨M, hM, ⟨eM⟩⟩ := T.essSurjP k X hX
  obtain ⟨N, hN, ⟨eN⟩⟩ := hess k Y hY
  have hQM := T.Q_of_P k M hM
  have hQN := hRQ k N hN
  obtain ⟨φ', rfl⟩ := T.exists_preimage_conj hQM hQN eM eN φ
  obtain ⟨ψ', rfl⟩ := T.exists_preimage_conj hQM hQN eM eN ψ
  have h₁ : (Bs.pbL k).map ((T.F k).map φ') = (Bs.pbL k).map ((T.F k).map ψ') := by
    simp only [Functor.map_comp] at h
    rw [← cancel_epi ((Bs.pbL k).map eM.inv), ← cancel_mono ((Bs.pbL k).map eN.hom)]
    simpa only [Category.assoc] using h
  have h₂ : (A.pbL k).map φ' = (A.pbL k).map ψ' := by
    exact T.faithfulL (T.QL_pbL k M hQM) (T.QL_pbL k N hQN) _ _
      ((map_eq_map_iff_of_iso (T.βL k) φ' ψ').2 h₁)
  obtain ⟨j, e, he⟩ := hA k M N hM hN φ' ψ' h₂
  refine ⟨j, e, ?_⟩
  have h₃ : (Bs.pb e).map ((T.F k).map φ') = (Bs.pb e).map ((T.F k).map ψ') :=
    (map_eq_map_iff_of_iso (T.β e) φ' ψ').1 (congrArg (T.F j).map he)
  simp only [Functor.map_comp, h₃]

include T in
/-- **The fullness clause into a target property passes up a comparison**, provided every object
of the target property of `Bs` is the image of an object of the target property of `A`, and the
latter lies in `Q`. -/
theorem fullnessInto (hRQ : ∀ j M, RA j M → T.Q j M)
    (hess : ∀ j X, RB j X → ∃ M, RA j M ∧ Nonempty ((T.F j).obj M ≅ X))
    (hA : A.FullnessInto RA) : Bs.FullnessInto RB := by
  intro k X Y hX hY φ
  obtain ⟨M, hM, ⟨eM⟩⟩ := T.essSurjP k X hX
  obtain ⟨N, hN, ⟨eN⟩⟩ := hess k Y hY
  have hQM := T.Q_of_P k M hM
  have hQN := hRQ k N hN
  let φB : (Bs.pbL k).obj ((T.F k).obj M) ⟶ (Bs.pbL k).obj ((T.F k).obj N) :=
    (Bs.pbL k).map eM.hom ≫ φ ≫ (Bs.pbL k).map eN.inv
  obtain ⟨φA, hφA⟩ := T.fullL (T.QL_pbL k M hQM) (T.QL_pbL k N hQN)
    ((T.βL k).hom.app M ≫ φB ≫ (T.βL k).inv.app N)
  obtain ⟨j, e, φ'A, hφ'A⟩ := hA k M N hM hN φA
  refine ⟨j, e, (Bs.pb e).map eM.inv ≫ (T.β e).inv.app M ≫ (T.F j).map φ'A ≫
    (T.β e).hom.app N ≫ (Bs.pb e).map eN.hom, ?_⟩
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

end TransferUp

end Stacks.ModuleColimit.PullbackSystem

end
