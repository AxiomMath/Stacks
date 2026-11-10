module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Irreducible
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs

/-!
# Geometric irreducibility is local on an irreducible scheme

For a scheme over a field, geometric irreducibility can be checked on all nonempty affine opens,
on one affine open covering together with irreducibility, or on a pairwise-intersecting open
covering by geometrically irreducible schemes. It is also inherited by every nonempty open
subscheme.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_tfae_local` gives the four equivalent local
  criteria.
* `AlgebraicGeometry.geometricallyIrreducible_open` says that every nonempty open subscheme of a
  geometrically irreducible scheme over a field is geometrically irreducible.

## Implementation notes

The algebra structure on the sections of an open is induced by the structure morphism, using the
canonical identification of the global sections of `Spec k` with `k`. Covers are expressed as
suprema of open subobjects. The two results correspond respectively to the enumerated equivalence
and to the final assertion of the source.

The leaf name carries a `_local` suffix because `AlgebraicGeometry.geometricallyIrreducible_tfae`
is already the corresponding equivalence for a `k`-algebra; that one characterizes geometric
irreducibility by base change to distinguished extensions of the ground field, whereas this one
localizes the condition on the scheme.

## References

* [Stacks Project, Tag 038G](https://stacks.math.columbia.edu/tag/038G)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The restriction of a structure morphism to a nonempty open is surjective onto the
spectrum of a field. -/
private lemma surjective_open_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : Nonempty U) :
    Surjective (U.ι ≫ f) :=
  ⟨fun _ ↦ ⟨hU.some, Subsingleton.elim _ _⟩⟩

/-- The source of a geometrically irreducible morphism to the spectrum of a field is nonempty. -/
private lemma nonempty_of_geometricallyIrreducible (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [GeometricallyIrreducible f] : Nonempty X :=
  ⟨(f.surjective (Classical.choice inferInstance)).choose⟩

/-- Geometric irreducibility of the sections over an affine open is geometric irreducibility
of the restricted structure morphism. -/
private lemma isGeometricallyIrreducible_sections_iff (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U) :
    let : Algebra k Γ(X, U) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
    Algebra.IsGeometricallyIrreducible k Γ(X, U) ↔
      GeometricallyIrreducible (U.ι ≫ f) := by
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  dsimp only [Algebra.IsGeometricallyIrreducible]
  let : MorphismProperty.RespectsIso (@GeometricallyIrreducible) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have heq : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f := by
    change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appLE ⊤ U (by simp)) = hU.fromSpec ≫ f
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU (by simp), Spec.map_comp,
      IsAffineOpen.fromSpec_top]
    congr 1
    rw [← cancel_mono (Spec (.of k)).toSpecΓ]
    simp
  rw [heq, ← hU.isoSpec_inv_ι_assoc]
  exact MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyIrreducible) hU.isoSpec.inv _

/-- A scheme over a field covered by pairwise-intersecting opens, each geometrically irreducible,
is geometrically irreducible. -/
private lemma geometricallyIrreducible_of_iSup_eq_top (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {I : Type u} [Nonempty I] (U : I → X.Opens)
    (hcover : ⨆ i, U i = ⊤) (hU : ∀ i, GeometricallyIrreducible ((U i).ι ≫ f))
    (hinter : ∀ i j, U i ⊓ U j ≠ ⊥) : GeometricallyIrreducible f := by
  refine ⟨fun K _ y Z fst snd hsquare ↦ ?_⟩
  have : Surjective y := ⟨fun _ ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩
  have hfst : Function.Surjective fst :=
    (show Surjective fst from
      MorphismProperty.of_isPullback (P := @Surjective) hsquare.flip inferInstance).surj
  let V : I → Z.Opens := fun i ↦ fst ⁻¹ᵁ U i
  have hVcover : (⨆ i, V i) = ⊤ := fst.iSup_preimage_eq_top hcover
  have hVirred (i : I) : IrreducibleSpace (V i) :=
    (hU i).geometrically_irreducibleSpace y (fst ∣_ U i) ((V i).ι ≫ snd)
      ((isPullback_morphismRestrict fst (U i)).paste_vert hsquare)
  have hVinter : Pairwise (Function.onFun (¬ Disjoint · ·) V) := by
    intro i j hij hd
    have hn : Set.Nonempty ((U i : Set X) ∩ (U j : Set X)) :=
      Set.nonempty_iff_ne_empty.mpr fun heq ↦
        hinter i j (SetLike.coe_injective (by simpa using heq))
    obtain ⟨x, hxi, hxj⟩ := hn
    obtain ⟨z, hz⟩ := hfst x
    apply hd.le_bot
    show z ∈ V i ⊓ V j
    simpa [V, hz] using And.intro hxi hxj
  have := PreirreducibleSpace.of_isOpenCover hVinter hVcover
    fun i ↦ (hVirred i).toPreirreducibleSpace
  exact IrreducibleSpace.mk ((hVirred (Classical.arbitrary I)).toNonempty.map fun x ↦ x.1)

/-- **Stacks Project, Tag 038G.** For a scheme over a field, geometric irreducibility is
equivalent to each of the three stated local criteria. -/
@[stacks 038G "equivalent conditions"]
public theorem geometricallyIrreducible_tfae_local
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    let geometricallyIrreducibleSections := fun U : X.Opens ↦
      let : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
      Algebra.IsGeometricallyIrreducible k Γ(X, U)
    List.TFAE
      [ GeometricallyIrreducible f,
        Nonempty X ∧ ∀ U : X.affineOpens,
          Nonempty (U : Set X) → geometricallyIrreducibleSections U.1,
        IrreducibleSpace X ∧
          ∃ (I : Type u) (U : I → X.affineOpens),
            (⨆ i, (U i).1) = ⊤ ∧ ∀ i, geometricallyIrreducibleSections (U i).1,
        ∃ (I : Type u) (_ : Nonempty I) (U : I → X.Opens),
          (⨆ i, U i) = ⊤ ∧
            (∀ i, GeometricallyIrreducible ((U i).ι ≫ f)) ∧
            ∀ i j, U i ⊓ U j ≠ ⊥ ] := by
  classical
  tfae_have 1 → 2 := by
    intro hf
    refine ⟨nonempty_of_geometricallyIrreducible k f, fun U hU ↦ ?_⟩
    have := surjective_open_comp k f U.1 hU
    exact (isGeometricallyIrreducible_sections_iff k f U.1 U.2).mpr inferInstance
  tfae_have 2 → 3 := by
    rintro ⟨hX, h⟩
    have hIrred : IrreducibleSpace X := by
      apply ((Scheme.irreducibleSpace_tfae X).out 3 1).mp
      refine ⟨hX, fun U hU hne ↦ ?_⟩
      have := (isGeometricallyIrreducible_sections_iff k f U hU).mp (h ⟨U, hU⟩ hne)
      exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := U.ι ≫ f)
    refine ⟨hIrred, ?_⟩
    let I := { U : X.affineOpens // Nonempty (U : Set X) }
    refine ⟨I, fun i ↦ i.1, ?_, fun i ↦ h i.1 i.2⟩
    apply le_antisymm le_top
    rw [← iSup_affineOpens_eq_top X]
    refine iSup_le fun U ↦ ?_
    by_cases hne : Nonempty (U : Set X)
    · exact le_iSup (fun i : I ↦ (i.1 : X.Opens)) ⟨U, hne⟩
    · rw [show (U : X.Opens) = ⊥ from SetLike.coe_injective
        (Set.eq_empty_of_forall_notMem fun x hx ↦ hne ⟨⟨x, hx⟩⟩)]
      exact bot_le
  tfae_have 3 → 4 := by
    rintro ⟨hX, I, U, hcover, hU⟩
    have hI : Nonempty I := not_isEmpty_iff.mp fun _ ↦ by simp at hcover
    have hg (i : I) := (isGeometricallyIrreducible_sections_iff k f (U i).1 (U i).2).mp (hU i)
    refine ⟨I, hI, fun i ↦ (U i).1, hcover, hg, ?_⟩
    intro i j
    have hne (i : I) : Nonempty ((U i).1 : Set X) := by
      have := hg i
      exact nonempty_of_geometricallyIrreducible k ((U i).1.ι ≫ f)
    have hn : Set.Nonempty (((U i).1 : Set X) ∩ ((U j).1 : Set X)) := by
      obtain ⟨⟨xi, hxi⟩⟩ := hne i
      obtain ⟨⟨xj, hxj⟩⟩ := hne j
      simpa using (PreirreducibleSpace.isPreirreducible_univ
        ((U i).1 : Set X) ((U j).1 : Set X) (U i).1.2 (U j).1.2
        ⟨xi, trivial, hxi⟩ ⟨xj, trivial, hxj⟩)
    intro heq
    obtain ⟨x, hxi, hxj⟩ := hn
    have hx : x ∈ (U i).1 ⊓ (U j).1 := ⟨hxi, hxj⟩
    simp [heq] at hx
  tfae_have 4 → 1 := by
    rintro ⟨I, hI, U, hcover, hU, hinter⟩
    exact geometricallyIrreducible_of_iSup_eq_top k f U hcover hU hinter
  tfae_finish

/-- **Stacks Project, Tag 038G.** Every nonempty open subscheme of a geometrically irreducible
scheme over a field is geometrically irreducible. -/
@[stacks 038G "nonempty open subschemes"]
public theorem geometricallyIrreducible_open
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIrreducible f] (U : X.Opens) (hU : Nonempty U) :
    GeometricallyIrreducible (U.ι ≫ f) := by
  let := surjective_open_comp k f U hU
  infer_instance

end AlgebraicGeometry
