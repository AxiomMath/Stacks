module

public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyConstant
public import StacksFrontier.AlgebraicTopology.Decalage
public import StacksFrontier.AlgebraicTopology.SimplicialHomotopyTensor
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Alexander–Whitney map of a décalage

The *décalage* `dec N` of a simplicial object is contractible over `N _⦋0⦌`: its augmentation
`dec N ⟶ const (N _⦋0⦌)` is a homotopy equivalence of simplicial objects, because the décalage
carries an extra degeneracy. A homotopy equivalence in the second variable is inverted by the
Alexander–Whitney comparison — the comparison is natural, and both of the maps it is natural
against are homotopy equivalences after tensoring — so the Alexander–Whitney map of a décalage
is a quasi-isomorphism, the constant case already being known.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_hom_of_extraDegeneracy`: the
  augmentation of an augmented simplicial object with an extra degeneracy is a homotopy
  equivalence.
* `CategoryTheory.SimplicialObject.homotopyEquivalences_whiskerLeft`: a homotopy equivalence
  stays one after tensoring on the left.
* `AlgebraicTopology.quasiIso_alexanderWhitney_of_homotopyEquivalences`: the Alexander–Whitney
  map is a quasi-isomorphism for the source of a homotopy equivalence as soon as it is one for
  the target.
* `AlgebraicTopology.quasiIso_alexanderWhitney_dec`: the Alexander–Whitney map of a décalage is
  a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The augmentation of an augmented simplicial object with an extra degeneracy is a homotopy
equivalence of simplicial objects: the section of the extra degeneracy is a homotopy inverse. -/
@[sga "4 XVII 6.3.23.2" "more general"]
public lemma homotopyEquivalences_hom_of_extraDegeneracy (X : SimplicialObject.Augmented C)
    (ed : X.ExtraDegeneracy) : SimplicialObject.homotopyEquivalences C X.hom :=
  ⟨ed.section_, Relation.EqvGen.rel _ _ ⟨ed.homotopy⟩, ed.section_comp_hom ▸ .refl _⟩

variable [MonoidalCategory C]

/-- A homotopy equivalence of simplicial objects stays a homotopy equivalence after tensoring on
the left with a simplicial object: a simplicial homotopy survives the tensoring. -/
public lemma homotopyEquivalences_whiskerLeft (M : SimplicialObject C)
    {U V : SimplicialObject C} {a : U ⟶ V} (ha : SimplicialObject.homotopyEquivalences C a) :
    SimplicialObject.homotopyEquivalences C (M ◁ a) := by
  obtain ⟨b, h₁, h₂⟩ := ha
  have key {X : SimplicialObject C} {f g : X ⟶ X}
      (h : Relation.EqvGen (fun f g : X ⟶ X => Nonempty (Homotopy f g)) f g) :
      Relation.EqvGen (fun f g : M ⊗ X ⟶ M ⊗ X => Nonempty (Homotopy f g)) (M ◁ f) (M ◁ g) :=
    h.map _ fun _ _ hfg => ⟨Homotopy.whiskerLeft M hfg.some⟩
  exact ⟨M ◁ b, by simpa using key h₁, by simpa using key h₂⟩

end CategoryTheory.SimplicialObject

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C] [CategoryWithHomology C]

omit [HasZeroObject C] in
/-- A homotopy equivalence in the second variable is inverted by the Alexander–Whitney
comparison: if the comparison is a quasi-isomorphism for the target it is one for the source. -/
public lemma quasiIso_alexanderWhitney_of_homotopyEquivalences (M : SimplicialObject C)
    {N N' : SimplicialObject C} (g : N ⟶ N')
    (hg : SimplicialObject.homotopyEquivalences C g)
    (h : QuasiIso (alexanderWhitney M N')) : QuasiIso (alexanderWhitney M N) := by
  have h₁ : QuasiIso ((alternatingFaceMapComplex C).map (M ◁ g)) :=
    _root_.homotopyEquivalences_le_quasiIso C (ComplexShape.down ℕ) _
      (homotopyEquivalences_alternatingFaceMapComplex_map
        (SimplicialObject.homotopyEquivalences_whiskerLeft M hg))
  have h₂ : QuasiIso (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
      ((alternatingFaceMapComplex C).map g)) := by
    obtain ⟨e, he⟩ := homotopyEquivalences_alternatingFaceMapComplex_map hg
    refine _root_.homotopyEquivalences_le_quasiIso C (ComplexShape.down ℕ) _
      ⟨tensorHomotopyEquivRight ((alternatingFaceMapComplex C).obj M) e, ?_⟩
    rw [← he]
    rfl
  have h₃ : QuasiIso (alexanderWhitney M N ≫ HomologicalComplex.tensorHom
      (𝟙 ((alternatingFaceMapComplex C).obj M)) ((alternatingFaceMapComplex C).map g)) := by
    rw [alexanderWhitney_naturality_right]
    infer_instance
  exact quasiIso_of_comp_right (alexanderWhitney M N)
    (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
      ((alternatingFaceMapComplex C).map g))

/-- **The Alexander–Whitney map of a décalage is a quasi-isomorphism.** -/
public instance quasiIso_alexanderWhitney_dec (M N : SimplicialObject C) :
    QuasiIso (alexanderWhitney M (SimplicialObject.dec N)) :=
  quasiIso_alexanderWhitney_of_homotopyEquivalences M (SimplicialObject.decAug N)
    (SimplicialObject.homotopyEquivalences_hom_of_extraDegeneracy _
      (SimplicialObject.decExtraDegeneracy N)) inferInstance

end AlgebraicTopology

end
