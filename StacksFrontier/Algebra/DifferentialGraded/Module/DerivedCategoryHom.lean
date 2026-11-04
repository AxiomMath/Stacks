module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.RightOrthogonalAcyclic

/-!
# Morphisms of the derived category computed by a resolution

Let `(A, d)` be a differential graded algebra and let `M` and `N` be right differential graded
`A`-modules. The morphism modules of the derived category `D(A, d)` are computed in the homotopy
category `K(A, d)` as soon as one of the two arguments is replaced by a resolution: for a
property-(P) resolution `P → M` one has `Hom_{D(A,d)}(M, N) = Hom_{K(A,d)}(P, N)`, and for a
property-(I) resolution `N → I` one has `Hom_{D(A,d)}(M, N) = Hom_{K(A,d)}(M, I)`.

Both halves rest on the same mechanism. The localization functor
`Q : K(A, d) ⥤ D(A, d)` is bijective on morphisms *out of* an object orthogonal on the left to
the acyclic modules and on morphisms *into* an object orthogonal on the right to them, because
the quasi-isomorphisms are the class `trW` attached to the acyclic objects, and that class has
the two calculi of fractions. A module with property (P) is left orthogonal and one with
property (I) is right orthogonal, so each of the two resolutions turns the morphism module of
the derived category into one of the homotopy category; the resolution map itself becomes
invertible in `D(A, d)`, which moves the remaining argument into place.

## Main results

* `DifferentialGradedModule.bijective_q_map_of_leftOrthogonal` and
  `DifferentialGradedModule.bijective_q_map_of_rightOrthogonal`: the localization functor is
  bijective on morphisms out of a left-orthogonal object, resp. into a right-orthogonal one.
* `DifferentialGradedModule.bijective_q_map_of_propertyP` and
  `DifferentialGradedModule.bijective_q_map_of_propertyI`: the same for a module with
  property (P), resp. property (I).
* `DifferentialGradedModule.exists_homEquiv_of_propertyPResolution`: **Stacks 09KY(1)**.
* `DifferentialGradedModule.exists_homEquiv_of_propertyIResolution`: **Stacks 09KY(2)**.

## Implementation notes

The source writes an equality of morphism sets. Here each half is the existence of a bijection
*together with the equation that pins it down*: the bijection sends a morphism of the homotopy
category to the composite of the resolution map with the given morphism of the derived category,
read through `Q`. Mere existence of a bijection between two morphism modules would say almost
nothing; the equation says that the identification is the canonical one, and it determines the
bijection, since `Q` is bijective on those morphism modules.

Both resolutions are taken as a module for which a filtration exists, `Nonempty
(PropertyPFiltration P)`, rather than one equipped with a chosen filtration: that is the form in
which Tag 09KP and Tag 09KU produce them, and the conclusion is a proposition, so nothing is
lost.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules live in a single universe `u`, following the bundled encoding of Tag 09JJ.

## References

* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY); the two resolutions are
  [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) and
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), their orthogonality is
  [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) and
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), and the derived category is
  [Tag 09KX](https://stacks.math.columbia.edu/tag/09KX).
-/

@[expose] public section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The localization functor to the derived category is a localization at the class of morphisms
attached to the acyclic objects, which is the form the orthogonality criteria of
`Mathlib.CategoryTheory.Triangulated.Orthogonal` ask for. -/
theorem isLocalization_q_acyclic_trW :
    (quasiIsomorphisms' A).Q.IsLocalization (acyclic' A).trW := by
  rw [acyclic_trW_eq_quasiIsomorphisms']
  infer_instance

/-- **Morphisms out of a left-orthogonal object are not changed by localization.** If `X` is
orthogonal on the left to the acyclic objects of `K(A, d)`, then `Q` is bijective from
`Hom_{K(A,d)}(X, Y)` to `Hom_{D(A,d)}(Q X, Q Y)` for every `Y`. -/
theorem bijective_q_map_of_leftOrthogonal {X : HomotopyCategory A}
    (hX : (acyclic' A).leftOrthogonal X) (Y : HomotopyCategory A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map : (X ⟶ Y) → _) := by
  have := isLocalization_q_acyclic_trW (A := A)
  exact hX.map_bijective_of_isTriangulated _ Y

/-- **Morphisms into a right-orthogonal object are not changed by localization.** If `Y` is
orthogonal on the right to the acyclic objects of `K(A, d)`, then `Q` is bijective from
`Hom_{K(A,d)}(X, Y)` to `Hom_{D(A,d)}(Q X, Q Y)` for every `X`. -/
theorem bijective_q_map_of_rightOrthogonal {Y : HomotopyCategory A}
    (hY : (acyclic' A).rightOrthogonal Y) (X : HomotopyCategory A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map : (X ⟶ Y) → _) := by
  have := isLocalization_q_acyclic_trW (A := A)
  exact hY.map_bijective_of_isTriangulated _ X

/-- A module with property (P) computes morphisms out of itself in the derived category: `Q` is
bijective from `Hom_{K(A,d)}(P, N)` to `Hom_{D(A,d)}(Q P, Q N)`. -/
theorem bijective_q_map_of_propertyP {P : DifferentialGradedModule A}
    (hP : Nonempty (PropertyPFiltration P)) (N : DifferentialGradedModule A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map :
      ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj N) → _) :=
  bijective_q_map_of_leftOrthogonal (leftOrthogonal_acyclic_of_propertyP hP.some) _

/-- A module with property (I) computes morphisms into itself in the derived category: `Q` is
bijective from `Hom_{K(A,d)}(M, I)` to `Hom_{D(A,d)}(Q M, Q I)`. -/
theorem bijective_q_map_of_propertyI {I : DifferentialGradedModule A}
    (hI : Nonempty (PropertyIFiltration I)) (M : DifferentialGradedModule A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map :
      ((toHomotopyCategory A).obj M ⟶ (toHomotopyCategory A).obj I) → _) :=
  bijective_q_map_of_rightOrthogonal (rightOrthogonal_acyclic_of_propertyI hI.some) _

/-- The image in the derived category of a quasi-isomorphism of differential graded modules is an
isomorphism. -/
theorem isIso_q_map_toHomotopyCategory_map {M N : DifferentialGradedModule A} (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex A).map f)) :
    IsIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f)) :=
  Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
    ((quasiIsomorphisms_map_iff' A f).2 hf)

/-- **Stacks 09KY(1).** *"Let `P → M` be a P-resolution as in Lemma 09KP. Then
`Hom_{D(A,d)}(M, N) = Hom_{K(Mod_{(A,d)})}(P, N)`."*

The identification sends a morphism `g : M ⟶ N` of the derived category to the unique morphism
`P ⟶ N` of the homotopy category whose image in `D(A, d)` is the resolution map followed by
`g`. -/
@[stacks 09KY "morphisms_from_p_resolution"]
theorem exists_homEquiv_of_propertyPResolution {P M : DifferentialGradedModule A} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex A).map f))
    (hP : Nonempty (PropertyPFiltration P)) (N : DifferentialGradedModule A) :
    ∃ e : ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj M) ⟶
            (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj N)) ≃
          ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj N),
      ∀ g, (quasiIsomorphisms' A).Q.map (e g) =
        (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f) ≫ g := by
  have := isIso_q_map_toHomotopyCategory_map f hf
  let e₁ := Equiv.ofBijective _ (bijective_q_map_of_propertyP hP N)
  let e₂ := asIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f))
  exact ⟨e₂.homFromEquiv.symm.trans e₁.symm, fun g => e₁.apply_symm_apply _⟩

/-- **Stacks 09KY(2).** *"Let `N → I` be an I-resolution as in Lemma 09KU. Then
`Hom_{D(A,d)}(M, N) = Hom_{K(Mod_{(A,d)})}(M, I)`."*

The identification sends a morphism `g : M ⟶ N` of the derived category to the unique morphism
`M ⟶ I` of the homotopy category whose image in `D(A, d)` is `g` followed by the resolution
map. -/
@[stacks 09KY "morphisms_into_i_resolution"]
theorem exists_homEquiv_of_propertyIResolution {N I : DifferentialGradedModule A} (f : N ⟶ I)
    (hf : QuasiIso ((forgetToCochainComplex A).map f))
    (hI : Nonempty (PropertyIFiltration I)) (M : DifferentialGradedModule A) :
    ∃ e : ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj M) ⟶
            (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj N)) ≃
          ((toHomotopyCategory A).obj M ⟶ (toHomotopyCategory A).obj I),
      ∀ g, (quasiIsomorphisms' A).Q.map (e g) =
        g ≫ (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f) := by
  have := isIso_q_map_toHomotopyCategory_map f hf
  let e₁ := Equiv.ofBijective _ (bijective_q_map_of_propertyI hI M)
  let e₂ := asIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f))
  exact ⟨e₂.homToEquiv.trans e₁.symm, fun g => e₁.apply_symm_apply _⟩

end DifferentialGradedModule

end
