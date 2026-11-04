module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialAlgebra
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality

/-!
# Squares of ring maps which factor through the base ring of the target

A commutative square of ring maps `A → A'`, `B → B'` may admit an arrow `κ : B → A'` fitting into
it, so that `κ` recovers `A → A'` on the image of `A` and `A' → B'` recovers `B → B'` after `κ`.
The square then factors through the identity `A' → A'`, whose cotangent complex is contractible,
and therefore the induced map `L_{B/A} → L_{B'/A'}` is homotopic to zero.

## Main definitions

* `CommAlgCat.squareRestrictScalarsCompIso`: the identification of the restriction of scalars
  along a horizontal composition of squares with the composition of the two restrictions.

## Main results

* `CommAlgCat.nonempty_homotopy_id_cotangentMooreComplex_zero`: for a polynomial algebra with
  vanishing differentials, the Moore complex of the cotangent simplicial module is contractible.
* `CommAlgCat.squareCotangentTermMap_comp` and `CommAlgCat.squareCotangentMooreMap_comp`: the
  degreewise maps and the maps of Moore complexes compose along a horizontal composition of
  squares.
* `CommAlgCat.nonempty_homotopy_squareCotangentComplexMap_comp_zero`: a map of cotangent
  complexes which factors through the cotangent complex of a polynomial algebra with vanishing
  differentials is homotopic to zero.
* `CommAlgCat.nonempty_homotopy_squareCotangentComplexMap_zero`: **Stacks 08SB**.

## Implementation notes

The argument is run on the Moore complexes rather than on the cotangent complexes. That is where
the contraction of a polynomial algebra's standard resolution already lives — the extra
degeneracy at the last face of `CommAlgCat.cotangentExtraDegeneracyLast` exhibits the Moore
complex as homotopy equivalent to `Ω[B⁄A]` in degree zero, which is a zero object as soon as
`Ω[B⁄A]` vanishes — and the reindexing into cohomological degrees transports a homotopy by
`Homotopy.extend`, the map of cotangent complexes being by construction the reindexing of the map
of Moore complexes.

Contractibility is used through the observation that *every* map out of a contractible complex is
homotopic to zero, so only a factorization of the functoriality map is needed, not the
compatibility of the factorization with any particular choice of comparison isomorphism.

Taking `A'` itself for the middle algebra of the factorization would place it one universe too
low, so `ULift A'` is used instead; it is a polynomial algebra over `A'` on the empty set, and its
differentials vanish because its structure map is surjective. The two base rings are therefore
required to lie in a common universe, which is what the horizontal composition of squares
`CommAlgCat.AlgebraSquare.comp` expresses.

The source reaches the same conclusion from its own claim about the standard resolutions, that the
functoriality map `P_• → P'_•` is homotopic to the composition `P_• → B → A' → P'_•`. That claim
is `CommAlgCat.eqvGen_homotopy_squareResolutionRingMap_baseMap` of
`StacksFrontier.Cotangent.SquareResolutionBaseHomotopy`, which follows the source's proof through the
standard resolution of `A'` over itself; the argument of this file is an independent route to the
conclusion, and does not consume it.

## References

* [Stacks Project, Tag 08SB](https://stacks.math.columbia.edu/tag/08SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct ChangeOfRings

universe u v

namespace CommAlgCat

/-! ### Contractibility of the cotangent complex of a trivial polynomial algebra -/

/-- If `B` is a polynomial algebra over `A` whose module of differentials vanishes, the Moore
complex of its cotangent simplicial module is contractible. -/
public theorem nonempty_homotopy_id_cotangentMooreComplex_zero (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (hB : Algebra.IsPolynomialAlgebra A B)
    [Subsingleton (KaehlerDifferential A B)] :
    Nonempty (Homotopy (𝟙 (cotangentMooreComplex.{u, v} A B)) 0) := by
  obtain ⟨ed⟩ := nonempty_standardResolutionExtraDegeneracyLast.{u, v} A B hB
  have he : HomotopyEquiv (cotangentMooreComplex.{u, v} A B)
      ((ChainComplex.single₀ (ModuleCat.{max u v} B)).obj
        (ModuleCat.of B (KaehlerDifferential A B))) :=
    (cotangentExtraDegeneracyLast.{u, v} A B ed).homotopyEquiv
  have hz : IsZero ((ChainComplex.single₀ (ModuleCat.{max u v} B)).obj
      (ModuleCat.of B (KaehlerDifferential A B))) :=
    Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)
  refine ⟨he.homotopyHomInvId.symm.trans (Homotopy.ofEq ?_)⟩
  rw [hz.eq_of_src he.inv 0, comp_zero]

/-! ### Composition of squares -/

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {B : CommAlgCat.{max u v} A} {B' : CommAlgCat.{max u v} A'} {B'' : CommAlgCat.{max u v} A''}

/-- Restricting scalars along the algebra map of a horizontal composition of squares is
restricting scalars along the two algebra maps in turn. -/
public noncomputable def squareRestrictScalarsCompIso (sq : AlgebraSquare.{u, v, u} A A' B B')
    (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'') :
    ModuleCat.restrictScalars.{max u v} sq'.map ⋙ ModuleCat.restrictScalars sq.map ≅
      ModuleCat.restrictScalars (sq.comp sq').map :=
  (ModuleCat.restrictScalarsComp' sq.map sq'.map (sq.comp sq').map rfl).symm

/-- The degreewise maps of cotangent terms compose along a horizontal composition of squares. -/
public theorem squareCotangentTermMap_comp (sq : AlgebraSquare.{u, v, u} A A' B B')
    (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'') (n : SimplexCategoryᵒᵖ) :
    squareCotangentTermMap.{u, v, u} (sq.comp sq') n =
      squareCotangentTermMap.{u, v, u} sq n ≫
        (ModuleCat.restrictScalars sq.map).map (squareCotangentTermMap.{u, v, u} sq' n) ≫
          (squareRestrictScalarsCompIso.{u, v} sq sq').hom.app
            (cotangentTerm.{u, max u v} A'' B'' n) := by
  refine cotangentTerm_hom_ext.{u, max u v} A B n _ _ fun p => ?_
  have hr : ∀ y : cotangentTerm.{u, max u v} A B n,
      (squareCotangentTermMap.{u, v, u} sq n ≫
          (ModuleCat.restrictScalars sq.map).map (squareCotangentTermMap.{u, v, u} sq' n) ≫
            (squareRestrictScalarsCompIso.{u, v} sq sq').hom.app
              (cotangentTerm.{u, max u v} A'' B'' n)) y =
        squareCotangentTermMap.{u, v, u} sq' n
          (squareCotangentTermMap.{u, v, u} sq n y) := fun _ => rfl
  rw [hr, squareCotangentTermMap_D, squareCotangentTermMap_D, squareCotangentTermMap_D,
    standardResolutionSquareMap_comp]
  rfl

/-- The maps of Moore complexes compose along a horizontal composition of squares. -/
public theorem squareCotangentMooreMap_comp (sq : AlgebraSquare.{u, v, u} A A' B B')
    (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'') :
    squareCotangentMooreMap.{u, v, u} (sq.comp sq') =
      squareCotangentMooreMap.{u, v, u} sq ≫
        ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (squareCotangentMooreMap.{u, v, u} sq') ≫
          (Functor.mapHomologicalComplexCompIso (squareRestrictScalarsCompIso.{u, v} sq sq')
            (ComplexShape.down ℕ)).hom.app
              (cotangentMooreComplex.{u, max u v} A'' B'') := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    squareCotangentMooreMap_f]
  exact squareCotangentTermMap_comp.{u, v} sq sq' (op ⦋n⦌)

/-! ### Null-homotopy of a functoriality map factoring through a trivial polynomial algebra -/

/-- A map of cotangent complexes which factors through the cotangent complex of a polynomial
algebra with vanishing differentials is homotopic to zero. -/
public theorem nonempty_homotopy_squareCotangentComplexMap_comp_zero
    (sq : AlgebraSquare.{u, v, u} A A' B B') (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'')
    (hB' : Algebra.IsPolynomialAlgebra A' B')
    [Subsingleton (KaehlerDifferential A' B')] :
    Nonempty (Homotopy (squareCotangentComplexMap.{u, v, u} (sq.comp sq')) 0) := by
  obtain ⟨hmid⟩ := nonempty_homotopy_id_cotangentMooreComplex_zero.{u, max u v} A' B' hB'
  set F := (ModuleCat.restrictScalars.{max u v} sq.map).mapHomologicalComplex
    (ComplexShape.down ℕ)
  have h₁ : Homotopy (𝟙 (F.obj (cotangentMooreComplex.{u, max u v} A' B'))) 0 := by
    have h := (ModuleCat.restrictScalars.{max u v} sq.map).mapHomotopy
      (c := ComplexShape.down ℕ) hmid
    rwa [F.map_id, F.map_zero] at h
  have h₂ : Homotopy (squareCotangentMooreMap.{u, v, u} (sq.comp sq')) 0 := by
    rw [squareCotangentMooreMap_comp.{u, v} sq sq']
    refine Homotopy.trans (Homotopy.compLeft ?_ (squareCotangentMooreMap.{u, v, u} sq))
      (Homotopy.ofEq comp_zero)
    exact ((Homotopy.ofEq (Category.id_comp _).symm).trans (h₁.compRight _)).trans
      (Homotopy.ofEq zero_comp)
  have h₃ := h₂.extend (ComplexShape.embeddingUpIntLE (0 : ℤ))
  rw [HomologicalComplex.extendMap_zero] at h₃
  exact ⟨(h₃.compRight _).trans (Homotopy.ofEq zero_comp)⟩

/-! ### The remark -/

/-- **Stacks Project, Tag 08SB.** Let `A → A'`, `B → B'` be a commutative square of ring maps
compatible with the algebra structures `A → B` and `A' → B'`. If there is a ring map
`κ : B → A'` which agrees with `A → A'` on the image of `A` and which recovers `B → B'` after
`A' → B'`, then the induced map of cotangent complexes `L_{B/A} → L_{B'/A'}` is homotopic to
zero. -/
@[stacks 08SB "the conclusion of the remark: the induced map on cotangent complexes is homotopic \
to zero. The claim of the remark itself, that the functoriality map of standard resolutions is \
homotopic to the composition through `κ`, is \
`CommAlgCat.eqvGen_homotopy_squareResolutionRingMap_baseMap` of \
`StacksFrontier.Cotangent.SquareResolutionBaseHomotopy`; the proof here does not pass through it, \
factoring the square through the identity of `A'` instead."]
public theorem nonempty_homotopy_squareCotangentComplexMap_zero
    (sq : AlgebraSquare.{u, v, u} A A' B B') (κ : B →+* A')
    (hκ : ∀ a : A, κ (algebraMap A B a) = sq.base a)
    (hκ' : ∀ b : B, algebraMap A' B' (κ b) = sq.map b) :
    Nonempty (Homotopy (squareCotangentComplexMap.{u, v, u} sq) 0) := by
  have : Subsingleton (KaehlerDifferential A' (ULift.{v, u} A')) :=
    KaehlerDifferential.subsingleton_of_surjective A' (ULift.{v, u} A') fun a => ⟨a.down, rfl⟩
  have hpoly : Algebra.IsPolynomialAlgebra A' (ULift.{v, u} A') :=
    ⟨PEmpty.{max u v + 1}, ⟨(MvPolynomial.isEmptyAlgEquiv A' (PEmpty.{max u v + 1})).trans
      ULift.algEquiv.symm⟩⟩
  let M : CommAlgCat.{max u v} A' := CommAlgCat.of A' (ULift.{v, u} A')
  let sq₁ : AlgebraSquare.{u, v, u} A A' B M :=
    { base := sq.base
      map := (ULift.ringEquiv.symm : A' ≃+* ULift.{v, u} A').toRingHom.comp κ
      map_algebraMap := fun a => congrArg ULift.up (hκ a) }
  let sq₂ : AlgebraSquare.{u, v, u} A' A' M B' :=
    { base := RingHom.id A'
      map := (algebraMap A' B').comp (ULift.ringEquiv : ULift.{v, u} A' ≃+* A').toRingHom
      map_algebraMap := fun _ => rfl }
  have hext : ∀ s t : AlgebraSquare.{u, v, u} A A' B B',
      s.base = t.base → s.map = t.map → s = t := by
    rintro ⟨b₁, m₁, h₁⟩ ⟨b₂, m₂, h₂⟩ rfl rfl
    rfl
  have hcomp : sq₁.comp sq₂ = sq :=
    hext _ _ (RingHom.id_comp _) (RingHom.ext hκ')
  rw [← hcomp]
  exact nonempty_homotopy_squareCotangentComplexMap_comp_zero.{u, v} sq₁ sq₂ hpoly

end CommAlgCat

end
