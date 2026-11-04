module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.ResolutionCotangentDerived
public import StacksFrontier.Cotangent.Triangle.FirstVertex
public import StacksFrontier.Cotangent.Triangle.FundamentalDisplay

/-!
# The fundamental triangle of the cotangent complex

For ring maps `A → B → C`, Equation 92.7.0.1 of the Stacks Project displays the triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`, whose three vertices are `CommAlgCat.fundamentalVertex₁`,
`CommAlgCat.fundamentalVertex₂` and `CommAlgCat.fundamentalVertex₃`. This file assembles that
triangle out of the short exact sequence of differentials of Tag 08SD, for `B → C` injective and
granted that the base-changed resolution `Q_• ⊗_{P_•} B` is a resolution of `C` over `B`.

## Main definitions

* `CommAlgCat.towerHom`: the map of `A`-algebras `B ⟶ C` underlying a scalar tower `A → B → C`.
* `CommAlgCat.baseChangedRelativeCotangentComplex`: the complex `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` of the
  base-changed resolution, the third vertex of the triangle of Tag 08SD.

## Main results

* `CommAlgCat.nonempty_q_baseChangedRelativeCotangentComplex_iso_cotangentComplex`: if the
  base-changed resolution is a resolution of `C` over `B`, then its complex computes `L_{C/B}` in
  `D(C)`.
* `CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution`: the fundamental triangle on the
  three vertices of the display, under the two hypotheses above.

## Implementation notes

The triangle of Tag 08SD, with the derived base change for its first vertex, is
`CommAlgCat.exists_distinguished_derivedBaseChange_cotangentTriangle`; its vertices are the first
vertex of the display, by `CommAlgCat.cotangentTriangle_obj₁DerivedBaseChangeIso`, the second
vertex of the display, by `CommAlgCat.cotangentTriangle_obj₂`, and the complex
`Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` of the base-changed resolution `Q̄_• = Q_• ⊗_{P_•} B`, which is identified
with `L_{C/B}` by Tag 08PU at the base-changed resolution, read against the standard resolution of
`C` over `B`.

The three rings are taken in one universe, which is no restriction: three rings with maps between
them always lie in a common universe.

Proposition 08QX has no hypothesis beyond the three ring maps; two are carried here. First, `B → C`
is injective, as in Tag 08SD, which makes each term of the standard resolution of `C` a polynomial
algebra over the corresponding term for `B`; removing it is the passage to `A → B → B × C` of
Tag 08SD, through the product decomposition of Tag 08SC. Second, the base-changed resolution is a
resolution of `C` over `B`, the key fact of Tag 08SD, which rests on Tag 08RX.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-- The map of `A`-algebras `B ⟶ C` underlying a scalar tower `A → B → C`. -/
noncomputable abbrev towerHom (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    CommAlgCat.of A B ⟶ CommAlgCat.of A C :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C)

/-- The complex `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` of the base-changed resolution `Q̄_• = Q_• ⊗_{P_•} B`, read
in cohomological degrees `≤ 0`: the third vertex of the triangle of Tag 08SD. -/
noncomputable abbrev baseChangedRelativeCotangentComplex (A : Type u) [CommRing A]
    {B C : CommAlgCat.{u} A} (f : B ⟶ C) : CochainComplex (ModuleCat.{u} C) ℤ :=
  (alternatingFaceMapCochainComplex (ModuleCat.{u} C)).obj (relativeCotangentSimplicialObject A f)

section

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The algebra `C` over `B` carried by the base-changed resolution of a scalar tower is the given
one: two algebra structures with the same structure map are equal. -/
theorem baseChangedStandardResolution_right_eq :
    (baseChangedStandardResolution A (towerHom A B C)).right = CommAlgCat.of B C :=
  congrArg (fun i => @CommAlgCat.of B _ C _ i) (Algebra.algebra_ext _ _ fun _ => rfl)

/-- **The complex of the base-changed resolution computes `L_{C/B}`.** If every term of
`Q̄_• = Q_• ⊗_{P_•} B` is a polynomial algebra over `B` and the augmentation `Q̄_• → C` is a
trivial Kan fibration on underlying simplicial sets — that is, if `Q̄_•` is a resolution of `C`
over `B` — then `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` and `L_{C/B}` are isomorphic in `D(C)`. -/
theorem nonempty_q_baseChangedRelativeCotangentComplex_iso_cotangentComplex
    (hP : ∀ n, IsPolynomialAlgebra B
      ((baseChangedStandardResolution A (towerHom A B C)).left.obj n))
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A (towerHom A B C)).hom (forget (CommAlgCat.{u} B)))) :
    Nonempty (DerivedCategory.Q.obj
        (baseChangedRelativeCotangentComplex A (towerHom A B C)) ≅
      fundamentalVertex₃.{u, u, u + 1} B C) := by
  choose ι hι using hP
  have hPκ : ∀ n, IsPolynomialAlgebraBelow B
      (max (standardResolutionVarCardinal B
          (baseChangedStandardResolution A (towerHom A B C)).right)
        (Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, ι n)))
      ((baseChangedStandardResolution A (towerHom A B C)).left.obj n) := by
    intro n
    refine ⟨ι n, le_trans (Cardinal.mk_le_of_injective
      (f := fun x => (⟨n, x⟩ : Σ m : SimplexCategoryᵒᵖ, ι m)) fun x y hxy => ?_) (le_max_right _ _),
      hι n⟩
    exact eq_of_heq (Sigma.mk.injEq .. ▸ hxy).2
  have he : DerivedCategory.Q.obj (cotangentComplex B
        (baseChangedStandardResolution A (towerHom A B C)).right) =
      fundamentalVertex₃.{u, u, u + 1} B C :=
    let F : Algebra B C → DerivedCategory (ModuleCat.{u} C) :=
      fun i => DerivedCategory.Q.obj (cotangentComplex B (@CommAlgCat.of B _ C _ i))
    congrArg F (Algebra.algebra_ext _ _ fun _ => rfl)
  exact ⟨smallResolutionCotangentDerivedLowerShriekIso
      (baseChangedStandardResolution A (towerHom A B C)).hom _ hPκ hε ≪≫
    (standardResolutionCotangentDerivedLowerShriekIsoOfLE B _ _ (le_max_left _ _)).symm ≪≫
    eqToIso he⟩

end

/-- Three isomorphisms onto the objects of a distinguished triangle produce a distinguished
triangle on the three targets, with the morphisms conjugated from those of the given one. -/
private lemma exists_distTriang_of_iso {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
    {X Y Z : D} (T : Triangle D) (hT : T ∈ distTriang D)
    (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) :
    ∃ (α : X ⟶ Y) (β : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk α β δ ∈ distTriang D := by
  refine ⟨d₁.inv ≫ T.mor₁ ≫ d₂.hom, d₂.inv ≫ T.mor₂ ≫ d₃.hom,
    d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ d₁.symm d₂.symm d₃.symm (by simp) (by simp) (by simp)

/-- **The fundamental triangle of the cotangent complex.** Let `A → B → C` be ring maps. Then there
is a distinguished triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`, on the three vertices of the display of Tag 08QS.

Two hypotheses the source does not have are carried: `B → C` is injective, as in Tag 08SD, and the
base-changed resolution `Q̄_• = Q_• ⊗_{P_•} B` of Tag 08SD is a resolution of `C` over `B` — its
terms are polynomial algebras over `B` and its augmentation to `C` is a trivial Kan fibration on
underlying simplicial sets. -/
@[stacks 08QX "the triangle on the three vertices of the display of Tag 08QS, under TWO carried \
  hypotheses the source lacks: `B → C` injective, as in Tag 08SD, whose removal needs the \
  product decomposition of Tag 08SC; and the key fact of Tag 08SD, that the base-changed \
  resolution Q_bullet ⊗_{P_bullet} B is a resolution of C over B, which rests on Tag 08RX. \
  Neither tag is proved in this library"]
theorem exists_distTriang_fundamentalVertex_of_isResolution
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hf : Function.Injective (algebraMap B C))
    (hP : ∀ n, IsPolynomialAlgebra B
      ((baseChangedStandardResolution A (towerHom A B C)).left.obj n))
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A (towerHom A B C)).hom (forget (CommAlgCat.{u} B)))) :
    ∃ (α : fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ⟶ fundamentalVertex₂.{u, u, u + 1} A C)
      (β : fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C)
      (δ : fundamentalVertex₃.{u, u, u + 1} B C ⟶
        (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) := by
  obtain ⟨e₃⟩ := nonempty_q_baseChangedRelativeCotangentComplex_iso_cotangentComplex A B C hP hε
  have hf' : Function.Injective (towerHom A B C).hom := hf
  exact exists_distTriang_of_iso _ (cotangentTriangle_distinguished A (towerHom A B C) hf')
    (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C) hf')
    (eqToIso (cotangentTriangle_obj₂ A (towerHom A B C) hf')) e₃

end CommAlgCat

end
