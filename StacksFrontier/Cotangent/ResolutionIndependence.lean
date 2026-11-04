module

public import StacksFrontier.Cotangent.ResolutionCotangentDerived
public import StacksFrontier.Cotangent.ResolutionCotangentDerivedNaturality
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Remark 08QI: every resolution computes the cotangent complex

Let `A → B` be a ring map. [Stacks, Remark 08QI] records that for *any* resolution
`ε : P_• ⟶ B` of `B` over `A` — every term a polynomial algebra, the augmentation a trivial Kan
fibration — there is a canonical isomorphism

`L_{B/A} = Ω[P_•⁄A] ⊗_{P_•} B` in `D(B)`,

and that being free to choose the resolution is useful. This file proves that statement, in both
the forms it is consumed in:

* the **object level**: the complex of an arbitrary resolution is the cotangent complex in `D(B)`;
* the **arrow level**: whenever two resolutions are related by a morphism, the map the morphism
  induces on their complexes is a quasi-isomorphism.

The arrow-level form is the one a comparison of two presentations actually needs: the object-level
isomorphism alone leaves unpinned which arrow realizes it.

## The route

`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` — [Stacks, Tag 08PU] in `D(B)` for an
arbitrary resolution whose terms have at most `κ` variables — identifies the complex of a
resolution with `Lπ_!(i^*Ω_{𝒪/A})`, an object which does not mention the resolution, and
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality` says that identification is
functorial in the resolution. So the map induced by a morphism of resolutions becomes, after
`DerivedCategory.Q`, a composite of two isomorphisms, hence is invertible; a map of complexes
whose image in `D(B)` is invertible is a quasi-isomorphism.

The cardinal bound is not a restriction: there are countably many simplicial degrees, so the
variable sets of the terms of a resolution are bounded by a single cardinal, and two resolutions
can always be read at a common bound.

## Main results

* `CommAlgCat.exists_cardinal_isPolynomialAlgebraBelow`: the terms of a degreewise polynomial
  simplicial algebra are polynomial on at most `κ` variables for a single cardinal `κ`.
* `CommAlgCat.quasiIso_alternatingFaceMapComplex_map_resolutionOverMap` and
  `CommAlgCat.quasiIso_alternatingFaceMapComplex_map_of_isResolution`: **Remark 08QI at the arrow
  level** — a morphism of resolutions of `B` over `A` induces a quasi-isomorphism of the complexes
  `Ω[−⁄A] ⊗ B`, the second form taking the resolutions with no cardinal bound named.
* `CommAlgCat.resolutionCotangentComplexIso`: **Remark 08QI at the object level** — the complex of
  an arbitrary resolution is `L_{B/A}` in `D(B)`.

## Implementation notes

A morphism `ψ` of the simplicial objects of `Over B` attached to two augmentations is the same
thing as a morphism `w` of the underlying simplicial algebras with `w ≫ ε' = ε`:
`CommAlgCat.resolutionOverForget` is the passage from `ψ` to `w`, and
`CommAlgCat.resolutionOverMap_resolutionOverForget` says that
`CommAlgCat.resolutionOverMap` inverts it. Only the first direction is available from
`StacksFrontier/Cotangent/ResolutionCotangentDerivedNaturality.lean`, and the arrow-level statement is
wanted for an arbitrary `ψ`, which is the form in which a comparison of resolutions presents it.

## References

* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace CommAlgCat

/-! ### A cardinal bound for the terms of a resolution -/

/-- **The terms of a degreewise polynomial simplicial algebra are jointly bounded.** There are
countably many simplicial degrees, so the supremum of the cardinalities of the variable sets is a
cardinal bounding all of them at once. -/
theorem exists_cardinal_isPolynomialAlgebraBelow {A : Type u} [CommRing A]
    {P : SimplicialObject (CommAlgCat.{u} A)} (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) :
    ∃ κ : Cardinal.{u}, ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n) := by
  choose ι hι using hP
  exact ⟨⨆ n, Cardinal.mk (ι n),
    fun n => ⟨ι n, le_ciSup Cardinal.bddAbove_of_small n, hι n⟩⟩

/-! ### A morphism of augmented simplicial algebras, read upstairs and downstairs -/

section Morphism

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P P' : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- **The morphism of simplicial algebras underlying a morphism of the simplicial objects of
`Over B`.** Composing `CommAlgCat.resolutionOver` with the forgetful functor `Over B ⥤ CommAlgCat`
returns the simplicial algebra itself, so whiskering a morphism with the forgetful functor is a
morphism of the simplicial algebras. -/
def resolutionOverForget (ψ : resolutionOver ε ⟶ resolutionOver ε') : P ⟶ P' :=
  Functor.whiskerRight ψ (Over.forget B)

/-- The underlying morphism is compatible with the augmentations: that is what lying over `B`
degreewise says. -/
lemma resolutionOverForget_comp (ψ : resolutionOver ε ⟶ resolutionOver ε') :
    resolutionOverForget ε ε' ψ ≫ ε' = ε :=
  NatTrans.ext (funext fun n => Over.w (ψ.app n))

/-- Reading a morphism of simplicial algebras over `B` as a morphism of the simplicial objects of
`Over B` inverts `CommAlgCat.resolutionOverForget`: the two descriptions of a morphism of
augmented simplicial algebras agree. -/
lemma resolutionOverMap_resolutionOverForget (ψ : resolutionOver ε ⟶ resolutionOver ε') :
    resolutionOverMap ε ε' (resolutionOverForget ε ε' ψ)
        (resolutionOverForget_comp ε ε' ψ) = ψ := by
  ext n
  exact rfl

end Morphism

/-! ### Remark 08QI at the arrow level -/

section Arrow

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P P' : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- **The map induced by a morphism of resolutions is a quasi-isomorphism**, read on the complexes
in cohomological degrees `≤ 0`. [Stacks, Tag 08PU] in `D(B)` identifies each of the two complexes
with `Lπ_!(i^*Ω_{𝒪/A})`, and `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`
says the induced map is the comparison of those two identifications; so its image in `D(B)` is a
composite of isomorphisms. -/
private theorem quasiIso_resolutionCotangentComplexMap
    (κ : Cardinal.{u}) (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))
    (hP'κ : ∀ n, IsPolynomialAlgebraBelow A κ (P'.obj n))
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (hε' : SSet.trivialKanFibrations (Functor.whiskerRight ε' (forget (CommAlgCat.{u} A))))
    (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    QuasiIso (resolutionCotangentComplexMap ε ε' w hw) := by
  have key :=
    smallResolutionCotangentDerivedLowerShriekIso_naturality ε ε' κ hPκ hP'κ w hw hε hε'
  have hEq : DerivedCategory.Q.map (resolutionCotangentComplexMap ε ε' w hw) =
      (smallResolutionCotangentDerivedLowerShriekIso ε κ hPκ hε).hom ≫
        (smallResolutionCotangentDerivedLowerShriekIso ε' κ hP'κ hε').inv := by
    rw [← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hiso : IsIso (DerivedCategory.Q.map (resolutionCotangentComplexMap ε ε' w hw)) := by
    rw [hEq]; infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} (B : Type u)) _).1 hiso

/-- **Remark 08QI at the arrow level, for resolutions read at a common cardinal bound.** A
morphism `ψ` of the simplicial objects of `Over B` attached to two resolutions of `B` over `A`
induces a quasi-isomorphism of the complexes `Ω[−⁄A] ⊗ B`. This is
`CommAlgCat.quasiIso_resolutionCotangentComplexMap` read before the reindexing into cohomological
degrees `≤ 0`, which does not change the homology. -/
theorem quasiIso_alternatingFaceMapComplex_map_resolutionOverMap
    (κ : Cardinal.{u}) (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))
    (hP'κ : ∀ n, IsPolynomialAlgebraBelow A κ (P'.obj n))
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (hε' : SSet.trivialKanFibrations (Functor.whiskerRight ε' (forget (CommAlgCat.{u} A))))
    (ψ : resolutionOver ε ⟶ resolutionOver ε') :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).map
      (Functor.whiskerRight ψ (overDifferentialsFunctor (A := A) (B := B)))) := by
  have h := quasiIso_resolutionCotangentComplexMap ε ε' κ hPκ hP'κ hε hε'
    (resolutionOverForget ε ε' ψ) (resolutionOverForget_comp ε ε' ψ)
  rw [resolutionCotangentComplexMap, resolutionOverMap_resolutionOverForget,
    ComplexShape.Embedding.extendFunctor_map] at h
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).1 h

end Arrow

/-! ### Remark 08QI, with no cardinal bound named -/

section Unbounded

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P P' : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- **Remark 08QI at the arrow level.** Let `ε : P_• ⟶ B` and `ε' : P'_• ⟶ B` be resolutions of
`B` over `A` in the sense of [Stacks, Tag 08QI]. Every morphism `ψ` of the attached simplicial
objects of `Over B` — equivalently, every morphism `P_• ⟶ P'_•` of simplicial `A`-algebras
compatible with the augmentations — induces a quasi-isomorphism

`Ω[P_•⁄A] ⊗_{P_•} B ⟶ Ω[P'_•⁄A] ⊗_{P'_•} B`.

So any resolution computes the cotangent complex, and the isomorphism is the one a morphism of
resolutions induces; no cardinal bound appears, the terms of the two resolutions being bounded by
a single cardinal. -/
@[stacks 08QI "the remark's payoff, at the arrow level: for any two resolutions of B over A and \
  any morphism between them, the induced map of the complexes Omega[-/A] ⊗ B is a \
  quasi-isomorphism, so any resolution computes L_{B/A} and the comparison is the induced map"]
theorem quasiIso_alternatingFaceMapComplex_map_of_isResolution
    (hres : IsResolution A (B : Type u) P ε) (hres' : IsResolution A (B : Type u) P' ε')
    (ψ : resolutionOver ε ⟶ resolutionOver ε') :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).map
      (Functor.whiskerRight ψ (overDifferentialsFunctor (A := A) (B := B)))) := by
  obtain ⟨κ, hκ⟩ := exists_cardinal_isPolynomialAlgebraBelow hres.isPolynomialAlgebra
  obtain ⟨κ', hκ'⟩ := exists_cardinal_isPolynomialAlgebraBelow hres'.isPolynomialAlgebra
  exact quasiIso_alternatingFaceMapComplex_map_resolutionOverMap ε ε' (max κ κ')
    (fun n => (hκ n).mono (le_max_left _ _)) (fun n => (hκ' n).mono (le_max_right _ _))
    hres.trivialKanFibration hres'.trivialKanFibration ψ

/-- **Remark 08QI at the object level.** The complex `Ω[P_•⁄A] ⊗_{P_•} B` of an arbitrary
resolution of `B` over `A`, read in cohomological degrees `≤ 0`, is the cotangent complex
`L_{B/A}` in `D(B)`. Both are identified with `Lπ_!(i^*Ω_{𝒪/A})` by [Stacks, Tag 08PU] in `D(B)`,
read at a bound containing both the given resolution and the standard one. -/
@[stacks 08QI "the remark's payoff, at the object level: for any resolution of B over A the \
  complex Omega[P_./A] ⊗_{P_.} B is L_{B/A} in D(B)"]
def resolutionCotangentComplexIso (hres : IsResolution A (B : Type u) P ε) :
    DerivedCategory.Q.obj
        (((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
            (resolutionOver ε ⋙ overDifferentialsFunctor)).extend
          (ComplexShape.embeddingUpIntLE (0 : ℤ))) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A B) :=
  letI h := exists_cardinal_isPolynomialAlgebraBelow hres.isPolynomialAlgebra
  letI κ := Classical.choose h
  haveI hκ := Classical.choose_spec h
  smallResolutionCotangentDerivedLowerShriekIso ε (max κ (standardResolutionVarCardinal A B))
      (fun n => (hκ n).mono (le_max_left _ _)) hres.trivialKanFibration ≪≫
    (standardResolutionCotangentDerivedLowerShriekIsoOfLE A B
      (max κ (standardResolutionVarCardinal A B)) (le_max_right _ _)).symm

end Unbounded

end CommAlgCat

end
