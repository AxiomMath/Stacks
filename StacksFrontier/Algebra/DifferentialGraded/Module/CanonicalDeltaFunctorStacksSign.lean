module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.ConeSignClasses
public import StacksFrontier.Algebra.DifferentialGraded.Module.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated

/-!
# The canonical delta-functor in the sign convention of the Stacks project

Let `(A, d)` be a differential graded algebra. Tag 09L0 states that the canonical functor
`Mod_{(A, d)} → D(A, d)` is a `δ`-functor with `δ_{K → L → M} = - p ∘ q⁻¹`, where
`q : C(f) → M` is the comparison of the mapping cone of `f : K ⟶ L` with `M` and
`p : C(f) → K[1]` is the cone projection. The sign is relative to the triangulation of the
Stacks project, in which `(K, L, C(f), f, i, -p)` is distinguished (Tag 09KF). This file states
and proves Tag 09L0 against exactly that triangulation: the admissible-sequence structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` of Tag 09KH on the homotopy
category, and its localization `DifferentialGradedModule.derivedCategory'` at the
quasi-isomorphisms.

## Main results

* `DifferentialGradedModule.exists_deltaFunctorStructure_δ_eq_neg`: **Stacks 09L0** — the
  canonical functor to `DifferentialGradedModule.derivedCategory' A` carries a `δ`-functor
  structure whose connecting morphism is `- p ∘ q⁻¹`.
* `DifferentialGradedModule.mappingConeTriangle_mem_distTriang`: the triangle
  `(K, L, C(f), f, i, -p)` is distinguished for that triangulation.

## Implementation notes

The library's default triangulation of the homotopy category,
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, declares the unsigned cone
triangle `(K, L, C(f), f, i, p)` distinguished instead, and against it the connecting morphism
is `p ∘ q⁻¹` (`DifferentialGradedModule.canonicalDeltaFunctorStructure_δ_eq`). The two
triangulations differ exactly by negating third arrows
(`DifferentialGradedModule.mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃`).
The admissible-sequence structure is not an instance, so it is activated in this file as a local
instance. The proof is the one of `DifferentialGradedModule.canonicalDeltaFunctorStructure` with
the cone projection negated throughout: the comparison `q` and the map of cones are reused, the
distinguished triangle is `DifferentialGradedModule.mappingConeTriangle` (Tag 09KF, through
`DifferentialGradedModule.isDistinguishedTriangle_mappingConeTriangle`), and naturality of `-p`
is the negation of the naturality of `p`.

## References

* [Stacks Project, Tag 09L0](https://stacks.math.columbia.edu/tag/09L0); the triangle of the cone
  is [Tag 09KF](https://stacks.math.columbia.edu/tag/09KF) and the triangulation is
  [Tag 09KH](https://stacks.math.columbia.edu/tag/09KH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

section StacksConvention

/- This section is stated against the admissible-sequence pretriangulated structure of
Tag 09KH, in which `(K, L, C(f), f, i, -p)` is distinguished (Tag 09KF); it is not an instance
and is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- The canonical functor from differential graded `A`-modules to the derived category
`D(A, d)` built from the admissible-sequence triangulation of Tag 09KH: the quotient by homotopy
followed by the localization at the quasi-isomorphisms. -/
abbrev toDerivedCategory' (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModule A ⥤ derivedCategory' A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q

/-- The comparison `C(f) ⟶ M` of a short exact sequence becomes invertible in the derived
category `derivedCategory' A`. -/
theorem isIso_toDerivedCategory'_map_coneDescShortComplex
    (S : ShortComplex (DifferentialGradedModule A)) (hS : S.ShortExact) :
    IsIso ((toDerivedCategory' A).map (coneDescShortComplex S)) :=
  Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
    ((quasiIsomorphisms_map_iff' A _).2 (quasiIso_coneDescShortComplex S hS))

/-- The connecting morphism `δ = - p ∘ q⁻¹` of a short exact sequence, in the convention of the
Stacks project: the inverse in `D(A, d)` of the comparison `q : C(f) ⟶ M`, followed by the class
of the negated cone projection `-p : C(f) ⟶ K[1]` (the third morphism of
`DifferentialGradedModule.mappingConeTriangle`, by
`DifferentialGradedModule.mappingConeTriangle_mor₃_eq_neg`), read in `D(A, d)`. -/
def shortExactδ' {S : ShortComplex (DifferentialGradedModule A)} (hS : S.ShortExact) :
    (toDerivedCategory' A).obj S.X₃ ⟶ ((toDerivedCategory' A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  have := isIso_toDerivedCategory'_map_coneDescShortComplex S hS
  inv ((toDerivedCategory' A).map (coneDescShortComplex S)) ≫
    (quasiIsomorphisms' A).Q.map
      (-((toHomotopyCategory A).map (coneProj S.f) ≫ (quotientShiftIso S.X₁ 1).hom)) ≫
      ((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.app
        ((toHomotopyCategory A).obj S.X₁)

/-- The triangle `(K, L, C(f), f, i, -p)` is distinguished for the admissible-sequence
triangulation of Tag 09KH; this is Tag 09KF. -/
theorem mappingConeTriangle_mem_distTriang {K L : DifferentialGradedModule A} (f : K ⟶ L) :
    mappingConeTriangle f ∈ distTriang (HomotopyCategory A) := by
  rw [distinguishedTriangles_eq]
  exact isDistinguishedTriangle_mappingConeTriangle A f

/-- The triangle `(K, L, C(f), f, i, -p)`, written with the negated third arrow of the cone
triangle, is distinguished for the admissible-sequence triangulation of Tag 09KH. -/
theorem negConeTriangle_mem_distTriang {K L : DifferentialGradedModule A} (f : K ⟶ L) :
    Triangle.mk ((toHomotopyCategory A).map f) ((toHomotopyCategory A).map (coneIncl f))
        (-((toHomotopyCategory A).map (coneProj f) ≫ (quotientShiftIso K 1).hom)) ∈
      distTriang (HomotopyCategory A) :=
  isomorphic_distinguished _ (mappingConeTriangle_mem_distTriang f) _
    (mappingConeTriangleIsoNegMor₃ConeTriangle f).symm

/-- The negated cone projections `-p` are natural in a morphism of short complexes, through the
induced map of cones. -/
private theorem negConeProj_naturality
    {S₁ S₂ : ShortComplex (DifferentialGradedModule A)} (φ : S₁ ⟶ S₂) :
    (-((toHomotopyCategory A).map (coneProj S₁.f) ≫ (quotientShiftIso S₁.X₁ 1).hom)) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
          ((toHomotopyCategory A).map φ.τ₁) =
      (toHomotopyCategory A).map (coneMapOfShortComplexHom φ) ≫
        (-((toHomotopyCategory A).map (coneProj S₂.f) ≫ (quotientShiftIso S₂.X₁ 1).hom)) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg]
  exact congrArg Neg.neg
    (coneTriangleMapOfHomotopy (f₁ := S₁.f) (f₂ := S₂.f) (a := φ.τ₁) (b := φ.τ₂)
      (Homotopy.ofEq φ.comm₁₂.symm)).comm₃

/-- **Stacks Project, Tag 09L0**, in the sign convention of the Stacks project. *"Let `(A, d)` be
a differential graded algebra. The functor `Mod_{(A, d)} → D(A, d)` defined has the natural
structure of a `δ`-functor, with `δ_{K → L → M} = - p ∘ q⁻¹` with `p` and `q` as explained
above."*

Here `D(A, d)` is `DifferentialGradedModule.derivedCategory' A`, the localization at the
quasi-isomorphisms of the homotopy category with the triangulation of Tag 09KH, whose
distinguished triangles are those isomorphic to the triangle of an admissible short exact
sequence, so that `(K, L, C(f), f, i, -p)` is distinguished (Tag 09KF,
`DifferentialGradedModule.mappingConeTriangle_mem_distTriang`). The statement gives a
`δ`-functor structure on the canonical functor together with, for every short exact sequence
`0 → K → L → M → 0`, the comparison `q : C(f) ⟶ M`, `(l, k) ↦ g l`, which restricts to `g`
along the cone inclusion `i` and is a quasi-isomorphism, hence invertible in `D(A, d)`, and the
identification of the connecting morphism with `- p ∘ q⁻¹`: the inverse of `q` followed by the
class of the negated cone projection `-p : C(f) ⟶ K[1]` (composed with the commutation of the
localization with the shift), which is the third arrow of
`DifferentialGradedModule.mappingConeTriangle` by
`DifferentialGradedModule.mappingConeTriangle_mor₃_eq_neg`. Since the remaining fields of a
`δ`-functor structure are `Prop`-valued, this formula determines the structure.

Sign dictionary: the library's default triangulation of the homotopy category,
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, declares the unsigned cone
triangle `(K, L, C(f), f, i, p)` distinguished instead; against it and its localization
`DifferentialGradedModule.derivedCategory` the same statement holds with `δ = p ∘ q⁻¹`, which is
`DifferentialGradedModule.canonicalDeltaFunctorStructure_δ_eq`. A triangle is distinguished for
one structure exactly when negating its third arrow makes it distinguished for the other
(`DifferentialGradedModule.mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃`). -/
@[stacks 09L0 "delta-functor structure with δ = -p ∘ q⁻¹, Stacks sign convention"]
theorem exists_deltaFunctorStructure_δ_eq_neg :
    ∃ d : (toDerivedCategory' A).DeltaFunctorStructure (DifferentialGradedModule A)
        (derivedCategory' A),
      ∀ {S : ShortComplex (DifferentialGradedModule A)} (hS : S.ShortExact),
        (∀ x : (coneObject S.f).M, (coneDescShortComplex S).toFun x = S.g.toFun x.1) ∧
        coneIncl S.f ≫ coneDescShortComplex S = S.g ∧
        quasiIsomorphisms' A ((toHomotopyCategory A).map (coneDescShortComplex S)) ∧
        ∃ _ : IsIso ((toDerivedCategory' A).map (coneDescShortComplex S)),
          d.δ hS =
            inv ((toDerivedCategory' A).map (coneDescShortComplex S)) ≫
              (quasiIsomorphisms' A).Q.map
                (-((toHomotopyCategory A).map (coneProj S.f) ≫ (quotientShiftIso S.X₁ 1).hom)) ≫
                ((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.app
                  ((toHomotopyCategory A).obj S.X₁) := by
  refine ⟨{ δ := fun hS => shortExactδ' hS, distinguished := ?_, δ_naturality := ?_ },
    fun {S} hS => ⟨coneDescShortComplex_toFun_apply S, coneIncl_coneDescShortComplex S,
      (quasiIsomorphisms_map_iff' A _).2 (quasiIso_coneDescShortComplex S hS),
      isIso_toDerivedCategory'_map_coneDescShortComplex S hS, rfl⟩⟩
  · intro S hS
    have hiso := isIso_toDerivedCategory'_map_coneDescShortComplex S hS
    have hcomp := (toDerivedCategory' A).map_comp (coneIncl S.f) (coneDescShortComplex S)
    rw [coneIncl_coneDescShortComplex] at hcomp
    refine isomorphic_distinguished _
      ((quasiIsomorphisms' A).Q.map_distinguished _ (negConeTriangle_mem_distTriang S.f)) _ ?_
    refine (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((toDerivedCategory' A).map (coneDescShortComplex S))).symm ?_ ?_ ?_)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change (toDerivedCategory' A).map S.g ≫
          inv ((toDerivedCategory' A).map (coneDescShortComplex S)) =
        𝟙 _ ≫ (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map (coneIncl S.f))
      rw [Category.id_comp, IsIso.comp_inv_eq]
      exact hcomp
    · change shortExactδ' hS ≫ (CategoryTheory.shiftFunctor (derivedCategory' A) (1 : ℤ)).map
            (𝟙 ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj S.X₁))) =
          inv ((toDerivedCategory' A).map (coneDescShortComplex S)) ≫
            (quasiIsomorphisms' A).Q.map
              (-((toHomotopyCategory A).map (coneProj S.f) ≫ (quotientShiftIso S.X₁ 1).hom)) ≫
            ((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.app
              ((toHomotopyCategory A).obj S.X₁)
      rw [show (CategoryTheory.shiftFunctor (derivedCategory' A) (1 : ℤ)).map
          (𝟙 ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj S.X₁))) = 𝟙 _ from
        CategoryTheory.Functor.map_id _ _]
      exact Category.comp_id _
  · intro S₁ S₂ h₁ h₂ φ
    have hiso₁ := isIso_toDerivedCategory'_map_coneDescShortComplex S₁ h₁
    have hiso₂ := isIso_toDerivedCategory'_map_coneDescShortComplex S₂ h₂
    have hq := congrArg (toDerivedCategory' A).map
      (coneMapOfShortComplexHom_comp_coneDescShortComplex φ)
    rw [Functor.map_comp, Functor.map_comp] at hq
    have hp : (quasiIsomorphisms' A).Q.map
          ((-((toHomotopyCategory A).map (coneProj S₁.f) ≫ (quotientShiftIso S₁.X₁ 1).hom)) ≫
            (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
              ((toHomotopyCategory A).map φ.τ₁)) =
        (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map (coneMapOfShortComplexHom φ) ≫
          (-((toHomotopyCategory A).map (coneProj S₂.f) ≫ (quotientShiftIso S₂.X₁ 1).hom))) :=
      congrArg _ (negConeProj_naturality φ)
    have hξ : ((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory A).obj S₁.X₁) ≫
          (CategoryTheory.shiftFunctor (derivedCategory' A) (1 : ℤ)).map
            ((toDerivedCategory' A).map φ.τ₁) =
        (quasiIsomorphisms' A).Q.map
            ((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
              ((toHomotopyCategory A).map φ.τ₁)) ≫
          ((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory A).obj S₂.X₁) :=
      (((quasiIsomorphisms' A).Q.commShiftIso (1 : ℤ)).hom.naturality
        ((toHomotopyCategory A).map φ.τ₁)).symm
    change shortExactδ' h₁ ≫ _ = _ ≫ shortExactδ' h₂
    rw [shortExactδ', shortExactδ']
    apply (cancel_epi ((toDerivedCategory' A).map (coneDescShortComplex S₁))).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc ((toDerivedCategory' A).map (coneDescShortComplex S₁)), ← hq,
      Category.assoc, IsIso.hom_inv_id_assoc, hξ, ← Category.assoc,
      ← Functor.map_comp, hp, Functor.map_comp, Category.assoc]
    rfl

end StacksConvention

end DifferentialGradedModule

end
