module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectBoundedQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedLiftGeneral
public import StacksFrontier.Homology.DerivedCategory.SplitLiftTower

/-!
# [Stacks, Tag 09IN]: the complement, and how far down its cohomology can be pushed

`StacksFrontier/AlgebraicGeometry/Perfect/SupportedLiftGeneral.lean` proves [Stacks, Tag 09IM] in
the strengthened form its own proof gives: the complement of `P` in `R|_U` is a finite biproduct
of positive shifts of `P`, and `R|_U ⟶ E|_U` is the projection onto `P` followed by the given
`α`. `StacksFrontier/Homology/DerivedCategory/SplitLiftTower.lean` iterates that construction with
no geometry in it. This module joins the two and registers the remark.

## Main results

* `Stacks.Perfect.SupportedLiftDegree.exists_isPerfect_supported_hom_biprod_sumShifts_isZero`:
  **[Stacks, Tag 09IN]**, both clauses.

## The classes the iteration is run with

The iteration of `DerivedCategory.exists_hom_biprod_iso_of_fibreOracle` separates three classes.

* `Out`, the class the lifts must lie in, is "perfect and supported on `T`"; its stability under
  cones is `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished` together
  with `AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished` on the rotation.
* `Amb`, the class the ambient objects may lie in, is "quasi-coherent cohomology sheaves". Its
  two-out-of-three closures are those of the weak Serre subcategory of quasi-coherent modules,
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`, read through
  `DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished` and its shift-stability.
* `GQ`, the class downstairs that [Stacks, Tag 09IM] accepts, is "a finite biproduct of positive
  shifts of `P`, or `P` itself". The second alternative is forced: the class has to contain `P`,
  which is the input of the first stage, and `P` is not a biproduct of positive shifts of
  itself. It is removed again at the end by a case split; see below.

## Why the final case split is not bookkeeping

The iteration returns a complement `J` with `GQ J`, that is: `J` is a finite biproduct of
positive shifts of `P`, *or* `J` is `P`. In the second case the degree clause already says that
`P` has no cohomology in any degree `≥ n`, so [Stacks, Tag 09IM] applied once with the bound
`n - 1` produces a lift whose complement is a biproduct of positive shifts of `P` and has no
cohomology in any degree `≥ n - 1`, hence none in any degree `≥ n`. Both branches therefore
deliver both clauses, and the statement registered below carries them for one and the same `R`.

## Implementation notes

**`HasDerivedCategory X.Modules` is not found by instance search**, because
`AlgebraicGeometry.Scheme.Modules` is a semireducible `def`; the closures of the quasi-coherent
class are stated at that spelling, so the instance is supplied by hand through
`Stacks.DerivedQCoh.hasDerivedCategorySchemeModules` and passed with `@`. Left to search the
error is a missing `CategoryTheory.Category` instance on the derived category, naming nothing.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in every module
this one consumes.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.GlueingComplexes
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.SupportedLiftTwoOpens (openInclusion)
open Stacks.SumOfPositiveShifts (IsSumOfPositiveShifts)

universe u

namespace Stacks.Perfect.SupportedLiftDegree

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- **The derived category of `𝒪_X`-modules, read at the `AlgebraicGeometry.Scheme.Modules`
spelling.** Instance search does not cross from the ringed-space spelling to this one, because
`AlgebraicGeometry.Scheme.Modules` is a semireducible `def`; this is the crossing of
`Stacks.DerivedQCoh.hasDerivedCategorySchemeModules`, named so that it can be passed explicitly. -/
@[instance_reducible]
def hasDerivedCategoryModules : HasDerivedCategory.{u + 1} X.Modules :=
  Stacks.DerivedQCoh.hasDerivedCategorySchemeModules X (HasDerivedCategory.standard _)

/-! ### The ambient class: quasi-coherent cohomology sheaves -/

/-- Quasi-coherent cohomology, as a property of an object of `D(𝒪_X)`. -/
abbrev HasQuasicoherentHomology (Y : DerivedModules X.toRingedSpace) : Prop :=
  ∀ i : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj Y).IsQuasicoherent

variable {X}

/-- **Quasi-coherent cohomology passes to the middle vertex of a distinguished triangle.** This
is `DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished` for the weak Serre subcategory
of quasi-coherent `𝒪_X`-modules. -/
theorem hasQuasicoherentHomology_obj₂ {Y₁ Y₂ Y₃ : DerivedModules X.toRingedSpace} (f : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedModules X.toRingedSpace))
    (h₁ : HasQuasicoherentHomology X Y₁) (h₃ : HasQuasicoherentHomology X Y₃) :
    HasQuasicoherentHomology X Y₂ :=
  @DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished X.Modules _ _
    (hasDerivedCategoryModules X) (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
    (Triangle.mk f g h) hT h₁ h₃

/-- Quasi-coherent cohomology is stable under every shift. -/
private theorem hasQuasicoherentHomology_shift {Y : DerivedModules X.toRingedSpace} (n : ℤ)
    (hY : HasQuasicoherentHomology X Y) : HasQuasicoherentHomology X (Y⟦n⟧) :=
  @DerivedCategoryB.derivedCategoryB_shift_mem X.Modules _ _ (hasDerivedCategoryModules X) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) n _ hY

/-- **Quasi-coherent cohomology passes to the third vertex of a distinguished triangle**, by
`Stacks.Perfect.SupportedLiftDegree.hasQuasicoherentHomology_obj₂` on the rotation. -/
theorem hasQuasicoherentHomology_obj₃ {Y₁ Y₂ Y₃ : DerivedModules X.toRingedSpace} (f : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedModules X.toRingedSpace))
    (h₁ : HasQuasicoherentHomology X Y₁) (h₂ : HasQuasicoherentHomology X Y₂) :
    HasQuasicoherentHomology X Y₃ :=
  hasQuasicoherentHomology_obj₂ _ _ _ (rot_of_distTriang _ hT) h₂
    (hasQuasicoherentHomology_shift 1 h₁)

/-- **Quasi-coherent cohomology passes to the first vertex of a distinguished triangle**, by
`Stacks.Perfect.SupportedLiftDegree.hasQuasicoherentHomology_obj₂` on the inverse rotation. This
is the closure the fibre device of [Stacks, Tag 09IN] needs and that a single class cannot
give. -/
theorem hasQuasicoherentHomology_obj₁ {Y₁ Y₂ Y₃ : DerivedModules X.toRingedSpace} (f : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedModules X.toRingedSpace))
    (h₂ : HasQuasicoherentHomology X Y₂) (h₃ : HasQuasicoherentHomology X Y₃) :
    HasQuasicoherentHomology X Y₁ :=
  hasQuasicoherentHomology_obj₂ _ _ _ (inv_rot_of_distTriang _ hT)
    (hasQuasicoherentHomology_shift (-1) h₃) h₂

/-! ### The output class: perfect and supported on `T` -/

/-- **Perfectness and support on `T` pass to the third vertex of a distinguished triangle.**
Perfectness is the third-object clause of [Stacks, Tag 08CR]; the support is the two-out-of-three
property of `AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished` applied to the
rotation, whose third vertex is `Y₁⟦1⟧`. -/
theorem isPerfect_supported_obj₃ (T : Set X)
    {Y₁ Y₂ Y₃ : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory (OXMod.{u, u} X.toRingedSpace)))
    (h₁ : IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) Y₁ ∧
      AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T Y₁)
    (h₂ : IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) Y₂ ∧
      AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T Y₂) :
    IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) Y₃ ∧
      AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T Y₃ :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      (Triangle.mk f g h) hT h₁.1 h₂.1,
    AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished _ T
      (Triangle.mk f g h).rotate (rot_of_distTriang _ hT) h₂.2
      (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift _ T 1 h₁.2)⟩

/-! ### [Stacks, Tag 09IN] -/

/-- **[Stacks, Tag 09IN].** Let `X` be a quasi-compact quasi-separated scheme, `U ⊆ X` a
quasi-compact open, `T ⊆ X` closed with `X ∖ T` retrocompact, and `E` an object of `D(𝒪_X)` with
quasi-coherent cohomology. Let `P` be a perfect object of `D(𝒪_U)` supported on `T ∩ U` and
`α : P ⟶ E|_U`. Then for every degree `n` there are a perfect object `R` of `D(𝒪_X)` supported on
`T`, a map `β : R ⟶ E`, an object `Q` of `D(𝒪_U)` and an isomorphism `R|_U ≅ P ⊞ Q` through which
`β|_U` is the projection onto `P` followed by `α`, with `Q` a finite biproduct of positive shifts
of `P` and `Hⁱ(Q) = 0` for every `i ≥ n`.

The two clauses are the remark's two sentences: the shape
`R|_U = P ⊕ P^{⊕n_1}[1] ⊕ ⋯ ⊕ P^{⊕n_m}[m]`, recorded as
`Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts`, and the agreement of the cohomology sheaves
of `R|_U` and of `P` above the given degree, which for a splitting is the vanishing of the
complement there. The degree is fixed first: the other reading, one `R` serving every `n`, is
false, because a perfect object is bounded, so agreement in every degree would make `P ⟶ R|_U`
an isomorphism and extend `P` to a perfect object of `D(𝒪_X)`.

The statement proved here is stronger than the remark in one further respect, and that
strengthening is what makes the iteration possible: `β|_U` is the projection `R|_U ⟶ P` followed
by `α`, not merely a map restricting to `α` on the summand.

**Where the formalisation departs from the source's recipe.** The remark says to repeat the
construction "for the map `P^{⊕n_1}[1] ⊕ ⋯ ⊕ P^{⊕n_m}[m] ⟶ R|_U`", that is, with ambient object
`R` and then to take cones. A map out of `cone(ρ)` extends a map out of `R` only when its
composite with `ρ` vanishes, and with ambient object `R` nothing makes `ρ ≫ β` vanish, so that
route loses the map to `E` at the first cone. The route taken instead carries, at each stage `k`,
the fibre `F_k` of `β_k : R_k ⟶ E` — the first vertex of a distinguished triangle
`F_k ⟶ R_k ⟶ E ⟶ F_k⟦1⟧` — and applies [Stacks, Tag 09IM] with ambient object `F_k`; the cone is
then formed on `ρ := β'' ≫ u` with `u : F_k ⟶ R_k`, and `ρ ≫ β_k = β'' ≫ (u ≫ β_k) = 0` because
`u` and `β_k` are consecutive maps of a distinguished triangle. The octahedral axiom returns both
the new map to `E` and the new fibre at once. The device is
`Stacks.SplitLiftTower.exists_biprod_iso_lift_of_fibre_octahedron` and the iteration is
`DerivedCategory.exists_hom_biprod_iso_of_fibreOracle`.

[Stacks, Tag 09IM] itself is registered on another declaration and is used here
through
`Stacks.Perfect.SupportedLiftGeneral.exists_isPerfect_supported_hom_biprod_sumShifts`. -/
@[stacks 09IN "The complement of `P` in `R|_U` is a finite biproduct of positive shifts of `P`,
and for every degree `n` the construction can be iterated so that the complement has vanishing
cohomology in all degrees `≥ n`, which is the agreement of the cohomology sheaves of `R|_U` and
of `P` above `n`."]
theorem exists_isPerfect_supported_hom_biprod_sumShifts_isZero (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact ((U : X.Opens) : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsRetrocompact (Tᶜ : Set X))
    (E : DerivedModules X.toRingedSpace) (hE : HasQuasicoherentHomology X E)
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hP : IsPerfect.{u, u, u + 1} (X := X.toRingedSpace.restrict U.isOpenEmbedding) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict (openInclusion X U)).obj E) :
    ∀ n : ℤ, ∃ (R : DerivedModules X.toRingedSpace) (β : R ⟶ E),
      (IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) R ∧
          AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R) ∧
        ∃ (Q : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
          (e : (derivedRestrict (openInclusion X U)).obj R ≅ P ⊞ Q),
          IsSumOfPositiveShifts P Q ∧
            (∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))) i).obj Q)) ∧
              e.inv ≫ (derivedRestrict (openInclusion X U)).map β = biprod.fst ≫ α := by
  classical
  intro n
  have : CompactSpace (X.toRingedSpace.restrict U.isOpenEmbedding).carrier :=
    isCompact_iff_compactSpace.mp hU
  obtain ⟨b, hb⟩ := AlgebraicGeometry.RingedSpace.exists_isZero_homology_of_isPerfect P hP
  have hclass : ∀ F : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding),
      (IsSumOfPositiveShifts P F ∨ F = P) →
      IsPerfect.{u, u, u + 1} (X := X.toRingedSpace.restrict U.isOpenEmbedding) F ∧
        AlgebraicGeometry.CohomologySupportedOn
          (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
          (Subtype.val ⁻¹' T) F := by
    rintro F (hF | rfl)
    · exact ⟨Stacks.Perfect.SupportedLiftGeneral.isPerfect_of_isSumOfPositiveShifts.{u} hP hF,
        Stacks.Perfect.SupportedLiftGeneral.cohomologySupportedOn_of_isSumOfPositiveShifts.{u}
          _ hPT hF⟩
    · exact ⟨hP, hPT⟩
  have oracle : ∀ Y : DerivedModules X.toRingedSpace, HasQuasicoherentHomology X Y →
      ∀ F : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding),
        (IsSumOfPositiveShifts P F ∨ F = P) → ∀ m : ℤ,
          (∀ i : ℤ, m < i → IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))) i).obj F)) →
          ∀ a : F ⟶ (derivedRestrict (openInclusion X U)).obj Y,
            ∃ (R' : DerivedModules X.toRingedSpace) (ρ' : R' ⟶ Y)
              (N : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
              (f' : (derivedRestrict (openInclusion X U)).obj R' ≅ F ⊞ N),
              (IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) R' ∧
                  AlgebraicGeometry.CohomologySupportedOn
                    (structureSheafRing X.toRingedSpace) T R') ∧
                (IsSumOfPositiveShifts P N ∨ N = P) ∧
                  (∀ i : ℤ, m - 1 < i → IsZero ((DerivedCategory.homologyFunctor
                    (SheafOfModules.{u} (structureSheafRing
                      (X.toRingedSpace.restrict U.isOpenEmbedding))) i).obj N)) ∧
                    f'.inv ≫ (derivedRestrict (openInclusion X U)).map ρ' =
                      biprod.fst ≫ a := by
    intro Y hY F hF m hm a
    obtain ⟨R', ρ', hOut', N, f', hsum', hc'⟩ :=
      Stacks.Perfect.SupportedLiftGeneral.exists_isPerfect_supported_hom_biprod_sumShifts
        X U hU T hT hTc Y hY F (hclass F hF).1 (hclass F hF).2 a
    refine ⟨R', ρ', N, f', hOut', ?_, ?_, by rw [hc']; simp⟩
    · exact hF.elim (fun hs => Or.inl (hs.trans hsum')) (fun hs => Or.inl (hs ▸ hsum'))
    · exact fun i hi =>
        Stacks.SumOfPositiveShifts.isZero_homology_of_isSumOfPositiveShifts hm hsum' i (by lia)
  let iC : IsTriangulated (DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)) :=
    inferInstance
  let iAdd : ∀ m : ℤ, (shiftFunctor (DerivedModules X.toRingedSpace) m).Additive :=
    fun _ => inferInstance
  let iPt : Pretriangulated (DerivedModules X.toRingedSpace) := inferInstance
  let iTri : IsTriangulated (DerivedModules X.toRingedSpace) := inferInstance
  let iCS : (derivedRestrict (openInclusion X U)).CommShift ℤ := inferInstance
  let iRT : (derivedRestrict (openInclusion X U)).IsTriangulated := inferInstance
  obtain ⟨R, -, -, β, -, J, e, -, hOutR, -, hGQJ, -, hcompat, -, hbound⟩ :=
    @DerivedCategory.exists_hom_biprod_iso_of_fibreOracle
      (SheafOfModules.{u} (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding)))
      _ _ _ iC (DerivedModules X.toRingedSpace) _ _ _ _ iAdd iPt iTri
      (derivedRestrict (openInclusion X U)) iCS iRT
      (fun R => IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R)
      (HasQuasicoherentHomology X)
      (fun F => IsSumOfPositiveShifts P F ∨ F = P)
      (fun Y hY i => AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect
        X Y hY.1 i)
      (fun f g h hTri h₁ h₂ => isPerfect_supported_obj₃ T f g h hTri h₁ h₂)
      (fun f g h hTri h₁ h₂ => hasQuasicoherentHomology_obj₃ f g h hTri h₁ h₂)
      (fun f g h hTri h₂ h₃ => hasQuasicoherentHomology_obj₁ f g h hTri h₂ h₃)
      (fun F hF => hF.elim (fun hs => Or.inl (hs.shift_nonneg 1 (by norm_num)))
        (fun hs => Or.inl (hs ▸ .shift 1 le_rfl)))
      oracle E hE P (Or.inr rfl) b hb α (b - n).toNat
  have hbn : b - n ≤ ((b - n).toNat : ℤ) := Int.self_le_toNat _
  have hb0 : (0 : ℤ) ≤ ((b - n).toNat : ℤ) := Int.natCast_nonneg _
  have hJn : ∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))) i).obj J) :=
    fun i hi => hbound i (by lia)
  rcases hGQJ with hsum | hJP
  · exact ⟨R, β, hOutR, J, e, hsum, hJn, hcompat⟩
  · have hPn : ∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))) i).obj P) :=
      fun i hi => hJP ▸ hJn i hi
    obtain ⟨R', ρ', hOut', J', f', hsum', hc'⟩ :=
      Stacks.Perfect.SupportedLiftGeneral.exists_isPerfect_supported_hom_biprod_sumShifts
        X U hU T hT hTc E hE P hP hPT α
    refine ⟨R', ρ', hOut', J', f', hsum', fun i hi => ?_, by rw [hc']; simp⟩
    exact Stacks.SumOfPositiveShifts.isZero_homology_of_isSumOfPositiveShifts
      (b := n - 1) (fun j hj => hPn j (by lia)) hsum' i (by lia)

end Stacks.Perfect.SupportedLiftDegree

end
