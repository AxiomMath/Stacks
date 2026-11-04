module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryCone
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TopDegreeInductionStep

/-!
# Quasi-coherence of the cohomology travels to the cone of the induction's triangle

Let `S` be a scheme.  The induction of Stacks 08HE (2) ⇒ (1),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`, carries a predicate `P` on
objects of `D(𝒪_S)` from `E` to the third vertex of the triangle its step produces; in the
application of Stacks 0DII, `P E` is the conjunction of "`ε^*E` is `m`-pseudo-coherent" and
"the cohomology sheaves of `E` are quasi-coherent".  The first conjunct's propagation is
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleConePropagation.lean`.  This
module supplies the **second**, which is a statement about `D(𝒪_S)` with no `ε` in it.

## Main results

* `AlgebraicGeometry.isQuasicoherent_isWeakSerre_zariskiRingedSite`: the quasi-coherent
  `𝒪_S`-modules are a weak Serre subcategory, at the spelling
  `AlgebraicGeometry.RingedSite.ringSheaf` of the structure sheaf which the induction's statements
  use.
* `AlgebraicGeometry.isQuasicoherent_homology_obj₃_of_distinguished_zariskiRingedSite`:
  **quasi-coherence of all cohomology sheaves travels to the cone of a distinguished triangle of
  `D(𝒪_S)`.**
* `AlgebraicGeometry.isQuasicoherent_homology_shift_singleFunctor_obj_free`: the cohomology of the
  induction triangle's first vertex, `(𝒪_S^{⊕t}[0])[-n]`, is quasi-coherent — so that the
  propagation needs no hypothesis there.
* `AlgebraicGeometry.exists_distTriang_free_of_lift_isQuasicoherent`: **the composition.**  It is
  `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` with the quasi-coherence half of
  `P` on the third vertex added to the conclusion, which is the second of the two data
  `isPseudoCoherentFrom_of_descentStep` asks of its step.  Its conclusion also *names* the first
vertex, `Nonempty (T.obj₁ ≅ 𝒪_S^{⊕t}[n])`, so that a further standing hypothesis can be read on
the triangle it produces rather than on a triangle of its own.

## Implementation notes

The mathematics is the long exact sequence of the triangle in cohomology together with closure of
the quasi-coherent modules under kernels, cokernels and extensions, and both halves are in the library:
the closure is
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`, and reading it
along a triangle is `DerivedCategoryB.derivedCategoryB_mem_obj₃_of_distinguished`
(`StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategoryCone.lean`), the rotation of the
existing middle-vertex form.  Nothing about quasi-coherence is reproved here.

Two spellings have to be crossed.  `AlgebraicGeometry.RingedSite.ringSheaf` is a `def`, so
`S.zariskiRingedSite.ringSheaf` does not reduce to `S.ringCatSheaf` at instance transparency even
though the two are equal by `rfl` (`AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf`); the
weak Serre statement is stated at the second spelling and the induction is stated at the first, so
`isQuasicoherent_isWeakSerre_zariskiRingedSite` writes out the retyping once.  And
`DerivedCategoryB.derivedCategoryB` of `SheafOfModules.isQuasicoherent` is by definition
"every cohomology sheaf is quasi-coherent", which is the form the predicate `P` of the induction
takes; the statements below are therefore phrased with the explicit `∀ j` and converted at use.

`exists_distTriang_free_of_lift_isQuasicoherent` repeats the lines that build the triangle in
`AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` rather than invoking it, for the
same reason as its `ε`-side counterpart
`AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift_mapDerivedCategory`: that theorem
binds its triangle existentially, so the identity of the first vertex — which is what makes the
quasi-coherence of its cohomology available — is not recoverable from its conclusion.  Nothing in
the repeat is weaker; the conclusion here is that one with a further conjunct.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- **The quasi-coherent `𝒪_S`-modules are a weak Serre subcategory**, written at the spelling
`AlgebraicGeometry.RingedSite.ringSheaf` of the structure sheaf of the small Zariski ringed site.

This is `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` retyped.
The retyping is definitional — `AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf` is `rfl` —
and it is written out because `AlgebraicGeometry.RingedSite.ringSheaf` is a `def`, so instance
search does not cross between the two spellings. -/
public theorem isQuasicoherent_isWeakSerre_zariskiRingedSite :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherent
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]

/-- **Quasi-coherence of the cohomology sheaves travels to the cone.**  Let `T` be a distinguished
triangle of `D(𝒪_S)`.  If every cohomology sheaf of `T.obj₁` and of `T.obj₂` is quasi-coherent,
then so is every cohomology sheaf of `T.obj₃`.

This is the long exact sequence of the triangle in cohomology together with closure of the
quasi-coherent `𝒪_S`-modules under kernels, cokernels and extensions: the quasi-coherent modules
form a weak Serre subcategory, and
`DerivedCategoryB.derivedCategoryB_mem_obj₃_of_distinguished` reads that along the triangle. -/
public theorem isQuasicoherent_homology_obj₃_of_distinguished_zariskiRingedSite
    (T : Triangle (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))))
    (h₁ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        T.obj₁).IsQuasicoherent)
    (h₂ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        T.obj₂).IsQuasicoherent)
    (j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        T.obj₃).IsQuasicoherent :=
  DerivedCategoryB.derivedCategoryB_mem_obj₃_of_distinguished _
    (isQuasicoherent_isWeakSerre_zariskiRingedSite S) T hT h₁ h₂ j

/-- **The cohomology of the induction triangle's first vertex is quasi-coherent.**  A finite free
`𝒪_S`-module is quasi-coherent, being locally free, so `(𝒪_S^{⊕t}[0])[-n]` — `𝒪_S^{⊕t}` in
cohomological degree `n`, in the shape the induction step of Stacks 08HE (2) ⇒ (1) produces it —
has quasi-coherent cohomology in every degree. -/
public theorem isQuasicoherent_homology_shift_singleFunctor_obj_free (n : ℤ) (ι : Type u)
    (j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
      (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
              0).obj
          (SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
              ι))⟦(-n : ℤ)⟧)).IsQuasicoherent :=
  DerivedCategoryB.derivedCategoryB_shift_mem _
    (isQuasicoherent_isWeakSerre_zariskiRingedSite S) (-n)
    (DerivedCategoryB.derivedCategoryB_singleFunctor_obj _
      (isQuasicoherent_isWeakSerre_zariskiRingedSite S) 0
      (inferInstance :
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          S.zariskiRingedSite.O)) ι).IsQuasicoherent)) j

/-- **The triangle of the induction step of Stacks 08HE (2) ⇒ (1), with quasi-coherence of the
cohomology carried to the third vertex.**

This is `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` together with the extra
conclusion that the cohomology sheaves of the third vertex are quasi-coherent, given that those of
`E` are: the second of the two data that
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks of its step, with the
quasi-coherence half of its predicate `P` discharged on the cone.  No hypothesis is placed on the
first vertex — it is `𝒪_S^{⊕t}` in a single degree, whose cohomology is quasi-coherent by
`isQuasicoherent_homology_shift_singleFunctor_obj_free`.

The conclusion carries one conjunct that
`AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` does not: the identification of the
first vertex with `𝒪_S^{⊕t}[n]`.  Without it the triangle is a black box, and a *second* standing
hypothesis — clause (2) of Stacks 08HE, say — could not be read on this triangle but only on one
rebuilt beside it, so that the two conjuncts of `P` would never meet on a single cone.  With it,
`AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale_quasicoherent` adds that
clause to this very triangle. -/
public theorem exists_distTriang_free_of_lift_isQuasicoherent (m n : ℤ)
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    [DerivedCategory.IsLE E n] (ι : Type u) [Finite ι]
    (φ : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
        ι ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) n).obj
          E)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
          ι) ⟶ E⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (E⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift E n φ)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent) :
    ∃ T : Triangle (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))),
      T ∈ distTriang (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) ∧
        Nonempty (T.obj₂ ≅ E) ∧ S.zariskiRingedSite.IsPseudoCoherentFrom T.obj₁ m ∧
          Nonempty (T.obj₁ ≅ (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
              n).obj
              (SheafOfModules.free
                (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι)) ∧
          (∀ j : ℤ, ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
              j).obj T.obj₃).IsQuasicoherent) ∧
            ∀ j : ℤ, n ≤ j →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
                  S.zariskiRingedSite.O)) j).obj T.obj₃) := by
  have := hφ
  -- `𝒪_S^{⊕t}` in degree zero, shifted by `-n`, is `𝒪_S^{⊕t}` in degree `n`.
  let e : ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
              0).obj
          (SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι))⟦(-n : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) n).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
          ι) :=
    ((DerivedCategory.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          S.zariskiRingedSite.O))).shiftIso (-n) n 0 (by omega)).app
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι)
  have hK : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        (((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
                0).obj
            (SheafOfModules.free
              (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
                ι))⟦(-n : ℤ)⟧)) :=
    fun j hj =>
      IsZero.of_iso (DerivedCategory.isZero_of_isLE _ n j hj)
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
            j).mapIso e)
  obtain ⟨Q, g, h, hT, hQ⟩ := RingedSite.exists_distTriang_isZero_homology_obj₃_of_epi n
    (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg E n).hom) hK
    (fun j hj => DerivedCategory.isZero_of_isLE E n j hj)
    (DerivedCategory.epi_homologyMap_shiftBack_of_lift E n f _ hf
      (DerivedCategory.epi_homologyMap_singleMapTruncGEZeroShift E n φ))
  refine ⟨Triangle.mk (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg E n).hom) g h, hT, ⟨Iso.refl _⟩,
    RingedSite.isPseudoCoherentFrom_of_iso S.zariskiRingedSite m
      (S.zariskiRingedSite.isPseudoCoherentFrom_singleFunctor_obj_free n m ι) e,
    ⟨e⟩, ?_, hQ⟩
  exact isQuasicoherent_homology_obj₃_of_distinguished_zariskiRingedSite S _ hT
    (isQuasicoherent_homology_shift_singleFunctor_obj_free S n ι) hE

end AlgebraicGeometry

end
