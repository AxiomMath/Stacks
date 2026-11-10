module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.ProjectiveLineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.ProjectiveLinePowerContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineContractionAlgClosed

/-!
# Stacks 0AEM and 0AEN

[Stacks, Tag 0AEM]: let `k` be a field, let `n ≥ 1` and let `Z` be an algebraic space over `k`
which is separated and of finite type over `k`. Every morphism `(ℙ¹_k)^n ⟶ Z` factors as the
projection onto the coordinates in some subset `I ⊆ {1, …, n}` followed by a *finite* morphism.

The contraction process itself runs over the algebraic closure of `k`, where rational points are
available; it is
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_isAlgClosed`. This file
descends its conclusion to `k` and assembles the tag.

* The base change to `k̄` of the power of the projective line over `k` is the power of the
  projective line over `k̄`, compatibly with the coordinate projections
  (`AlgebraicGeometry.Space.projectiveLinePowerFieldExtensionIso` and
  `AlgebraicGeometry.Space.relocalizeRestrict_map_coordinateProjection`), so the conclusion over
  `k̄` is a statement about the base change of the morphism over `k`.
* Base change preserves separatedness and local finite type over the base
  (`AlgebraicGeometry.Space.isSeparated_toBase_relocalizeRestrict` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_toBase_relocalizeRestrict`), so the contraction
  process applies to the base change.
* The factorization and the finiteness of the fibres then descend to `k`, because the coordinate
  projections are split and base change is surjective on points
  (`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_algebraicClosure`).
* Finally a morphism out of a finite power of the projective line all of whose fibres on points
  are finite is finite (`AlgebraicGeometry.Space.isFinite_of_finite_fibres`), which turns the
  factorization into the statement of 0AEM.

[Stacks, Tag 0AEN] is then unconditional: every morphism from the projective line over `k` to a
separated group algebraic space locally of finite type over `k` is constant. Its proof is
`AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant`, which carried the contraction
step of 0AEM as the hypothesis `h0AEMfibres`; that hypothesis is
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres` below.

## Main results

* `AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres`: the contraction step of
  [Stacks, Tag 0AEM] over an arbitrary field, in the shape 0AEN consumes.
* `AlgebraicGeometry.Space.exists_coordinateProjection_isFinite`: **[Stacks, Tag 0AEM].**
* `AlgebraicGeometry.Space.morphism_projectiveLine_constant`: **[Stacks, Tag 0AEN].**

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- **The contraction step of [Stacks, Tag 0AEM] over an arbitrary field.** Let `k` be a field,
let `Z` be an algebraic space over `Spec k` separated and locally of finite type over `Spec k`
and let `f : (ℙ¹_k)^n ⟶ Z`. Then `f` factors through the projection onto the coordinates in some
subset `I ⊆ Fin n` by a morphism all of whose fibres on points are finite.

The process runs over the algebraic closure of `k`, where the base change of `Z` is again an
algebraic space separated and locally of finite type over the base and the base change of
`(ℙ¹_k)^n` is `(ℙ¹_{k̄})^n` compatibly with the coordinate projections; the conclusion descends
by `AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_algebraicClosure`. -/
theorem exists_coordinateProjection_finite_fibres (n : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hlft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    (f : projectiveLinePower k B hk (Fin n) ⟶ Z) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      f = coordinateProjection k B hk n I ≫ g ∧
        ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
              y}.Finite := by
  classical
  refine exists_coordinateProjection_finite_fibres_of_algebraicClosure k B hk n hZ z hsep f ?_
  obtain ⟨I, gg, heq, hfib⟩ := exists_coordinateProjection_finite_fibres_of_isAlgClosed
    (AlgebraicClosure k) B (B.contains_spec_algebraicClosure k hk) n
    (isAlgebraicSpace_relocalizeRestrict_algebraicClosureMap B k hk Z hZ)
    ((baseYoneda_isTerminal B (Spec (CommRingCat.of (AlgebraicClosure k)))
      (B.contains_spec_algebraicClosure k hk)).from _)
    (isSeparated_toBase_relocalizeRestrict B (Spec (CommRingCat.of (AlgebraicClosure k)))
      (Spec (CommRingCat.of k)) (B.contains_spec_algebraicClosure k hk) hk
      (algebraicClosureMap B k hk) z hsep)
    (isLocallyOfFiniteType_toBase_relocalizeRestrict B
      (Spec (CommRingCat.of (AlgebraicClosure k))) (Spec (CommRingCat.of k))
      (B.contains_spec_algebraicClosure k hk) hk (algebraicClosureMap B k hk) hZ z hlft)
    ((projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
        (B.contains_spec_algebraicClosure k hk) (Fin n)).inv ≫
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f)
  refine ⟨I, (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
    (B.contains_spec_algebraicClosure k hk) I).hom ≫ gg, ?_, ?_⟩
  · calc (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f
        = (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) (Fin n)).hom ≫
            (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) (Fin n)).inv ≫
              (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f :=
          (Iso.hom_inv_id_assoc _ _).symm
      _ = (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) (Fin n)).hom ≫
            coordinateProjection (AlgebraicClosure k) B
              (B.contains_spec_algebraicClosure k hk) n I ≫ gg := by rw [heq]
      _ = ((projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) (Fin n)).hom ≫
            coordinateProjection (AlgebraicClosure k) B
              (B.contains_spec_algebraicClosure k hk) n I) ≫ gg :=
          (Category.assoc _ _ _).symm
      _ = ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map
              (coordinateProjection k B hk n I) ≫
            (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) I).hom) ≫ gg := by
          rw [relocalizeRestrict_map_coordinateProjection]
      _ = (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map
            (coordinateProjection k B hk n I) ≫
          (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
            (B.contains_spec_algebraicClosure k hk) I).hom ≫ gg := Category.assoc _ _ _
  · intro w
    have hcomp := pointsMap_comp B (Spec (CommRingCat.of (AlgebraicClosure k)))
      (B.contains_spec_algebraicClosure k hk) _
      (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
        (B.contains_spec_algebraicClosure k hk) I).hom gg
    have hinv := pointsMap_comp B (Spec (CommRingCat.of (AlgebraicClosure k)))
      (B.contains_spec_algebraicClosure k hk) _
      (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
        (B.contains_spec_algebraicClosure k hk) I).hom
      (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
        (B.contains_spec_algebraicClosure k hk) I).inv
    rw [Iso.hom_inv_id, pointsMap_id] at hinv
    have hinj : Function.Injective (pointsMap B
        (Spec (CommRingCat.of (AlgebraicClosure k)))
        (B.contains_spec_algebraicClosure k hk) _
        (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
          (B.contains_spec_algebraicClosure k hk) I).hom) :=
      (Function.leftInverse_iff_comp.2 hinv.symm).injective
    have hset : {x | pointsMap B (Spec (CommRingCat.of (AlgebraicClosure k)))
          (B.contains_spec_algebraicClosure k hk) _
          ((projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
            (B.contains_spec_algebraicClosure k hk) I).hom ≫ gg) x = w} =
        pointsMap B (Spec (CommRingCat.of (AlgebraicClosure k)))
            (B.contains_spec_algebraicClosure k hk) _
            (projectiveLinePowerFieldExtensionIso B k (AlgebraicClosure k) hk
              (B.contains_spec_algebraicClosure k hk) I).hom ⁻¹'
          {x | pointsMap B (Spec (CommRingCat.of (AlgebraicClosure k)))
            (B.contains_spec_algebraicClosure k hk) _ gg x = w} := by
      ext x
      rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, hcomp, Function.comp_apply]
    rw [hset]
    exact (hfib w).preimage hinj.injOn

/-- **Stacks 0AEM.** Let `k` be a field, let `n` be a positive integer, let `Z` be an algebraic
space over `Spec k` separated and of finite type over `Spec k` and let `w : (ℙ¹_k)^n ⟶ Z`. Then
`w` factors as the projection onto the coordinates in some subset `I ⊆ Fin n` followed by a
finite morphism.

The contraction step is
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres`, and a morphism out of a
finite power of the projective line all of whose fibres on points are finite is finite by
`AlgebraicGeometry.Space.isFinite_of_finite_fibres`. -/
@[stacks 0AEM]
theorem exists_coordinateProjection_isFinite (n : ℕ) (hn : 0 < n)
    (Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hft : IsFiniteType B (Spec (CommRingCat.of k)) hk z)
    (w : projectiveLinePower k B hk (Fin n) ⟶ Z) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      w = coordinateProjection k B hk n I ≫ g ∧
        IsFinite B (Spec (CommRingCat.of k)) hk g :=
  exists_coordinateProjection_isFinite_of_exists_finite_fibres k B hk n hn Z hZ z hsep hft w
    (exists_coordinateProjection_finite_fibres k B hk n hZ z hsep hft.1 w)

/-- **Stacks 0AEN.** Let `k` be a field and let `G` be a separated group algebraic space locally
of finite type over `k`. Every morphism from the projective line over `k` to `G` over `Spec k`
is constant: it factors through a section of the structure morphism of `G`.

This is `AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant` with its hypothesis
`h0AEMfibres` — the contraction step of [Stacks, Tag 0AEM] — supplied by
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres`. -/
@[stacks 0AEN]
theorem morphism_projectiveLine_constant
    (G : GroupAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (Over.mk (𝟙 (B.obj hk))))
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _))
    (hsep : IsSeparatedOver B (Spec (CommRingCat.of k)) hk G.obj.X.left)
    (hft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk G.obj.X.hom)
    (f : projectiveLineOverBase k B hk ⟶ G.obj.X) :
    ∃ c : yoneda.obj (Over.mk (𝟙 (B.obj hk))) ⟶ G.obj.X.left,
      c ≫ G.obj.X.hom = 𝟙 _ ∧
        f.left = (projectiveLineOverBase k B hk).hom ≫ c :=
  morphism_projectiveLine_eq_constant k B hk G hsep hft
    (fun n _ _ hZ z hz hzft w =>
      exists_coordinateProjection_finite_fibres k B hk n hZ z hz hzft.1 w) f

end AlgebraicGeometry.Space

end
