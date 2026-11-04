module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts

/-!
# Cohomology preserves direct sums

Let `A` be an abelian category in which the direct sum functor
`colim : (Discrete J ⥤ A) ⥤ A` preserves homology — Grothendieck's axiom AB4 for the index type
`J`, which a Grothendieck abelian category satisfies for every `J` in its own universe. Then the
homology functor of short complexes, the cohomology functors of cochain complexes and the
cohomology functors of the derived category all *preserve* `J`-indexed direct sums: not merely
`Hⁿ(⨁ⱼ Kⱼ) ≅ ⨁ⱼ Hⁿ(Kⱼ)`, but the canonical comparison assembled from the injections is an
isomorphism.

## Main results

* `Stacks.Duality.preservesColimitsOfShape_shortComplexHomologyFunctor` — the homology functor of
  short complexes preserves `J`-indexed direct sums.
* `Stacks.Duality.preservesColimitsOfShape_homologicalComplexHomologyFunctor` — the same for the
  cohomology functors of cochain complexes.
* `Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor` — the same for the cohomology
  functors of the derived category of a Grothendieck abelian category.
* `Stacks.Duality.isLE_sigmaObj` and `Stacks.Duality.isGE_sigmaObj` — a direct sum of objects of
  `D(A)` lying in degrees `≤ n`, respectively in degrees `≥ n`, again lies in those degrees.

## Implementation notes

`Stacks.Duality.homologyCoprodShortComplexIso` already produces the isomorphism
`Hⁿ(⨁ⱼ Kⱼ) ≅ ⨁ⱼ Hⁿ(Kⱼ)`. What is added here is that the comparison assembled from the injections
is the isomorphism, which is what upgrades the isomorphism to a `PreservesColimitsOfShape`
instance, and that is the shape in which the compactness hypothesis of Brown representability is
stated.

The argument is run first for a diagram of short complexes of the special form
`(ShortComplex.functorEquivalence _ _).functor.obj T`, coming from a short complex `T` of
`Discrete J`-diagrams. For such a diagram the evaluation of `T` at `j` *is* the `j`-th object of
the diagram and the direct sum of the diagram *is* `T.map colim`, so the only input needed is
`CategoryTheory.ShortComplex.homologyMap_mapNatTrans` for the natural transformation
`Stacks.Duality.evaluationToColim` from evaluation at `j` to the direct-sum functor, whose
component at a diagram is the colimit injection: that lemma says exactly that the comparison
isomorphisms `ShortComplex.mapHomologyIso` for evaluation and for `colim` intertwine the injection
of the homologies with the homology of the injection. A general diagram is isomorphic to one of
that form — `ShortComplex.functorEquivalence` is an equivalence — and preservation of a colimit is
invariant under isomorphism of the diagram. Running the chase only in the special case avoids
comparing `(ShortComplex.functorEquivalence _ _).functor.obj T` with a general diagram
objectwise, which is where the definitional-unfolding obstructions of that equivalence live.

The passage from cochain complexes to the derived category uses that `DerivedCategory.Q`
preserves direct sums (`Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts`) and is
essentially surjective, so every `Discrete J`-diagram in `D(A)` is isomorphic to the image of one
in `C(A)`, where the statement is the cochain-complex one read through
`DerivedCategory.homologyFunctorFactors`.

## References

* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace Stacks.Duality

/-! ### Direct sums of short complexes -/

section

variable {A : Type u} [Category.{v} A] [Abelian A] {J : Type w} [HasCoproductsOfShape J A]

/-- The colimit injection at `j`, read as a natural transformation from evaluation at `j` to the
direct-sum functor `colim : (Discrete J ⥤ A) ⥤ A`. -/
@[simps]
def evaluationToColim (j : Discrete J) :
    (evaluation (Discrete J) A).obj j ⟶ colim (J := Discrete J) (C := A) where
  app F := colimit.ι F j
  naturality _ _ α := (ι_colimMap α j).symm

variable (T : ShortComplex (Discrete J ⥤ A))

/-- The direct sum `T.map colim` of the diagram of short complexes attached to a short complex
`T` of `Discrete J`-diagrams, with the injections `T.mapNatTrans` of the colimit injections. -/
@[simps]
def mapColimCofan : Cocone ((ShortComplex.functorEquivalence (Discrete J) A).functor.obj T) where
  pt := T.map (colim (J := Discrete J) (C := A))
  ι := Discrete.natTrans fun j => T.mapNatTrans (evaluationToColim j)

/-- `Stacks.Duality.mapColimCofan` is a direct sum: direct sums of short complexes are computed
componentwise, and componentwise it is the direct sum of the three diagrams of `T`. -/
def mapColimIsColimit : IsColimit (mapColimCofan T) :=
  ShortComplex.isColimitOfIsColimitπ _ (colimit.isColimit T.X₁) (colimit.isColimit T.X₂)
    (colimit.isColimit T.X₃)

variable [(colim (J := Discrete J) (C := A)).PreservesHomology]

/-- The comparison isomorphisms of `ShortComplex.mapHomologyIso` for the evaluation functors
assemble into an isomorphism between the diagram of homologies of the diagram of short complexes
attached to `T` and the diagram `T.homology` of homologies of `T`. -/
def mapHomologyDiagramIso :
    (ShortComplex.functorEquivalence (Discrete J) A).functor.obj T ⋙
        ShortComplex.homologyFunctor A ≅ T.homology :=
  Discrete.natIso fun j =>
    (T.mapHomologyIso ((evaluation (Discrete J) A).obj j) :
      ((ShortComplex.functorEquivalence (Discrete J) A).functor.obj T ⋙
        ShortComplex.homologyFunctor A).obj j ≅ T.homology.obj j)

/-- **Homology preserves the direct sum of a diagram of short complexes coming from a short
complex of diagrams.** -/
def isColimitMapHomologyCofan :
    IsColimit ((ShortComplex.homologyFunctor A).mapCocone (mapColimCofan T)) :=
  ((IsColimit.precomposeHomEquiv (mapHomologyDiagramIso T) (colimit.cocone T.homology)).2
      (colimit.isColimit T.homology)).ofIsoColimit
    (Cocone.ext (T.mapHomologyIso (colim (J := Discrete J) (C := A))).symm fun j =>
      (Category.assoc _ _ _).trans
        (ShortComplex.homologyMap_mapNatTrans T (evaluationToColim (A := A) j)).symm)

/-- **Homology of short complexes preserves direct sums**, as soon as the direct-sum functor
`colim : (Discrete J ⥤ A) ⥤ A` preserves homology. -/
theorem preservesColimitsOfShape_shortComplexHomologyFunctor :
    PreservesColimitsOfShape (Discrete J) (ShortComplex.homologyFunctor A) where
  preservesColimit {K} :=
    have : PreservesColimit
        (((ShortComplex.functorEquivalence (Discrete J) A).inverse ⋙
          (ShortComplex.functorEquivalence (Discrete J) A).functor).obj K)
        (ShortComplex.homologyFunctor A) :=
      preservesColimit_of_preserves_colimit_cocone (mapColimIsColimit _)
        (isColimitMapHomologyCofan _)
    preservesColimit_of_iso_diagram _
      ((ShortComplex.functorEquivalence (Discrete J) A).counitIso.app K)

end

/-! ### Direct sums of cochain complexes -/

section

variable (A : Type u) [Category.{v} A] [Abelian A] {J : Type w} [HasCoproductsOfShape J A]
  [(colim (J := Discrete J) (C := A)).PreservesHomology]

/-- **Cohomology of cochain complexes preserves direct sums** — Grothendieck's axiom AB4 in the
form that the canonical map `⨁ⱼ Hⁿ(Kⱼ) ⟶ Hⁿ(⨁ⱼ Kⱼ)` is an isomorphism. -/
theorem preservesColimitsOfShape_homologicalComplexHomologyFunctor (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) :=
  have := preservesColimitsOfShape_shortComplexFunctor A (J := J) n
  have := preservesColimitsOfShape_shortComplexHomologyFunctor (A := A) (J := J)
  inferInstanceAs (PreservesColimitsOfShape (Discrete J)
    (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n ⋙
      ShortComplex.homologyFunctor A))

end

/-! ### Direct sums in the derived category -/

section

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{w'} A] {J : Type w}

/-- **Cohomology on the derived category preserves direct sums.** Direct sums in `D(A)` are
computed by termwise direct sums of complexes, because the localization `Q : C(A) ⥤ D(A)`
preserves them, and cohomology of a termwise direct sum is the direct sum of the cohomologies. -/
theorem preservesColimitsOfShape_derivedHomologyFunctor (n : ℤ) :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A n) where
  preservesColimit {F} := by
    have hQ := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts A J
    set C : Discrete J ⥤ CochainComplex A ℤ :=
      Discrete.functor fun j => DerivedCategory.Q.objPreimage (F.obj ⟨j⟩) with hC
    have hfac : PreservesColimit C (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A n) :=
      have := preservesColimitsOfShape_homologicalComplexHomologyFunctor A (J := J) n
      preservesColimit_of_natIso _ (DerivedCategory.homologyFunctorFactors A n).symm
    have : PreservesColimit (C ⋙ DerivedCategory.Q) (DerivedCategory.homologyFunctor A n) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves DerivedCategory.Q (colimit.isColimit C))
        (isColimitOfPreserves (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A n)
          (colimit.isColimit C))
    exact preservesColimit_of_iso_diagram _
      (Discrete.natIso (F := C ⋙ DerivedCategory.Q) (G := F) fun j =>
        DerivedCategory.Q.objObjPreimageIso (F.obj j))

end

/-! ### Cohomological bounds and direct sums -/

section Bounds

/-- A direct sum of zero objects is a zero object: its identity vanishes, because it does so on
every coprojection. -/
theorem isZero_sigmaObj {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {J : Type w}
    (X : J → C) [HasCoproduct X] (hX : ∀ j, IsZero (X j)) : IsZero (∐ X) := by
  refine (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ ?_)
  rw [comp_zero, Category.comp_id]
  exact (hX j).eq_of_src _ _

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{w'} A] {J : Type w}

attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

/-- If the degree-`i` cohomology of every member of a family vanishes, so does that of their
direct sum: cohomology preserves direct sums, and a direct sum of zero objects is zero. -/
theorem isZero_homologyFunctor_sigmaObj (K : J → DerivedCategory A) (i : ℤ)
    (hK : ∀ j, IsZero ((DerivedCategory.homologyFunctor A i).obj (K j))) :
    IsZero ((DerivedCategory.homologyFunctor A i).obj (∐ K)) :=
  have := preservesColimitsOfShape_derivedHomologyFunctor A (J := J) i
  (isZero_sigmaObj (fun j ↦ (DerivedCategory.homologyFunctor A i).obj (K j)) hK).of_iso
    (PreservesCoproduct.iso (DerivedCategory.homologyFunctor A i) K)

/-- **A direct sum of objects of `D(A)` lying in degrees `≤ n` lies in degrees `≤ n`.** -/
theorem isLE_sigmaObj (K : J → DerivedCategory A) (n : ℤ) (hK : ∀ j, (K j).IsLE n) :
    (∐ K).IsLE n :=
  (DerivedCategory.isLE_iff _ n).2 fun i hi ↦
    isZero_homologyFunctor_sigmaObj A K i fun j ↦
      have := hK j
      DerivedCategory.isZero_of_isLE (K j) n i hi

/-- **A direct sum of objects of `D(A)` lying in degrees `≥ n` lies in degrees `≥ n`.** -/
theorem isGE_sigmaObj (K : J → DerivedCategory A) (n : ℤ) (hK : ∀ j, (K j).IsGE n) :
    (∐ K).IsGE n :=
  (DerivedCategory.isGE_iff _ n).2 fun i hi ↦
    isZero_homologyFunctor_sigmaObj A K i fun j ↦
      have := hK j
      DerivedCategory.isZero_of_isGE (K j) n i hi

end Bounds

end Stacks.Duality

end
