module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonUnconditional

/-!
# Equation 48.8.0.1 for a morphism of quasi-compact quasi-separated schemes

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and let
`a = f^× : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the right adjoint of `Rf_*` given by [Stacks, Tag 0A9E].
For `K, L ∈ D_QCoh(𝒪_Y)` there is a canonical map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`,

adjoint to the composite

  `Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} a(L)) ≅ K ⊗ᴸ_{𝒪_Y} Rf_*(a(L)) ⟶ K ⊗ᴸ_{𝒪_Y} L`

of the inverse of the projection formula ([Stacks, Tag 08EU]) with the identity of `K` tensored
with the trace map `Rf_*a(L) ⟶ L`. At `L = 𝒪_Y`, followed by `a` of the right unitor
`K ⊗ᴸ 𝒪_Y ≅ K`, it gives the map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`

of Equation 48.8.0.1, [Stacks, Tag 0A9S], functorial in `K`.

Every ingredient is the library's own: the functor `a` is
`Stacks.Duality.twistedInverseImage`, available through the instance
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`
([Stacks, Tag 0A9E]); the restriction of `Rf_*` to `D_QCoh` is formed with
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` ([Stacks, Tag 08D5]); the
cotensorator of `Lf^*` and the right unitor are `Stacks.Duality.pullbackCotensorator` and
`Stacks.Duality.quasiCoherentRightUnitor`, from the monoidal structures on `D_QCoh`; and the
invertibility of the projection-formula map is the instance
`Stacks.Duality.isIso_projectionFormulaMap_pullbackCotensorator` ([Stacks, Tag 08EU]). The
quasi-compactness and quasi-separatedness of `f` are found by instance search from those of `X`
and `Y`.

## Main definitions

* `Stacks.Duality.qcqsCompareWithPullbackTensor` — the two-variable map
  `Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)`.
* `Stacks.Duality.qcqsCompareWithPullback` — **[Stacks, Tag 0A9S]**: the map
  `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` as a morphism of functors of `K`.

## Main results

* `Stacks.Duality.homEquiv_symm_qcqsCompareWithPullbackTensor` and
  `Stacks.Duality.projectionFormulaMap_comp_map_qcqsCompareWithPullbackTensor_comp_counit` — the
  defining property of the two-variable map.
* `Stacks.Duality.homEquiv_symm_qcqsCompareWithPullback_app` and
  `Stacks.Duality.projectionFormulaMap_comp_map_qcqsCompareWithPullback_app_comp_counit` — the
  defining property of Equation 48.8.0.1.
* `Stacks.Duality.qcqsCompareWithPullbackTensor_naturality` — naturality of the two-variable
  map in both arguments.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-! ### The two-variable map -/

/-- **The two-variable map of [Stacks, Tag 0A9S]** for a morphism `f : X ⟶ Y` of quasi-compact
quasi-separated schemes: `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`, where `a = f^×` is the right
adjoint of `Rf_*` of [Stacks, Tag 0A9E]. It is adjoint to the inverse of the projection formula
`Rf_*(Lf^*K ⊗ᴸ a(L)) ≅ K ⊗ᴸ Rf_*(a(L))` of [Stacks, Tag 08EU] followed by the identity of `K`
tensored with the trace map `Rf_*a(L) ⟶ L`. -/
@[stacks 0A9S "the two-variable map Lf^*K ⊗ a(L) ⟶ a(K ⊗ L) from which the source obtains the \
  equation, for a morphism of quasi-compact quasi-separated schemes and a = f^× of Tag 0A9E"]
def qcqsCompareWithPullbackTensor (K L : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L) ⟶
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (((quasiCoherentDerivedTensor Y).obj K).obj L) :=
  compareWithPullbackTensor f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (pullbackCotensorator f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) K L

/-- **The defining property of the two-variable map**: its adjoint transpose for `Rf_* ⊣ a` is
the inverse of the projection-formula isomorphism followed by the identity of `K` tensored with
the trace map `Rf_*a(L) ⟶ L`. This determines the map uniquely. -/
@[stacks 0A9S "defining property of the two-variable map: its adjoint is the inverse projection \
  formula of Tag 08EU followed by K tensored with the trace map"]
theorem homEquiv_symm_qcqsCompareWithPullbackTensor (K L : quasiCoherentDerivedCategory Y) :
    ((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv _ _).symm
        (qcqsCompareWithPullbackTensor f K L) =
      inv (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (pullbackCotensorator f)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L)
          K) ≫
        ((quasiCoherentDerivedTensor Y).obj K).map
          ((twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app L) :=
  homEquiv_symm_compareWithPullbackTensor f _ _ _ K L

/-- The defining property of the two-variable map with no inverse in it: the projection formula,
followed by `Rf_*` of the map and the trace map, is the identity of `K` tensored with the trace
map. -/
theorem projectionFormulaMap_comp_map_qcqsCompareWithPullbackTensor_comp_counit
    (K L : quasiCoherentDerivedCategory Y) :
    projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (pullbackCotensorator f)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L)
          K ≫
        (quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
            (qcqsCompareWithPullbackTensor f K L) ≫
          (twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
            (((quasiCoherentDerivedTensor Y).obj K).obj L) =
      ((quasiCoherentDerivedTensor Y).obj K).map
        ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app L) :=
  projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit f _ _ _ K L

/-- The two-variable map is natural in `K` and `L`. -/
theorem qcqsCompareWithPullbackTensor_naturality {K K' L L' : quasiCoherentDerivedCategory Y}
    (h : K ⟶ K') (g : L ⟶ L') :
    ((quasiCoherentDerivedTensor X).map ((quasiCoherentDerivedPullback' f).map h)).app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L) ≫
        ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K')).map
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
              g) ≫
          qcqsCompareWithPullbackTensor f K' L' =
      qcqsCompareWithPullbackTensor f K L ≫
        (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (((quasiCoherentDerivedTensor Y).map h).app L ≫
            ((quasiCoherentDerivedTensor Y).obj K').map g) :=
  compareWithPullbackTensor_naturality f _ _ _ h g

/-! ### Equation 48.8.0.1 -/

/-- **Equation 48.8.0.1 of [Stacks, Tag 0A9S].** Let `f : X ⟶ Y` be a morphism of quasi-compact
and quasi-separated schemes and let `a = f^×` be the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. The canonical map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`,

functorial in `K ∈ D_QCoh(𝒪_Y)`: the two-variable map `qcqsCompareWithPullbackTensor` at
`L = 𝒪_Y`, followed by `a` of the right unitor `K ⊗ᴸ_{𝒪_Y} 𝒪_Y ≅ K`. -/
@[stacks 0A9S]
def qcqsCompareWithPullback :
    quasiCoherentDerivedPullback' f ⋙
        (quasiCoherentDerivedTensor X).flip.obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y)) ⟶
      twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) where
  app K := compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (pullbackCotensorator f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    quasiCoherentRightUnitor K
  naturality _ _ h := compareWithPullback_naturality f _ _ _ _ h

/-- The component of `qcqsCompareWithPullback` at `K` is the two-variable map at `L = 𝒪_Y`
followed by `a` of the right unitor. -/
theorem qcqsCompareWithPullback_app (K : quasiCoherentDerivedCategory Y) :
    (qcqsCompareWithPullback f).app K =
      qcqsCompareWithPullbackTensor f K (derivedStructureSheaf Y) ≫
        (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (quasiCoherentRightUnitor.hom.app K) :=
  rfl

/-- **The defining property of Equation 48.8.0.1**: the adjoint transpose of
`Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` for `Rf_* ⊣ a` is the inverse of the projection formula
`Rf_*(Lf^*K ⊗ᴸ a(𝒪_Y)) ≅ K ⊗ᴸ Rf_*a(𝒪_Y)`, followed by the identity of `K` tensored with the
trace map `Rf_*a(𝒪_Y) ⟶ 𝒪_Y` and the right unitor `K ⊗ᴸ 𝒪_Y ≅ K`. -/
@[stacks 0A9S "defining property of the map: its adjoint is the inverse projection formula of \
  Tag 08EU, then K tensored with the trace map, then the unitor"]
theorem homEquiv_symm_qcqsCompareWithPullback_app (K : quasiCoherentDerivedCategory Y) :
    ((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv _ _).symm
        ((qcqsCompareWithPullback f).app K) =
      inv (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (pullbackCotensorator f)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y)) K) ≫
        ((quasiCoherentDerivedTensor Y).obj K).map
          ((twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
            (derivedStructureSheaf Y)) ≫
          quasiCoherentRightUnitor.hom.app K := by
  rw [qcqsCompareWithPullback_app, Adjunction.homEquiv_naturality_right_symm]
  exact (congrArg (· ≫ quasiCoherentRightUnitor.hom.app K)
    (homEquiv_symm_qcqsCompareWithPullbackTensor f K (derivedStructureSheaf Y))).trans
    (Category.assoc _ _ _)

/-- The defining property of Equation 48.8.0.1 with no inverse in it: the projection formula,
followed by `Rf_*` of `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` and the trace map `Rf_*a(K) ⟶ K`, is the
identity of `K` tensored with the trace map `Rf_*a(𝒪_Y) ⟶ 𝒪_Y`, followed by the right
unitor. -/
theorem projectionFormulaMap_comp_map_qcqsCompareWithPullback_app_comp_counit
    (K : quasiCoherentDerivedCategory Y) :
    projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (pullbackCotensorator f)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y)) K ≫
        (quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
            ((qcqsCompareWithPullback f).app K) ≫
          (twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K =
      ((quasiCoherentDerivedTensor Y).obj K).map
          ((twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
            (derivedStructureSheaf Y)) ≫
        quasiCoherentRightUnitor.hom.app K := by
  have h := congrArg
    (fun z => projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (pullbackCotensorator f)
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (derivedStructureSheaf Y)) K ≫ z)
    (homEquiv_symm_qcqsCompareWithPullback_app f K)
  simp only [Adjunction.homEquiv_counit, IsIso.hom_inv_id_assoc] at h
  exact h

end Stacks.Duality

end
