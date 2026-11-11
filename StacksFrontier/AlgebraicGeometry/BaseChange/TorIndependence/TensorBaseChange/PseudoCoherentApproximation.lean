module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackFlatPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Local perfect approximation of a pseudo-coherent object

Let `X` be a scheme, `E ∈ D(𝒪_X)` pseudo-coherent, `x ∈ X` and `m ∈ ℤ`. Then there are an open
neighbourhood `U` of `x` and a distinguished triangle

`P ⟶ E|_U ⟶ C ⟶ P[1]`

in `D(𝒪_U)` with `P` perfect and `C` concentrated in degrees `≤ m`, where `E|_U` is the derived
pullback of `E` along the open immersion `U ⟶ X`. Indeed, by `(m + 1)`-pseudo-coherence there is,
near `x`, a strictly perfect complex `P` with a map `P ⟶ E|_U` inducing isomorphisms on cohomology
in degrees `> m + 1` and a surjection in degree `m + 1`; its cone has cohomology only in degrees
`≤ m`.

## Main results

* `AlgebraicGeometry.exists_isPerfect_distTriang_derivedPullback_ι`: the local perfect
  approximation of a pseudo-coherent object, with an arbitrary bound on the cone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Local perfect approximation of a pseudo-coherent object.** For a pseudo-coherent
`E ∈ D(𝒪_X)`, a point `x` and an integer `m`, there are an open neighbourhood `U` of `x` and a
distinguished triangle `P ⟶ L(U.ι)^*E ⟶ C ⟶ P[1]` in `D(𝒪_U)` with `P` perfect and `C` in degrees
`≤ m`. -/
theorem exists_isPerfect_distTriang_derivedPullback_ι {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) E)
    (x : X) (m : ℤ) :
    ∃ (U : X.Opens) (_ : x ∈ U) (T : Triangle (DerivedCategory U.toScheme.Modules)),
      T ∈ distTriang _ ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) T.obj₁ ∧
      T.obj₂ = (derivedPullback U.ι.toLRSHom.toShHom).obj E ∧
      T.obj₃.IsLE m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨U, hxU, P, hP, α, hα₁, hα₂⟩ := hK (m + 1) x
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map α)
  have hZ := DerivedCategory.isLE_three_of_homologyMap_mor₁ _ hT (m + 1)
    (fun i hi => (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α i).2 (hα₁ i hi))
    ((DerivedCategory.epi_homologyFunctor_map_Q_map_iff α (m + 1)).2 hα₂)
  let φ := (derivedPullbackOpenSubspaceQIso X.toRingedSpace U K).symm ≪≫
    (derivedPullbackFunctor
      (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X.toRingedSpace U)).mapIso e
  let T : Triangle (DerivedCategory
      (StrictlyPerfect.OXMod (X.toRingedSpace.restrict U.isOpenEmbedding))) :=
    Triangle.mk (DerivedCategory.Q.map α ≫ φ.hom) (φ.inv ≫ g) δ
  have hTd : T ∈ distTriang _ :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) φ.symm (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
          exact (Category.assoc _ _ _).trans
            ((congrArg (DerivedCategory.Q.map α ≫ ·) φ.hom_inv_id).trans (Category.comp_id _)))
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; rfl)
      (by
        simp only [Iso.refl_hom, Category.id_comp]
        exact (congrArg (T.mor₃ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
          (Category.comp_id _)))
  have hPP : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.toRingedSpace.restrict U.isOpenEmbedding) T.obj₁ :=
    Stacks.Cohomology.PerfectDirectSummands.isPerfect_Q_obj_of_isStrictlyPerfect P hP
  have hT₃ : T.obj₃.IsLE m := by
    rw [show m + 1 - 1 = m by lia] at hZ
    exact hZ
  exact ⟨U, hxU, T, hTd, hPP, rfl, hT₃⟩

end AlgebraicGeometry
