module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatPushforwardHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.HomotopyColimitDualSections
import StacksCore.Tactic.StacksAttribute

/-!
# The derived sections of a flat pullback as a homotopy colimit

Let `A` be a ring and `f : U ⟶ X` a flat morphism of algebraic spaces of finite presentation
over `A`. Then `RΓ(U, Lf^*K)` is, functorially in `K ∈ D_QCoh(𝒪_X)`, a homotopy colimit
`hocolim RHom_X(Lₙ, K)` for an inverse system of perfect objects `Lₙ`, and a homotopy colimit
`hocolim RΓ(X, Eₙ ⊗^L K)` for a system of perfect objects `Eₙ` (Stacks 0CRW).

"Functorially in `K`" is formalized by natural maps `RΓ(X, Eₙ ⊗^L -) ⟶ RΓ(U, Lf^* -)` (resp.
`RHom_X(Lₙ, -) ⟶ RΓ(U, Lf^* -)`) which exhibit `RΓ(U, Lf^*K)` as the homotopy colimit for every
`K` (`CategoryTheory.Pretriangulated.IsHomotopyColimitCocone`). Derived sections over the base
`Spec A` take values in `D(Γ(Spec A, 𝒪))`.

## Main results

* `AlgebraicGeometry.Space.exists_isHomotopyColimitCocone_derivedSections_tensor_of_isFlat`:
  Stacks 0CRW (2).
* `AlgebraicGeometry.Space.exists_isHomotopyColimitCocone_derivedHom_of_isFlat`: Stacks 0CRW (1).

## References

* [Stacks Project, Tag 0CRW](https://stacks.math.columbia.edu/tag/0CRW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))

/-- The base `Spec A`, as an object of the big fppf site over itself, is affine. -/
instance isAffine_toScheme_baseSiteObj :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseSiteObj B (Spec (.of A)) hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- A morphism between algebraic spaces of finite presentation over `Spec A` is quasi-compact and
quasi-separated. -/
theorem isQuasiCompact_isQuasiSeparated_of_isFinitePresentation_toBase
    {U X : AlgebraicSpaces B (Spec (.of A)) hA} (f : U ⟶ X)
    (hX : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hU : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U).hom) :
    IsQuasiCompact B (Spec (.of A)) hA f.hom ∧ IsQuasiSeparated B (Spec (.of A)) hA f.hom := by
  have hZ := BigFppfSite.contains_terminal B
  have hT : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ
      (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A)) hA _ hZ
      ⟨_, inferInstanceAs (QuasiSeparatedSpace (Spec (.of A))),
        ⟨Functor.RepresentableBy.yoneda _⟩⟩
  have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA hZ X.2 hT hX.2.2
  have hUqc := isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of A)) hA _ hU.2.1
  have hUqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA hZ U.2 hT hU.2.2
  exact ⟨isQuasiCompact_of_isQuasiCompactSpace B (Spec (.of A)) hA hZ X.2 hXqs hUqc f.hom,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (Spec (.of A)) hA hZ U.2 hUqs f.hom⟩

/-- **Stacks 0CRW (2).** Let `A` be a ring and `f : U ⟶ X` a flat morphism of algebraic spaces
of finite presentation over `A`. There is a system `(Eₙ)` of perfect objects of `D(𝒪_X)` with
`RΓ(U, Lf^*K) = hocolim RΓ(X, Eₙ ⊗^L K)` in `D(A)` functorially in `K ∈ D_QCoh(𝒪_X)`: natural
maps `RΓ(X, Eₙ ⊗^L -) ⟶ RΓ(U, Lf^* -)` exhibit the homotopy colimit at every such `K`. -/
@[stacks 0CRW "part (2)"]
theorem exists_isHomotopyColimitCocone_derivedSections_tensor_of_isFlat
    {U X : AlgebraicSpaces B (Spec (.of A)) hA} (f : U ⟶ X)
    (hX : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hU : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U).hom)
    (hf : IsFlat B (Spec (.of A)) hA f.hom) :
    ∃ E : ℕ ⥤ DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      (∀ n, (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).IsPerfect (E.obj n)) ∧
      ∃ ι : ∀ n, (smallEtaleDerivedTensor B (Spec (.of A)) hA X).obj (E.obj n) ⋙
          derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X) ⋙
            representedAffineDerivedSections B (Spec (.of A)) hA
              (baseSiteObj B (Spec (.of A)) hA) ⟶
          smallEtaleDerivedModulePullback B (Spec (.of A)) hA f ⋙
            derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U) ⋙
              representedAffineDerivedSections B (Spec (.of A)) hA
                (baseSiteObj B (Spec (.of A)) hA),
        ∀ K, QcohDerived B (Spec (.of A)) hA X K →
          IsHomotopyColimitCocone
            (E ⋙ (smallEtaleDerivedTensor B (Spec (.of A)) hA X).flip.obj K ⋙
              derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X) ⋙
                representedAffineDerivedSections B (Spec (.of A)) hA
                  (baseSiteObj B (Spec (.of A)) hA))
            fun n ↦ (ι n).app K := by
  obtain ⟨E, hE, hP⟩ := exists_isHomotopyColimit_isPerfect_derivedPushforward_of_isFlat B hA f hX
    hU hf
  obtain ⟨hfqc, hfqs⟩ := isQuasiCompact_isQuasiSeparated_of_isFinitePresentation_toBase B hA f hX hU
  exact ⟨E, hE, exists_isHomotopyColimitCocone_derivedSections_pullback_of_isHomotopyColimit
    (baseSiteObj B (Spec (.of A)) hA) f (toBase B (Spec (.of A)) hA X)
    (toBase B (Spec (.of A)) hA U)
    ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _ |> ObjectProperty.hom_ext _)
    hfqc hfqs hX.2.1 hX.2.2 E hE hP⟩

/-- **Stacks 0CRW (1).** Let `A` be a ring and `f : U ⟶ X` a flat morphism of algebraic spaces
of finite presentation over `A`. There is an inverse system `(Lₙ)` of perfect objects of
`D(𝒪_X)` with `RΓ(U, Lf^*K) = hocolim RHom_X(Lₙ, K)` in `D(A)` functorially in
`K ∈ D_QCoh(𝒪_X)`, where `RHom_X(L, K) = RΓ(X, R𝓗om(L, K))`: natural maps
`RHom_X(Lₙ, -) ⟶ RΓ(U, Lf^* -)` exhibit the homotopy colimit at every such `K`. -/
@[stacks 0CRW "part (1)"]
theorem exists_isHomotopyColimitCocone_derivedHom_of_isFlat
    {U X : AlgebraicSpaces B (Spec (.of A)) hA} (f : U ⟶ X)
    (hX : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hU : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U).hom)
    (hf : IsFlat B (Spec (.of A)) hA f.hom) :
    ∃ L : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      (∀ n, (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).IsPerfect (L.obj n)) ∧
      ∃ ι : ∀ n, (smallEtaleDerivedSheafHom B (Spec (.of A)) hA X).obj (op (L.obj (op n))) ⋙
          derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X) ⋙
            representedAffineDerivedSections B (Spec (.of A)) hA
              (baseSiteObj B (Spec (.of A)) hA) ⟶
          smallEtaleDerivedModulePullback B (Spec (.of A)) hA f ⋙
            derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U) ⋙
              representedAffineDerivedSections B (Spec (.of A)) hA
                (baseSiteObj B (Spec (.of A)) hA),
        ∀ K, QcohDerived B (Spec (.of A)) hA X K →
          IsHomotopyColimitCocone
            (L.rightOp ⋙ (smallEtaleDerivedSheafHom B (Spec (.of A)) hA X).flip.obj K ⋙
              derivedModulePushforward B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X) ⋙
                representedAffineDerivedSections B (Spec (.of A)) hA
                  (baseSiteObj B (Spec (.of A)) hA))
            fun n ↦ (ι n).app K := by
  obtain ⟨E, hE, ι, hι⟩ :=
    exists_isHomotopyColimitCocone_derivedSections_tensor_of_isFlat B hA f hX hU hf
  exact exists_isHomotopyColimitCocone_derivedHom_of_tensor (baseSiteObj B (Spec (.of A)) hA) f
    (toBase B (Spec (.of A)) hA X) (toBase B (Spec (.of A)) hA U) E hE ι hι

end AlgebraicGeometry.Space

end
