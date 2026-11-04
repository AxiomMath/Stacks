module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Absolute Noetherian approximation of an algebraic space with no points

An algebraic space with no points is its own Noetherian approximation, over the one-element
directed set. Every section of a presheaf with no points lives over an object of the site whose
underlying scheme is empty, and so does every section of its view over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.Space.isEmpty_of_isEmpty_points`: a section of a presheaf with no points
  lives over an object with empty underlying scheme.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_forall_isEmpty`: an algebraic space all of
  whose sections live over empty schemes is quasi-compact.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_forall_isEmpty`: it is quasi-separated.
* `AlgebraicGeometry.Space.isFiniteType_viewOverIntegers_of_forall_isEmpty`: it is of finite type
  over `Spec ℤ`.
* `AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_isEmpty_points`: an
  algebraic space over `Spec ℤ` with no points has a Noetherian approximation satisfying the
  convention of Section 70.2.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A section of a presheaf with no points lives over an object of the site whose underlying
scheme is empty. -/
theorem isEmpty_of_isEmpty_points (h : IsEmpty (points B S hS F)) {A : BigFppfOver B S hS}
    (s : F.obj (op A)) : IsEmpty ((BigFppfOver.toScheme B S hS).obj A) :=
  ⟨fun y => h.false (pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm s)
    ((schemePointsHomeomorph B S hS A).symm y))⟩

/-- If every section of `F` lives over an empty scheme, so does every section of its view over
`Spec ℤ`. -/
theorem isEmpty_of_viewOverIntegers {hZ : B.Contains (⊤_ Scheme.{u})}
    (h : ∀ A : BigFppfOver B S hS, F.obj (op A) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A))
    {W : BigFppfOver B (⊤_ Scheme.{u}) hZ} (x : (viewOverIntegers B S hS hZ F).obj (op W)) :
    IsEmpty ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) :=
  h (Over.mk x.1.1) x.1.2

/-- An algebraic space all of whose sections live over empty schemes is quasi-compact. -/
theorem isQuasiCompactSpace_of_forall_isEmpty (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ A : BigFppfOver B S hS, F.obj (op A) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A)) :
    IsQuasiCompactSpace B S hS F := by
  obtain ⟨U, a, hs, he⟩ := hF.exists_atlas
  have := h U (yonedaEquiv a)
  exact ⟨U, a, inferInstance, hs, isEtale_of_presheaf_etale B S hS he⟩

/-- An algebraic space all of whose sections live over empty schemes is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_forall_isEmpty (hZ : B.Contains (⊤_ Scheme.{u}))
    (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ A : BigFppfOver B S hS, F.obj (op A) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A)) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  obtain ⟨U, q, hs, he⟩ := hF.exists_atlas
  have := h U (yonedaEquiv q)
  have hqc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q := by
    refine ⟨hs.1, fun a b g fst snd _ => ?_⟩
    have := h b (yonedaEquiv (fst ≫ q))
    exact ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have hfst := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback
    (IsPullback.of_hasPullback q q) hqc
  exact isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ F hF
    ⟨U, q, ⟨fun _ _ _ _ _ _ => (Set.toFinite _).isCompact⟩, hs, he, Or.inr hfst⟩

/-- An algebraic space all of whose sections live over empty schemes is of finite type over
`Spec ℤ`. -/
theorem isFiniteType_viewOverIntegers_of_forall_isEmpty (hZ : B.Contains (⊤_ Scheme.{u}))
    (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ A : BigFppfOver B S hS, F.obj (op A) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A)) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ F)) := by
  refine ⟨fun U V a b k _ _ _ => ?_, fun Z hZalg _ g => ?_⟩
  · have := isEmpty_of_viewOverIntegers h (yonedaEquiv a)
    show LocallyOfFiniteType ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map k)
    infer_instance
  · have hview : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F) :=
      isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) ⟨terminal.from S⟩ F hF
    have hterm : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ
        (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
      isAlgebraicSpace_of_iso B _ hZ
        (((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso
          terminalIsTerminal)
        (isAlgebraicSpace_yoneda B _ hZ _)
    exact isQuasiCompactSpace_of_forall_isEmpty
      (isAlgebraicSpace_pullback B _ hZ g _ hZalg hview hterm)
      (fun A x => isEmpty_of_viewOverIntegers h ((pullback.snd g _).app (op A) x))

/-- An algebraic space over `Spec ℤ` with no points has a Noetherian approximation satisfying
the convention of Section 70.2: the constant system over the one-element directed set. -/
theorem hasConventionalNoetherianApproximation_of_isEmpty_points
    {hZ : B.Contains (⊤_ Scheme.{u})} {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (h : IsEmpty (points B (⊤_ Scheme.{u}) hZ F)) :
    HasConventionalNoetherianApproximation B hZ F := by
  have h' := fun (A : BigFppfOver B (⊤_ Scheme.{u}) hZ) (s : F.obj (op A)) =>
    isEmpty_of_isEmpty_points h s
  exact ⟨NoetherianApproximation.const hF
    (isAbsolutelyQuasiSeparated_of_forall_isEmpty hZ hF h')
    (isFiniteType_viewOverIntegers_of_forall_isEmpty hZ hF h'),
    IsSiteSmall.siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ
      ((Functor.const PUnit.{u + 1}ᵒᵖ).obj F)
      (IsSiteSmall.of_mono fun _ _ _ => show Mono (𝟙 F) from inferInstance)⟩

end AlgebraicGeometry.Space

end
