module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EventualMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite

/-!
# A morphism of finite type of qcqs algebraic spaces is closed in one of finite presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, locally of finite type, with
`X` and `Y` quasi-compact and quasi-separated. Then `f` factors as a closed immersion `X ⟶ X'`
followed by a morphism of finite presentation `X' ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType`:
  a morphism of finite type of quasi-compact and quasi-separated algebraic spaces factors as a
  closed immersion followed by a morphism of finite presentation.

## References

* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type,
with `X` and `Y` quasi-compact and quasi-separated. Then there are a morphism of finite
presentation `f' : X' ⟶ Y` and a closed immersion `i : X ⟶ X'` with `i ≫ f' = f`. -/
theorem exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f := by
  obtain ⟨I, _, _, _, D, t, p, hp, hpt, hDalg, htfp, hDaff⟩ :=
    exists_isLimit_finitePresentation B S hS B.contains_terminal f hX hY hXqc hXqs hYqs
  have hDqs : ∀ i : I,
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (D.obj (op i)) := fun i =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal (hDalg (op i))
      hYqs (htfp (op i)).2.2
  obtain ⟨i, hi⟩ := (eventually_mono_comp_limitπ B S hS Y hY D (fun i => hDalg (op i)) t
    (Cone.mk X p) hp f hpt X hX hXqc (𝟙 X) (fun _ _ h => hDaff (homOfLE h).op) hDqs
    (by simpa using hf)).exists
  let g : X ⟶ D.obj (op i) := p.app (op i)
  have hgm : Mono g := by simpa using hi
  have hgt : g ≫ t.app (op i) = f := by
    simpa using NatTrans.congr_app hpt (op i)
  have hgft : IsLocallyOfFiniteType B S hS g :=
    isLocallyOfFiniteType_of_comp B S hS hX (hDalg (op i)) hY g (t.app (op i))
      (by rw [hgt]; exact hf)
  have hgqf : IsQuasiFinite B S hS g :=
    ⟨isLocallyQuasiFinite_of_mono B S hS hX (hDalg (op i)) g hgm hgft,
      isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal (hDalg (op i)) (hDqs i)
        hXqc g⟩
  have hgqa : IsQuasiAffineHom B S hS g :=
    isQuasiAffineHom_of_isQuasiFinite_isSeparated hX (hDalg (op i)) hgqf
      (isSeparated_of_mono g hgm)
  have hDqc : IsQuasiCompactSpace B S hS (D.obj (op i)) :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc (t.app (op i)) (htfp (op i)).2.1
  obtain ⟨X', f', j, hX', hf'fp, hj, hjf'⟩ :=
    exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_qcqs B S hS g hX
      (hDalg (op i)) hgft hgqa hDqc (hDqs i)
  refine ⟨X', j, f' ≫ t.app (op i), hX', hj,
    isFinitePresentation_comp B S hS hX' (hDalg (op i)) hY f' (t.app (op i)) hf'fp (htfp (op i)),
    ?_⟩
  rw [← Category.assoc, hjf', hgt]

end AlgebraicGeometry.Space

end
