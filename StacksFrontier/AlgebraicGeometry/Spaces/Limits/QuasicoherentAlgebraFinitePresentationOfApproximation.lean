module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentAlgebraFinitePresentationColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFilteredColimitOfApproximation

/-!
# Quasi-coherent algebras on a qcqs algebraic space, from Noetherian approximation

Granted absolute Noetherian approximation over `Spec ℤ` (Stacks 07SU, the hypothesis `h07SU`),
a quasi-coherent algebra on a quasi-compact and quasi-separated algebraic space is a filtered,
and indeed directed, colimit of quasi-coherent algebras of finite presentation (Stacks 082A).

## Main results

* `exists_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation`:
  a quasi-coherent algebra on a qcqs algebraic space is a filtered colimit of quasi-coherent
  algebras of finite presentation, given `h07SU`.
* `exists_directed_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation`:
  a quasi-coherent algebra on a qcqs algebraic space is a colimit, in the category of all algebra
  sheaves, of a system of quasi-coherent algebras of finite presentation indexed by a directed
  set, given `h07SU`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A quasi-coherent algebra on a qcqs algebraic space is a filtered colimit of quasi-coherent
algebras of finite presentation**, over absolute Noetherian approximation (`h07SU`). -/
theorem exists_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (𝒜 : AlgebraSheaf.{u, u} B S hS X hX) (h𝒜 : 𝒜.IsQuasicoherent) :
    ∃ (K : Type u) (inst : SmallCategory K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ AlgebraSheaf.{u, u} B S hS X hX)
        (φ : D ⟶ (Functor.const K).obj 𝒜),
        (∀ k, (D.obj k).IsQuasicoherent ∧ (D.obj k).IsFinitePresentation) ∧
          Nonempty (IsColimit (Cocone.mk 𝒜 φ)) :=
  exists_isColimit_isFinitePresentation_quasicoherentAlgebra B S hS X hX
    (fun G hG => exists_isColimit_isFinitePresentation_of_noetherianApproximation B S hS hZ h07SU
      hX hqc hqs G hG)
    (fun G _ => (isFiltered_and_nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_noetherianApproximation
      B S hS hZ h07SU hX hqc hqs G).2)
    𝒜 h𝒜

/-- Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and `𝒜` a
quasi-coherent `𝒪_Y`-algebra. Granted absolute Noetherian approximation over `Spec ℤ` (`h07SU`),
`𝒜` is a colimit, in the category of all algebra sheaves on `Y`, of a system of quasi-coherent
`𝒪_Y`-algebras of finite presentation indexed by a directed set. -/
theorem exists_directed_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    (Y : AlgebraicSpaces B S hS) (𝒜 : QuasicoherentAlgebra B S hS Y)
    (hqc : IsQuasiCompactSpace B S hS Y.obj) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.obj) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj 𝒜),
      Nonempty (IsColimit ((quasicoherentAlgebraInclusion B S hS Y).mapCocone
        (Cocone.mk 𝒜 φ))) ∧ ∀ i, (D.obj i).obj.IsFinitePresentation := by
  obtain ⟨K, inst, hK, D, φ, hP, ⟨hc⟩⟩ :=
    exists_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation
      B S hS hZ h07SU Y.2 hqc hqs 𝒜.obj 𝒜.property
  obtain ⟨I, hpre, hne, hdir, D', φ', hc', hP', -⟩ :=
    Stacks.FiniteAlgebraSurjectiveSystem.exists_directed_of_filtered_colimit_hom.{u}
      (fun A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2 => A.IsQuasicoherent ∧ A.IsFinitePresentation)
      (fun _ _ _ => True) D 𝒜.obj φ hc hP (fun _ _ _ => trivial)
  let D'' : I ⥤ QuasicoherentAlgebra B S hS Y :=
    ObjectProperty.lift _ D' fun i => (hP' i).1
  let φ'' : D'' ⟶ (Functor.const I).obj 𝒜 :=
    { app := fun i => ObjectProperty.homMk (φ'.app i)
      naturality := fun i j f => ObjectProperty.hom_ext _ (φ'.naturality f) }
  exact ⟨I, hpre, hne, hdir, D'', φ'', ⟨hc'⟩, fun i => (hP' i).2⟩

end AlgebraicGeometry.Space

end
