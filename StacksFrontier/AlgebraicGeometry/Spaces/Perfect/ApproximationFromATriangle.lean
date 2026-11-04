module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# An approximation of the third vertex of a triangle gives one of the second

Let `F` be an algebraic space over a scheme `S`, let `T` be a subset of `|F|` and let

`E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]`

be a distinguished triangle of `D(𝒪_F)` whose first vertex `E₁` is perfect and supported on `T`.
Suppose a perfect object `R` supported on `T` maps to `E₃` by a map which is an isomorphism on
cohomology in every degree above `m` and a surjection in degree `m`.  Then some perfect object
supported on `T` maps to `E₂` with the same two properties.

This is the step by which the induction of Stacks 08HN closes: there `E₁` is the perfect object
already constructed, `E₂` is the object being approximated, `E₃` is the quotient, and `R` is the
approximation of `(T, E₃, m)` produced by the inductive hypothesis.  The source calls the
argument "an easy diagram chase"; it is carried out here in full.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_approximation_of_distinguished`: the statement
  above.
* `AlgebraicGeometry.Space.approximationHolds_of_distinguished`: the same statement with both
  existentials read through `AlgebraicGeometry.Space.ApproximationHolds` of Stacks 08HI, which
  is the form the induction of Stacks 08HN consumes.

## The construction

Write `v : E₃ ⟶ E₁[1]` for the third map of the triangle and `α : R ⟶ E₃` for the given map.
The object produced is the second vertex `P` of a distinguished triangle

`E₁ ⟶ P ⟶ R --(α ≫ v)--> E₁[1]`,

which exists because every morphism into a shift is the third map of a distinguished triangle
(`CategoryTheory.Pretriangulated.distinguished_cocone_triangle₂`), and the map `P ⟶ E₂` is the
middle component of the morphism of triangles extending the identity of `E₁` and `α`
(`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₂`); the commuting
square that lemma asks for is the *definition* of the third map of the new triangle, so nothing
is assumed about it.

`P` is perfect by Stacks 08G9 — the second vertex of a distinguished triangle whose other two
vertices are perfect — in the form
`AlgebraicGeometry.RingedSite.isPerfect_obj₂_of_distinguished`, which is stated with the
objects, the morphisms and the module sections of the ringed site at independent universes and
therefore applies to `AlgebraicGeometry.Space.smallEtaleRingedSite`.

The two cohomological conclusions are the four and five lemmas applied to the long exact
cohomology sequences of the two triangles, which the morphism of triangles compares.  For
`i > m` the five lemma is applied to the five-term rows

`Hⁱ⁻¹(E₃) ⟶ Hⁱ(E₁) ⟶ Hⁱ(P) ⟶ Hⁱ(R) ⟶ Hⁱ⁺¹(E₁)` and
`Hⁱ⁻¹(E₃) ⟶ Hⁱ(E₁) ⟶ Hⁱ(E₂) ⟶ Hⁱ(E₃) ⟶ Hⁱ⁺¹(E₁)`,

whose second and fifth comparison maps are the identity of `Hⁱ(E₁)` and of `Hⁱ⁺¹(E₁)`, whose
fourth is `Hⁱ(α)` — an isomorphism because `i > m` — and whose first is `Hⁱ⁻¹(α)`, an
epimorphism because `i - 1 ≥ m`.  In degree `m` the epimorphism version of the four lemma is
applied to the four-term rows ending in `Hᵐ⁺¹(E₁)`, where the comparison maps are the identity,
`Hᵐ(α)` — an epimorphism by hypothesis — and the identity again.

Those two diagram lemmas are isolated as
`AlgebraicGeometry.Space.isIso_homologyFunctor_map_hom₂` and
`AlgebraicGeometry.Space.epi_homologyFunctor_map_hom₂`, private statements about a morphism of
distinguished triangles in the derived category of an arbitrary abelian category; they mention
no sheaf, no site and no perfectness.

## The support hypothesis

The lemmas take one hypothesis, `hmid`: that cohomological support on `T` is inherited by the
second vertex of a distinguished triangle from the other two.  It is a statement about the
small étale site alone, proved as
`AlgebraicGeometry.Space.cohomologySupportedOn_obj₂_of_distinguished`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportTriangles.lean`), from the exactness of
the stalk functors at geometric points; Stacks 08HN supplies it through the field `mid` of
`AlgebraicGeometry.Space.AmplitudeInductionInputs`.  It is kept as a hypothesis here only so
that this file does not depend on the stalk machinery.

## Implementation notes

The module sections are at the universe of the schemes: at that universe every
sheafification and local-bijectivity hypothesis that
`AlgebraicGeometry.RingedSite.IsPerfect` and `AlgebraicGeometry.Space.CohomologySupportedOn`
ask of the small étale site and of its slices is an instance, by
`AlgebraicGeometry.Space.RingedSite`, so none appears as a binder.

The conclusion is stated as an existential over the perfect object and the map rather than
through `AlgebraicGeometry.Space.ApproximationHolds`, because the object `E₂` being approximated
is here an arbitrary object of `D(𝒪_F)`: Stacks 08HI asks its triple to have the object in
`D_QCoh(𝒪_F)`, and quasi-coherence plays no part in this argument.  Unfolding the existential
against `ApproximationHolds` at a quasi-coherent `E₂` is immediate.

`T` is an arbitrary subset of `|F|` rather than a closed one, which is the convention of
`AlgebraicGeometry.Space.CohomologySupportedOn`; closedness is used nowhere.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08G9](https://stacks.math.columbia.edu/tag/08G9)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace AlgebraicGeometry.Space

/-! ### The four and five lemmas on the cohomology sequences of two triangles -/

section Diagram

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- A morphism `φ` of triangles of `D(A)` gives a commuting square on `Hⁱ` for the first maps. -/
private theorem homologyFunctor_map_comm₁ {U U' : Triangle (DerivedCategory A)} (φ : U ⟶ U')
    (i : ℤ) : (DerivedCategory.homologyFunctor A i).map U.mor₁ ≫
        (DerivedCategory.homologyFunctor A i).map φ.hom₂ =
      (DerivedCategory.homologyFunctor A i).map φ.hom₁ ≫
        (DerivedCategory.homologyFunctor A i).map U'.mor₁ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]

/-- A morphism `φ` of triangles of `D(A)` gives a commuting square on `Hⁱ` for the second maps. -/
private theorem homologyFunctor_map_comm₂ {U U' : Triangle (DerivedCategory A)} (φ : U ⟶ U')
    (i : ℤ) : (DerivedCategory.homologyFunctor A i).map U.mor₂ ≫
        (DerivedCategory.homologyFunctor A i).map φ.hom₃ =
      (DerivedCategory.homologyFunctor A i).map φ.hom₂ ≫
        (DerivedCategory.homologyFunctor A i).map U'.mor₂ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]

/-- **The five lemma on the cohomology sequences of two distinguished triangles.**  For a
morphism `φ` of distinguished triangles of `D(A)`, if `Hⁱ⁻¹(φ₃)` is an epimorphism, `Hⁱ(φ₁)` and
`Hⁱ(φ₃)` are isomorphisms and `Hⁱ⁺¹(φ₁)` is a monomorphism, then `Hⁱ(φ₂)` is an isomorphism.

The rows are the stretches `Hⁱ⁻¹(E₃) ⟶ Hⁱ(E₁) ⟶ Hⁱ(E₂) ⟶ Hⁱ(E₃) ⟶ Hⁱ⁺¹(E₁)` of the two long
exact cohomology sequences, exact by the three exactness clauses of
`CategoryTheory.Functor.homologySequence_exact₁`, `₂` and `₃`; the comparison of the two is `φ`
on the four vertices and the naturality of the connecting map at the two ends. -/
private theorem isIso_homologyFunctor_map_hom₂ {U U' : Triangle (DerivedCategory A)}
    (hU : U ∈ distTriang (DerivedCategory A)) (hU' : U' ∈ distTriang (DerivedCategory A))
    (φ : U ⟶ U') (i : ℤ)
    (h₀ : Epi ((DerivedCategory.homologyFunctor A (i - 1)).map φ.hom₃))
    (h₁ : IsIso ((DerivedCategory.homologyFunctor A i).map φ.hom₁))
    (h₃ : IsIso ((DerivedCategory.homologyFunctor A i).map φ.hom₃))
    (h₄ : Mono ((DerivedCategory.homologyFunctor A (i + 1)).map φ.hom₁)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map φ.hom₂) := by
  let H := DerivedCategory.homologyFunctor A 0
  let row (V : Triangle (DerivedCategory A)) :=
    ComposableArrows.mk₄ (H.homologySequenceδ V (i - 1) i (by omega))
      ((DerivedCategory.homologyFunctor A i).map V.mor₁)
      ((DerivedCategory.homologyFunctor A i).map V.mor₂)
      (H.homologySequenceδ V i (i + 1) rfl)
  have hexact (V : Triangle (DerivedCategory A)) (hV : V ∈ distTriang (DerivedCategory A)) :
      (row V).Exact :=
    ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₁ V hV (i - 1) i (by omega)).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (H.homologySequence_exact₂ V hV i).exact_toComposableArrows
        (H.homologySequence_exact₃ V hV i (i + 1) rfl).exact_toComposableArrows)
  let diagram : row U ⟶ row U' :=
    ComposableArrows.homMk₄
      ((DerivedCategory.homologyFunctor A (i - 1)).map φ.hom₃)
      ((DerivedCategory.homologyFunctor A i).map φ.hom₁)
      ((DerivedCategory.homologyFunctor A i).map φ.hom₂)
      ((DerivedCategory.homologyFunctor A i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor A (i + 1)).map φ.hom₁)
      (H.homologySequenceδ_naturality φ (i - 1) i (by omega)).symm
      (homologyFunctor_map_comm₁ φ i)
      (homologyFunctor_map_comm₂ φ i)
      (H.homologySequenceδ_naturality φ i (i + 1) rfl).symm
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (hexact U hU) (hexact U' hU')
    diagram h₀ h₁ h₃ h₄

/-- **The epimorphism version of the four lemma on the cohomology sequences of two
distinguished triangles.**  For a morphism `φ` of distinguished triangles of `D(A)`, if `Hⁱ(φ₁)`
and `Hⁱ(φ₃)` are epimorphisms and `Hⁱ⁺¹(φ₁)` is a monomorphism, then `Hⁱ(φ₂)` is an
epimorphism.

The rows are the stretches `Hⁱ(E₁) ⟶ Hⁱ(E₂) ⟶ Hⁱ(E₃) ⟶ Hⁱ⁺¹(E₁)` of the two long exact
cohomology sequences. -/
private theorem epi_homologyFunctor_map_hom₂ {U U' : Triangle (DerivedCategory A)}
    (hU : U ∈ distTriang (DerivedCategory A)) (hU' : U' ∈ distTriang (DerivedCategory A))
    (φ : U ⟶ U') (i : ℤ)
    (h₀ : Epi ((DerivedCategory.homologyFunctor A i).map φ.hom₁))
    (h₂ : Epi ((DerivedCategory.homologyFunctor A i).map φ.hom₃))
    (h₃ : Mono ((DerivedCategory.homologyFunctor A (i + 1)).map φ.hom₁)) :
    Epi ((DerivedCategory.homologyFunctor A i).map φ.hom₂) := by
  let H := DerivedCategory.homologyFunctor A 0
  let row (V : Triangle (DerivedCategory A)) :=
    ComposableArrows.mk₃
      ((DerivedCategory.homologyFunctor A i).map V.mor₁)
      ((DerivedCategory.homologyFunctor A i).map V.mor₂)
      (H.homologySequenceδ V i (i + 1) rfl)
  have hexact (V : Triangle (DerivedCategory A)) (hV : V ∈ distTriang (DerivedCategory A)) :
      (row V).Exact :=
    ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₂ V hV i).exact_toComposableArrows
      (H.homologySequence_exact₃ V hV i (i + 1) rfl).exact_toComposableArrows
  let diagram : row U ⟶ row U' :=
    ComposableArrows.homMk₃
      ((DerivedCategory.homologyFunctor A i).map φ.hom₁)
      ((DerivedCategory.homologyFunctor A i).map φ.hom₂)
      ((DerivedCategory.homologyFunctor A i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor A (i + 1)).map φ.hom₁)
      (homologyFunctor_map_comm₁ φ i)
      (homologyFunctor_map_comm₂ φ i)
      (H.homologySequenceδ_naturality φ i (i + 1) rfl).symm
  exact Abelian.epi_of_epi_of_epi_of_mono diagram (hexact U hU) (hexact U' hU') h₀ h₂ h₃

end Diagram

/-! ### The step of Stacks 08HN -/

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **An approximation of the third vertex of a distinguished triangle whose first vertex is
perfect and supported on `T` yields one of the second vertex.**

Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of `D(𝒪_F)` with `E₁` perfect and
supported on `T`, and let `α : R ⟶ E₃` be a map from a perfect object supported on `T` which is
an isomorphism on `Hⁱ` for `i > m` and a surjection on `Hᵐ`.  Then there are a perfect object
`P` supported on `T` and a map `P ⟶ E₂` with those same two properties.

This is the step by which the induction of Stacks 08HN closes; the construction and the one
carried hypothesis `hmid` are described in the module docstring. -/
theorem exists_isPerfect_approximation_of_distinguished
    (T : Set (points B S hS F)) (m : ℤ)
    (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hTri : Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hperf₁ : (smallEtaleRingedSite B S hS F hF).IsPerfect Tri.obj₁)
    (hsupp₁ : CohomologySupportedOn B S hS F hF T Tri.obj₁)
    (R : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hperfR : (smallEtaleRingedSite B S hS F hF).IsPerfect R)
    (hsuppR : CohomologySupportedOn B S hS F hF T R)
    (α : R ⟶ Tri.obj₃)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) m).map α))
    (hmid : ∀ Tri' : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)),
      Tri' ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) →
        CohomologySupportedOn B S hS F hF T Tri'.obj₁ →
        CohomologySupportedOn B S hS F hF T Tri'.obj₃ →
          CohomologySupportedOn B S hS F hF T Tri'.obj₂) :
    ∃ (P : DerivedCategory (Modules.{u, u} B S hS F hF)) (φ : P ⟶ Tri.obj₂),
      (smallEtaleRingedSite B S hS F hF).IsPerfect P ∧
        CohomologySupportedOn B S hS F hF T P ∧
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).map φ)) ∧
        Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) m).map φ) := by
  -- The new triangle `E₁ ⟶ P ⟶ R --(α ≫ v)--> E₁[1]`.
  obtain ⟨P, f, g, hP⟩ := distinguished_cocone_triangle₂ (α ≫ Tri.mor₃)
  -- The map `P ⟶ E₂`, by TR3 at the identity of `E₁` and at `α`.
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    complete_distinguished_triangle_morphism₂ (Triangle.mk f g (α ≫ Tri.mor₃)) Tri hP hTri
      (𝟙 Tri.obj₁) α (by simp)
  -- The morphism of triangles `(𝟙, φ, α)`.
  let ψ : Triangle.mk f g (α ≫ Tri.mor₃) ⟶ Tri :=
    { hom₁ := 𝟙 Tri.obj₁
      hom₂ := φ
      hom₃ := α
      comm₁ := hφ₁
      comm₂ := hφ₂
      comm₃ := by simp }
  have hid (j : ℤ) : IsIso ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) j).map ψ.hom₁) := by
    show IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).map
      (𝟙 Tri.obj₁))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  refine ⟨P, φ, RingedSite.isPerfect_obj₂_of_distinguished_general _ _ hP hperf₁ hperfR,
    hmid (Triangle.mk f g (α ≫ Tri.mor₃)) hP hsupp₁ hsuppR, ?_, ?_⟩
  · -- Isomorphism on `Hⁱ` for `i > m`, by the five lemma.
    intro i hi
    have hprev : Epi ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS F hF) (i - 1)).map ψ.hom₃) := by
      rcases eq_or_lt_of_le (show m ≤ i - 1 by omega) with heq | hlt
      · rw [← heq]
        exact hepi
      · have := hiso (i - 1) hlt
        exact inferInstanceAs (Epi ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS F hF) (i - 1)).map α))
    have := hid (i + 1)
    exact isIso_homologyFunctor_map_hom₂ hP hTri ψ i hprev (hid i) (hiso i hi) inferInstance
  · -- Surjection on `Hᵐ`, by the epimorphism version of the four lemma.
    have := hid m
    have := hid (m + 1)
    exact epi_homologyFunctor_map_hom₂ hP hTri ψ m inferInstance hepi inferInstance

/-- **The step of Stacks 08HN read through the predicate of Stacks 08HI.**  Let
`E₁ ⟶ E ⟶ E' ⟶ E₁[1]` be a distinguished triangle of `D(𝒪_F)` with `E₁` perfect and supported on
`T`, and let `E` and `E'` carry quasi-coherent cohomology.  If approximation holds for the
triple `(T, E', m)` then it holds for `(T, E, m)`.

This is `AlgebraicGeometry.Space.exists_isPerfect_approximation_of_distinguished` with the two
existentials matched against `AlgebraicGeometry.Space.ApproximationHolds`: the approximating
object of the triple `(T, E', m)` is the perfect object supported on `T` that the previous
statement takes, and the object it produces together with its map to `E` is the approximation of
`(T, E, m)`.  Both triangle vertices enter as objects of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` together with the identification of their
underlying derived objects, which is the device the formalization of Stacks 08HL uses for the same
purpose: Stacks 08HI asks its triple to lie in `D_QCoh(𝒪_F)`. -/
theorem approximationHolds_of_distinguished
    (T : Set (points B S hS F)) (m : ℤ)
    (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hTri : Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hperf₁ : (smallEtaleRingedSite B S hS F hF).IsPerfect Tri.obj₁)
    (hsupp₁ : CohomologySupportedOn B S hS F hF T Tri.obj₁)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF) (hE : E.obj = Tri.obj₂)
    (E' : QuasicoherentDerivedCategory.{u, u} B S hS F hF) (hE' : E'.obj = Tri.obj₃)
    (happrox : ApproximationHolds B S hS F hF T E' m)
    (hmid : ∀ Tri' : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)),
      Tri' ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) →
        CohomologySupportedOn B S hS F hF T Tri'.obj₁ →
        CohomologySupportedOn B S hS F hF T Tri'.obj₃ →
          CohomologySupportedOn B S hS F hF T Tri'.obj₂) :
    ApproximationHolds B S hS F hF T E m := by
  obtain ⟨Eobj, Eprop⟩ := E
  obtain ⟨E'obj, E'prop⟩ := E'
  subst hE hE'
  obtain ⟨R, hperfR, hsuppR, α, hiso, hepi⟩ := happrox
  obtain ⟨P, φ, hPperf, hPsupp, hPiso, hPepi⟩ :=
    exists_isPerfect_approximation_of_distinguished B S hS F hF T m Tri hTri hperf₁ hsupp₁ R
      hperfR hsuppR α hiso hepi hmid
  exact ⟨P, hPperf, hPsupp, φ, hPiso, hPepi⟩

end AlgebraicGeometry.Space

end
