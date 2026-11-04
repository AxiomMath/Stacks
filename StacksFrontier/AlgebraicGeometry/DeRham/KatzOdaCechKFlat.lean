module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ConcreteTotalKFlat
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.VanishingOfSpan
import all StacksFrontier.AlgebraicGeometry.Perfect.Coherator.KunnethTotalCech

/-!
# The total Čech complex of the relative de Rham complex of a smooth morphism is K-flat

Let `f : X ⟶ Y` be a smooth morphism of schemes with `Y` affine, `A = Γ(Y, 𝒪_Y)`, and let
`U : ι → X.Opens` be a finite family of opens all of whose Čech intersections are affine. Then
the total Čech complex `Tot(Č(U, Ω^•_{X/Y}))` of the sections of the relative de Rham complex is
a K-flat complex of `A`-modules.

This is the input of [Stacks, Tag 0FMQ] used in the proof of [Stacks, Tag 0FUM], for the
complex of the sections of `Ω^•_{X/Y}` on the Čech intersections
(`Stacks.CategoryTheory.CechComplex.cechTot`). Its two hypotheses are checked here: the terms
`Γ(U_t, Ω^a_{X/Y})` are flat over `A`, since `Ω^a_{X/Y}` is flat over `Y`; and they vanish for
`a` large, uniformly in `t`, since the intersections `U_t` are finitely many affine opens, over
each of which `Ω_{X/Y}` is a finitely generated module (a smooth algebra is of finite type).

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.exists_subsingleton_forms`: on an affine open, the forms
  of high degree vanish.
* `AlgebraicGeometry.DeRhamKatzOdaCech.kFlat_cechTot_sectionsDeRhamComplex`: the K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.CategoryTheory.CechComplex

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Smooth f]

/-- **On an affine open, the relative forms of high degree vanish**: `Ω_{X/Y}` is generated over
`Γ(V, 𝒪_X)` by finitely many elements, say `r`, so `Ω^a_{X/Y}(V) = ⋀^a Ω` vanishes for `a > r`. -/
theorem exists_subsingleton_forms {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ r : ℕ, ∀ a : ℕ, r < a →
      Subsingleton Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), V) := by
  have hs : (chartMap f V).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top Y⟩ ⟨V, hV⟩ _
  let := (chartMap f V).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, V) :=
    RingHom.FiniteType.of_finitePresentation hs.finitePresentation
  have hfin : Module.Finite Γ(X, V) (CommRingCat.KaehlerDifferential (chartMap f V)) :=
    inferInstanceAs (Module.Finite Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, ⊤)])
  obtain ⟨s, hspan⟩ := hfin.fg_top
  refine ⟨s.card, fun a ha => ?_⟩
  have hrange : Set.range (fun i : Fin s.card =>
      (s.equivFin.symm i : CommRingCat.KaehlerDifferential (chartMap f V))) =
      (s : Set (CommRingCat.KaehlerDifferential (chartMap f V))) := by
    ext x
    refine ⟨?_, fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  have := exteriorPower.subsingleton_of_span_eq_top (R := Γ(X, V))
    (fun i : Fin s.card => (s.equivFin.symm i : CommRingCat.KaehlerDifferential (chartMap f V)))
    (by rwa [hrange]) ha
  exact (formsEquiv f hV a).toEquiv.subsingleton

variable {ι : Type u} (U : ι → X.Opens)

omit [IsAffine Y] [Smooth f] in
/-- The Čech intersections of a finite family of opens take only finitely many values. -/
theorem finite_range_inter [Finite ι] :
    (Set.range fun σ : Σ m : ℕ, Fin (m + 1) → ι => inter U σ.2).Finite := by
  classical
  let := Fintype.ofFinite ι
  refine (Set.finite_range fun s : Finset ι => ⨅ i ∈ s, U i).subset ?_
  rintro _ ⟨⟨m, t⟩, rfl⟩
  refine ⟨Finset.univ.image t, ?_⟩
  simp only [inter_eq_iInf, Finset.mem_image, Finset.mem_univ, true_and, iInf_exists]
  rw [iInf_comm]
  simp

open scoped Classical in
/-- A degree above which the relative forms vanish on every Čech intersection. -/
def formsBound [Finite ι] : ℕ :=
  (finite_range_inter U).toFinset.sup fun W =>
    if hW : IsAffineOpen W then Classical.choose (exists_subsingleton_forms f hW) else 0

/-- If all Čech intersections of a finite family of opens are affine, then the relative forms of
degree `a > formsBound f U` on every Čech intersection form a subsingleton. -/
theorem subsingleton_forms [Finite ι]
    (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (a : ℕ)
    (ha : formsBound f U < a) {m : ℕ} (t : Fin (m + 1) → ι) :
    Subsingleton Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), inter U t) := by
  classical
  have hmem : inter U t ∈ (finite_range_inter U).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨m, t⟩, rfl⟩
  have hle := Finset.le_sup (f := fun W =>
    if hW : IsAffineOpen W then Classical.choose (exists_subsingleton_forms f hW) else 0) hmem
  simp only [dite_eq_left (haff t)] at hle
  exact Classical.choose_spec (exists_subsingleton_forms f (haff t)) a (hle.trans_lt ha)

/-- **The total Čech complex of the relative de Rham complex is K-flat** ([Stacks, Tag 0FMQ] for
`Ω^•_{X/Y}`): for `f : X ⟶ Y` smooth with `Y` affine and a finite family of opens of `X` with
affine Čech intersections, `Tot(Č(U, Ω^•_{X/Y}))` is a K-flat complex of `Γ(Y, 𝒪_Y)`-modules. -/
theorem kFlat_cechTot_sectionsDeRhamComplex [Finite ι]
    (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) :
    CochainComplex.KFlat.{u, u} (cechTot U f.sectionsDeRhamComplex) :=
  kFlat_cechTot U f.sectionsDeRhamComplex (formsBound f U)
    (fun a ha _ t => subsingleton_forms f U haff a ha t)
    (fun a _ t => AlgebraicGeometry.sections_flat f
      (fun _ : ℤ => Scheme.Hom.relativeDifferentialForms f (a : ℤ))
      (fun _ => Scheme.Hom.isQuasicoherent_relativeDifferentialForms f a)
      (fun _ => ProperSmoothDeRham.isFlatOver_relativeDifferentialForms f a) 0 (inter U t)
      (haff t))

end AlgebraicGeometry.DeRhamKatzOdaCech

end
