module

public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksFrontier.AlgebraicGeometry.Size.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.MvPolynomial.Cardinal

/-!
# A monomorphism locally of finite type that increases size (Stacks 04VA)

Stacks 04VA bounds `size X ≤ size Y` for a monomorphism `f : X ⟶ Y` that is quasi-compact or
locally of finite presentation (`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`,
`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation`), and states that the bound
does not hold for monomorphisms locally of finite type. This file proves that final statement.

Stacks' example takes `B = ∏_{n ∈ ℕ} 𝔽₂` and the coproduct `X = ∐_𝒰 Spec 𝔽₂` over the
ultrafilters `𝒰` on `ℕ`. The example proved here takes `Y = Spec 𝔽₂[x₀, x₁, …]`, of size `ℵ₀`, and
`X = ∐_s Spec 𝔽₂` over the rational points `s : ℕ → 𝔽₂`, which has `2 ^ ℵ₀` affine opens.

## Main results

* `AlgebraicGeometry.Scheme.exists_mono_locallyOfFiniteType_not_size_le`: some monomorphism
  `X ⟶ Y` locally of finite type has `¬ size X ≤ size Y`.

## References

* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
-/

@[expose] public section

open Cardinal CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The field `𝔽₂`, in universe `u`. -/
private abbrev F₂ : Type u := ULift.{u} (ZMod 2)

/-- The polynomial ring `𝔽₂[x₀, x₁, …]` in countably many variables, in universe `u`. -/
private abbrev polyF₂ : Type u := MvPolynomial (ULift.{u} ℕ) F₂.{u}

/-- The rational point of `Spec 𝔽₂[x₀, x₁, …]` with coordinates `s`, as the morphism
`Spec 𝔽₂ ⟶ Spec 𝔽₂[x₀, x₁, …]` induced by evaluation at `s`. -/
private noncomputable def evalPoint (s : ULift.{u} ℕ → F₂.{u}) :
    Spec (.of F₂.{u}) ⟶ Spec (.of polyF₂.{u}) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval s))

private instance isClosedImmersion_evalPoint (s : ULift.{u} ℕ → F₂.{u}) :
    IsClosedImmersion (evalPoint s) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩

/-- The coproduct of the rational points `Spec 𝔽₂ ⟶ Spec 𝔽₂[x₀, x₁, …]`, one for each
`s : ℕ → 𝔽₂`. -/
private noncomputable def evalPoints :
    (∐ fun _ : ULift.{u} ℕ → F₂.{u} => Spec (.of F₂.{u})) ⟶ Spec (.of polyF₂.{u}) :=
  Limits.Sigma.desc evalPoint

private theorem evalPoints_injective : Function.Injective evalPoints.{u} := by
  intro a b h
  obtain ⟨⟨s, x⟩, rfl⟩ := (sigmaMk _).surjective a
  obtain ⟨⟨t, y⟩, rfl⟩ := (sigmaMk _).surjective b
  simp only [sigmaMk_mk, evalPoints, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc] at h ⊢
  obtain rfl : s = t := by
    funext i
    have hmem : MvPolynomial.X i - MvPolynomial.C (s i) ∈ (evalPoint s x).asIdeal := by
      change MvPolynomial.eval s (MvPolynomial.X i - MvPolynomial.C (s i)) ∈ x.asIdeal
      simp
    rw [h] at hmem
    change MvPolynomial.eval t (MvPolynomial.X i - MvPolynomial.C (s i)) ∈ y.asIdeal at hmem
    rw [(Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top, Ideal.mem_bot] at hmem
    simpa [sub_eq_zero, eq_comm] using hmem
  rw [Subsingleton.elim x y]

private instance mono_evalPoints : Mono evalPoints.{u} := by
  have : SurjectiveOnStalks evalPoints.{u} :=
    IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  exact SurjectiveOnStalks.mono_of_injective evalPoints_injective

private instance locallyOfFiniteType_evalPoints : LocallyOfFiniteType evalPoints.{u} :=
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun _ => inferInstance

/-- `Spec 𝔽₂[x₀, x₁, …]` has size `ℵ₀`, its ring of global sections being countable. -/
private theorem size_spec_polyF₂_le : (Spec (.of polyF₂.{u})).size ≤ ℵ₀ := by
  rw [Scheme.size_of_isAffine, max_le_iff]
  refine ⟨le_rfl, ?_⟩
  rw [(Scheme.ΓSpecIso (.of polyF₂.{u})).commRingCatIsoToRingEquiv.toEquiv.cardinal_eq]
  refine MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl)
  · exact (Cardinal.mk_le_aleph0 (α := F₂.{u}))
  · exact (Cardinal.mk_le_aleph0 (α := ULift.{u} ℕ))

/-- The source of `evalPoints` has at least `2 ^ ℵ₀` affine opens: the components
`Spec 𝔽₂`, one for each `s : ℕ → 𝔽₂`. -/
private theorem aleph0_lt_size_sigma :
    ℵ₀ < (∐ fun _ : ULift.{u} ℕ → F₂.{u} => Spec (.of F₂.{u})).size := by
  set g := fun _ : ULift.{u} ℕ → F₂.{u} => Spec (.of F₂.{u})
  have hinj : Function.Injective fun s : ULift.{u} ℕ → F₂.{u} =>
      (⟨(Limits.Sigma.ι g s).opensRange, isAffineOpen_opensRange _⟩ : (∐ g).affineOpens) := by
    intro s t hst
    have hrange : (Limits.Sigma.ι g s).opensRange = (Limits.Sigma.ι g t).opensRange :=
      congrArg Subtype.val hst
    have hmem : Limits.Sigma.ι g s default ∈ (Limits.Sigma.ι g t).opensRange := by
      rw [← hrange]
      exact ⟨default, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    exact (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff g t s y default).mp hy)).1.symm
  have hcard : #(ULift.{u} ℕ → F₂.{u}) = 2 ^ ℵ₀ := by
    rw [← Cardinal.power_def]
    simp
  calc ℵ₀ < 2 ^ ℵ₀ := Cardinal.cantor ℵ₀
    _ = #(ULift.{u} ℕ → F₂.{u}) := hcard.symm
    _ ≤ #(∐ g).affineOpens := Cardinal.mk_le_of_injective hinj
    _ ≤ (∐ g).size := Scheme.mk_affineOpens_le_size _

/-- **Stacks 04VA, the final statement.** The bound `size X ≤ size Y` does not hold for
monomorphisms locally of finite type: there is a monomorphism `f : X ⟶ Y` locally of finite type
with `¬ size X ≤ size Y`.

Here `Y = Spec 𝔽₂[x₀, x₁, …]` has size `ℵ₀`, and `X = ∐_s Spec 𝔽₂` is the coproduct of its
rational points, one for each `s : ℕ → 𝔽₂`, mapped to `Y` by evaluation at `s`. Each component
is a closed immersion, so `f` is locally of finite type and surjective on stalks, and `f` is
injective on points, hence a monomorphism. The components give `2 ^ ℵ₀` affine opens of `X`.
Stacks takes `Y = Spec ∏_{n ∈ ℕ} 𝔽₂` and `X` the coproduct of its points over the ultrafilters on
`ℕ`; the countable ring used here gives the same failure with a cardinality count that is
Cantor's theorem. -/
@[stacks 04VA "final statement: the bound fails for monomorphisms locally of finite type"]
theorem Scheme.exists_mono_locallyOfFiniteType_not_size_le :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), Mono f ∧ LocallyOfFiniteType f ∧ ¬ X.size ≤ Y.size :=
  ⟨_, _, evalPoints, inferInstance, inferInstance,
    fun h => (aleph0_lt_size_sigma.trans_le h).not_ge size_spec_polyF₂_le⟩

end AlgebraicGeometry
