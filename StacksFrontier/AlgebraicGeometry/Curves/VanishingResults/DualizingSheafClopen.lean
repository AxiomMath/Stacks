module

public import StacksFrontier.AlgebraicGeometry.ClopenModules.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension

/-!
# The dualizing sheaf of an open and closed piece of a proper curve

Let `X` be a proper scheme of dimension at most one over a field `k`, with dualizing sheaf `ω_X`
of [Stacks, Tag 0BS2].

## Main results

* `Stacks.Duality.dualizingSheafOverFieldClopenIso`: for `X = U ⊔ V` with `U`, `V` open and
  disjoint, `ω_U ≅ ω_X|_U`.
* `Stacks.Duality.isZero_dualizingSheafOverField_of_topologicalKrullDim_le_zero`: the dualizing
  sheaf of a proper scheme of dimension zero vanishes.

## Implementation notes

`U ⟶ X` is a closed immersion, so `ω_U = 𝓗om(𝒪_U, ω_X)` by [Stacks, Tag 0E33], the sheaf Hom
with exact support being the right adjoint of the pushforward. For an open and closed piece that
right adjoint is restriction (`AlgebraicGeometry.Scheme.Modules.rightAdjointObjIsoRestrict`).

In dimension zero `H^1` vanishes, so clause (5) of [Stacks, Tag 0BS2],
`Hom(ℱ, ω_X) = H^1(X, ℱ)^∨`, makes `Hom(ω_X, ω_X)` trivial.

## References

* [Stacks Project, Tag 0E33](https://stacks.math.columbia.edu/tag/0E33)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- The inclusion of an open subscheme whose complement is open is a closed immersion. -/
theorem isClosedImmersion_ι_of_inf_eq_bot {U V : X.Opens} (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    have : (U : Set X) = (V : Set X)ᶜ := by
      ext x
      refine ⟨fun hx hxV => ?_, fun hx => ?_⟩
      · have : x ∈ (U ⊓ V : X.Opens) := ⟨hx, hxV⟩
        rw [hdisj] at this
        exact this
      · have : x ∈ (U ⊔ V : X.Opens) := by
          rw [hcov]
          trivial
        exact this.resolve_right hx
    rw [this]
    exact V.isOpen.isClosed_compl)

/-- **The dualizing sheaf of an open and closed piece is the restriction**: for `X = U ⊔ V` with
`U` and `V` open and disjoint, `ω_U ≅ ω_X|_U`, for any structure morphism `f'` of `U` equal to
`U ⟶ X ⟶ Spec k`. By [Stacks, Tag 0E33] `ω_U` is the sheaf Hom with exact support out of `𝒪_U`
into `ω_X`, which is the right adjoint of the pushforward along the closed immersion `U ⟶ X`; for
an open and closed piece that right adjoint is restriction. -/
def dualizingSheafOverFieldClopenIso (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    {U V : X.Opens} (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)
    {f' : U.toScheme ⟶ Spec (CommRingCat.of k)} [IsProper f'] (hf' : U.ι ≫ f = f') :
    dualizingSheafOverField f' ≅ (dualizingSheafOverField f).restrict U.ι := by
  subst hf'
  letI := isClosedImmersion_ι_of_inf_eq_bot hdisj hcov
  exact dualizingSheafOverFieldClosedImmersionIso f U.ι hdim ≪≫
    Scheme.Modules.rightAdjointObjIsoRestrict hdisj hcov
      (closedQuotient U.ι).modulePushforwardSheafHomExactSupportAdjunction _

/-- **The dualizing sheaf of a proper scheme of dimension zero is zero.** By clause (5) of
[Stacks, Tag 0BS2], `Hom(ω_X, ω_X)` is dual to `H^1(X, ω_X)`, which vanishes in dimension zero. -/
theorem isZero_dualizingSheafOverField_of_topologicalKrullDim_le_zero
    (hdim : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) :
    IsZero (dualizingSheafOverField f) := by
  let := AlgebraicGeometry.modulesLinearOverField k f
  have h1 : IsZero (cohomologyOverField k f (dualizingSheafOverField f) 1) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f _ (d := 0) (by exact_mod_cast hdim)
      (by omega)
  have := ModuleCat.subsingleton_of_isZero h1
  rw [IsZero.iff_id_eq_zero]
  exact (homDualizingSheafLinearEquiv f (hdim.trans (by exact_mod_cast zero_le_one)) _
    (isQuasicoherent_dualizingSheafOverField f)).injective (Subsingleton.elim _ _)

end Stacks.Duality
