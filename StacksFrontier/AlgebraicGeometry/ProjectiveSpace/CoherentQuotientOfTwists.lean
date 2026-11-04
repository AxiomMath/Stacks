module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf

/-!
# A coherent sheaf on projective space is a quotient of a finite direct sum of twists

This is assertion (1) of [Stacks, Tag 01YS]: for `F` a coherent sheaf on `ℙⁿ_R` there are an
`r ≥ 0`, integers `d₁, …, d_r` and a surjection

$$ \bigoplus\nolimits_{j = 1}^{r} \mathcal{O}_{\mathbf{P}^n_R}(d_j) \longrightarrow \mathcal{F}. $$

The source's proof is two steps: `𝒪(1)` is ample on `ℙⁿ_R`, "which follows directly from the
definition since `ℙⁿ_R` is covered by the standard affine opens `D₊(Tᵢ)`"; and then clause (8) of
[Stacks, Tag 01Q3] — every finite-type quasi-coherent module is a quotient of a finite direct sum
of negative tensor powers of an ample invertible module. Coherent and finite-type quasi-coherent
agree on `ℙⁿ_R` by [Stacks, Tag 01XZ], which is where coherence enters and the only place it does.

Both steps are now theorems in this library:
`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf` and
`Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`.

## Main results

* `Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule`: **assertion (1) of
  [Stacks, Tag 01YS]**, for a quasi-coherent module of finite type over an arbitrary affine base,
  and with the degrees bounded above by any prescribed integer.
* `Stacks.ProjectiveSpace.exists_epi_biproduct_of_isCoherent`: the same for a coherent module,
  which is the source's literal statement.
* `Stacks.ProjectiveSpace.exists_shortExact_biproduct_tensorPowModule`: the strengthening the
  source's own dévissage consumes — the surjection fits in a short exact sequence whose kernel is
  quasi-coherent, which is what assertions (3), (4) and (5) are proved from.

## Implementation notes

**Generality.** The source assumes `R` Noetherian and `F` coherent. Neither is used: the
statement below is for a quasi-coherent module of finite type over an arbitrary affine base
scheme, and `Stacks.ProjectiveSpace.exists_epi_biproduct_of_isCoherent` recovers the source's
reading from it, since a coherent module is quasi-coherent (`isQuasicoherent_of_isCoherent`) and
of finite type (`IsCoherent.toIsFiniteType`) over any ringed space. Dropping Noetherianness is
what makes the appeal to Tag 01XZ unnecessary in the direction the source uses it.

**`𝒪(d)` is `𝒪(1) ^⊗ d`.** The twists appear as
`Stacks.Ample.tensorPowModule (ℙⁿ_S) (𝒪(1)) (d j)`, the integer tensor powers of the hyperplane
sheaf ([Stacks, Tag 01CU]), because that is the family the ample theory and clause (8) are stated
over. This is the source's `𝒪(dⱼ)`: `AlgebraicGeometry.projectiveSpaceTwistingSheaf` is the
pullback of the degree-one twist of the integral model, and its tensor powers are the twists.

**The degree bound points downwards.** Clause (8) produces powers `L ^⊗ (-dⱼ)` with the `dⱼ`
bounded *below* by a prescribed `n₀`; read as `𝒪(eⱼ)` with `eⱼ = -dⱼ` the bound is an upper bound
on the `eⱼ`. Either way the content is that the degrees may be taken arbitrarily negative, which
is what the dévissage of assertions (3) and (4) needs: it must be able to put the twists below any
given degree.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.ProjectiveSpace

/-- **Assertion (1) of [Stacks, Tag 01YS].** A quasi-coherent module of finite type on projective
`n`-space over an affine base is a quotient of a finite direct sum of twists
`𝒪(d₁), …, 𝒪(d_r)` of the structure sheaf, and the degrees may be taken below any prescribed
integer.

The source assumes the base ring Noetherian and the module coherent; neither is needed, and
`Stacks.ProjectiveSpace.exists_epi_biproduct_of_isCoherent` is the source's reading.

The proof is the source's: `𝒪(1)` is ample on `ℙⁿ_S`
(`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`), and clause (8) of
[Stacks, Tag 01Q3] (`Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`) presents
a finite-type quasi-coherent module as a quotient of a finite direct sum of negative tensor
powers of an ample invertible module. -/
@[stacks 01YS "assertion (1)"]
theorem exists_epi_biproduct_tensorPowModule (n : ℕ) (S : Scheme.{u}) [IsAffine S] (k : ℤ)
    (F : (projectiveSpaceOver n S).Modules) (hFqc : F.IsQuasicoherent)
    (hFft : SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (b : Bicone fun j : Fin r => tensorPowModule (projectiveSpaceOver n S)
        (projectiveSpaceTwistingSheaf n S) (d j))
      (_ : b.IsBilimit) (p : b.pt ⟶ F), Epi p ∧ ∀ j, d j ≤ k := by
  obtain ⟨T, r, d, b, hb, he, hexact, hX3, hqc, hd⟩ :=
    Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple
      (projectiveSpaceTwistingSheaf n S)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n S) (-k) F hFqc hFft
  subst hX3
  refine ⟨r, fun j => -(d j), b, hb, he.inv ≫ T.g, ?_, fun j => by linarith [hd j]⟩
  have : Epi T.g := hexact.epi_g
  infer_instance

/-- **Assertion (1) of [Stacks, Tag 01YS], in the source's reading**: a *coherent* sheaf on
projective `n`-space over an affine base is a quotient of a finite direct sum of twists of the
structure sheaf.

A coherent module is quasi-coherent and of finite type over any ringed space, so this is
`Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule`. The converse implication —
that a finite-type quasi-coherent module on `ℙⁿ_R` is coherent, which is how the source passes
between the two — is [Stacks, Tag 01XZ] and is not needed here. -/
theorem exists_epi_biproduct_of_isCoherent (n : ℕ) (S : Scheme.{u}) [IsAffine S] (k : ℤ)
    (F : (projectiveSpaceOver n S).Modules) [F.IsCoherent] :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (b : Bicone fun j : Fin r => tensorPowModule (projectiveSpaceOver n S)
        (projectiveSpaceTwistingSheaf n S) (d j))
      (_ : b.IsBilimit) (p : b.pt ⟶ F), Epi p ∧ ∀ j, d j ≤ k :=
  exists_epi_biproduct_tensorPowModule n S k F
    (isQuasicoherent_of_isCoherent F) (IsCoherent.toIsFiniteType F)

/-- **Assertion (1) of [Stacks, Tag 01YS] with the kernel**, which is the form the source's own
proof of assertions (3), (4) and (5) consumes: the surjection of assertion (1) fits in a short
exact sequence

`0 ⟶ G ⟶ ⨁_{j} 𝒪(dⱼ) ⟶ F ⟶ 0`

with `G` quasi-coherent, and the degrees `dⱼ` below any prescribed integer. The source obtains
coherence of `G` from [Stacks, Tag 01Y0]; quasi-coherence is what clause (8) of
[Stacks, Tag 01Q3] delivers directly. -/
theorem exists_shortExact_biproduct_tensorPowModule (n : ℕ) (S : Scheme.{u}) [IsAffine S] (k : ℤ)
    (F : (projectiveSpaceOver n S).Modules) (hFqc : F.IsQuasicoherent)
    (hFft : SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (T : ShortComplex (projectiveSpaceOver n S).Modules) (r : ℕ) (d : Fin r → ℤ)
      (b : Bicone fun j : Fin r => tensorPowModule (projectiveSpaceOver n S)
        (projectiveSpaceTwistingSheaf n S) (d j))
      (_ : b.IsBilimit) (_ : T.X₂ ≅ b.pt),
      T.ShortExact ∧ T.X₃ = F ∧ T.X₁.IsQuasicoherent ∧ ∀ j, d j ≤ k := by
  obtain ⟨T, r, d, b, hb, he, hexact, hX3, hqc, hd⟩ :=
    Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple
      (projectiveSpaceTwistingSheaf n S)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n S) (-k) F hFqc hFft
  exact ⟨T, r, fun j => -(d j), b, hb, he, hexact, hX3, hqc, fun j => by linarith [hd j]⟩

end Stacks.ProjectiveSpace

end
