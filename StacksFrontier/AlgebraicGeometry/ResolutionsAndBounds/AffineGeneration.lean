module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees

/-!
# Generation of a quasi-coherent module by sections over an affine open

Let `X` be a scheme, `M` a quasi-coherent `𝒪_X`-module and `U ⊆ X` an affine open. If a finite
family of sections `s : Fin k → Γ(M, U)` spans `Γ(M, U)` over `Γ(X, U)`, then it generates
`M` over `U` as a sheaf: every section of `M` over an open `V ⊆ U` is, on a neighbourhood of
each of its points, an `𝒪_X`-linear combination of the restrictions of the `s j`.

For a coherent module on a locally Noetherian scheme such a family always exists, because the
sections over an affine open form a finite module over the ring of sections of the structure
sheaf.

## Main results

* `AlgebraicGeometry.exists_sum_smul_sections_of_span_eq_top`: **sections spanning `Γ(M, U)`
  generate `M` over `U` locally**, in the form a section-level epimorphism criterion consumes.
* `AlgebraicGeometry.exists_fin_span_sections_of_isCoherent`: the sections of a coherent module
  over an affine open of a locally Noetherian scheme are spanned by a finite family.
* `AlgebraicGeometry.exists_fin_sections_generating_of_isCoherent`: the two combined — a
  coherent module on a locally Noetherian scheme is generated over an affine open by finitely
  many sections.

## Implementation notes

The local combination is produced on a basic open `D(a) ⊆ V` of the affine open `U`, where the
sections of `M` are the localization of `Γ(M, U)` away from `a`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`): a section over
`D(a)` becomes a section coming from `U` after multiplication by a power of `a`, and `a`
restricts to a unit on `D(a)`, so dividing by that power produces the coefficients. The
`Γ(X, U)`-module structure on `Γ(M, D(a))` used by the localization statement is restriction of
scalars along `Γ(X, U) ⟶ Γ(X, D(a))`, which is what `smul_moduleOfLE` identifies with the
native action.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Γ(X, U)`-action on the sections of a module over a smaller open is the native action of
`Γ(X, V)` on the restriction of the scalar. -/
private theorem smul_moduleOfLE (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (x : Γ(M, V)) :
    letI := moduleOfLE M h
    r • x = (X.presheaf.map (homOfLE h).op r) • x := rfl

/-- **Sections spanning the sections over an affine open generate the module there.** Let `M` be
a quasi-coherent `𝒪_X`-module, `U` an affine open and `s : Fin k → Γ(M, U)` a family spanning
`Γ(M, U)` over `Γ(X, U)`. Then every section `t` of `M` over an open `V ⊆ U` agrees, on a
neighbourhood `W` of any given point of `V`, with an `𝒪_X(W)`-linear combination of the
restrictions of the `s j`.

This is the form in which the section-level criterion for an epimorphism of sheaves of modules
consumes the generation statement: the neighbourhood is allowed to depend on the point and on
the section. -/
theorem exists_sum_smul_sections_of_span_eq_top (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {k : ℕ} (s : Fin k → Γ(M, U))
    (hs : Submodule.span Γ(X, U) (Set.range s) = ⊤)
    {V : X.Opens} (hVU : V ≤ U) (t : Γ(M, V)) (p : X) (hp : p ∈ V) :
    ∃ (W : X.Opens) (hWV : W ≤ V) (hWU : W ≤ U), p ∈ W ∧
      ∃ c : Fin k → Γ(X, W),
        M.presheaf.map (homOfLE hWV).op t =
          ∑ j, c j • M.presheaf.map (homOfLE hWU).op (s j) := by
  obtain ⟨a, haV, hpa⟩ := hU.exists_basicOpen_le (V := V) ⟨p, hp⟩ (hVU hp)
  refine ⟨X.basicOpen a, haV, X.basicOpen_le a, hpa, ?_⟩
  let := moduleOfLE M (X.basicOpen_le a)
  have hloc : IsLocalizedModule.Away a (restrictₗ M (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ M hU a rfl (X.basicOpen_le a)
  obtain ⟨⟨m, ⟨b, n, (hn : a ^ n = b)⟩⟩, hmb⟩ :=
    IsLocalizedModule.surj (Submonoid.powers a) (restrictₗ M (X.basicOpen_le a))
      (M.presheaf.map (homOfLE haV).op t)
  have hmem : m ∈ Submodule.span Γ(X, U) (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).1 hmem
  set v := X.presheaf.map (homOfLE (X.basicOpen_le a)).op a with hv
  have hvunit : IsUnit v := X.toRingedSpace.isUnit_res_basicOpen a
  obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen a), w * v ^ n = 1 :=
    ⟨↑(hvunit.pow n).unit⁻¹, by simp⟩
  refine ⟨fun j => w * X.presheaf.map (homOfLE (X.basicOpen_le a)).op (d j), ?_⟩
  have hres : (restrictₗ M (X.basicOpen_le a)) m
      = ∑ j, X.presheaf.map (homOfLE (X.basicOpen_le a)).op (d j) •
          M.presheaf.map (homOfLE (X.basicOpen_le a)).op (s j) := by
    rw [← hd, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul]
    exact smul_moduleOfLE M (X.basicOpen_le a) (d j) _
  calc M.presheaf.map (homOfLE haV).op t
      = w • (v ^ n • M.presheaf.map (homOfLE haV).op t) := by rw [← mul_smul, hw, one_smul]
    _ = w • ∑ j, X.presheaf.map (homOfLE (X.basicOpen_le a)).op (d j) •
          M.presheaf.map (homOfLE (X.basicOpen_le a)).op (s j) := by
      rw [← hres, ← hmb, Submonoid.smul_def,
        smul_moduleOfLE M (X.basicOpen_le a) (b : Γ(X, U)), ← hn, hv, map_pow]
    _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm

/-- **The sections of a coherent module over an affine open are spanned by a finite family.**
On a locally Noetherian scheme they form a finite module over the ring of sections of the
structure sheaf. -/
theorem exists_fin_span_sections_of_isCoherent [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (U : X.affineOpens) :
    ∃ (k : ℕ) (s : Fin k → Γ(F, U.1)), Submodule.span Γ(X, U.1) (Set.range s) = ⊤ :=
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections F U
  Module.Finite.exists_fin

/-- **A coherent module on a locally Noetherian scheme is generated over an affine open by
finitely many sections.** This is the statement the proof of [Stacks, Tag 0FZ0] uses: on each
member of an affine open cover the module is generated by finitely many sections, with
generation read as the section-level criterion for an epimorphism. -/
theorem exists_fin_sections_generating_of_isCoherent [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (U : X.affineOpens) :
    ∃ (k : ℕ) (s : Fin k → Γ(F, U.1)),
      ∀ {V : X.Opens}, V ≤ U.1 → ∀ (t : Γ(F, V)) (p : X), p ∈ V →
        ∃ (W : X.Opens) (hWV : W ≤ V) (hWU : W ≤ U.1), p ∈ W ∧
          ∃ c : Fin k → Γ(X, W),
            F.presheaf.map (homOfLE hWV).op t =
              ∑ j, c j • F.presheaf.map (homOfLE hWU).op (s j) := by
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨k, s, hs⟩ := exists_fin_span_sections_of_isCoherent F U
  exact ⟨k, s, fun hVU ↦ exists_sum_smul_sections_of_span_eq_top F U.2 s hs hVU⟩

end AlgebraicGeometry

end

end
