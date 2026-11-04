module

public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseSixConverse

/-!
# Stacks Tag 01Q3 as a single statement: the nine clauses are equivalent

[Stacks, Tag 01Q3] is the assertion that, for an invertible `𝒪_X`-module `L` on a **quasi-compact**
scheme `X` and `S = Γ_*(X, L)`, nine conditions are equivalent. The individual implications are
spread over `./Basic.lean`, `./ClauseFive.lean`, `./ClauseSixConverse.lean`,
`../AmpleLocalGeneration/FromExtension.lean` and `../SectionExtensionAffineCover/Basic.lean`. This
file closes the three links that were available only at a strength other than the clause's own, and
then states the tag itself: a single `List.TFAE` over the nine clauses, under the one standing
hypothesis `[CompactSpace X]` the source Proposition carries.

## Main results

* `Stacks.AmpleCharacterization.isBasisNonvanishing_of_isAmple` and
  `Stacks.AmpleCharacterization.isBasisAffineNonvanishing_of_isAmple`: **clause (1) implies clause
  (3)** and **clause (1) implies clause (4)**, each stated on its own and spelled out, in the
  `Stacks.Ample.IsAmple` vocabulary the other eight clauses are stated in.
* `Stacks.AmpleCharacterization.isAmple_of_isBasisAffineNonvanishing`: **clause (4) implies clause
  (1)** from clause (4) alone. The conjunction
  `Stacks.AmpleCharacterization.isAmple_of_isBasisNonvanishing_and_isBasisAffineNonvanishing`
  carries clause (3) as well, which is more than clause (4) says.
* `Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple`:
  **clause (1) implies clause (7)** with the twists merely *globally generated*, which is what the
  clause asserts.
  `Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple`
  concludes the stronger statement that the generating family may be taken finite.
* `Stacks.AmpleCharacterization.isAmple_of_quasiSeparatedSpace_and_isGeneratedByGlobalSections`:
  **clause (7) implies clause (1)**, from clause (7) at its own strength.
* `Stacks.AmpleCharacterization.isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct`:
  **clause (8) implies clause (1)**.
* `Stacks.AmpleCharacterization.tfae_isAmple`: **[Stacks, Tag 01Q3]** — the nine clauses are
  equivalent.

## What the nine entries of the list are

1. `L` is ample.
2. The opens `X_s`, for `s ∈ S₊` homogeneous, cover `X`, and the resulting morphism
   `X ⟶ Proj S` is an open immersion. The covering is a `Prop`, so the dependent pair
   `∃ h : nvUnion L = ⊤, IsOpenImmersion (projHomOfCovers L h)` is by proof irrelevance exactly
   the conjunction of the two assertions; it has to be a dependent pair because the morphism of
   [Stacks, Tag 01PZ] is only defined once the covering is given.
3. The opens `X_s`, for `s ∈ S₊` homogeneous, form a basis for the topology of `X`, in
   neighbourhood form.
4. The same with the `X_s` affine.
5. For every quasi-coherent `F` the sum of the images of the canonical maps
   `Γ(X, F ⊗ L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ F`, `n ≥ 1`, is `F`. The `n`-th canonical map is the sum over
   `m ∈ Γ(X, F ⊗ L^{⊗ n})` of `Stacks.AmpleCharacterization.twistHom L F n m`, and the equality of
   subsheaves is read on stalks; see `./ClauseFive.lean` for both readings.
6. The same with `F` ranging over the quasi-coherent sheaves of ideals, a sheaf of ideals being a
   module with a monomorphism into `𝒪_X`.
7. `X` is quasi-separated and every quasi-coherent `F` of finite type has an `n₀` with
   `F ⊗ L^{⊗ n}` globally generated — [Stacks, Tag 03DE] (3), nothing asked of the generating
   family — for all `n ≥ n₀`.
8. `X` is quasi-separated and every quasi-coherent `F` of finite type is, for some `n > 0` and some
   finite `ι`, a quotient of a direct sum of copies of `L ^⊗ (-n)` indexed by `ι`. The `k` of the
   source is `Nat.card ι`.
9. The same with `F` ranging over the quasi-coherent sheaves of ideals of finite type.

Clause (1) is `Stacks.Ample.IsAmple`, which already contains the quasi-compactness; the
`[CompactSpace X]` instance is what makes the other eight clauses hypotheses of the same strength
the source gives them.

## Where each link comes from

| link | declaration |
| - | - |
| `1 ↔ 2` | `isAmple_iff_exists_nvUnion_eq_top_and_isOpenImmersion` |
| `1 ↔ 3` | `Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisNonvanishing` |
| `1 ↔ 4` | `Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisAffineNonvanishing` |
| `1 ↔ 5` | `isAmple_iff_iSup_range_twistHom` |
| `1 ↔ 6` | `isAmple_iff_iSup_range_twistHom_ideal` |
| `1 ↔ 7` | `isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections` |
| `1 ↔ 8` | `isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct` |
| `1 ↔ 9` | `isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct_ideal` |

Each of those is proved from the source's own implications; the cycles the source runs are
`(1) ⇒ (2) ⇒ (4) ⇒ (1)`, `(1) ⇒ (3) ⇒ (1)`, `(1) ⇒ (5) ⇒ (6) ⇒ (1)` and
`(1) ⇒ (7) ⇒ (8) ⇒ (9) ⇒ (1)`.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample
open Stacks.AmpleTheory (powNonvanishingOpen)

universe u

namespace Stacks.AmpleCharacterization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-! ### Clauses (3) and (4) from ampleness -/

/-- **Clause (1) of [Stacks, Tag 01Q3] implies clause (3)** — the clause labelled 01Q6: for `L`
ample the opens `X_s`, with `s ∈ S₊` homogeneous, form a basis for the topology of `X`.

The clause is written out rather than named, and in the `Stacks.Ample.IsAmple` vocabulary the
other eight clauses of the tag are stated in. The content is
`Stacks.SectionExtension.isBasisNonvanishing_of_isAmple`. -/
@[stacks 01Q3 "clause (3)", ega "II 4.5.2" "(a) ⇒ (a')"]
theorem isBasisNonvanishing_of_isAmple (hL : IsAmple X L) :
    ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
        x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U :=
  Stacks.SectionExtension.isBasisNonvanishing_of_isAmple X L hL

/-- **Clause (1) of [Stacks, Tag 01Q3] implies clause (4)** — the clause labelled 01Q7: for `L`
ample the opens `X_s`, with `s ∈ S₊` homogeneous, **which are affine** form a basis for the
topology of `X`.

The content is `Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple`, namely clause (3)
followed by [Stacks, Tag 01PX], which is unconditional here because [Stacks, Tag 01PV] is
proved. -/
@[stacks 01Q3 "clause (4)", ega "II 4.5.2" "(a) ⇒ (a')"]
theorem isBasisAffineNonvanishing_of_isAmple (hL : IsAmple X L) :
    ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
        IsAffineOpen (powNonvanishingOpen X L n s) ∧
          x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U :=
  Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple X L hL

/-! ### Clause (4) implies clause (1), from clause (4) alone -/

/-- **Clause (4) of [Stacks, Tag 01Q3] implies clause (1)**, with clause (4) as the tag states it
and nothing else beyond the standing quasi-compactness: if the affine opens `X_s`, for `s ∈ S₊`
homogeneous, form a basis for the topology of the quasi-compact scheme `X`, then `L` is ample.

`Stacks.AmpleCharacterization.isAmple_of_isBasisNonvanishing_and_isBasisAffineNonvanishing` proves
the same conclusion from the *conjunction* of clauses (3) and (4), which is more than this clause
supplies; the clause's own strength suffices, because clause (4) applied at the ambient open `⊤` is
already condition (2) of [Stacks, Tag 01PS]. That is
`Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing`. -/
@[stacks 01Q3 "clause (4) implies (1)", ega "II 4.5.2" "(a) ⇐ (a')"]
theorem isAmple_of_isBasisAffineNonvanishing [CompactSpace X]
    (h : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
        IsAffineOpen (powNonvanishingOpen X L n s) ∧
          x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U) :
    IsAmple X L :=
  Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X L ‹CompactSpace X› h

/-! ### Clause (7), at the strength the tag states it -/

/-- **Clause (1) of [Stacks, Tag 01Q3] implies clause (7)** — the clause labelled 01QA — *as the
tag states it*: `X` is quasi-separated, and for every quasi-coherent sheaf `F` of finite type there
is an `n₀` with `F ⊗ L ^⊗ n` globally generated, [Stacks, Tag 03DE] (3), for all `n ≥ n₀`. Nothing
is asked of the generating family.

`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple`
concludes the stronger statement that the generating family may be taken **finite**, which is more
than the clause says; this is the clause itself, and it is the form the equivalence below and the
implication `(7) ⇒ (8)` of
`Stacks.AmpleCharacterization.quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections`
are stated at. -/
@[stacks 01Q3 "clause (7)", ega "II 4.5.5" "(a) ⇒ (d)", ega "II 2.7.9"]
theorem quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple (hL : IsAmple X L) :
    QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          _root_.SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
            ((F ⊗ tensorPowModule X L n : X.Modules)) :=
  haveI : CompactSpace X := hL.1
  (isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections L).mp hL

/-- **Clause (7) of [Stacks, Tag 01Q3] implies clause (1)**, from clause (7) at its own strength —
the twists merely globally generated, with no bound on the generating family — and with no
hypothesis beyond the tag's standing quasi-compactness.

The route is the source's own: clause (7) implies clause (8)
(`Stacks.AmpleCharacterization.quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections`,
where the quasi-compactness cuts the generating family down to a finite one by
[Stacks, Tag 01BB]), clause (8) implies clause (9), and clause (9) implies clause (1). -/
@[stacks 01Q3 "clause (7) implies (1)", ega "II 4.5.5" "(d) ⇒ (a)"]
theorem isAmple_of_quasiSeparatedSpace_and_isGeneratedByGlobalSections [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          _root_.SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
            ((F ⊗ tensorPowModule X L n : X.Modules))) :
    IsAmple X L :=
  (isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections L).mpr h

/-! ### Clause (8) implies clause (1) -/

/-- **Clause (8) of [Stacks, Tag 01Q3] implies clause (1)**: the source's `(8) ⇒ (9) ⇒ (1)` in one
step, `Stacks.AmpleCharacterization.quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_exists_epi_biproduct`
followed by
`Stacks.AmpleCharacterization.isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`. -/
@[stacks 01Q3 "clause (8) implies (1)", ega "II 4.5.5" "(d') ⇒ (a)"]
theorem isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p) :
    IsAmple X L :=
  (isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct L).mpr h

/-! ### The tag -/

/-- **[Stacks, Tag 01Q3].** Let `X` be a quasi-compact scheme, `L` an invertible `𝒪_X`-module, and
`S = Γ_*(X, L)`. The nine conditions of the source Proposition are equivalent:

1. `L` is ample;
2. the opens `X_s`, `s ∈ S₊` homogeneous, cover `X` and the resulting `X ⟶ Proj S` is an open
   immersion;
3. those opens form a basis for the topology of `X`;
4. the affine ones among them form a basis for the topology of `X`;
5. for every quasi-coherent `F` the images of the canonical maps
   `Γ(X, F ⊗ L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ F`, `n ≥ 1`, sum to `F`;
6. the same for `F` a quasi-coherent sheaf of ideals;
7. `X` is quasi-separated and every finite-type quasi-coherent `F` has `F ⊗ L^{⊗ n}` globally
   generated for all large `n`;
8. `X` is quasi-separated and every finite-type quasi-coherent `F` is a quotient of a finite direct
   sum of copies of a single `L ^⊗ (-n)`, `n > 0`;
9. the same for `F` a finite-type quasi-coherent sheaf of ideals.

The only hypothesis is the source's own: `X` quasi-compact, which is `[CompactSpace X]`, plus the
invertibility of `L`. Clause (1), `Stacks.Ample.IsAmple`, carries the quasi-compactness in its own
definition, so the instance is what puts the remaining eight clauses at the strength the source
gives them. The module docstring says where each `1 ↔ i` comes from. -/
@[stacks 01Q3, ega "II 4.5.2", ega "II 4.5.5", ega "II 2.7.10",
  sga "6 II 2.2.3" "single L"]
theorem tfae_isAmple [CompactSpace X] :
    List.TFAE
      [ IsAmple X L,
        ∃ h : Stacks.SectionRingProjMorphism.nvUnion L = ⊤,
          IsOpenImmersion (Stacks.SectionRingProjMorphism.projHomOfCovers L h),
        ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
          ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
            x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U,
        ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
          ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
            IsAffineOpen (powNonvanishingOpen X L n s) ∧
              x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U,
        ∀ F : X.Modules, F.IsQuasicoherent → ∀ x : X,
          (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(F ⊗ tensorPowModule X L (n : ℤ), ⊤)),
            LinearMap.range (Stacks.ModuleStalk.map (twistHom L F (n : ℤ) m) x)) = ⊤,
        ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j → J.IsQuasicoherent →
          ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
            LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤,
        QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
          SheafOfModules.IsFiniteType.{u, u, u} F →
            ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
              _root_.SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
                ((F ⊗ tensorPowModule X L n : X.Modules)),
        QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
          SheafOfModules.IsFiniteType.{u, u, u} F →
            ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
              ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
                (p : b.pt ⟶ F), Epi p,
        QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
          J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
            ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
              ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
                (p : b.pt ⟶ J), Epi p ] := by
  tfae_have 1 ↔ 2 := isAmple_iff_exists_nvUnion_eq_top_and_isOpenImmersion L
  tfae_have 1 ↔ 3 :=
    (Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisNonvanishing X L).trans
      (and_iff_right ‹CompactSpace X›)
  tfae_have 1 ↔ 4 :=
    (Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisAffineNonvanishing X L).trans
      (and_iff_right ‹CompactSpace X›)
  tfae_have 1 ↔ 5 := isAmple_iff_iSup_range_twistHom L
  tfae_have 1 ↔ 6 := isAmple_iff_iSup_range_twistHom_ideal L
  tfae_have 1 ↔ 7 := isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections L
  tfae_have 1 ↔ 8 := isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct L
  tfae_have 1 ↔ 9 := isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct_ideal L
  tfae_finish

end Stacks.AmpleCharacterization

end
