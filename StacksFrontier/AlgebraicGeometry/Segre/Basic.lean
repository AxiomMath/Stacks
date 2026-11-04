module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.RelativeProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Segre embedding, reduced to a monomorphism between the integral models

**Stacks 01WD** (Constructions of Schemes, Chapter 29) asserts, for every scheme `S`, a closed
immersion `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm + n + m}_S`. Its proof opens with *"It suffices to prove this
when `S = Spec(ℤ)`"*, and this file carries out that reduction and one more:

* **base**: a closed immersion `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ` of the integral models, with **no
  compatibility condition imposed on it**, yields a closed immersion `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙᴺ_S`
  **over `S`** for every base `S`;
* **property**: for the integral models a bare **monomorphism** suffices. The source is proper
  over the terminal scheme and the target is separated over it, so any morphism between them is
  proper, and a proper monomorphism is a closed immersion.

Together these turn Stacks 01WD into a statement with no base scheme, no compatibility clause and
no local condition: *there is a monomorphism of schemes
`ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm+n+m}_ℤ`.* Nothing beyond the morphism itself and its injectivity
has to be checked — in particular none of the affine-chart surjectivity of the source's proof.

`AlgebraicGeometry.ProjectiveSpace n S` is by construction the base change `S ×_{⊤} ℙⁿ_ℤ` of the
integral model along the structure morphism of `S`
(`StacksFrontier/AlgebraicGeometry/Limits/ProjectiveSpace.lean`), so the fibre product
`ℙⁿ_S ×_S ℙᵐ_S` is the base change of `ℙⁿ_ℤ ×_{⊤} ℙᵐ_ℤ`, and the relative Segre morphism is the
base change of the absolute one. Closed immersions are stable under base change, which is the
whole content of the first reduction. The integral models live over the *terminal* scheme, so
"a morphism over the base" is no condition at all downstairs and every square in sight commutes
by `CategoryTheory.Limits.terminal.hom_ext`.

## Main definitions

* `AlgebraicGeometry.HasSegreEmbeddingZ` and `AlgebraicGeometry.HasSegreEmbeddingZSharp`: the
  absolute hypothesis, with the target dimension existential resp. equal to `n * m + n + m`.
* `AlgebraicGeometry.HasSegreMonoZ` and `AlgebraicGeometry.HasSegreMonoZSharp`: the same two
  statements with `IsClosedImmersion` weakened to `CategoryTheory.Mono`. These are the forms in
  which the residue of Stacks 01WD should be attacked.
* `AlgebraicGeometry.HasSegreEmbeddingSharp` is Stacks 01WD for the base `S`, i.e. the predicate
  `AlgebraicGeometry.HasSegreEmbedding` with the existential over the target dimension removed.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_mono_of_isProper_of_comp`: a monomorphism from a scheme
  proper over `S` to a scheme separated over `S`, over `S`, is a closed immersion.
* `AlgebraicGeometry.hasSegreEmbeddingZ_of_hasSegreMonoZ` and
  `AlgebraicGeometry.hasSegreEmbeddingZSharp_of_hasSegreMonoZSharp`: for the integral models a
  monomorphism is already a closed immersion.
* `AlgebraicGeometry.exists_isClosedImmersion_pullback_projectiveSpace_of_projectiveSpaceZ`: the
  base reduction, for a fixed triple `(n, m, N)`.
* `AlgebraicGeometry.hasSegreEmbedding_of_hasSegreEmbeddingZ`: the absolute hypothesis gives
  `AlgebraicGeometry.HasSegreEmbedding S` for **every** base `S`, which is what the proof of
  Chow's lemma over a Noetherian base consumes.
* `AlgebraicGeometry.hasSegreEmbeddingSharp_of_hasSegreEmbeddingZSharp`: the same with the
  explicit dimension on both sides.
* `AlgebraicGeometry.IsPullback.of_isPullback_four`: the fibre-product associativity behind the
  base reduction, stated for cartesian squares rather than for `pullback` objects.

## Implementation notes

No `@[stacks 01WD]` attribute is attached to anything here. Every result in this file is
conditional on an absolute Segre embedding, and 01WD asserts its conclusion outright; the tag
belongs on `AlgebraicGeometry.hasSegreEmbeddingSharp_of_hasSegreEmbeddingZSharp` composed with a
proof of `AlgebraicGeometry.HasSegreEmbeddingZSharp`, and nothing in this repository proves that.

What the absolute statement still needs is the morphism, and the source builds it from Stacks
01NE out of `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` and the sections `XᵢYⱼ`. Both ends of that are present:
`Stacks.ProjectiveSpaceSections.morphismAtUniverse`
(`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceSections/Glue.lean`) is 01NE — a morphism
to projective space from an invertible `X.Modules` with global sections whose nonvanishing loci
cover — and `AlgebraicGeometry.ProjectiveSpaceZ n` is *definitionally* an
`AlgebraicGeometry.Proj`, so `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`
(`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwist.lean:166`) is its `𝒪(1)`. Four things
are missing in between, and none of them is the geometry of 01WD: the twisting sheaf is a
`SheafOfModules` over `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf` rather than an
`AlgebraicGeometry.Scheme.Modules`, and 01NE consumes the latter; its invertibility is not
recorded; the pullback along the two projections and the tensor product of the results are not
formed; and the `(n+1)(m+1)` sections `XᵢYⱼ` of that tensor product, and the fact that their
nonvanishing loci cover, are not constructed.

The alternative route — `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective`
(`StacksFrontier/AlgebraicGeometry/ProjClosedImmersion/Basic.lean`, which is Stacks 01N0
part (2)) applied to the surjection of `ℤ[Z₀, …, Z_N]` onto the Segre subring
`⨁_d ℤ[X]_d ⊗ ℤ[Y]_d` — needs instead an isomorphism of `Proj` of that subring with the fibre
product, and the graded subring itself does not exist in this library: there is no bigraded ring
and no `GradedRing` structure on a tensor product of two graded rings anywhere.

The projective space used here is the capital `AlgebraicGeometry.ProjectiveSpace` of
`StacksFrontier/AlgebraicGeometry/Limits/ProjectiveSpace.lean`, because that is the one
`AlgebraicGeometry.HasSegreEmbedding` and `AlgebraicGeometry.HasChowModification` are stated
against. The repository's lowercase `AlgebraicGeometry.projectiveSpaceOver` is *definitionally
the same scheme* (`StacksFrontier/AlgebraicGeometry/HProjectiveProper/Basic.lean`), so no
second notion is involved and no third is introduced.

The chain of cartesian squares is assembled from `CategoryTheory.IsPullback.of_hasPullback` by
`CategoryTheory.IsPullback.paste_horiz` and `CategoryTheory.IsPullback.of_right`, and nothing
here is a recursive definition over a list, so no transparency option is needed; compare the
implementation notes of
`StacksFrontier/AlgebraicGeometry/ChowNoetherian/RelativeProduct.lean`.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Fibre-product associativity, in the form a base change needs.** Given cartesian squares
exhibiting `A` as `S ×_Z X`, `B` as `S ×_Z Y`, `Q` as `X ×_Z Y` and `W` as `A ×_S B`, together
with a morphism `ρ : W ⟶ Q` over `X` and over `Y`, the square exhibiting `W` as `S ×_Z Q` is
cartesian. -/
theorem IsPullback.of_isPullback_four {C : Type*} [Category C] {Z S X Y A B Q W : C}
    {tS : S ⟶ Z} {tX : X ⟶ Z} {tY : Y ⟶ Z} {a : A ⟶ S} {aX : A ⟶ X} {b : B ⟶ S} {bY : B ⟶ Y}
    {qX : Q ⟶ X} {qY : Q ⟶ Y} {p : W ⟶ A} {r : W ⟶ B} {ρ : W ⟶ Q}
    (hA : IsPullback a aX tS tX) (hB : IsPullback b bY tS tY) (hQ : IsPullback qX qY tX tY)
    (hW : IsPullback p r a b) (hρX : ρ ≫ qX = p ≫ aX) (hρY : ρ ≫ qY = r ≫ bY) :
    IsPullback (p ≫ a) ρ tS (qX ≫ tX) := by
  -- `W = A ×_Z Y`, by pasting the square for `B` onto the square for `W`
  have hJ := hW.flip.paste_horiz hB.flip
  -- hence `W = A ×_X Q`, by cancelling the square for `Q`
  have hF : IsPullback ρ p qX aX := by
    refine IsPullback.of_right ?_ hρX hQ.flip
    rw [hρY, ← hA.w]
    exact hJ
  -- and finally `W = S ×_Z Q`, by pasting the square for `A`
  exact hF.flip.paste_horiz hA

/-- **A monomorphism from a proper scheme into a separated one is a closed immersion.** If
`f : X ⟶ S` is proper, `g : Y ⟶ S` is separated and `θ : X ⟶ Y` is a monomorphism with
`θ ≫ g = f`, then `θ` is a closed immersion.

`θ` is proper because `f` is and `g` is separated, and a proper monomorphism is a closed
immersion, which is Stacks 04XV. -/
@[ega "IV 18.12.6" "(b)⇒(a)", ega "IV 8.11.5" "b ⇒ a", sga "3 VIB 1.4.2" "more general"]
theorem isClosedImmersion_of_mono_of_isProper_of_comp {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (θ : X ⟶ Y) (hθ : θ ≫ g = f) [IsProper f] [IsSeparated g] [Mono θ] :
    IsClosedImmersion θ := by
  have hp : IsProper (θ ≫ g) := by rw [hθ]; infer_instance
  exact (IsClosedImmersion.iff_isProper_and_mono θ).mpr ⟨IsProper.of_comp θ g, ‹Mono θ›⟩

/-- **The Segre embedding of the integral models.** For all `n` and `m` there are an `N` and a
closed immersion `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ`, where `Spec ℤ` is realised as the terminal
scheme.

No compatibility with the maps to `Spec ℤ` is asked for, because there is only one such map out
of each scheme. -/
def HasSegreEmbeddingZ : Prop :=
  ∀ n m : ℕ, ∃ (N : ℕ) (e : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} N), IsClosedImmersion e

/-- **Stacks 01WD for the integral models**: a closed immersion
`ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm + n + m}_ℤ`, with the dimension the source produces. -/
def HasSegreEmbeddingZSharp : Prop :=
  ∀ n m : ℕ, ∃ e : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} (n * m + n + m),
    IsClosedImmersion e

/-- **The Segre embedding of the integral models, asked for only as a monomorphism.** This is
equivalent to `AlgebraicGeometry.HasSegreEmbeddingZ` — see
`AlgebraicGeometry.hasSegreEmbeddingZ_of_hasSegreMonoZ` — and is the weakest form in which the
residue of Stacks 01WD can be stated. -/
def HasSegreMonoZ : Prop :=
  ∀ n m : ℕ, ∃ (N : ℕ) (e : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} N), Mono e

/-- **Stacks 01WD for the integral models, asked for only as a monomorphism.** -/
def HasSegreMonoZSharp : Prop :=
  ∀ n m : ℕ, ∃ e : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} (n * m + n + m), Mono e

/-- **Stacks 01WD for the base `S`.** The fibre product over `S` of `ℙⁿ_S` and `ℙᵐ_S` admits a
closed immersion into `ℙ^{nm + n + m}_S` over `S`.

This is `AlgebraicGeometry.HasSegreEmbedding` with the existential over the target dimension
replaced by the dimension Stacks 01WD actually produces, so it is strictly stronger. -/
def HasSegreEmbeddingSharp (S : Scheme.{u}) : Prop :=
  ∀ n m : ℕ, ∃ e : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶
      ProjectiveSpace (n * m + n + m) S,
    IsClosedImmersion e ∧ e ≫ (ProjectiveSpace (n * m + n + m) S ↘ S) =
      pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
        (ProjectiveSpace n S ↘ S)

/-- A closed immersion `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm + n + m}_ℤ` for all `n` and `m` gives
`AlgebraicGeometry.HasSegreEmbeddingZ`, with `N = n * m + n + m`. -/
theorem HasSegreEmbeddingZSharp.hasSegreEmbeddingZ (h : HasSegreEmbeddingZSharp.{u}) :
    HasSegreEmbeddingZ.{u} := by
  intro n m
  obtain ⟨e, he⟩ := h n m
  exact ⟨n * m + n + m, e, he⟩

/-- A monomorphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm + n + m}_ℤ` for all `n` and `m` gives
`AlgebraicGeometry.HasSegreMonoZ`, with `N = n * m + n + m`. -/
theorem HasSegreMonoZSharp.hasSegreMonoZ (h : HasSegreMonoZSharp.{u}) :
    HasSegreMonoZ.{u} := by
  intro n m
  obtain ⟨e, he⟩ := h n m
  exact ⟨n * m + n + m, e, he⟩

/-- `AlgebraicGeometry.HasSegreEmbeddingSharp S` implies `AlgebraicGeometry.HasSegreEmbedding S`,
with target dimension `n * m + n + m`. -/
theorem HasSegreEmbeddingSharp.hasSegreEmbedding {S : Scheme.{u}}
    (h : HasSegreEmbeddingSharp S) : HasSegreEmbedding S := by
  intro n m
  obtain ⟨e, he, hc⟩ := h n m
  exact ⟨n * m + n + m, e, he, hc⟩

/-- **The fibre product of the two integral models is proper over the terminal scheme.** -/
theorem isProper_terminal_from_pullback (n m : ℕ) :
    IsProper (terminal.from (pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)))) := by
  have hn := ProjectiveSpace.isProper_terminal_from.{u} n
  have hm := ProjectiveSpace.isProper_terminal_from.{u} m
  have h : terminal.from (pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m))) =
      pullback.fst (terminal.from (ProjectiveSpaceZ.{u} n))
        (terminal.from (ProjectiveSpaceZ.{u} m)) ≫ terminal.from (ProjectiveSpaceZ.{u} n) :=
    terminal.hom_ext _ _
  rw [h]
  infer_instance

/-- **A monomorphism between the integral models is already a closed immersion.** The source is
proper over the terminal scheme and the target is separated over it, so the morphism is proper
by `AlgebraicGeometry.IsProper.of_comp`, and a proper monomorphism is a closed immersion by
Stacks 04XV. -/
theorem isClosedImmersion_of_mono_projectiveSpaceZ {n m N : ℕ}
    (e : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} N) [Mono e] :
    IsClosedImmersion e := by
  have := isProper_terminal_from_pullback.{u} n m
  have := ProjectiveSpace.isProper_terminal_from.{u} N
  exact isClosedImmersion_of_mono_of_isProper_of_comp
    (terminal.from (pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m))))
    (terminal.from (ProjectiveSpaceZ.{u} N)) e (terminal.hom_ext _ _)

/-- If for all `n` and `m` there is a monomorphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ` for some `N`,
then there is a closed immersion of the same form. -/
theorem hasSegreEmbeddingZ_of_hasSegreMonoZ (h : HasSegreMonoZ.{u}) : HasSegreEmbeddingZ.{u} := by
  intro n m
  obtain ⟨N, e, he⟩ := h n m
  exact ⟨N, e, isClosedImmersion_of_mono_projectiveSpaceZ e⟩

/-- If for all `n` and `m` there is a monomorphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm + n + m}_ℤ`,
then there is a closed immersion of the same form. -/
theorem hasSegreEmbeddingZSharp_of_hasSegreMonoZSharp (h : HasSegreMonoZSharp.{u}) :
    HasSegreEmbeddingZSharp.{u} := by
  intro n m
  obtain ⟨e, he⟩ := h n m
  exact ⟨e, isClosedImmersion_of_mono_projectiveSpaceZ e⟩

/-- **The Segre embedding over an arbitrary base is the base change of the absolute one.** A
closed immersion `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ` of the integral models induces, for every base
scheme `S`, a closed immersion `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙᴺ_S` compatible with the structure morphisms
to `S`.

This is the first sentence of the proof of Stacks 01WD, *"It suffices to prove this when
`S = Spec(ℤ)`"*. -/
theorem exists_isClosedImmersion_pullback_projectiveSpace_of_projectiveSpaceZ {n m N : ℕ}
    (e₀ : pullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)) ⟶ ProjectiveSpaceZ.{u} N)
    (he₀ : IsClosedImmersion e₀) (S : Scheme.{u}) :
    ∃ e : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶ ProjectiveSpace N S,
      IsClosedImmersion e ∧ e ≫ (ProjectiveSpace N S ↘ S) =
        pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
          (ProjectiveSpace n S ↘ S) := by
  -- the defining cartesian squares of the three relative projective spaces
  have hA : IsPullback (ProjectiveSpace n S ↘ S)
      (pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n)))
      (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n)) :=
    IsPullback.of_hasPullback _ _
  have hB : IsPullback (ProjectiveSpace m S ↘ S)
      (pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} m)))
      (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} m)) :=
    IsPullback.of_hasPullback _ _
  have hN : IsPullback (ProjectiveSpace N S ↘ S)
      (pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} N)))
      (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} N)) :=
    IsPullback.of_hasPullback _ _
  -- the morphism from `ℙⁿ_S ×_S ℙᵐ_S` to the absolute fibre product
  obtain ⟨ρ, hρX, hρY⟩ :
      ∃ ρ : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶
        pullback (terminal.from (ProjectiveSpaceZ.{u} n))
          (terminal.from (ProjectiveSpaceZ.{u} m)),
        ρ ≫ pullback.fst (terminal.from (ProjectiveSpaceZ.{u} n))
              (terminal.from (ProjectiveSpaceZ.{u} m)) =
            pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
              pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n)) ∧
        ρ ≫ pullback.snd (terminal.from (ProjectiveSpaceZ.{u} n))
              (terminal.from (ProjectiveSpaceZ.{u} m)) =
            pullback.snd (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
              pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} m)) :=
    ⟨pullback.lift _ _ (terminal.hom_ext _ _), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- `ℙⁿ_S ×_S ℙᵐ_S = S ×_{⊤} (ℙⁿ_ℤ ×_{⊤} ℙᵐ_ℤ)`
  have hW := IsPullback.of_isPullback_four hA hB
    (IsPullback.of_hasPullback (terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from (ProjectiveSpaceZ.{u} m)))
    (IsPullback.of_hasPullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S)) hρX hρY
  -- the relative Segre morphism, as a lift into `ℙᴺ_S = S ×_{⊤} ℙᴺ_ℤ`
  obtain ⟨e, hefst, hesnd⟩ :
      ∃ e : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶ ProjectiveSpace N S,
        e ≫ (ProjectiveSpace N S ↘ S) =
            pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
              (ProjectiveSpace n S ↘ S) ∧
          e ≫ pullback.snd (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} N)) =
            ρ ≫ e₀ :=
    ⟨pullback.lift _ _ (terminal.hom_ext _ _), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- it is the base change of `e₀` along `S ⟶ Spec ℤ`
  have heq : e₀ ≫ terminal.from (ProjectiveSpaceZ.{u} N) =
      pullback.fst (terminal.from (ProjectiveSpaceZ.{u} n))
        (terminal.from (ProjectiveSpaceZ.{u} m)) ≫ terminal.from (ProjectiveSpaceZ.{u} n) :=
    terminal.hom_ext _ _
  have hs : IsPullback ρ (e ≫ (ProjectiveSpace N S ↘ S))
      (e₀ ≫ terminal.from (ProjectiveSpaceZ.{u} N)) (terminal.from S) := by
    rw [hefst, heq]
    exact hW.flip
  exact ⟨e, MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_bot hs hesnd.symm hN.flip) he₀, hefst⟩

/-- **The Segre embedding over the integral models gives it over every base.** Granted
`AlgebraicGeometry.HasSegreEmbeddingZ`, the hypothesis `AlgebraicGeometry.HasSegreEmbedding S`
consumed by the proof of Chow's lemma over a Noetherian base holds for every `S`. -/
theorem hasSegreEmbedding_of_hasSegreEmbeddingZ (h : HasSegreEmbeddingZ.{u}) (S : Scheme.{u}) :
    HasSegreEmbedding S := by
  intro n m
  obtain ⟨N, e₀, he₀⟩ := h n m
  exact ⟨N, exists_isClosedImmersion_pullback_projectiveSpace_of_projectiveSpaceZ e₀ he₀ S⟩

/-- **Stacks 01WD over the integral models gives Stacks 01WD over every base**, with the explicit
dimension `n * m + n + m` on both sides. -/
theorem hasSegreEmbeddingSharp_of_hasSegreEmbeddingZSharp (h : HasSegreEmbeddingZSharp.{u})
    (S : Scheme.{u}) : HasSegreEmbeddingSharp S := by
  intro n m
  obtain ⟨e₀, he₀⟩ := h n m
  exact exists_isClosedImmersion_pullback_projectiveSpace_of_projectiveSpaceZ e₀ he₀ S

end AlgebraicGeometry

end
