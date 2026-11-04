module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.ShrinkInstances
public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.FibreProductColimit

/-!
# The charting morphism to the spectrum of the fibre product

The second leg of the glueing of Tag 07RN is built, by `Stacks.StageSubalgebra.specLeg`, from a
family of morphisms `γ k : W_k ⟶ Spec B_k` from the models of the overlap to the spectra of the
fibre-product rings.  In the one-affine-open step that family is the canonical composite

`W_k ⟶ Spec Γ(W_k, ⊤) ⟶ Spec (B ×_R Γ(W_k, ⊤))`,

the second factor being the spectrum of the second projection of the fibre product.  This file
proves two facts about it:

* that it is **compatible with the transition morphisms** — the hypothesis `hγ` of
  `Stacks.StageSubalgebra.specLeg`;

* that the localizations of the fibre-product rings at the charting family are of **finite type
  over the integers** — the hypothesis the cofinality of the charted subalgebras runs on, and
  hence what makes the index of pairs nonempty and directed.

## Main results

* `AlgebraicGeometry.toSpecΓ_comp_SpecMap_snd_naturality`: the compatibility with the transition
  morphisms.
* `AlgebraicGeometry.finiteType_localization_away_charting`: the finite-type statement.

## Implementation notes

The compatibility combines Mathlib's `AlgebraicGeometry.Scheme.toSpecΓ_naturality` for the first
factor with `Stacks.FibreProduct.snd_diagramMap` for the second.  The latter holds by
reflexivity — the transition of the diagram of fibre products acts on the second component
only — so the ring identity underneath is `RingHom.ext` of a reflexivity, and the geometry is
three reassociations and `AlgebraicGeometry.Spec.map_comp` twice.  It is proved by
`CommRingCat.hom_ext` and `RingHom.ext` rather than by `simp`, since
`Stacks.FibreProduct.snd_diagramMap` is not a simp lemma, its left-hand side having a different
simp normal form.  The compatibility is stated for the *unfolded* composite rather than for a
named `γ`, so a consumer that names its own `γ` gets it by reflexivity.

The finite-type statement is `AlgebraicGeometry.finiteType_localization_away_of_basicOpen_le` at
the charting morphism; the one hypothesis it needs beyond the charting data is that the *models
of the overlap* are of finite type over the terminal scheme, which they are, being opens of the
stages, by `AlgebraicGeometry.locallyOfFiniteType_terminal_from_opens`.  With it,
`Stacks.StageSubalgebra.isDirected_isChartedSubalgebra` and
`Stacks.StageSubalgebra.nonempty_isChartedSubalgebra` apply, which is what the index fields of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation` need.  It is stated with the rings at the
stages as a *bare family of types* and not as the fibre products themselves: written at the
fibre products, the open-immersion instance is requested at `CommRingCat.of ↥(…)` while the
hypothesis has it at `…`, and the structure-eta step between them is not taken at instance
transparency.  With a bare family the spellings agree, and the one bridge happens at the call
site, where definitional equality is checked at default transparency.

Both statements are written at the spellings the surrounding machinery produces —
`τ₀.app (op (OrderDual.toDual k))` rather than through an abbreviation — because `rw` does not
unfold a `def`.

The stages, the rings and the schemes are in the single universe `u`.  The index of the ring
cocone is the opposite of the dual of the stage preorder, which is where the ring-level results
used here live; `Stacks.preorderToOpDual` reads it back as a diagram over the preorder itself,
and the statements below are at the opposite spelling because that is the spelling the cocone
comes in.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Preorder K] {Dw : Kᵒᵈ ⥤ Scheme.{u}} {R B : CommRingCat.{u}}
  (τ₀ : Dw.op ⋙ Scheme.Γ ⟶ (Functor.const (Kᵒᵈ)ᵒᵖ).obj R) (s : B ⟶ R)

/-- **The charting morphism is compatible with the transition morphisms.**  This is the
hypothesis `hγ` of `Stacks.StageSubalgebra.specLeg`: the first factor by Mathlib's
`AlgebraicGeometry.Scheme.toSpecΓ_naturality`, the second by
`Stacks.FibreProduct.snd_diagramMap`, which holds by reflexivity. -/
lemma toSpecΓ_comp_SpecMap_snd_naturality {k k' : K} (h : k ≤ k') :
    Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫
        ((Dw.obj (OrderDual.toDual k)).toSpecΓ ≫
          Spec.map (Stacks.FibreProduct.snd s (τ₀.app (op (OrderDual.toDual k))))) =
      ((Dw.obj (OrderDual.toDual k')).toSpecΓ ≫
          Spec.map (Stacks.FibreProduct.snd s (τ₀.app (op (OrderDual.toDual k'))))) ≫
        Spec.map (Stacks.FibreProduct.diagramMap (Dw.op ⋙ Scheme.Γ) τ₀ s
          ((homOfLE (OrderDual.toDual_le_toDual.mpr h)).op)) := by
  have hring : Stacks.FibreProduct.diagramMap (Dw.op ⋙ Scheme.Γ) τ₀ s
        ((homOfLE (OrderDual.toDual_le_toDual.mpr h)).op) ≫
          Stacks.FibreProduct.snd s (τ₀.app (op (OrderDual.toDual k'))) =
      Stacks.FibreProduct.snd s (τ₀.app (op (OrderDual.toDual k))) ≫
        (Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h))).appTop :=
    CommRingCat.hom_ext <| RingHom.ext fun x ↦
      Stacks.FibreProduct.snd_diagramMap (Dw.op ⋙ Scheme.Γ) τ₀ s
        ((homOfLE (OrderDual.toDual_le_toDual.mpr h)).op) x
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc]
  exact congrArg (fun m ↦ (Dw.obj (OrderDual.toDual k')).toSpecΓ ≫ m)
    (((Spec.map_comp _ _).symm.trans (congrArg Spec.map hring).symm).trans (Spec.map_comp _ _))

/-- **The localizations of the fibre-product rings at the charting family are of finite type over
the integers.**  This is what the cofinality of the charted subalgebras runs on, and hence what
makes the index of pairs nonempty and directed.

The models of the overlap are opens of the stages, so their finite type over the terminal scheme
is `AlgebraicGeometry.locallyOfFiniteType_terminal_from_opens`; with that, this is
`AlgebraicGeometry.finiteType_localization_away_of_basicOpen_le` at the charting morphism. -/
lemma finiteType_localization_away_charting
    [∀ a : Kᵒᵈ, LocallyOfFiniteType (terminal.from (Dw.obj a))]
    (A : K → Type u) [∀ k, CommRing (A k)]
    (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (.of (A k)))
    (hoi : ∀ k : K, IsOpenImmersion (γ k)) {n : ℕ} (b : ∀ k : K, Fin n → A k)
    (hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (b k l) : (Spec (.of (A k))).Opens) ≤ (γ k).opensRange)
    (k : K) (l : Fin n) :
    Algebra.FiniteType ℤ (Localization.Away (b k l)) :=
  have := hoi k
  finiteType_localization_away_of_basicOpen_le (γ k) (b k l) (hrU k l)

end AlgebraicGeometry
