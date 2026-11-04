module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsChartExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsRankInduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsRepresentability

/-!
# The generic-rank locus as a locally closed immersion

In the situation of Tag 05MP — a smooth morphism `f : X ⟶ S` with geometrically irreducible
fibres together with a finite type quasi-coherent module `ℱ` on `X` — the functor `H_p` of
Tag 05MR sends a scheme `T` over `S` to a singleton exactly when the base change `ℱ_T` is free
of rank `p` in a neighbourhood of the generic point `ξ_t` of the fibre `X_t`, for every
`t ∈ T`. Tag 05UC asserts that `H_p` is representable by a locally closed immersion
`S_p ⟶ S`, and that `S_p ⟶ S` is of finite presentation when `ℱ` is.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.isImmersion_representableBy_fittingRankStratum`:
  the first assertion of Tag 05UC, also stated as `exists_immersion_representableBy` and as
  `AlgebraicGeometry.freeAtGenericPointsFunctor_representableBy_immersion`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.finitePresentation_hom_of_representableBy`:
  the second assertion, for every morphism representing `H_p`, also stated as
  `AlgebraicGeometry.finitePresentation_of_representableBy_freeAtGenericPointsFunctor`.

## Implementation notes

The proof is the source's. Every point `s` of the base has a rank `p(s)`: the module pulled back
to the fibre over `s` is free of rank `p(s)` near the generic point of that fibre. Around `s`
there is a chart: an affine open `V ∋ s`, an affine open `U` of `X` surjecting onto `V`, and a
surjection `𝒪_U^{⊕ p(s)} ⟶ ℱ|_U`. Over `V` the functor `H_{p(s)}` is the functor `F_iso` of that
surjection, so Theorem 05PF represents it by a closed immersion, while `H_q` is empty over `V` for
`q > p(s)` and lives over the open complement of the closed stratum for `q < p(s)`, where the rank
drops; induction on the maximal rank gives representatives over the charts, and these glue
(Stacks 02W5, 02W8, 02YM), see
`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_representsOn_top`.

When `ℱ` is of finite presentation the representing immersion is locally of finite presentation
because `H_p` is limit preserving (Stacks 05MS (2), 05LX), quasi-compact because along the
induction each stratum is quasi-compact over affine opens (the complement of a closed immersion
of finite presentation into an affine scheme is quasi-compact), and quasi-separated because a
representing morphism of a subterminal functor is a monomorphism. Any two representatives are
isomorphic over the base, so the assertion holds for every representative.

The source's "locally closed immersion" is Mathlib's `AlgebraicGeometry.IsImmersion`, and the
source's "of finite presentation" is `AlgebraicGeometry.FinitePresentation` as pinned down by
Tag 01TP.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- The generic-rank functor has a section over `T` exactly when `T` satisfies the
generic-point freeness condition. -/
theorem nonempty_freeAtGenericPointsFunctor_obj_iff (T : Over D.S) :
    Nonempty ((D.freeAtGenericPointsFunctor p).obj (Opposite.op T)) ↔ D.Condition p T :=
  ⟨fun h ↦ h.some.down.down, fun h ↦ ⟨⟨⟨h⟩⟩⟩⟩

/-- An immersion representing the generic-point condition over the whole base represents the
generic-rank functor. -/
noncomputable def representableByOfRepresentsOn {Z : Scheme.{u}} {i : Z ⟶ D.S}
    (h : Stacks.Flatness.RepresentsOn (D.condProp p) ⊤ i) :
    (D.freeAtGenericPointsFunctor p).RepresentableBy (Over.mk i) :=
  representableByOfSubsingleton _ (Over.mk i) h.mono fun T ↦ by
    rw [D.nonempty_freeAtGenericPointsFunctor_obj_iff p T]
    refine (h.2.2 T.left T.hom (fun _ _ ↦ trivial)).trans ?_
    exact ⟨fun ⟨b, hb⟩ ↦ ⟨Over.homMk b hb⟩, fun ⟨b⟩ ↦ ⟨b.left, Over.w b⟩⟩

/-- The generic-point condition is represented over the whole base by an immersion, which is
quasi-compact when the module is of finite presentation. -/
theorem exists_representsOn_top' :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), Stacks.Flatness.RepresentsOn (D.condProp p) ⊤ i ∧
      (D.F.IsFinitePresentation → Stacks.Flatness.QCOn ⊤ i) :=
  D.exists_representsOn_top (D.exists_condition_residueField)
    (fun _ W hs _ hq ↦ D.exists_chart W hs hq) p

/-- **Stacks Project, Tag 05UC.** In Situation 05MP, for each `p ≥ 0` the functor `H_p` of
05MR is representable by a locally closed immersion `S_p ⟶ S`. -/
@[stacks 05UC "representability of H_p by a locally closed immersion"]
theorem isImmersion_representableBy_fittingRankStratum :
    ∃ W : Over D.S, IsImmersion W.hom ∧
      Nonempty ((D.freeAtGenericPointsFunctor p).RepresentableBy W) := by
  obtain ⟨Z, i, h, -⟩ := D.exists_representsOn_top' p
  exact ⟨Over.mk i, h.1, ⟨D.representableByOfRepresentsOn p h⟩⟩

/-- In Situation 05MP, for each `p ≥ 0` the functor `H_p` of 05MR is representable by a locally
closed immersion `S_p ⟶ S`; the same statement as
`AlgebraicGeometry.FreeAtGenericPointsSituation.isImmersion_representableBy_fittingRankStratum`. -/
alias exists_immersion_representableBy :=
  AlgebraicGeometry.FreeAtGenericPointsSituation.isImmersion_representableBy_fittingRankStratum

/-- **Stacks Project, Tag 05UC.** In Situation 05MP, if `ℱ` is of finite presentation then
`S_p ⟶ S` is of finite presentation.

The assertion is proved for an arbitrary morphism representing the generic-rank functor, which
is legitimate because any two representatives are isomorphic over the base. -/
@[stacks 05UC "finite presentation of S_p ⟶ S when the module is of finite presentation"]
theorem finitePresentation_hom_of_representableBy [D.F.IsFinitePresentation]
    {W : Over D.S} (e : (D.freeAtGenericPointsFunctor p).RepresentableBy W) :
    FinitePresentation W.hom := by
  obtain ⟨Z, i, h, hqc⟩ := D.exists_representsOn_top' p
  have e₀ := D.representableByOfRepresentsOn p h
  have hqc₀ : QuasiCompact (Over.mk i).hom :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun U hU ↦
      hqc inferInstance U le_top hU
  exact FinitePresentation.mk
    (D.locallyOfFinitePresentation_hom_of_representableBy p e)
    (Stacks.Flatness.quasiCompact_hom_of_representableBy e₀ e hqc₀)
    (Stacks.Flatness.quasiSeparated_hom_of_representableBy e)

end FreeAtGenericPointsSituation

/-- The generic-rank functor is represented by a locally closed immersion into the base: the
first assertion of Tag 05UC, in the form
`AlgebraicGeometry.FreeAtGenericPointsSituation.isImmersion_representableBy_fittingRankStratum`. -/
theorem freeAtGenericPointsFunctor_representableBy_immersion
    (D : FreeAtGenericPointsSituation.{u}) (p : ℕ) :
    ∃ W : Over D.S, IsImmersion W.hom ∧
      Nonempty ((D.freeAtGenericPointsFunctor p).RepresentableBy W) :=
  D.isImmersion_representableBy_fittingRankStratum p

/-- When the module is of finite presentation, every morphism representing the generic-rank
functor is of finite presentation: the second assertion of Tag 05UC, in the form
`AlgebraicGeometry.FreeAtGenericPointsSituation.finitePresentation_hom_of_representableBy`. -/
theorem finitePresentation_of_representableBy_freeAtGenericPointsFunctor
    (D : FreeAtGenericPointsSituation.{u}) (p : ℕ) [D.F.IsFinitePresentation]
    (W : Over D.S)
    (hW : Nonempty ((D.freeAtGenericPointsFunctor p).RepresentableBy W)) :
    FinitePresentation W.hom :=
  D.finitePresentation_hom_of_representableBy p hW.some

end AlgebraicGeometry

end
