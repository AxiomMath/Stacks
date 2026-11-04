module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.ChowConsumption
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementFibreProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inner affine refinement of a standard ph covering along a Chow modification

Stacks 0DBF part (2) refines the composite `E.bind F` of two successive standard ph coverings of
an affine scheme `T` by a single standard ph covering. Writing `g : U ⟶ T` for the proper
surjection presenting the outer covering `E` and `jj i : E.X i ⟶ U` for its affine open
covering, the Stacks proof proceeds in two stages, and the fibre-product stage 2 is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementFibreProduct`:

1. each proper surjection `g i : W i ⟶ E.X i` presenting the inner covering `F i` is replaced by
   a morphism proper over the *whole* of `U` whose part over `E.X i` still carries the members of
   `F i`;
2. the resulting proper surjections `V i ⟶ U` are multiplied together over `U`.

This file completes stage 1. Chow's lemma (Stacks 0202) replaces `W i` by a proper surjective
modification `W' ⟶ W i` closed-immersed in `ℙⁿ_{E.X i}`, and the compactification step of
`AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_isClosedImmersion` then needs an
affine open covering **of `W'`**, each member mapping over `U` into a member of some `F i'`. The
members of `F i` are affine opens of `W i`, but `W' ⟶ W i` is only proper surjective, so they do
not pull back to affine opens of `W'`. What survives is that the preimage of an affine open is a
*quasi-compact* open, and a quasi-compact open is covered by finitely many affine opens; that is
`AlgebraicGeometry.exists_finite_affine_cover_of_quasiCompact` below, the sole mathematical
content of the step.

## Main results

* `AlgebraicGeometry.exists_finite_affine_cover_of_quasiCompact`: along a quasi-compact morphism
  `q : W' ⟶ W`, a finite covering of `W` by quasi-compact opens is refined by a finite covering
  of `W'` by affine opens, each mapping through `q` into a prescribed member of the given
  covering.
* `AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_hasChowModification`: **stage 1
  of Stacks 0DBF part (2)**, granted Chow's lemma for the single proper morphism it is applied
  to. A proper surjection onto an affine scheme `Uj`, open in `U`, whose source is covered by
  finitely many affine opens, yields a proper surjection onto `U` whose part over `Uj` is
  covered by finitely many affine opens mapping into that same family.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma`: Stacks 0DBF
  part (2), with Chow's lemma for proper morphisms onto affine schemes as an explicit
  hypothesis.

## Implementation notes

The last result is deliberately **not** given the Stacks 0DBF part (2) attribute. Its hypothesis
`hchow` is Stacks 0202, which this development does not prove; tagging the statement would
assert part (2) while assuming the one thing it still rests on. The same reasoning keeps the tag
off `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_extension`.

`AlgebraicGeometry.exists_finite_affine_cover_of_quasiCompact` produces its index type as
`Fin N`, because that is the shape in which
`AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_isClosedImmersion` consumes an
affine open covering; the natural index type is `Σ s, Fin (m s)`, and the two are reconciled by
`Finite.exists_equiv_fin`.

Two side conditions of the compactification step are discharged topologically rather than
geometrically. `QuasiCompact (i ≫ ℙⁿ_{Uj} ⟶ ℙⁿ_U)` holds because `W'` is a compact space
(it is proper over the affine `Uj`) and `ℙⁿ_U` is a quasi-separated space; the latter needs `U`
itself to be quasi-separated, which is why `QuasiSeparatedSpace U` appears as a hypothesis of
stage 1 and is supplied from `IsProper g` and `IsAffine T` at the Stacks 0DBF call site.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- **The inner affine refinement.** Let `q : W' ⟶ W` be a quasi-compact morphism of schemes and
let `κ s : Y s ⟶ W` be a finite family of open immersions covering `W` whose sources are
quasi-compact. Then `W'` is covered by finitely many affine opens `α k : A k ⟶ W'`, each of which
maps through `q` into one of the `Y s`.

The preimage under `q` of the range of `κ s` is a quasi-compact open of `W'`, so it is covered by
finitely many affine opens of `W'` contained in it
(`AlgebraicGeometry.exists_finite_affineOpens_subset_of_isCompact`); such an affine open maps
through `q` into the range of `κ s`, hence through `κ s` by
`AlgebraicGeometry.IsOpenImmersion.lift`. Since the `κ s` cover `W` and the index type is finite,
finitely many affine opens are obtained in all and they cover `W'`.

The sources `Y s` are *not* assumed affine: nothing more than quasi-compactness of their ranges
is used, and the conclusion does not place `Y s` in the covering. -/
@[ega "IV 1.8.1" "more general"]
theorem exists_finite_affine_cover_of_quasiCompact {W' W : Scheme.{u}} (q : W' ⟶ W)
    [QuasiCompact q] {S : Type v} [Finite S] {Y : S → Scheme.{u}} (κ : ∀ s, Y s ⟶ W)
    [∀ s, IsOpenImmersion (κ s)] [∀ s, CompactSpace (Y s)]
    (hκ : (⋃ s, Set.range (κ s)) = Set.univ) :
    ∃ (n : ℕ) (A : Fin n → Scheme.{u}) (α : ∀ k, A k ⟶ W') (σ : Fin n → S)
      (b : ∀ k, A k ⟶ Y (σ k)), (∀ k, IsAffine (A k)) ∧ (∀ k, IsOpenImmersion (α k)) ∧
      (∀ k, α k ≫ q = b k ≫ κ (σ k)) ∧ (⋃ k, Set.range (α k)) = Set.univ := by
  classical
  have hc : ∀ s, IsCompact ((q ⁻¹ᵁ (κ s).opensRange : W'.Opens) : Set W') := by
    intro s
    have h : IsCompact (((κ s).opensRange : W.Opens) : Set W) := isCompact_range (κ s).continuous
    rw [Scheme.Hom.coe_preimage]
    exact q.isCompact_preimage h
  choose m V hVaff hVle hVcov using
    fun s => exists_finite_affineOpens_subset_of_isCompact (q ⁻¹ᵁ (κ s).opensRange) (hc s)
  have hrange : ∀ s (l : Fin (m s)), Set.range ((V s l).ι ≫ q) ⊆ Set.range (κ s) := by
    intro s l x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : (V s l).ι y ∈ (q ⁻¹ᵁ (κ s).opensRange : W'.Opens) := hVle s l y.2
    rw [Scheme.Hom.comp_apply]
    exact hy
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ s : S, Fin (m s))
  refine ⟨N, fun k => (V (e.symm k).1 (e.symm k).2).toScheme,
    fun k => (V (e.symm k).1 (e.symm k).2).ι, fun k => (e.symm k).1,
    fun k => IsOpenImmersion.lift (κ (e.symm k).1) ((V (e.symm k).1 (e.symm k).2).ι ≫ q)
      (hrange _ _),
    fun k => hVaff _ _, fun k => inferInstance,
    fun k => (IsOpenImmersion.lift_fac _ _ (hrange _ _)).symm, ?_⟩
  rw [e.symm.surjective.iUnion_comp fun p : Σ s : S, Fin (m s) => Set.range (V p.1 p.2).ι,
    Set.eq_univ_iff_forall]
  intro x
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hκ ▸ Set.mem_univ (q x))
  have hx : x ∈ (q ⁻¹ᵁ (κ s).opensRange : W'.Opens) := hs
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hVcov s hx)
  exact Set.mem_iUnion.mpr ⟨⟨s, l⟩, by rw [Scheme.Opens.range_ι]; exact hl⟩

/-- **Stage 1 of the proof of Stacks 0DBF part (2), granted Chow's lemma for the morphism it is
applied to.** Let `jj : Uj ⟶ U` be an affine open of a quasi-separated scheme `U`, let
`gj : Wj ⟶ Uj` be proper and surjective, and let `Wj` be covered by finitely many affine opens
`κ s : Y s ⟶ Wj` lying over morphisms `y s : Y s ⟶ U`. If Chow's lemma holds for `gj`, then there
is a proper surjection `π : V ⟶ U` whose part over `Uj` is covered by finitely many affine opens,
each mapping over `U` through one of the `y s`.

Chow's lemma supplies a proper surjective modification `p : W' ⟶ Wj` and a closed immersion of
`W'` into `ℙⁿ_{Uj}`, upgraded from an immersion by
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_hasChowModification`. The affine
opens of `Wj` are transported to `W'` by
`AlgebraicGeometry.exists_finite_affine_cover_of_quasiCompact`, and
`AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_isClosedImmersion` takes the
scheme-theoretic closure of `W'` in `ℙⁿ_U` and glues a closed subscheme of `U` onto the
complement of `Uj` to make it surjective. -/
theorem exists_isProper_surjective_affine_cover_of_hasChowModification {U Uj Wj : Scheme.{u}}
    [QuasiSeparatedSpace U] (jj : Uj ⟶ U) [IsOpenImmersion jj] [IsAffine Uj] (gj : Wj ⟶ Uj)
    [IsProper gj] [Surjective gj] (hchow : HasChowModification gj) {S : Type v} [Finite S]
    {Y : S → Scheme.{u}} (κ : ∀ s, Y s ⟶ Wj) (y : ∀ s, Y s ⟶ U) [∀ s, IsOpenImmersion (κ s)]
    [∀ s, IsAffine (Y s)] (hκ : (⋃ s, Set.range (κ s)) = Set.univ)
    (hy : ∀ s, κ s ≫ gj ≫ jj = y s) :
    ∃ (V : Scheme.{u}) (π : V ⟶ U), IsProper π ∧ Surjective π ∧
      ∃ (n : ℕ) (A : Fin n → Scheme.{u}) (α : ∀ k, A k ⟶ V) (σ : Fin n → S)
        (b : ∀ k, A k ⟶ Y (σ k)), (∀ k, IsAffine (A k)) ∧ (∀ k, IsOpenImmersion (α k)) ∧
        (∀ k, α k ≫ π = b k ≫ y (σ k)) ∧
        π ⁻¹' Set.range jj ⊆ ⋃ k, Set.range (α k) := by
  obtain ⟨n, W', p, imm, hp, hps, himm, hcomm⟩ :=
    exists_isClosedImmersion_projectiveSpace_of_hasChowModification gj hchow
  have hpp : IsProper p := hp
  have hpsurj : Surjective p := hps
  have hcs : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (p ≫ gj)
  have hqs : QuasiSeparatedSpace (ProjectiveSpace n U) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace n U ↘ U)
  have hci : IsClosedImmersion imm := himm
  have hqc : QuasiCompact (imm ≫ ProjectiveSpace.baseChangeMap n jj) := inferInstance
  have hkey : imm ≫ ProjectiveSpace.baseChangeMap n jj ≫ (ProjectiveSpace n U ↘ U)
      = p ≫ gj ≫ jj := by
    rw [ProjectiveSpace.baseChangeMap_over, ← Category.assoc, ← hcomm, Category.assoc]
  obtain ⟨N, A, α, σ, b, hAaff, hαopen, hαfac, hαcov⟩ :=
    exists_finite_affine_cover_of_quasiCompact p κ hκ
  have hsurj : Set.range jj ⊆
      Set.range (imm ≫ ProjectiveSpace.baseChangeMap n jj ≫ (ProjectiveSpace n U ↘ U)) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz⟩ := gj.surjective t
    obtain ⟨r, hr⟩ := p.surjective z
    exact ⟨r, by rw [hkey, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hr, hz]⟩
  have hfac : ∀ k, α k ≫ imm ≫ ProjectiveSpace.baseChangeMap n jj ≫
      (ProjectiveSpace n U ↘ U) = b k ≫ y (σ k) := by
    intro k
    rw [hkey, ← Category.assoc, hαfac k, Category.assoc, hy (σ k)]
  obtain ⟨V, π, hπ, hπs, α', hα'open, hα'fac, hα'cov⟩ :=
    exists_isProper_surjective_affine_cover_of_isClosedImmersion y
      (ProjectiveSpace n U ↘ U) (ProjectiveSpace.baseChangeMap n jj) imm
      (O := Set.range jj) jj.opensRange.isOpen (ProjectiveSpace.range_baseChangeMap n jj)
      hsurj α b hαopen hfac hαcov
  exact ⟨V, π, hπ, hπs, N, A, α', σ, b, hAaff, hα'open, hα'fac, hα'cov⟩

/-- **Stacks Project, Tag 0DBF, part (2), granted Chow's lemma.** The composite `E.bind F` of a
standard ph covering `E` of an affine scheme `T` with standard ph coverings `F i` of its members
has a refinement which is a standard ph covering of `T`.

The hypothesis `hchow` is Chow's lemma (Stacks 0202) for a proper morphism onto an affine scheme,
which is all that the Stacks proof of part (2) uses; it is the only thing this development still
owes here. Given it, stage 1 is
`AlgebraicGeometry.exists_isProper_surjective_affine_cover_of_hasChowModification` and stage 2 is
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_extension`.

This statement carries no Stacks 0DBF attribute: it assumes Stacks 0202, so tagging it would
assert part (2) on the strength of an unproved hypothesis. -/
theorem exists_standardPHCovering_refinement_bind_of_chowLemma {T : Scheme.{u}} [IsAffine T]
    (E : PreZeroHypercover.{v} T) (hE : StandardPHCovering E.f)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, @StandardPHCovering (F i).I₀ (E.X i) (hE.isAffine i) (F i).X (F i).f)
    (hchow : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsAffine Y → IsProper f →
      HasChowModification f) :
    ∃ G : PreZeroHypercover.{max v w} T,
      StandardPHCovering G.f ∧ Nonempty (G.Hom (E.bind F)) := by
  obtain ⟨U, g, jj, hgp, hgs, hjjopen, hjjcov, hjjfac⟩ := hE.exists_presentation
  have : Finite E.I₀ := hE.finite
  have : ∀ i, IsAffine (E.X i) := hE.isAffine
  have : ∀ i, IsOpenImmersion (jj i) := hjjopen
  have : IsProper g := hgp
  have : Surjective g := hgs
  have hqsU : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated g
  refine exists_standardPHCovering_refinement_bind_of_extension g jj hjjcov hjjfac F fun i => ?_
  obtain ⟨Wj, gj, κ, hgjp, hgjs, hκopen, hκcov, hκfac⟩ := (hF i).exists_presentation
  have : Finite (F i).I₀ := (hF i).finite
  have : ∀ s, IsAffine ((F i).X s) := (hF i).isAffine
  have : ∀ s, IsOpenImmersion (κ s) := hκopen
  have : IsProper gj := hgjp
  have : Surjective gj := hgjs
  obtain ⟨V, π, hπ, hπs, n, A, α, σ, b, haff, hopen, hfac, hcov⟩ :=
    exists_isProper_surjective_affine_cover_of_hasChowModification (jj i) gj
      (hchow _ _ gj (hE.isAffine i) hgjp) κ (fun s => (F i).f s ≫ jj i) hκcov
      (fun s => by rw [← Category.assoc, hκfac s])
  exact ⟨V, π, hπ, hπs, n, A, α, fun k => ⟨i, σ k⟩, b, haff, hopen, hfac, hcov⟩

end AlgebraicGeometry

end
