module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementParts0DBF

/-!
# Stacks 0DBI parts (2) and (3): ph coverings compose and are stable under base change

The ph coverings of schemes satisfy the three axioms of Stacks 0DBI. Part (1), that a singleton
isomorphism is a ph covering, is
`AlgebraicGeometry.isPHCovering_of_isIso` in
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings`. The remaining two parts are proved here,
in their full generality: composition of a ph covering with ph coverings of its members, and base
change along an *arbitrary* morphism of schemes.

Both arguments run over a single affine open of the base and both need the same input, Stacks
0DBF part (2): a composite of two standard ph coverings of an affine scheme is refined by a single
standard ph covering. That is `AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, which
this development proves outright from its own Chow's lemma (Stacks 0202),
`AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`. This file sits above
both `StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings` and
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementParts0DBF` because the latter
already imports the former, so the general statements cannot be placed next to the definition of
a ph covering.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpens_confined`: a compact scheme over a scheme `T` is
  covered by finitely many affine opens, each mapping into an affine open of `T`.
* `AlgebraicGeometry.IsPHCovering.exists_standardPHCovering`: a ph covering of an affine scheme is
  refined by a standard ph covering of that scheme.
* `AlgebraicGeometry.isPHCovering_bind`: **Stacks 0DBI part (2)**.
* `AlgebraicGeometry.isPHCovering_pullback`: **Stacks 0DBI part (3)**.

## Implementation notes

Base change is where the confinement hypothesis of
`AlgebraicGeometry.isPHCovering_pullback_of_forall_exists_isAffineOpen` is removed. An affine open
`U'` of the source is a compact space, so `exists_finite_affineOpens_confined` covers it by
finitely many affine opens `W l`, each of which *is* confined: it maps into an affine open `V l` of
the target. Over each `V l` the given ph covering has a standard ph refinement, which base changes
to `W l` along `W l ⟶ V l` by `AlgebraicGeometry.StandardPHCovering.pullback`; the family
`{W l ⟶ U'}` is itself a standard ph covering of `U'`, presented by the identity of `U'`. Stacks
0DBF part (2) then collapses the resulting two-step covering of `U'` into a single standard ph
covering, which is what the definition of a ph covering asks for.

Composition runs the same way over an affine open `U` of the base: the outer covering has a
standard ph refinement `𝒜` over `U`, each member `𝒜.X q` is affine and maps to a member `E.X (i q)`
of the outer family, the inner covering of `E.X (i q)` base changes to a ph covering of `𝒜.X q` by
part (3), and `IsPHCovering.exists_standardPHCovering` turns that into a standard ph covering of
the affine scheme `𝒜.X q`. Stacks 0DBF part (2) collapses the two steps again.

`AlgebraicGeometry.IsPHCovering.exists_standardPHCovering` is the definition of a ph covering read
at the affine open `⊤` of an affine scheme, transported along the isomorphism
`AlgebraicGeometry.Scheme.topIso`; the transport is by hand rather than by `rw`, because the
members of the covering have to be kept and only the structure morphisms composed with the
isomorphism.

In both proofs the refinement morphism supplied by the definition is immediately read off as data
indexed by the original index type, exactly as in
`AlgebraicGeometry.isPHCovering_pullback_of_forall_exists_isAffineOpen`: the index type of a
`CategoryTheory.PreZeroHypercover.pullback₂` is only definitionally the original one, which blocks
rewriting inside terms that mention it.

## References

* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A compact scheme `S` over a scheme `T` is covered by finitely many affine opens, each of which
maps into an affine open of `T`.

Every point of `S` has an affine open neighbourhood in the preimage of an affine open of `T`,
because the affine opens form a basis of both topologies, and compactness extracts a finite
subcover. The pairs (affine open of `S`, affine open of `T` containing its image) are the index
set of the subcover, so the two families come out indexed by the same type. -/
public theorem exists_finite_affineOpens_confined {S T : Scheme.{u}} [CompactSpace S]
    (q : S ⟶ T) :
    ∃ (n : ℕ) (W : Fin n → S.Opens) (V : Fin n → T.Opens),
      (∀ l, IsAffineOpen (W l)) ∧ (∀ l, IsAffineOpen (V l)) ∧
      (∀ l, Set.range ((W l).ι ≫ q).base ⊆ (V l : Set T)) ∧
      (⋃ l, ((W l : Set S))) = Set.univ := by
  classical
  set P : Set (S.Opens × T.Opens) :=
    {p | IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ (p.1 : Set S) ⊆ q.base ⁻¹' (p.2 : Set T)}
  have hcov : (Set.univ : Set S) ⊆ ⋃ p ∈ P, (p.1 : Set S) := by
    intro x _
    obtain ⟨V, hV, hxV, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := T) (x := q.base x) (U := ⊤) trivial
    obtain ⟨W, hW, hxW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := x) (U := q ⁻¹ᵁ V) hxV
    exact Set.mem_biUnion (show (W, V) ∈ P from ⟨hW, hV, hWV⟩) hxW
  obtain ⟨b, hb, hbfin, hbcov⟩ := isCompact_univ.elim_finite_subcover_image
    (fun p (_ : p ∈ P) => p.1.isOpen) hcov
  have : Finite b := hbfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  refine ⟨n, fun l => ((e.symm l : S.Opens × T.Opens)).1,
    fun l => ((e.symm l : S.Opens × T.Opens)).2,
    fun l => (hb (e.symm l).2).1, fun l => (hb (e.symm l).2).2.1, fun l => ?_,
    Set.eq_univ_of_univ_subset (hbcov.trans ?_)⟩
  · rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (hb (e.symm l).2).2.2 z.2
  · rw [Set.biUnion_eq_iUnion]
    exact (e.symm.surjective.iUnion_comp
      fun p : b => (((p : S.Opens × T.Opens)).1 : Set S)).ge

/-- If `ψ : P ⟶ X ×_Z Y` lies over `v : P ⟶ Y`, then `ψ ≫ fst : P ⟶ X` lies over `v`
after composing to `Z`. -/
private theorem comp_fst_comp_eq {X Y Z P : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {ψ : P ⟶ pullback f g} {v : P ⟶ Y} (h : ψ ≫ pullback.snd f g = v) :
    (ψ ≫ pullback.fst f g) ≫ f = v ≫ g := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, h]

/-- A ph covering of `T` has, over each affine open `U`, a standard ph covering of `U` whose
members factor through the members of the covering, over `U`. -/
private theorem IsPHCovering.exists_standardPHCovering_factor {T : Scheme.{u}} {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsPHCovering X f) (U : T.Opens)
    (hU : IsAffineOpen U) :
    ∃ (𝒰 : PreZeroHypercover.{u} U.toScheme)
      (_ : @StandardPHCovering 𝒰.I₀ U.toScheme hU 𝒰.X 𝒰.f),
      ∀ a, ∃ (i : I) (φ : 𝒰.X a ⟶ pullback (f i) U.ι), φ ≫ pullback.snd (f i) U.ι = 𝒰.f a := by
  obtain ⟨𝒰, h1, ⟨ρ⟩⟩ := hf.2 U hU
  exact ⟨𝒰, h1, fun a => ⟨ρ.s₀ a, ρ.h₀ a, ρ.w₀ a⟩⟩

/-- A ph covering of an affine scheme `A` is refined by a standard ph covering of `A`.

This is the defining condition of a ph covering at the affine open `⊤` of `A`, carried across the
isomorphism `(⊤ : A.Opens).toScheme ≅ A`: the members of the standard ph covering of
`(⊤ : A.Opens).toScheme` are kept and their structure morphisms composed with `(⊤ : A.Opens).ι`,
which is proper and surjective because it is an isomorphism, so the presentation of the standard
ph covering survives; the refinement morphisms are the first projections of the fibre products
over `(⊤ : A.Opens).ι`. -/
public theorem IsPHCovering.exists_standardPHCovering {A : Scheme.{u}} [IsAffine A] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ A} (hf : IsPHCovering X f) :
    ∃ 𝒰 : PreZeroHypercover.{u} A, StandardPHCovering 𝒰.f ∧
      Nonempty (𝒰.Hom ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} A)) := by
  classical
  obtain ⟨𝒱, hstd, hρ⟩ := hf.exists_standardPHCovering_factor ⊤ (isAffineOpen_top A)
  have hiso : IsIso (⊤ : A.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  let _ : IsAffine (⊤ : A.Opens).toScheme := isAffineOpen_top A
  obtain ⟨V, g, j, hg, hgs, hj, hjcov, hjcomp⟩ := hstd.exists_presentation
  have : Finite 𝒱.I₀ := hstd.finite
  choose idx ψ hψ using hρ
  refine ⟨⟨𝒱.I₀, 𝒱.X, fun a => 𝒱.f a ≫ (⊤ : A.Opens).ι⟩, ?_,
    ⟨⟨idx, fun a => ψ a ≫ pullback.fst (f (idx a)) (⊤ : A.Opens).ι, fun a => ?_⟩⟩⟩
  · refine StandardPHCovering.of_presentation _ hstd.isAffine
      (g ≫ (⊤ : A.Opens).ι) j ?_ ?_ hj hjcov (fun a => ?_)
    · have := hg; infer_instance
    · have := hgs; infer_instance
    · rw [← Category.assoc, hjcomp a]
  · exact comp_fst_comp_eq (hψ a)

/-- **Stacks 0DBI part (3).** If `{X i ⟶ T}` is a ph covering and `g : T' ⟶ T` is any morphism of
schemes, then the base change `{X i ×_T T' ⟶ T'}` is a ph covering of `T'`.

Fix an affine open `U'` of `T'`. It is a compact space, so
`AlgebraicGeometry.exists_finite_affineOpens_confined` covers it by finitely many affine opens
`W l`, each mapping into an affine open `V l` of `T`; the family `{W l ⟶ U'}` is a standard ph
covering of `U'` presented by the identity of `U'`. Over `V l` the given covering has a standard
ph refinement, and `W l ⟶ V l` base changes it to a standard ph covering of `W l` refining the
base changed family, by the universal property of the fibre products involved. Stacks 0DBF
part (2), `AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, collapses this two-step
covering of `U'` into a single standard ph covering. -/
@[stacks 0DBI "part (3)"]
public theorem isPHCovering_pullback {T T' : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (hf : IsPHCovering X f) (g : T' ⟶ T) :
    IsPHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) := by
  classical
  refine ⟨fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (f i) g) (hf.1 i), fun U' hU' ↦ ?_⟩
  let _ : IsAffine U'.toScheme := hU'
  obtain ⟨n, W, V, hW, hV, hrange, hcov⟩ :=
    exists_finite_affineOpens_confined (U'.ι ≫ g)
  have hr : ∀ l, Set.range ((W l).ι ≫ U'.ι ≫ g).base ⊆ Set.range (V l).ι.base := by
    simpa only [Scheme.Opens.range_ι] using hrange
  let h : ∀ l, (W l).toScheme ⟶ (V l).toScheme := fun l =>
    IsOpenImmersion.lift (V l).ι ((W l).ι ≫ U'.ι ≫ g) (hr l)
  have hfac : ∀ l, h l ≫ (V l).ι = (W l).ι ≫ U'.ι ≫ g := fun l =>
    IsOpenImmersion.lift_fac _ _ (hr l)
  -- the standard ph coverings over the `V l`, with their refinements read off as data over `I`
  choose 𝒱 h𝒱 hdata using fun l : Fin n => hf.exists_standardPHCovering_factor (V l) (hV l)
  choose idx ψ hψ using hdata
  -- the covering of `U'` by the `W l` is standard, presented by the identity of `U'`
  let E : PreZeroHypercover.{u} U'.toScheme :=
    ⟨ULift.{u} (Fin n), fun l => (W l.down).toScheme, fun l => (W l.down).ι⟩
  have hE : StandardPHCovering E.f := by
    refine ⟨inferInstance, fun l => hW l.down, ⟨U'.toScheme, 𝟙 _, fun l => (W l.down).ι,
      inferInstance, inferInstance, fun l => inferInstance, ?_, fun l => Category.comp_id _⟩⟩
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨ULift.up l, by rwa [Scheme.Opens.range_ι]⟩
  -- base change the standard ph covering over `V l` to `W l`
  let F : ∀ l : E.I₀, PreZeroHypercover.{u} (E.X l) := fun l =>
    ⟨(𝒱 l.down).I₀, fun a => pullback ((𝒱 l.down).f a) (h l.down),
      fun a => pullback.snd ((𝒱 l.down).f a) (h l.down)⟩
  have hF : ∀ l, @StandardPHCovering (F l).I₀ (E.X l) (hE.isAffine l) (F l).X (F l).f := by
    intro l
    have : IsAffine (V l.down).toScheme := hV l.down
    have : IsAffine (W l.down).toScheme := hW l.down
    exact (h𝒱 l.down).pullback (h l.down)
  obtain ⟨G, hG, ⟨δ⟩⟩ := exists_standardPHCovering_refinement_bind E hE F hF
  -- the two-step covering refines the base changed family over `U'`
  have hφ : ∀ (l : Fin n) (a : (𝒱 l).I₀), ∃ φ : pullback ((𝒱 l).f a) (h l) ⟶
      pullback (pullback.snd (f (idx l a)) g) U'.ι,
      φ ≫ pullback.snd (pullback.snd (f (idx l a)) g) U'.ι
        = pullback.snd ((𝒱 l).f a) (h l) ≫ (W l).ι := by
    intro l a
    have hq : (pullback.fst ((𝒱 l).f a) (h l) ≫ ψ l a ≫
        pullback.fst (f (idx l a)) (V l).ι) ≫ f (idx l a)
        = ((pullback.snd ((𝒱 l).f a) (h l) ≫ (W l).ι) ≫ U'.ι) ≫ g := by
      simp only [Category.assoc]
      rw [pullback.condition (f := f (idx l a)), reassoc_of% hψ l a, pullback.condition_assoc,
        hfac l]
    exact ⟨pullback.lift (pullback.lift _ _ hq) (pullback.snd ((𝒱 l).f a) (h l) ≫ (W l).ι)
      (pullback.lift_snd _ _ hq), pullback.lift_snd _ _ _⟩
  choose φ hφ' using hφ
  exact ⟨G, hG, ⟨δ.comp ⟨fun s => idx s.1.down s.2, fun s => φ s.1.down s.2,
    fun s => hφ' s.1.down s.2⟩⟩⟩

/-- **Stacks 0DBI part (2).** If `E` is a ph covering of `T` and `F i` is a ph covering of the
member `E.X i` for each `i`, then the family of all composites `(F i).X j ⟶ E.X i ⟶ T`, which is
`CategoryTheory.PreZeroHypercover.bind`, is a ph covering of `T`.

Fix an affine open `U` of `T`. The outer covering has a standard ph refinement `𝒜` over `U`, say
with `𝒜.X q` mapping to `E.X (i q)` by a morphism `c q` over `U`. Each `𝒜.X q` is affine, so the
base change of the inner covering `F (i q)` along `c q`, which is a ph covering of `𝒜.X q` by
`AlgebraicGeometry.isPHCovering_pullback`, has a standard ph refinement
`𝒞 q` by `AlgebraicGeometry.IsPHCovering.exists_standardPHCovering`. The two-step covering
`𝒜.bind 𝒞` of `U` refines the base change of `E.bind F` to `U`, and Stacks 0DBF part (2),
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, collapses it into a single standard
ph covering of `U`. -/
@[stacks 0DBI "part (2)"]
public theorem isPHCovering_bind {T : Scheme.{u}} (E : PreZeroHypercover.{v} T)
    (hE : IsPHCovering E.X E.f) (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, IsPHCovering (F i).X (F i).f) :
    IsPHCovering (E.bind F).X (E.bind F).f := by
  classical
  refine ⟨?_, fun U hU => ?_⟩
  · rintro ⟨i, j⟩
    have := hE.1 i
    have := (hF i).1 j
    exact inferInstanceAs (LocallyOfFiniteType ((F i).f j ≫ E.f i))
  let _ : IsAffine U.toScheme := hU
  obtain ⟨𝒜, h𝒜, hρ⟩ := hE.exists_standardPHCovering_factor U hU
  choose iq χ hχ using hρ
  -- each member of the refinement maps to a member of the outer family, over `U`
  let c : ∀ q, 𝒜.X q ⟶ E.X (iq q) := fun q => χ q ≫ pullback.fst (E.f (iq q)) U.ι
  have hc : ∀ q, c q ≫ E.f (iq q) = 𝒜.f q ≫ U.ι := fun q => comp_fst_comp_eq (hχ q)
  -- base change the inner coverings and refine them by standard ph coverings
  have hinner : ∀ q : 𝒜.I₀, ∃ (𝒞 : PreZeroHypercover.{u} (𝒜.X q))
      (_ : @StandardPHCovering 𝒞.I₀ (𝒜.X q) (h𝒜.isAffine q) 𝒞.X 𝒞.f),
      ∀ m, ∃ (j : (F (iq q)).I₀) (θ : 𝒞.X m ⟶ pullback ((F (iq q)).f j) (c q)),
        θ ≫ pullback.snd ((F (iq q)).f j) (c q) = 𝒞.f m := by
    intro q
    have : IsAffine (𝒜.X q) := h𝒜.isAffine q
    obtain ⟨𝒞, h1, ⟨σ⟩⟩ :=
      (isPHCovering_pullback (hF (iq q)) (c q)).exists_standardPHCovering
    exact ⟨𝒞, h1, fun m => ⟨σ.s₀ m, σ.h₀ m, σ.w₀ m⟩⟩
  choose 𝒞 h𝒞 hdata using hinner
  choose jdx θ hθ using hdata
  obtain ⟨G, hG, ⟨δ⟩⟩ := exists_standardPHCovering_refinement_bind 𝒜 h𝒜 𝒞 h𝒞
  -- the two-step covering refines the base change of the composite family to `U`
  have hlift : ∀ (q : 𝒜.I₀) (m : (𝒞 q).I₀),
      (θ q m ≫ pullback.fst ((F (iq q)).f (jdx q m)) (c q)) ≫
        ((F (iq q)).f (jdx q m) ≫ E.f (iq q)) = ((𝒞 q).f m ≫ 𝒜.f q) ≫ U.ι := by
    intro q m
    simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% hθ q m, hc q]
  exact ⟨G, hG, ⟨δ.comp ⟨fun s => ⟨iq s.1, jdx s.1 s.2⟩,
    fun s => pullback.lift (θ s.1 s.2 ≫ pullback.fst ((F (iq s.1)).f (jdx s.1 s.2)) (c s.1))
      ((𝒞 s.1).f s.2 ≫ 𝒜.f s.1) (hlift s.1 s.2),
    fun s => pullback.lift_snd _ _ (hlift s.1 s.2)⟩⟩⟩

end AlgebraicGeometry

end
