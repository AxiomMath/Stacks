module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Modifications of an integral algebraic space

A *modification* of an integral algebraic space `X` over a scheme `S` is a birational proper
morphism `f : X' ⟶ X` of algebraic spaces over `S` whose source `X'` is again integral.

## Main definitions

* `AlgebraicGeometry.Space.IsIntegralModification` is the property of being a modification of
  an integral algebraic space.

## Main results

* `AlgebraicGeometry.Space.IsIntegralModification.exists_isIso_fromPreimage` is
  **Stacks 0AD9**: a modification is an isomorphism over a nonempty open subspace of its
  target.

## Implementation notes

The name. `AlgebraicGeometry.Space.IsModification` is already taken by Stacks 0BGY, a
different notion: a modification of an algebraic space `W` *outside* an open subspace `W₀`,
namely a morphism to `W` which is an isomorphism over `W₀`. The predicate of Stacks 0AD8 is
therefore `IsIntegralModification`, after the integrality of its source and target which is
what distinguishes it.

Integrality of `X'` is part of the predicate, not of its context, exactly as in the source;
integrality of `X` is context, because birationality is only stated for a morphism between
spaces with finitely many irreducible components, and that is what integrality supplies here
through `AlgebraicGeometry.Space.IsIntegralSpace.finite_irreducibleComponents`.

Birationality of a morphism, as formalized in
`StacksFrontier/AlgebraicGeometry/Spaces/BirationalMorphism.lean`, asks for decency at source and
target, which is what Stacks 086U turns into the representable open subspace with dense point
set that puts the generic points on the schematic locus.

Stacks 0AD9 is proved here from Stacks 0BBE rather than from the source's generic flatness:
the modification is already an isomorphism between *some* dense open subspaces `U₁ ⊆ X'` and
`V₁ ⊆ X`, and what remains is to shrink `V₁` so that its inverse image is exactly `U₁`.
Properness makes the image of the closed complement of `U₁` closed, and that image misses the
generic point of `|X|`, because the generic point of `|X'|` lies in `U₁` and is therefore the
only point above it, by Stacks 0AD5 in the form
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq`. Over the open
subspace `U` cut out by `V₁` minus that image the inverse image of `U` is contained in `U₁`,
so the isomorphism of Stacks 0BBE restricts to an inverse of `U.fromPreimage f`; that inverse
is produced by the universal property of the inverse image and identified using that the
inclusion of a subspace is a monomorphism.

## References

* [Stacks Project, Tag 0AD8](https://stacks.math.columbia.edu/tag/0AD8)
* [Stacks Project, Tag 0AD9](https://stacks.math.columbia.edu/tag/0AD9)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0BBE](https://stacks.math.columbia.edu/tag/0BBE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AD8.** A *modification* of an integral algebraic space `X` over `S` is a
birational proper morphism `f : X' ⟶ X` of algebraic spaces over `S` with `X'` integral.

No decency hypotheses are needed: an integral algebraic space is decent, so the decency of the
target is `hXint.isDecentSpace` and that of the source comes with its integrality. -/
@[stacks 0AD8]
def IsIntegralModification {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hXint : IsIntegralSpace B S hS X) (f : X' ⟶ X) : Prop :=
  ∃ hX'int : IsIntegralSpace B S hS X',
    IsBirational B S hS hX' hX hX'int.isDecentSpace hXint.isDecentSpace
        (hX'int.finite_irreducibleComponents B S hS X')
        (hXint.finite_irreducibleComponents B S hS X) f ∧
      IsProper B S hS f

/-- The source of a modification is an integral algebraic space. -/
theorem IsIntegralModification.isIntegralSpace {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : IsAlgebraicSpace B S hS X'} {hX : IsAlgebraicSpace B S hS X}
    {hXint : IsIntegralSpace B S hS X} {f : X' ⟶ X}
    (hf : IsIntegralModification B S hS hX' hX hXint f) :
    IsIntegralSpace B S hS X' :=
  hf.choose

/-- A modification is a proper morphism. -/
theorem IsIntegralModification.isProper {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : IsAlgebraicSpace B S hS X'} {hX : IsAlgebraicSpace B S hS X}
    {hXint : IsIntegralSpace B S hS X} {f : X' ⟶ X}
    (hf : IsIntegralModification B S hS hX' hX hXint f) :
    IsProper B S hS f :=
  hf.choose_spec.2

/-- A modification is birational. -/
theorem IsIntegralModification.isBirational {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : IsAlgebraicSpace B S hS X'} {hX : IsAlgebraicSpace B S hS X}
    {hXint : IsIntegralSpace B S hS X} {f : X' ⟶ X}
    (hf : IsIntegralModification B S hS hX' hX hXint f) :
    IsBirational B S hS hX' hX (hf.isIntegralSpace B S hS).isDecentSpace
      hXint.isDecentSpace
      ((hf.isIntegralSpace B S hS).finite_irreducibleComponents B S hS X')
      (hXint.finite_irreducibleComponents B S hS X) f :=
  hf.choose_spec.1

/-- The generic point of a space lies in every open subspace with dense point set. -/
private theorem mem_range_pointsMap_ι_of_isGenericPoint {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {y : points B S hS Y} (hy : IsGenericPoint y Set.univ) {V : Subfunctor Y}
    (hV : IsOpenSubspace B S hS V) (hdense : DenseRange (pointsMap B S hS V.toFunctor V.ι)) :
    y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) :=
  (hy.mem_open_set_iff (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2)).2
    (hdense.inter_open_nonempty _ isOpen_univ ⟨y, trivial⟩)

/-- **Stacks 0AD9.** A modification of an integral algebraic space over `S` is an isomorphism
over a nonempty open subspace of its target. -/
@[stacks 0AD9]
theorem IsIntegralModification.exists_isIso_fromPreimage
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : IsAlgebraicSpace B S hS X'} {hX : IsAlgebraicSpace B S hS X}
    {hXint : IsIntegralSpace B S hS X} {f : X' ⟶ X}
    (hf : IsIntegralModification B S hS hX' hX hXint f) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      Nonempty (points B S hS U.toFunctor) ∧ IsIso (U.fromPreimage f) := by
  classical
  have hX'int : IsIntegralSpace B S hS X' := hf.isIntegralSpace B S hS
  have hbir := hf.isBirational B S hS
  have hproper : IsProper B S hS f := hf.isProper B S hS
  have hlft : IsLocallyOfFiniteType B S hS f := hproper.isFiniteType.1
  have hdom : IsDominant B S hS f :=
    isDominant_of_isBirational B S hS hX' hX hX'int.isDecentSpace hXint.isDecentSpace
      (hX'int.finite_irreducibleComponents B S hS X')
      (hXint.finite_irreducibleComponents B S hS X) hbir
  -- The two generic points.
  have _ : QuasiSober (points B S hS X') :=
    quasiSober_points_of_isDecentSpace B S hS hX' hX'int.isDecentSpace
  have _ : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hXint.isDecentSpace
  have _ : IrreducibleSpace (points B S hS X') := hX'int.irreducibleSpace B S hS X'
  have _ : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace B S hS X
  obtain ⟨x', hx'⟩ := QuasiSober.sober
    (IrreducibleSpace.isIrreducible_univ (points B S hS X')) isClosed_univ
  obtain ⟨x, hx⟩ := QuasiSober.sober
    (IrreducibleSpace.isIrreducible_univ (points B S hS X)) isClosed_univ
  -- Stacks 0BBE: an isomorphism between dense open subspaces.
  obtain ⟨U₁, V₁, ψ, hU₁, hV₁, hU₁dense, hV₁dense, hψ, hψiso⟩ :=
    exists_dense_isOpenSubspace_isIso_of_isBirational B S hS hX' hX
      hX'int.isDecentSpace hXint.isDecentSpace
      (hX'int.finite_irreducibleComponents B S hS X')
      (hXint.finite_irreducibleComponents B S hS X) f hbir
      (Or.inl ⟨hlft, hXint.hasEtaleLocalProperty_isReduced B S hS X⟩)
  have _ := hψiso
  -- The generic point of the source lies in `U₁`, where `f` is locally quasi-finite.
  have hU₁x' : x' ∈ Set.range (pointsMap B S hS U₁.toFunctor U₁.ι) :=
    mem_range_pointsMap_ι_of_isGenericPoint B S hS hx' hU₁ hU₁dense
  obtain ⟨u, hu⟩ := hU₁x'
  have hqf : IsQuasiFiniteAt B S hS f x' := by
    refine ⟨U₁, hU₁, u, hu, ?_⟩
    rw [← hψ]
    exact isLocallyQuasiFinite_comp B S hS hU₁.1 hV₁.1 hX ψ V₁.ι
      (isLocallyQuasiFinite_of_isEtale B S hS hV₁.1 (isEtale_of_isIso B S hS ψ))
      (isLocallyQuasiFinite_of_isEtale B S hS hX (isEtale_ι_of_isOpenSubspace hV₁))
  have huniq := (isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B S hS hX' hX hXint f hlft
    hdom hx' hx).1 hqf
  -- The image of the complement of `U₁` is closed and misses the generic point of `|X|`.
  have hEclosed : IsClosed (pointsMap B S hS X' f ''
      (Set.range (pointsMap B S hS U₁.toFunctor U₁.ι))ᶜ) :=
    isClosed_of_universallyClosed B S hS hX f hproper.universallyClosed _
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS U₁.ι hU₁.2).isClosed_compl
  have hxE : x ∉ pointsMap B S hS X' f ''
      (Set.range (pointsMap B S hS U₁.toFunctor U₁.ι))ᶜ := by
    rintro ⟨z, hz, hzx⟩
    exact hz (by rw [huniq z hzx]; exact ⟨u, hu⟩)
  -- The open subspace cut out by `V₁` minus that image.
  set W : Set (points B S hS X) := Set.range (pointsMap B S hS V₁.toFunctor V₁.ι) ∩
    (pointsMap B S hS X' f '' (Set.range (pointsMap B S hS U₁.toFunctor U₁.ι))ᶜ)ᶜ with hWdef
  have hWopen : IsOpen W :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS V₁.ι hV₁.2).inter hEclosed.isOpen_compl
  set U : Subfunctor X := openSubspaceOfPoints B S hS X W with hUdef
  have hU : IsOpenSubspace B S hS U := isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen
  have hUpts : Set.range (pointsMap B S hS U.toFunctor U.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  have hxU : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    rw [hUpts]
    exact ⟨mem_range_pointsMap_ι_of_isGenericPoint B S hS hx hV₁ hV₁dense, hxE⟩
  refine ⟨U, hU, ⟨hxU.choose⟩, ?_⟩
  -- The inverse image of `U` sits inside `U₁`, and `U` inside `V₁`.
  have hsq : IsPullback (U.fromPreimage f) (U.preimage f).ι U.ι f :=
    Subfunctor.isPullback_preimage f U
  have hUV : U ≤ V₁ :=
    le_of_range_pointsMap_ι_subset B S hS hV₁ (by rw [hUpts]; exact Set.inter_subset_left)
  have hPU₁ : U.preimage f ≤ U₁ := by
    refine le_of_range_pointsMap_ι_subset B S hS hU₁ ?_
    rw [range_pointsMap_ι_preimage' B S hS f U, hUpts]
    intro z hz
    by_contra hzU
    exact hz.2 ⟨z, hzU, rfl⟩
  have hi : Subfunctor.homOfLe hUV ≫ V₁.ι = U.ι := Subfunctor.homOfLe_ι hUV
  have hj : Subfunctor.homOfLe hPU₁ ≫ U₁.ι = (U.preimage f).ι := Subfunctor.homOfLe_ι hPU₁
  -- The inverse, produced by the universal property of the inverse image.
  have hcond : 𝟙 U.toFunctor ≫ U.ι =
      (Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι) ≫ f := by
    calc 𝟙 U.toFunctor ≫ U.ι = Subfunctor.homOfLe hUV ≫ V₁.ι := by rw [Category.id_comp, hi]
      _ = Subfunctor.homOfLe hUV ≫ (inv ψ ≫ ψ) ≫ V₁.ι := by rw [IsIso.inv_hom_id,
            Category.id_comp]
      _ = Subfunctor.homOfLe hUV ≫ inv ψ ≫ ψ ≫ V₁.ι := by rw [Category.assoc]
      _ = Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι ≫ f := by rw [hψ]
      _ = (Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι) ≫ f := by
            simp only [Category.assoc]
  have hfi : U.fromPreimage f ≫ Subfunctor.homOfLe hUV =
      Subfunctor.homOfLe hPU₁ ≫ ψ := by
    refine (cancel_mono V₁.ι).1 ?_
    calc (U.fromPreimage f ≫ Subfunctor.homOfLe hUV) ≫ V₁.ι
        = U.fromPreimage f ≫ U.ι := by rw [Category.assoc, hi]
      _ = (U.preimage f).ι ≫ f := hsq.w
      _ = (Subfunctor.homOfLe hPU₁ ≫ U₁.ι) ≫ f := by rw [hj]
      _ = Subfunctor.homOfLe hPU₁ ≫ ψ ≫ V₁.ι := by rw [Category.assoc, ← hψ]
      _ = (Subfunctor.homOfLe hPU₁ ≫ ψ) ≫ V₁.ι := by rw [Category.assoc]
  refine ⟨hsq.lift (𝟙 U.toFunctor) (Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι) hcond, ?_,
    hsq.lift_fst _ _ _⟩
  refine (cancel_mono (U.preimage f).ι).1 ?_
  calc (U.fromPreimage f ≫ hsq.lift (𝟙 U.toFunctor)
        (Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι) hcond) ≫ (U.preimage f).ι
      = U.fromPreimage f ≫ (Subfunctor.homOfLe hUV ≫ inv ψ ≫ U₁.ι) := by
        rw [Category.assoc, hsq.lift_snd]
    _ = (U.fromPreimage f ≫ Subfunctor.homOfLe hUV) ≫ inv ψ ≫ U₁.ι := by
        simp only [Category.assoc]
    _ = (Subfunctor.homOfLe hPU₁ ≫ ψ) ≫ inv ψ ≫ U₁.ι := by rw [hfi]
    _ = Subfunctor.homOfLe hPU₁ ≫ U₁.ι := by
        simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = 𝟙 (U.preimage f).toFunctor ≫ (U.preimage f).ι := by rw [hj, Category.id_comp]

end AlgebraicGeometry.Space

end
