module

public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf

/-!
# Finite local freeness of a fixed rank: the pointwise form and restriction

Tag 01C6 states finite local freeness of rank `r` as the existence of one datum consisting of a
cover of the whole space together with a free presentation of rank `r` over each member
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`). The pointwise form
(`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`) instead asks, for each point, for
some open neighbourhood over which the sheaf is free of rank `r`. This file identifies the two
and records that the pointwise form is inherited by restrictions, is local on the base, and only
depends on the isomorphism class.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff`: the pointwise form and the
  single-datum form agree.
* `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso`,
  `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top` and
  `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.pushforward_of_iso`: invariance
  under isomorphisms, restriction, gluing over an open cover, and direct image along an
  isomorphism of schemes.

## Implementation notes

Everything here is the rank-indexed companion of the already-available statements for
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, and the proofs are the same, with the
index type of the free presentation held fixed at `ULift (Fin r)`. The direction from a single
datum to the pointwise form is already available as
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules`, which is why this
file imports the Picard-group file that carries it rather than reproving it.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism of the restriction of a sheaf of modules to an open with a free sheaf of rank
`r` gives a free presentation of rank `r` of the sheaf over that open. -/
theorem exists_generatingSections_of_restrict_iso_of_rank {X : Scheme.{u}} (M : X.Modules)
    (V : X.Opens) (r : ℕ)
    (e : M.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin r))) :
    ∃ σ : (M.over V).GeneratingSections, IsIso σ.π ∧ Nonempty (σ.I ≃ Fin r) := by
  let I := ULift.{u, 0} (Fin r)
  let F := Scheme.Modules.overEquiv (X := X) V
  have hdisc : Limits.PreservesColimitsOfShape (Discrete I) F.functor :=
    Limits.preservesColimitsOfShape_of_discrete F.functor
  have hunit : SheafOfModules.unit (V.toScheme).ringCatSheaf ≅
      F.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
  let e' : F.functor.obj (M.over V) ≅ F.functor.obj (SheafOfModules.free.{u} I) :=
    (Scheme.Modules.overFunctorEquiv (X := X) V).app M ≪≫ e ≪≫ eFree
  let e'' : M.over V ≅ SheafOfModules.free.{u} I := F.fullyFaithfulFunctor.preimageIso e'
  refine ⟨(SheafOfModules.free.generatingSections I).ofEpi e''.inv, ?_, ⟨Equiv.ulift⟩⟩
  have h₀ : IsIso (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over V) I).π := by
    rw [SheafOfModules.free.generatingSections_π]
    exact IsIso.id _
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₀ inferInstance

/-- A sheaf of modules on a scheme is finite locally free of rank `r` at every point, in the
sense of `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, exactly when there is a
single datum consisting of a cover of the whole space and a free presentation of rank `r` over
each member. -/
theorem isFiniteLocallyFreeOfRank_iff {X : Scheme.{u}} (M : X.Modules) (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank M r ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := by
  refine ⟨fun h ↦ ?_, isFiniteLocallyFreeOfRank_of_sheafOfModules M r⟩
  choose U hU hiso using h
  choose σ hσ₁ hσ₂ using fun x ↦
    exists_generatingSections_of_restrict_iso_of_rank M (U x) r (hiso x).some
  let q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} M :=
    { I := X
      X := U
      coversTop := (_root_.Opens.coversTop_iff X U).mpr <|
        eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
      generators := σ }
  have h₁ : q.IsLocallyFreeData.{u, u, u, u} := by
    constructor
    exact hσ₁
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q, h₁, fun x ↦ hσ₂ x⟩ }

/-- Finite local freeness of rank `r` depends only on the isomorphism class of a sheaf of
modules. -/
theorem IsFiniteLocallyFreeOfRank.of_iso {X : Scheme.{u}} {M N : X.Modules} {r : ℕ} (e : M ≅ N)
    (h : IsFiniteLocallyFreeOfRank M r) : IsFiniteLocallyFreeOfRank N r := by
  intro x
  obtain ⟨U, hU, ⟨ε⟩⟩ := h x
  exact ⟨U, hU, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ ε⟩⟩

/-- If `p` factors through an open immersion `q` via an open immersion `k`, and the restriction
along `q` is free of rank `r`, then so is the restriction along `p`. -/
private theorem nonempty_restrict_iso_free_of_fac {Y P Q : Scheme.{u}} (M : Y.Modules)
    (p : P ⟶ Y) (q : Q ⟶ Y) (k : P ⟶ Q) [IsOpenImmersion p] [IsOpenImmersion q]
    [IsOpenImmersion k] (hk : k ≫ q = p) (r : ℕ)
    (ε : M.restrict q ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin r))) :
    Nonempty (M.restrict p ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin r))) := by
  subst hk
  exact ⟨(restrictFunctorComp k q).app M ≪≫ (restrictFunctor k).mapIso ε ≪≫
    (restrictFreeIso k (ULift.{u, 0} (Fin r))).symm⟩

/-- Finite local freeness of rank `r` is inherited by the restriction along an open immersion. -/
theorem IsFiniteLocallyFreeOfRank.restrict {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    {M : Y.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank M r) :
    IsFiniteLocallyFreeOfRank (M.restrict g) r := by
  intro x
  obtain ⟨U, hU, ⟨ε⟩⟩ := h (g.base x)
  obtain ⟨e⟩ := nonempty_restrict_iso_free_of_fac M ((g ⁻¹ᵁ U).ι ≫ g) U.ι (g ∣_ U)
    (morphismRestrict_ι g U) r ε
  exact ⟨g ⁻¹ᵁ U, hU, ⟨((restrictFunctorComp (g ⁻¹ᵁ U).ι g).app M).symm ≪≫ e⟩⟩

/-- A sheaf of modules whose restriction to each member of an open cover of the base is finite
locally free of rank `r` is itself finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_iSup_eq_top {X : Scheme.{u}} {M : X.Modules} {ι : Type*}
    {r : ℕ} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsFiniteLocallyFreeOfRank (M.restrict (U i).ι) r) :
    IsFiniteLocallyFreeOfRank M r := by
  intro x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU ▸ trivial : x ∈ (⨆ i, U i : X.Opens))
  obtain ⟨V, hV, ⟨ε⟩⟩ := h i ⟨x, hi⟩
  have hrange : Set.range ((U i).ι ''ᵁ V).ι = Set.range (V.ι ≫ (U i).ι) := by
    simp [Set.range_comp]
  obtain ⟨e⟩ := nonempty_restrict_iso_free_of_fac M ((U i).ι ''ᵁ V).ι (V.ι ≫ (U i).ι)
    (IsOpenImmersion.isoOfRangeEq ((U i).ι ''ᵁ V).ι (V.ι ≫ (U i).ι) hrange).hom
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange) r
    ((restrictFunctorComp V.ι (U i).ι).app M ≪≫ ε)
  exact ⟨(U i).ι ''ᵁ V, ⟨⟨x, hi⟩, hV, rfl⟩, ⟨e⟩⟩

/-- Finite local freeness of rank `r` is preserved by the direct image along an isomorphism of
schemes. -/
theorem IsFiniteLocallyFreeOfRank.pushforward_of_iso {S S' : Scheme.{u}} (e : S ≅ S')
    {N : S.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank N r) :
    IsFiniteLocallyFreeOfRank ((pushforward e.hom).obj N) r :=
  .of_iso (pushforwardIsoRestrict e N).symm (h.restrict e.inv)

end AlgebraicGeometry.Scheme.Modules

end
