module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionSheafHomRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageQcqs
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasicoherentComplexDevissage
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper

/-!
# The upper shriek of a dualizing complex along a closed immersion is dualizing

Let `i : Z ⟶ W` be a closed immersion into a quasi-compact locally Noetherian scheme (for
instance a morphism of `FTS_S` in Situation 48.16.1 whose underlying morphism is a closed
immersion). If `K` is a dualizing complex on `W`, then `i^! K` is a dualizing complex on `Z`.
This is the closed-immersion step of the proof of [Stacks, Tag 0AA3]: by
[Stacks, Tag 0AA2] / [Stacks, Tag 0A9X] `i^! = R ℰom(𝒪_Z, -)` on bounded-below objects, and
`R ℰom(𝒪_Z, K)` is dualizing locally by [Stacks, Tag 0A78] part (2) and [Stacks, Tag 0AX0]
(`Stacks.Duality.ClosedImmersionRestriction.isDualizingComplex_locallySmall_derivedSheafHom`).

The one input this file adds is that a dualizing complex on a quasi-compact scheme is bounded
below: over each affine open it is the associated sheaf of a dualizing complex over the ring,
which is bounded ([Stacks, Tag 0A7B]), and finitely many affine opens cover the scheme. So no
boundedness is assumed of `K`, as in the source.

## Main results

* `Stacks.Duality.isBoundedBelow_of_isDualizingComplex`: a dualizing complex on a quasi-compact
  locally Noetherian scheme is cohomologically bounded below.
* `Stacks.Duality.ClosedImmersionRestriction.isDualizingComplex_rightAdjoint_of_compactSpace`:
  for a closed immersion `i : Z ⟶ W` with `W` quasi-compact and locally Noetherian and any right
  adjoint `a` of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`, `a` carries dualizing complexes to
  dualizing complexes.
* `Stacks.Duality.ClosedImmersionRestriction.isDualizingComplex_upperShriek_of_isClosedImmersion`:
  the same in Situation 48.16.1 for the upper shriek `i^!` of [Stacks, Tag 0A9Y].

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

namespace Stacks.Duality

/-- **A dualizing complex on a quasi-compact locally Noetherian scheme is bounded below.** Over
an affine open `U` it is the associated sheaf of a dualizing complex `ω` over `Γ(X, U)`, which is
bounded, so the cohomology sheaves of `K|_U` vanish in degrees below a bound depending on `U`;
finitely many affine opens cover `X`, and a module vanishing on each member of an open cover
vanishes. -/
theorem isBoundedBelow_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) : DerivedCategoryB.IsBoundedBelow K := by
  have hloc : ∀ U : X.affineOpens, ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ →
      IsZero ((Scheme.Modules.restrictFunctor U.1.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
    intro U
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let := HasDerivedCategory.standard U.1.toScheme.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U.1))
    obtain ⟨ω, hω, ⟨e⟩⟩ := hK U.1 U.2
    obtain ⟨n₀, hn₀⟩ := Dualizing.isBoundedBelow_of_bounded.{u, u} ω hω.bounded
    refine ⟨n₀, fun n hn => ?_⟩
    let F := tilde.functor Γ(X, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    exact (((F.map_isZero (hn₀ n hn)).of_iso ((F.mapDerivedCategoryHomologyIso n).app ω)).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e)).of_iso
        (((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategoryHomologyIso n).app K).symm
  choose N hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]
        trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨-∑ U ∈ t, |N U|, fun n hn => ?_⟩
  refine Stacks.DerivedQCoh.isZero_schemeModules_of_cover _ (fun U : t => U.1.1) ?_
    (fun U => hN U.1 n ?_)
  · apply top_unique
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · have h := Finset.single_le_sum (f := fun U => |N U|) (fun U _ => abs_nonneg (N U)) U.2
    have := neg_abs_le (N U.1)
    omega

namespace ClosedImmersionRestriction

/-- **The upper shriek of a dualizing complex along a closed immersion is dualizing.** Let
`i : Z ⟶ W` be a closed immersion into a quasi-compact locally Noetherian scheme and let `a` be a
right adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` (this `a` is `i^!`, [Stacks, Tag 0AA2]). If
`K ∈ D_QCoh(𝒪_W)` is a dualizing complex, then `a(K)` is a dualizing complex on `Z`.

The dualizing complex is bounded below by `Stacks.Duality.isBoundedBelow_of_isDualizingComplex`,
so `a(K) = R ℰom(𝒪_Z, K)` by [Stacks, Tag 0A9X] and
`isDualizingComplex_rightAdjoint_of_isClosedImmersion` applies. This is the closed-immersion step
of [Stacks, Tag 0AA3]. -/
theorem isDualizingComplex_rightAdjoint_of_compactSpace {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] [IsLocallyNoetherian W] [CompactSpace W]
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ a)
    (K : quasiCoherentDerivedCategory W) (hK : IsDualizingComplex K.obj) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex (a.obj K).obj :=
  isDualizingComplex_rightAdjoint_of_isClosedImmersion i
    (LocallySmall.isQuasicoherent_homology_derivedPushforward_of_isAffineHom i) a adj K
    (isBoundedBelow_of_isDualizingComplex K.obj hK) hK

/-- **The upper shriek of a dualizing complex along a closed immersion is dualizing, in
Situation 48.16.1.** Let `S` be a Noetherian scheme and let `i : X ⟶ Y` be a morphism of
`FTS_S` whose underlying morphism of schemes is a closed immersion. If `K` is a dualizing complex
for `Y`, then `i^! K` is a dualizing complex for `X`, where `i^!` is the upper shriek of
[Stacks, Tag 0A9Y] at the compactification `X̄ = X` that a proper morphism is.

This is the closed-immersion case of [Stacks, Tag 0AA3], the step "`i^!` transforms dualizing
complexes into dualizing complexes" of its proof: `Y` is Noetherian, being of finite type over
`S`, and `isDualizingComplex_rightAdjoint_of_compactSpace` applies to the adjunction
`Ri_* ⊣ i^!`. -/
theorem isDualizingComplex_upperShriek_of_isClosedImmersion {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (i : X ⟶ Y) [IsClosedImmersion i.left] (K : quasiCoherentDerivedCategory Y.left)
    (hK : IsDualizingComplex K.obj) :
    IsDualizingComplex ((upperShriek i (properCompactification i)).obj K).obj :=
  isDualizingComplex_rightAdjoint_of_compactSpace i.left _
    ((twistedInverseImageAdjunction i.left
        (LocallySmall.isQuasicoherent_homology_derivedPushforward_of_isAffineHom
          i.left)).ofNatIsoRight
      ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (quasiCoherentDerivedPullbackIdIso
        X.left (isQuasicoherent_homology_derivedPullback' (𝟙 X.left))).symm)) K hK

end ClosedImmersionRestriction

end Stacks.Duality

end
