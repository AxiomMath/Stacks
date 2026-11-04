module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree

/-!
# Descending the degree of a finite locally free morphism along a limit of schemes

Let a scheme be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and let a scheme of finite presentation over one stage
be such that its base change to the limit is finite locally free of degree `d` over the limit.
Then its base change to some later stage is finite locally free of degree `d` over that stage.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_overPullbackObj_of_isLimit`: the
  fixed-degree refinement of Stacks Tag 06AC, for the structure morphism of an object over a
  stage.

## Implementation notes

Degree-free finite local freeness descends by Stacks Tag 06AC. What the degree adds is that the
degree stratum of the stage reached there eventually swallows the whole system. The degree strata
are the pieces of the open and closed decomposition of Stacks Tag 04MH; the stratum of degree `d`
contains the image of the limit, because the degree of a finite locally free morphism is well
defined at a point of its target; and an open subset of a stage containing the image of the limit
contains the image of some later stage, which is `AlgebraicGeometry.exists_map_eq_top`.

The target of the morphism being descended is the stage itself rather than an arbitrary scheme
over it, so no second inverse system enters: the system of targets is the given system. The
translation between a morphism of the over category and the structure morphism of an object of it
is `AlgebraicGeometry.overPullback_map_terminal_iff`.

## References

* [Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two base changes of one morphism along one morphism satisfy the same morphism properties:
the comparison isomorphism of the two cartesian squares identifies them. -/
theorem prop_iff_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Z S T A B : Scheme.{u}} {p : Z ⟶ S} {b : T ⟶ S}
    {a₁ : A ⟶ Z} {f₁ : A ⟶ T} {a₂ : B ⟶ Z} {f₂ : B ⟶ T}
    (sq₁ : IsPullback a₁ f₁ p b) (sq₂ : IsPullback a₂ f₂ p b) : P f₁ ↔ P f₂ := by
  rw [← sq₁.isoIsPullback_hom_snd Z T sq₂]
  exact MorphismProperty.cancel_left_of_respectsIso P _ f₂

/-- Base changing twice in succession is base changing along the composite. -/
theorem isPullback_pullback_snd_comp {Z S T T' : Scheme.{u}} (p : Z ⟶ S) (b : T ⟶ S)
    (b' : T' ⟶ T) :
    IsPullback (pullback.fst (pullback.snd p b) b' ≫ pullback.fst p b)
      (pullback.snd (pullback.snd p b) b') p (b' ≫ b) :=
  (IsPullback.of_hasPullback (pullback.snd p b) b').paste_horiz (IsPullback.of_hasPullback p b)

/-- A base change of the restriction of `p` to an open `U` of its target, along a morphism into
`U`, is a base change of `p` itself along the composite with the inclusion of `U`. -/
theorem isPullback_pullback_snd_morphismRestrict {Z S T' : Scheme.{u}} (p : Z ⟶ S)
    (U : S.Opens) (h : T' ⟶ U.toScheme) (b : T' ⟶ S) (hb : h ≫ U.ι = b) :
    IsPullback (pullback.fst (p ∣_ U) h ≫ (p ⁻¹ᵁ U).ι) (pullback.snd (p ∣_ U) h) p b := by
  subst hb
  exact (IsPullback.of_hasPullback (p ∣_ U) h).paste_horiz
    (isPullback_morphismRestrict p U).flip

/-- The restriction of a base change of `p` along `b` to an open `V` of the target of `b` is a
base change of `p` along the composite of the inclusion of `V` with `b`. -/
theorem isPullback_morphismRestrict_pullback_snd {Z S T : Scheme.{u}} (p : Z ⟶ S) (b : T ⟶ S)
    (V : T.Opens) :
    IsPullback (((pullback.snd p b) ⁻¹ᵁ V).ι ≫ pullback.fst p b)
      ((pullback.snd p b) ∣_ V) p (V.ι ≫ b) :=
  (isPullback_morphismRestrict (pullback.snd p b) V).flip.paste_horiz
    (IsPullback.of_hasPullback p b)

/-- Any base change of `p` along `b` is finite locally free of degree `d` if `b` factors through
an open `U` of the target over which `p` is finite locally free of degree `d`. -/
private theorem isFiniteLocallyFreeOfRank_of_isPullback_of_factors {Z S T B : Scheme.{u}}
    (p : Z ⟶ S) (U : S.Opens) (d : ℕ) (hU : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (p ∣_ U) d)
    (h : T ⟶ U.toScheme) (b : T ⟶ S) (hb : h ≫ U.ι = b) {a₂ : B ⟶ Z} {f₂ : B ⟶ T}
    (sq : IsPullback a₂ f₂ p b) : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f₂ d := by
  have := hU
  exact (prop_iff_of_isPullback (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
    (isPullback_pullback_snd_morphismRestrict p U h b hb) sq).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback (p ∣_ U) h))

/-- If a morphism factors through an open of the target over which `p` is finite locally free of
degree `d`, then the base change of `p` along it is finite locally free of degree `d`. -/
theorem isFiniteLocallyFreeOfRank_pullback_snd_of_preimage_eq_top {Z S T : Scheme.{u}}
    (p : Z ⟶ S) (b : T ⟶ S) (U : S.Opens) (d : ℕ)
    (hU : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (p ∣_ U) d) (hb : b ⁻¹ᵁ U = ⊤) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd p b) d := by
  have hrange : Set.range b ⊆ Set.range U.ι := by
    rw [U.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hb.ge (Set.mem_univ t)
  exact isFiniteLocallyFreeOfRank_of_isPullback_of_factors p U d hU
    (IsOpenImmersion.lift U.ι b hrange) b
    (IsOpenImmersion.lift_fac U.ι b hrange) (IsPullback.of_hasPullback p b)

/-- If the base change of a finite locally free morphism `p` along `b` has constant degree `d`,
then `b` factors through the degree-`d` stratum of the target of `p`. -/
theorem preimage_eq_top_of_isFiniteLocallyFreeOfRank_pullback_snd {Z S T : Scheme.{u}}
    (p : Z ⟶ S) (b : T ⟶ S) (U : ℕ → S.Opens) (hU : Stacks.Chow.IsClopenDecomposition U)
    (hrank : ∀ n, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (p ∣_ U n) n) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd p b) d] :
    b ⁻¹ᵁ U d = ⊤ := by
  refine le_antisymm le_top fun t _ ↦ ?_
  obtain ⟨n, hn⟩ := hU.exists_mem (b.base t)
  suffices hnd : n = d from hnd ▸ hn
  let y : ((b ⁻¹ᵁ U n).toScheme : Scheme.{u}) := ⟨t, hn⟩
  have hbase : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((pullback.snd p b) ∣_ (b ⁻¹ᵁ U n)) d :=
    IsZariskiLocalAtTarget.restrict
      (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) ‹_› _
  have hother : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((pullback.snd p b) ∣_ (b ⁻¹ᵁ U n)) n :=
    isFiniteLocallyFreeOfRank_of_isPullback_of_factors p (U n) n (hrank n) (b ∣_ U n)
      ((b ⁻¹ᵁ U n).ι ≫ b) (morphismRestrict_ι b (U n))
      (isPullback_morphismRestrict_pullback_snd p b (b ⁻¹ᵁ U n))
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point _ y hother hbase

/-- **Stacks Project, Tag 06AC, fixed-degree form, for the structure morphism of an object over a
stage.** Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated schemes with
affine transition morphisms and limit cone `c`, and let `Z` be of finite presentation over the
stage `D.obj i₀`. If the base change of `Z` to the limit is finite locally free of degree `d` over
the limit, then its base change to `D.obj i` is finite locally free of degree `d` over `D.obj i`
for some later stage `i`. -/
@[stacks 06AC "the fixed-degree refinement, for a morphism whose target is the stage itself"]
theorem exists_isFiniteLocallyFreeOfRank_overPullbackObj_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) (Z : Over (D.obj i₀))
    (hZ : FinitePresentation Z.hom) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((Over.pullback (c.π.app i₀)).obj Z).hom d] :
    ∃ (i : I) (g : i ⟶ i₀),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((Over.pullback (D.map g)).obj Z).hom d := by
  have : MorphismProperty.RespectsIso (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : LocallyOfFinitePresentation Z.hom := hZ.1
  have : QuasiCompact Z.hom := hZ.2.1
  have : QuasiSeparated Z.hom := hZ.2.2
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have : LocallyOfFinitePresentation
      (Over.homMk Z.hom (Category.comp_id Z.hom) : Z ⟶ Over.mk (𝟙 (D.obj i₀))).left := hZ.1
  -- Tag 06AC without the degree: the base change is finite locally free at some stage `i₁`.
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((Over.pullback (c.π.app i₀)).map
        (Over.homMk Z.hom (Category.comp_id Z.hom) :
          Z ⟶ Over.mk (𝟙 (D.obj i₀)))).left :=
    (overPullback_map_terminal_iff (@Stacks.Morphisms.IsFiniteLocallyFree.{u})
      (c.π.app i₀) Z).mpr (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)
  obtain ⟨i₁, g₁, hfree⟩ := exists_isFiniteLocallyFree_baseChange_of_isLimit D c hc i₀
    Z (Over.mk (𝟙 (D.obj i₀))) (Over.homMk Z.hom (Category.comp_id Z.hom))
  have : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd Z.hom (D.map g₁)) :=
    (overPullback_map_terminal_iff (@Stacks.Morphisms.IsFiniteLocallyFree.{u})
      (D.map g₁) Z).mp hfree
  -- Tag 04MH: decompose `D.obj i₁` into the degree strata.
  obtain ⟨U, hdec, hrank⟩ :=
    Stacks.Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank
      (pullback.snd Z.hom (D.map g₁))
  -- The limit lands in the degree-`d` stratum, hence so does some later stage.
  have hsq := isPullback_pullback_snd_comp Z.hom (D.map g₁) (c.π.app i₁)
  rw [c.w g₁] at hsq
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd (pullback.snd Z.hom (D.map g₁)) (c.π.app i₁)) d :=
    (prop_iff_of_isPullback (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      hsq (IsPullback.of_hasPullback Z.hom (c.π.app i₀))).mpr ‹_›
  obtain ⟨i, a, ha⟩ := exists_map_eq_top D c hc (U d)
    (preimage_eq_top_of_isFiniteLocallyFreeOfRank_pullback_snd _ (c.π.app i₁) U hdec hrank d)
  refine ⟨i, a ≫ g₁, ?_⟩
  have hsq' := isPullback_pullback_snd_comp Z.hom (D.map g₁) (D.map a)
  rw [← D.map_comp] at hsq'
  exact (prop_iff_of_isPullback (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
    hsq' (IsPullback.of_hasPullback Z.hom (D.map (a ≫ g₁)))).mp
    (isFiniteLocallyFreeOfRank_pullback_snd_of_preimage_eq_top _ (D.map a) (U d) d (hrank d) ha)

end AlgebraicGeometry

end
