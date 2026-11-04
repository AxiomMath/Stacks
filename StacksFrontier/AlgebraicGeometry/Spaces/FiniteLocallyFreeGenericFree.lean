module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaFree
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOpenChartTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardDegreeOne
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# A finite locally free module is free on a nonempty open subspace

Let `X` be a decent algebraic space with a point and `ℰ` a finite locally free `𝒪_X`-module of
rank `r` (Stacks 0409). Then there is a nonempty open subspace `j : U ⟶ X` with
`j^*ℰ ≅ 𝒪_U^{⊕ r}`.

Finite local freeness on the small étale site only gives *étale* neighbourhoods on which `ℰ` is
free; an open subspace needs a Zariski trivialization. Decency provides a nonempty representable
open subspace (Stacks 086U), that is, an étale chart `C₀` of `X` whose structure morphism is an
open immersion and whose scheme has a point `y`. Over the scheme of `C₀` the module is Zariski
finite locally free, so `y` has a Zariski open neighbourhood `O` over which `ℰ` is finite free
(`AlgebraicGeometry.Space.exists_mem_isFiniteFree_over_openChart`). The open chart `T` that `O`
cuts out of `C₀` is again an open immersion chart with a point, and the inverse image of `ℰ`
along its structure morphism is a coproduct of `n` copies of the structure sheaf. Uniqueness of
the rank on a nonempty space gives `n = r`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_nonempty_iso_free_of_isFiniteLocallyFreeOfRank`:
  on a decent algebraic space with a point, a finite locally free module of rank `r` is
  isomorphic to `𝒪^{⊕ r}` on a nonempty open subspace.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isGood_nonempty_iso_freeTower`: the same on a
  good algebraic space over the base of the theory of cycles, with the open subspace good; here
  the rank is `n + 1` and the trivialization is onto the free tower
  `AlgebraicGeometry.Space.freeTower`.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isGood_dense_iso_freeTower`: on an integral
  good algebraic space the open subspace is moreover dense.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology HasBinaryBiproducts.of_hasBinaryProducts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- On a decent algebraic space with a point there is an étale chart whose structure morphism
is an open immersion and whose scheme has a point: the chart of a nonempty representable open
subspace (Stacks 086U). -/
theorem exists_isOpenImmersion_chart_nonempty_of_isDecentSpace {X : AlgebraicSpaces B S hS}
    (hdec : IsDecentSpace B S hS X.1) (x : points B S hS X.1) :
    ∃ C : SmallEtale B S hS X.1, IsOpenImmersion B S hS C.1.hom ∧ Nonempty (chartScheme C) := by
  obtain ⟨H, hHopen, hHrep, hHdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS X.2 hdec
  obtain ⟨w⟩ : Nonempty (points B S hS H.toFunctor) := hHdense.nonempty_iff.mpr ⟨x⟩
  let e := H.toFunctor.reprW
  let q : yoneda.obj H.toFunctor.reprX ⟶ X.1 := e.hom ≫ H.ι
  have hq : IsOpenImmersion B S hS q :=
    MorphismProperty.RespectsIso.precomp _ e.hom H.ι hHopen.2
  exact ⟨⟨CostructuredArrow.mk q, presheaf_etale_of_isOpenImmersion B S hS hq⟩, hq,
    ⟨pointsToScheme B S hS H.toFunctor.reprX (pointsMap B S hS H.toFunctor e.inv w)⟩⟩

/-- **A finite locally free module is free on a nonempty open subspace.** On a decent algebraic
space `X` with a point, a finite locally free `𝒪_X`-module `ℰ` of rank `r` (Stacks 0409) admits
an open immersion `j : U ⟶ X` with `U` nonempty and `j^*ℰ ≅ 𝒪_U^{⊕ r}`. -/
theorem exists_isOpenImmersion_nonempty_iso_free_of_isFiniteLocallyFreeOfRank
    {X : AlgebraicSpaces B S hS} (hdec : IsDecentSpace B S hS X.1) (x : points B S hS X.1)
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r) :
    ∃ (U : AlgebraicSpaces B S hS) (j : U ⟶ X), IsOpenImmersion B S hS j.hom ∧
      Nonempty (points B S hS U.1) ∧
      Nonempty ((modulePullback B S hS j).obj E ≅
        SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS U) (ULift.{u} (Fin r))) := by
  obtain ⟨C₀, hC₀, ⟨y⟩⟩ := exists_isOpenImmersion_chart_nonempty_of_isDecentSpace hdec x
  obtain ⟨O, hyO, hff⟩ := exists_mem_isFiniteFree_over_openChart B S hS X E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) C₀ hr.isFiniteLocallyFreeOnSite y
  set T := openChart B S hS X.1 C₀ O
  obtain ⟨n, ι, hc⟩ := (SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 hff
  obtain ⟨ι', ⟨hc'⟩⟩ :=
    exists_isColimitCofan_modulePullback_chartToSpace_of_over B S hS X E T ⟨ι, hc⟩
  let e : (modulePullback B S hS (chartToSpace B S hS X T)).obj E ≅
      SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS X T))
        (ULift.{u} (Fin n)) :=
    ((Cofan.mk _ ι').isColimitEquivOfEquiv Equiv.ulift hc').coconePointUniqueUpToIso
      (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin n)))
  have hpt : Nonempty (points B S hS (chartSpace B S hS X T).1) :=
    ⟨(schemePointsHomeomorph B S hS _).symm ⟨y, hyO⟩⟩
  obtain rfl : r = n :=
    eq_of_isFiniteLocallyFreeOfRank_of_isFiniteLocallyFreeOfRank
      (isFiniteLocallyFreeOfRank_modulePullback B S hS (chartToSpace B S hS X T) E r hr)
      (RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm
        (isFiniteLocallyFreeOfRank_free_ulift_fin n)) hpt.some
  exact ⟨chartSpace B S hS X T, chartToSpace B S hS X T, isOpenImmersion_openChart C₀ hC₀ O,
    hpt, ⟨e⟩⟩

/-! ### The free tower is the free module -/

section Tower

variable (X : AlgebraicSpaces B S hS)

/-- The free tower `F_n` is a coproduct of `n + 1` copies of the structure sheaf. -/
theorem exists_isColimit_cofan_freeTower : ∀ n : ℕ,
    ∃ ι : ∀ _ : Fin (n + 1),
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶ freeTower X n,
      Nonempty (IsColimit (Cofan.mk (freeTower X n) ι))
  | 0 => ⟨fun _ => 𝟙 _, ⟨Stacks.Cohomology.Torsors.Generators.cofanFinOneIsColimitOfIso
      (Iso.refl _)⟩⟩
  | n + 1 => by
    obtain ⟨ι, ⟨hc⟩⟩ := exists_isColimit_cofan_freeTower n
    let c₂ : BinaryCofan (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2)
        (Cofan.mk (freeTower X n) ι).pt :=
      BinaryCofan.mk (biprod.inr : _ ⟶ addUnit X.2 (freeTower X n)) biprod.inl
    have t₂ : IsColimit c₂ :=
      BinaryCofan.IsColimit.mk _ (fun f g => biprod.desc g f) (fun f g => biprod.inr_desc g f)
        (fun f g => biprod.inl_desc g f) (fun f g m h₁ h₂ =>
          biprod.hom_ext' _ _ (h₂.trans (biprod.inl_desc g f).symm)
            (h₁.trans (biprod.inr_desc g f).symm))
    exact ⟨_, ⟨extendCofanIsColimit
      (fun _ => (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2)) hc t₂⟩⟩

/-- **The free tower `F_n` is the free module of rank `n + 1`.** -/
def freeTowerIsoFree (n : ℕ) :
    freeTower X n ≅ SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS X)
      (ULift.{u} (Fin (n + 1))) :=
  ((Cofan.mk _ (exists_isColimit_cofan_freeTower X n).choose).isColimitEquivOfEquiv Equiv.ulift
      (exists_isColimit_cofan_freeTower X n).choose_spec.some).coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin (n + 1))))

end Tower

/-- **A finite locally free module is a free tower on a nonempty open subspace.** On a decent
algebraic space `X` with a point, a finite locally free module `ℰ` of rank `n + 1` admits an open
immersion `j : U ⟶ X` with `U` nonempty and `j^*ℰ ≅ F_n = 𝒪_U^{⊕(n+1)}`, the free tower of
`AlgebraicGeometry.Space.freeTower`. -/
theorem exists_isOpenImmersion_nonempty_iso_freeTower_of_isFiniteLocallyFreeOfRank
    {X : AlgebraicSpaces B S hS} (hdec : IsDecentSpace B S hS X.1) (x : points B S hS X.1)
    (E : Modules.{u, u} B S hS X.1 X.2) {n : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E (n + 1)) :
    ∃ (U : AlgebraicSpaces B S hS) (j : U ⟶ X), IsOpenImmersion B S hS j.hom ∧
      Nonempty (points B S hS U.1) ∧
      Nonempty ((modulePullback B S hS j).obj E ≅ freeTower U n) := by
  obtain ⟨U, j, hj, hU, ⟨e⟩⟩ :=
    exists_isOpenImmersion_nonempty_iso_free_of_isFiniteLocallyFreeOfRank hdec x E hr
  exact ⟨U, j, hj, hU, ⟨e ≪≫ (freeTowerIsoFree U n).symm⟩⟩

/-! ### Over the base of the theory of cycles -/

section Good

variable (D : BaseSpaceDimensionSituation.{u})

/-- **A finite locally free module on a good algebraic space is a free tower on a nonempty open
subspace.** Let `Y` be a good algebraic space over the base of the theory of cycles with a point,
and `ℱ` finite locally free of rank `n + 1`. There is an open immersion `j : U ⟶ Y` with `U`
nonempty and `j^*ℱ ≅ F_n = 𝒪_U^{⊕(n+1)}`: a good space is decent. -/
theorem exists_isOpenImmersion_nonempty_iso_freeTower_of_isGood
    {Y : AlgebraicSpaces D.site D.base D.base_mem} (sY : Y.1 ⟶ D.space) (hY : D.IsGood sY)
    (y : points D.site D.base D.base_mem Y.1) (F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2)
    {n : ℕ} (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1)) :
    ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
      IsOpenImmersion D.site D.base D.base_mem j.hom ∧
      Nonempty (points D.site D.base D.base_mem U.1) ∧
      Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n) :=
  exists_isOpenImmersion_nonempty_iso_freeTower_of_isFiniteLocallyFreeOfRank
    (D.isDecentSpace_of_isGood sY hY) y F hr

/-- **A finite locally free module on a good algebraic space is a free tower on a nonempty good
open subspace.** Let `X` be a good algebraic space over the base of the theory of cycles with a
point `x`, and `ℰ` finite locally free of rank `n + 1`. There is an open immersion `j : U ⟶ X`
with `U` nonempty and good and `j^*ℰ ≅ F_n = 𝒪_U^{⊕(n+1)}`. -/
theorem exists_isOpenImmersion_isGood_nonempty_iso_freeTower
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (x : points D.site D.base D.base_mem X)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) {n : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1)) :
    ∃ (U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
      (hU : IsAlgebraicSpace D.site D.base D.base_mem U) (j : U ⟶ X),
      IsOpenImmersion D.site D.base D.base_mem j ∧ D.IsGood (j ≫ sX) ∧
      Nonempty (points D.site D.base D.base_mem U) ∧
      Nonempty ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk j : (⟨U, hU⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩)).obj E ≅ freeTower ⟨U, hU⟩ n) := by
  obtain ⟨U, j, hj, hU, ⟨e⟩⟩ :=
    exists_isOpenImmersion_nonempty_iso_freeTower_of_isFiniteLocallyFreeOfRank
      (X := ⟨X, hX.1⟩) (D.isDecentSpace_of_isGood sX hX) x E hr
  exact ⟨U.1, U.2, j.hom, hj, isGood_comp_of_isOpenImmersion D sX hX U.2 hj, hU, ⟨e⟩⟩

/-- **On an integral good algebraic space the free tower trivializes on a dense good open
subspace.** Same as
`AlgebraicGeometry.Space.exists_isOpenImmersion_isGood_nonempty_iso_freeTower`, with the image of
`U` dense in `|X|`: a nonempty open set of points of an irreducible space is dense. -/
theorem exists_isOpenImmersion_isGood_dense_iso_freeTower
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) {n : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1)) :
    ∃ (U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
      (hU : IsAlgebraicSpace D.site D.base D.base_mem U) (j : U ⟶ X),
      IsOpenImmersion D.site D.base D.base_mem j ∧ D.IsGood (j ≫ sX) ∧
      Nonempty (points D.site D.base D.base_mem U) ∧
      Dense (Set.range (pointsMap D.site D.base D.base_mem U j)) ∧
      Nonempty ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk j : (⟨U, hU⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩)).obj E ≅ freeTower ⟨U, hU⟩ n) := by
  have : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  obtain ⟨u⟩ : Nonempty (points D.site D.base D.base_mem X) := inferInstance
  obtain ⟨U, hU, j, hj, hg, ⟨w⟩, he⟩ :=
    exists_isOpenImmersion_isGood_nonempty_iso_freeTower D sX hX u E hr
  exact ⟨U, hU, j, hj, hg, ⟨w⟩,
    (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem j hj).dense
      ⟨_, Set.mem_range_self w⟩, he⟩

end Good

end AlgebraicGeometry.Space

end
