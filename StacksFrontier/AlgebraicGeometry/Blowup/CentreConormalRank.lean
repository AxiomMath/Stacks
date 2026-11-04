module

public import StacksFrontier.AlgebraicGeometry.Blowup.BlowUpIsProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDivisorCentreBundle
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleRankZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankBaseOpen
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalLocallyFree

/-!
# The rank decomposition of the centre of a blowup with smooth centre

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`. The conormal sheaf
`𝒞 = ℐ/ℐ²` of the centre, read on `Z` (`Stacks.AlgebraicGeometry.centreConormal`), is finite
locally free, since `i` is a regular immersion ([Stacks, Tag 067U]). Its rank is therefore locally
constant, `Z` is the disjoint union of the open and closed pieces `Z_r` on which the rank is `r`,
and `𝒞` restricts to a finite locally free module of rank `r` on `Z_r`. This is the decomposition
of the centre by its codimension in the proof of [Stacks, Tag 0FUW].

## Main definitions

* `Stacks.AlgebraicGeometry.centreRankPiece`: the open and closed piece `Z_r`.
* `Stacks.AlgebraicGeometry.centreBundlePieceMap`: the open immersion `𝐏(𝒞|_{Z_r}) ⟶ 𝐏(𝒞)`, the
  base change of `Z_r ⊆ Z`, with `centreBundlePieceTwistIso` identifying the restriction of
  `𝒪_{𝐏(𝒞)}(1)` with `𝒪_{𝐏(𝒞|_{Z_r})}(1)`.

## Main results

* `Stacks.AlgebraicGeometry.isFiniteLocallyFree_centreConormal`: `𝒞` is finite locally free.
* `Stacks.AlgebraicGeometry.isFiniteLocallyFreeOfRank_centreConormal_restrict`: on `Z_r` it has
  rank `r`.
* `Stacks.AlgebraicGeometry.mem_interior_range_of_mem_centreRankPiece_zero`: at a point of `Z_0`
  the centre is a neighbourhood of its image in `X`: no point of the blowup lies over it, because
  the projective bundle of a module of rank zero is empty, while the image of the blowup is closed
  and contains the complement of the centre.
* `Stacks.AlgebraicGeometry.centreRankPiece_zero_eq_bot`: if `Z` contains no nonempty open subset
  of `X` (positive codimension at every point), then `Z_0` is empty.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 067U](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeProj (projectiveBundleToBase)

universe u

namespace Stacks.AlgebraicGeometry

/-- Finite local freeness of a sheaf of modules only depends on its isomorphism class. -/
theorem isFiniteLocallyFree_of_iso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree N := by
  obtain ⟨q, hq, hq'⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.hom q, inferInstance,
    inferInstance⟩

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

include f in
/-- **The conormal sheaf of the centre is finite locally free**: `i` is a regular immersion
([Stacks, Tag 067U]), so `ℐ/ℐ²` is finite locally free on `V(ℐ)`, and so is its pullback to `Z`. -/
theorem isFiniteLocallyFree_centreConormal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (centreConormal i) := by
  have := smooth_subschemeι_comp f i
  have := RegularIdealSheaf.isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion
    i.ker.subschemeι
    (isQuasiRegularImmersion_of_smooth_of_smooth f i.ker.subschemeι)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) :=
    isFiniteLocallyFree_of_iso (h := this) (Stacks.Conormal.conormalDegreeOneIso i.ker.subschemeι)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme i.toImage _
    inferInstance

/-- **The piece `Z_r` of the centre** on which the conormal sheaf has rank `r`: an open and closed
subscheme of `Z`. -/
def centreRankPiece (r : ℕ) : Z.Opens :=
  haveI := isFiniteLocallyFree_centreConormal f i
  Scheme.Modules.rankStratum (centreConormal i) r

/-- The piece `Z_r` is open and closed in `Z`. -/
theorem isClopen_centreRankPiece (r : ℕ) : IsClopen (centreRankPiece f i r : Set Z) :=
  have := isFiniteLocallyFree_centreConormal f i
  Scheme.Modules.isClopen_rankStratum (centreConormal i) r

/-- The pieces `Z_r` and `Z_s` are disjoint for `r ≠ s`. -/
theorem disjoint_centreRankPiece {r s : ℕ} (h : r ≠ s) :
    Disjoint (centreRankPiece f i r) (centreRankPiece f i s) :=
  have := isFiniteLocallyFree_centreConormal f i
  Scheme.Modules.disjoint_rankStratum (centreConormal i) h

/-- The pieces `Z_r` cover `Z`. -/
theorem iSup_centreRankPiece : ⨆ r : ℕ, centreRankPiece f i r = ⊤ :=
  have := isFiniteLocallyFree_centreConormal f i
  Scheme.Modules.iSup_rankStratum (centreConormal i)

/-- **On `Z_r` the conormal sheaf is finite locally free of rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_centreConormal_restrict (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (centreRankPiece f i r).ι).obj (centreConormal i)) r :=
  have := isFiniteLocallyFree_centreConormal f i
  Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_range_subset (centreConormal i) _ r
    (by rw [Scheme.Opens.range_ι]; exact subset_rfl)

/-- In a cartesian square of schemes, a point of the bottom-left corner mapping into the image of
the right edge lies in the image of the left edge. -/
theorem mem_range_snd_of_isPullback {P X' Y' T : Scheme.{u}} {fst : P ⟶ X'} {snd : P ⟶ Y'}
    {f' : X' ⟶ T} {g' : Y' ⟶ T} (h : IsPullback fst snd f' g') {y : Y'}
    (hy : g'.base y ∈ Set.range f'.base) : y ∈ Set.range snd.base := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
  refine ⟨h.isoPullback.inv.base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd]
  exact hw

/-- **No point of the blowup lies over a point of `Z_0`.** The exceptional divisor is
`X' ×_X Z` and is identified with `𝐏(𝒞)` over `Z`, and `𝐏(𝒞)` restricted to `Z_0` is the
projective bundle of a module of rank zero, which is empty. -/
theorem not_mem_range_blowUpToBase_of_mem_centreRankPiece_zero {z : Z}
    (hz : z ∈ centreRankPiece f i 0) :
    i.base z ∉ Set.range (Stacks.Blowup.blowUpToBase i.ker).base := by
  intro hb
  obtain ⟨e, he⟩ := mem_range_snd_of_isPullback (Stacks.Blowup.isPullback_exceptionalToCentre i) hb
  have hy : (centreRankPiece f i 0).ι.base ⟨z, hz⟩ ∈
      Set.range (projectiveBundleToBase Z (centreConormal i)).base := by
    refine ⟨(exceptionalDivisorIsoCentreBundle f i).hom.base e, ?_⟩
    have h := Scheme.Hom.comp_apply (exceptionalDivisorIsoCentreBundle f i).hom
      (projectiveBundleToBase Z (centreConormal i)) e
    rw [exceptionalDivisorIsoCentreBundle_hom_toBase] at h
    exact h.symm.trans he
  have := isFiniteLocallyFreeOfRank_centreConormal_restrict f i 0
  have : ((Scheme.Modules.pullback (centreRankPiece f i 0).ι).obj
      (centreConormal i)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance
  have := Stacks.ProjectiveBundleDeRham.isEmpty_projectiveBundle_of_rank_zero
    ((Scheme.Modules.pullback (centreRankPiece f i 0).ι).obj (centreConormal i))
  obtain ⟨v, -⟩ := mem_range_snd_of_isPullback
    (Stacks.RelativeProj.isPullback_projectiveBundleBaseChange
      (centreRankPiece f i 0).ι (centreConormal i) _ (Iso.refl _)) hy
  exact IsEmpty.false v

/-- The image of the blowing up contains the complement of the centre: the blowing up is an
isomorphism over it ([Stacks, Tag 02OS]). -/
theorem compl_range_subset_range_blowUpToBase :
    (Set.range i.base)ᶜ ⊆ Set.range (Stacks.Blowup.blowUpToBase i.ker).base := by
  intro x hx
  have hsupp : x ∉ (i.ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    exact hx
  let V : X.Opens := ⟨i.ker.supportᶜ, i.ker.support.isClosed.isOpen_compl⟩
  have := isIso_blowUp_restrict_compl_support i.ker
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    ((AlgebraicGeometry.blowUpToBase i.ker ∣_ V).base)).2 ⟨x, hsupp⟩
  have hx' : (AlgebraicGeometry.blowUpToBase i.ker).base
      ((AlgebraicGeometry.blowUpToBase i.ker ⁻¹ᵁ V).ι.base y) = x := by
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
    rfl
  refine ⟨(Stacks.Blowup.blowUpIso i.ker).inv.base
    ((AlgebraicGeometry.blowUpToBase i.ker ⁻¹ᵁ V).ι.base y), ?_⟩
  rw [← Stacks.Blowup.blowUpIso_hom_comp, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply
    (Stacks.Blowup.blowUpIso i.ker).inv, Iso.inv_hom_id]
  exact hx'

include f in
/-- The image of the blowing up is closed: the blowing up of a scheme in a quasi-coherent ideal
of finite type is projective, hence proper ([Stacks, Tag 02NS]). -/
theorem isClosed_range_blowUpToBase :
    IsClosed (Set.range (Stacks.Blowup.blowUpToBase i.ker).base) := by
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i f
  have hI : i.ker.IsFiniteType := (locallyOfFinitePresentation_iff_fg_ker i).mp inferInstance
  have := (Stacks.Blowup.isProjective_blowUpToBase i.ker hI).isProper
  have h : Set.range (Stacks.Blowup.blowUpToBase i.ker).base =
      Set.range (AlgebraicGeometry.blowUpToBase i.ker).base := by
    rw [← Stacks.Blowup.blowUpIso_hom_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Set.range_eq_univ.mpr
        (ConcreteCategory.bijective_of_isIso (Stacks.Blowup.blowUpIso i.ker).hom.base).2,
      Set.image_univ]
  rw [h, ← Set.image_univ]
  exact (AlgebraicGeometry.blowUpToBase i.ker).isClosedMap _ isClosed_univ

/-- **At a point of `Z_0` the centre is a neighbourhood of its image in `X`.** -/
theorem mem_interior_range_of_mem_centreRankPiece_zero {z : Z}
    (hz : z ∈ centreRankPiece f i 0) : i.base z ∈ interior (Set.range i.base) := by
  rw [interior_eq_compl_closure_compl]
  exact fun h => not_mem_range_blowUpToBase_of_mem_centreRankPiece_zero f i hz
    (closure_minimal (compl_range_subset_range_blowUpToBase i) (isClosed_range_blowUpToBase f i) h)

/-- **If the centre has positive codimension at every point, the conormal sheaf has positive rank
everywhere**: `Z` containing no nonempty open subset of `X`, the piece `Z_0` is empty. -/
theorem centreRankPiece_zero_eq_bot (hint : interior (Set.range i.base) = ∅) :
    centreRankPiece f i 0 = ⊥ :=
  eq_bot_iff.mpr fun z hz => by
    have := mem_interior_range_of_mem_centreRankPiece_zero f i hz
    rw [hint] at this
    exact this.elim

/-! ### The projective bundle over the pieces -/

/-- The conormal sheaf restricted to the piece `Z_r`. -/
abbrev centreConormalPiece (r : ℕ) : (centreRankPiece f i r).toScheme.Modules :=
  (Scheme.Modules.pullback (centreRankPiece f i r).ι).obj (centreConormal i)

/-- The restriction of the conormal sheaf to `Z_r` is quasi-coherent. -/
instance isQuasicoherent_centreConormalPiece (r : ℕ) :
    (centreConormalPiece f i r).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance

/-- The restriction of the conormal sheaf to `Z_r` is finite locally free of rank `r`. -/
instance isFiniteLocallyFreeOfRank_centreConormalPiece (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (centreConormalPiece f i r) r :=
  isFiniteLocallyFreeOfRank_centreConormal_restrict f i r

/-- **The projective bundle of `𝒞|_{Z_r}` inside `𝐏(𝒞)`**: the base change of the inclusion of
`Z_r` into `Z`. -/
def centreBundlePieceMap (r : ℕ) :
    Stacks.RelativeProj.projectiveBundle (centreRankPiece f i r) (centreConormalPiece f i r) ⟶
      Stacks.RelativeProj.projectiveBundle Z (centreConormal i) :=
  Stacks.RelativeProj.projectiveBundleBaseChange (centreRankPiece f i r).ι (centreConormal i)
    (centreConormalPiece f i r) (Iso.refl _)

/-- The square formed by `centreBundlePieceMap`, the two bundle projections and the inclusion
`Z_r ⟶ Z` is cartesian. -/
theorem isPullback_centreBundlePieceMap (r : ℕ) :
    IsPullback (centreBundlePieceMap f i r)
      (projectiveBundleToBase (centreRankPiece f i r) (centreConormalPiece f i r))
      (projectiveBundleToBase Z (centreConormal i)) (centreRankPiece f i r).ι :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange _ _ _ _

/-- The map `𝐏(𝒞|_{Z_r}) ⟶ 𝐏(𝒞)` is an open immersion. -/
instance isOpenImmersion_centreBundlePieceMap (r : ℕ) :
    IsOpenImmersion (centreBundlePieceMap f i r) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_centreBundlePieceMap f i r).flip inferInstance

/-- `𝒪_{𝐏(𝒞)}(1)` restricts on `𝐏(𝒞|_{Z_r})` to its `𝒪(1)`. -/
def centreBundlePieceTwistIso (r : ℕ) :
    (Scheme.Modules.pullback (centreBundlePieceMap f i r)).obj
        (Stacks.RelativeProj.tautologicalDatumTwist (centreConormal i)) ≅
      Stacks.RelativeProj.tautologicalDatumTwist (centreConormalPiece f i r) :=
  Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso _ _ _ _

end Stacks.AlgebraicGeometry

end
