module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructibleUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteUniversalHomeomorphismPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteUniversalHomeomorphismPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along a finite morphism of finite presentation preserves constructible sheaves

**Stacks 095R for sheaves of sets.** Let `p : T ⟶ S` be a finite morphism of finite presentation
of a big étale site. If `ℱ` is a constructible sheaf of sets on `T_étale`, then so is `p_*ℱ` on
`S_étale`. No hypothesis is imposed on `S` or `T`.

The proof is the source's. By Stacks 095F constructibility may be checked over the affine opens of
`S`, and over an affine open the restriction of `p_*ℱ` is the direct image of the restriction of
`ℱ` along the base change of `p` (Stacks 0959 for an open immersion). So let `S` be affine. Stacks
095K (1) provides a surjective morphism `g : S' ⟶ S` from an affine scheme and a thickening
`i : Z' ⟶ T' = S' ×_S T` such that `Z' ⟶ S'` is finite étale. By Stacks 095Q (1) it suffices to
show that `g⁻¹p_*ℱ` is constructible, and that is `p'_*(g')⁻¹ℱ` by Stacks 0959, where `p'` and
`g'` are the two projections of the fibre product. The thickening `i` is a finite universal
homeomorphism, so the unit `(g')⁻¹ℱ ⟶ i_*i⁻¹(g')⁻¹ℱ` is an isomorphism — the case of Stacks 04DZ
the argument needs, proved here by stalks — and `p'_* i_*` is the direct image along the finite
étale `Z' ⟶ S'`, which preserves constructibility by Stacks 095H; the sheaf `i⁻¹(g')⁻¹ℱ` is
constructible by Stacks 095G.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_isFinite` — **Stacks 095R for sheaves
  of sets**.

The other two coefficient categories of the tag are
`Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleAbelianDirectImage_of_isFinite`
(sheaves of abelian groups) and
`Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite` (sheaves of
modules over a Noetherian ring).

## Implementation notes

The schemes `S'`, `T'` and `Z'` must be objects of the big étale site. This is why Stacks 095K (1)
is stated with `g` locally of finite type: then `S'` is of finite type over the affine `S`, hence
below the size cutoff of the site (Stacks 000R (5)), and so are `T'`, finite over `S'`, and its
closed subscheme `Z'`.

## References

* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 095K](https://stacks.math.columbia.edu/tag/095K)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 095H](https://stacks.math.columbia.edu/tag/095H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Stacks 095R for sheaves of sets over an affine base. -/
@[sga "4 IX 2.14" "(i), special case", sga "4 XIV 1.11" "finite-morphism case"]
private theorem isConstructibleSetSheaf_pushforward_of_isFinite_of_isAffine {T S : B.Scheme}
    (p : T ⟶ S) [IsFinite (B.inclusion.map p)] [IsAffine (B.inclusion.obj S)]
    (hfp : FinitePresentation (B.inclusion.map p))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  have : IsAffine (B.inclusion.obj T) := isAffine_of_isAffineHom (B.inclusion.map p)
  obtain ⟨S', hS'aff, g, hg, hgft, Z', i, hi, hfin, het⟩ :=
    exists_surjective_affine_baseChange_thickening_finiteEtale_general (B.inclusion.map p) hfp
  have := hi.1
  have hS' : B.Contains S' := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g S.property
  have hP : B.Contains (pullback (B.inclusion.map p) g) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd _ _) hS'
  have hZ : B.Contains Z' := Scheme.size_lt_of_isClosedImmersion i hP
  let oS' : B.Scheme := B.obj S' hS'
  let oP : B.Scheme := B.obj _ hP
  let oZ : B.Scheme := B.obj Z' hZ
  let gB : oS' ⟶ S := ObjectProperty.homMk g
  let fstB : oP ⟶ T := ObjectProperty.homMk (pullback.fst _ _)
  let sndB : oP ⟶ oS' := ObjectProperty.homMk (pullback.snd _ _)
  let iB : oZ ⟶ oP := ObjectProperty.homMk i
  have sq : IsPullback (B.inclusion.map fstB) (B.inclusion.map sndB) (B.inclusion.map p)
      (B.inclusion.map gB) := IsPullback.of_hasPullback _ _
  have hcomm : fstB ≫ p = sndB ≫ gB := B.inclusion.map_injective sq.w
  have : IsAffine (B.inclusion.obj oS') := hS'aff
  have : IsFinite (B.inclusion.map iB) := inferInstanceAs (IsFinite i)
  have : UniversalHomeomorphism (B.inclusion.map iB) :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi.2
  have : IsFinite (B.inclusion.map (iB ≫ sndB)) := hfin
  have : Etale (B.inclusion.map (iB ≫ sndB)) := het
  refine setConstructibilityDescendsAlongSurjective B oS' S gB hg.surj
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _)
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _ ?_
  have := isIso_smallEtaleBaseChangeNatTrans_univ.{u, 0} B fstB sndB p gB sq hcomm F
  refine isConstructibleSetSheaf_congr B _
    (asIso ((smallEtaleBaseChangeNatTransUniv.{u, 0} B fstB sndB p gB hcomm).app F)).symm ?_
  let G := (B.smallInverseImage fstB (Type (u + 1))).obj F
  have := isIso_unit_smallPullbackAdjunction_of_universalHomeomorphism B iB G
  refine isConstructibleSetSheaf_congr B _ ((B.smallPushforward sndB (Type (u + 1))).mapIso
    (asIso ((B.smallPullbackAdjunction iB (Type (u + 1))).unit.app G))).symm ?_
  refine isConstructibleSetSheaf_congr B _
    ((smallEtaleSheafPushforwardCompIso B oZ oP oS' iB sndB (Type (u + 1))).app _).symm ?_
  exact isConstructibleSetSheaf_pushforward_unconditional B (iB ≫ sndB) _
    (isConstructibleFiniteSheaf_pullback B iB G (isConstructibleFiniteSheaf_pullback B fstB F hF))

/-- **Stacks 095R for sheaves of sets.** Let `p : T ⟶ S` be a finite morphism of finite
presentation of a big étale site and let `ℱ` be a constructible sheaf of sets on `T_étale`. Then
`p_*ℱ` is a constructible sheaf of sets on `S_étale`. No hypothesis is imposed on `S` or `T`.

By Stacks 095F constructibility may be checked on the covering of `S` by its affine opens, and
over an affine open `U` the restriction of `p_*ℱ` is the direct image of the restriction of `ℱ`
along the base change of `p` to `U`, which is again finite and of finite presentation; there the
source's reduction applies: base change along the surjection of Stacks 095K (1) (Stacks 095Q (1)
and 0959), replace the pullback by its finite étale thickening (the unit of a finite universal
homeomorphism is an isomorphism), and conclude by Stacks 095H. -/
@[stacks 095R "sheaves of sets",
  sga "4 IX 2.14" "(i), sets variant",
  sga "4 XIV 1.1" "special case",
  sga "4 XIV 1.11" "partial",
  sga "4 XIV 1.5" "special case"]
public theorem isConstructibleSetSheaf_pushforward_of_isFinite {T S : B.Scheme} (p : T ⟶ S)
    [IsFinite (B.inclusion.map p)] (hfp : FinitePresentation (B.inclusion.map p))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  have hUopen : ∀ i, IsOpenImmersion ((B.inclusion.obj S).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj S).affineOpenCover.openCover.map_prop i
  have hUc : ∀ i, B.Contains ((B.inclusion.obj S).affineOpenCover.openCover.X i) := fun i =>
    have := hUopen i
    Scheme.size_lt_of_isOpenImmersion ((B.inclusion.obj S).affineOpenCover.openCover.f i)
      S.property
  let W : (B.inclusion.obj S).affineOpenCover.openCover.I₀ →
      SmallEtale B S.1 S.property := fun i =>
    ⟨Over.mk (ObjectProperty.homMk
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) :
        B.obj _ (hUc i) ⟶ B.obj S.1 S.property), by
      have := hUopen i
      show Etale ((B.inclusion.obj S).affineOpenCover.openCover.f i)
      infer_instance⟩
  refine isConstructibleFiniteSheaf_of_openCover B S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) hUopen
    (B.inclusion.obj S).affineOpenCover.openCover.iUnion_range.symm fun i => ?_
  have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
  have : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
  have : IsAffine (B.inclusion.obj (W i).obj.left) :=
    Scheme.isAffine_affineCover (B.inclusion.obj S) i
  refine isConstructibleSetSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
      (Type (u + 1))).app _).symm ?_
  refine isConstructibleSetSheaf_congr B _
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i) (Type (u + 1))).app F) ?_
  exact isConstructibleSetSheaf_pushforward_of_isFinite_of_isAffine B
    (baseChangedEtaleProjection B p (W i))
    (FinitePresentation.of_isPullback (isPullback_splitBaseChange B p (W i)) hfp) _
    (isConstructibleFiniteSheaf_smallEtaleRestriction B T
      ((smallEtaleBaseChange B p).obj (W i)) F hF)

end AlgebraicGeometry

end
