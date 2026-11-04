module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensAcyclicityTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedFibreTwoChartVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of torsion sheaves on curves which need not be separated (Stacks 03RT)

Let `X` be a scheme of finite type and of dimension at most one over an algebraically closed field
`k`, and let `F` be a torsion abelian sheaf on `X_étale`. Then `H^q_étale(X, F) = 0` for `q ≥ 3`,
and if `X` is affine also `H^2_étale(X, F) = 0` ([Stacks, Tag 03RT]). Unlike Theorem 03SC, no
separatedness is assumed.

The proof is the source's. If `X` is affine it is Theorem 03SC (2), Tag 0A54. In general `X` is
covered by finitely many affine opens `X_1, …, X_n`, and by induction on `n` the vanishing holds
over `U = X_1 ∪ ⋯ ∪ X_{n-1}`; the Mayer--Vietoris sequence of Tag 0A50,

`H^{q-1}(U ∩ X_n, F) ⟶ H^q(X, F) ⟶ H^q(U, F) ⊕ H^q(X_n, F)`,

then gives the vanishing over `X` once `H^{q-1}(U ∩ X_n, F) = 0` for `q ≥ 3`. The source obtains
that from the affineness of `U ∩ X_n`, an open of the affine curve `X_n`. Here it is obtained from
Theorem 03SC applied on the affine `X_n` and on its open `W = U ∩ X_n` directly, with no appeal to
the affineness of `W`: in degree `2` the restriction `H^2(X_n, F) ⟶ H^2(W, F)` is surjective by
Tag 0A5A and its source vanishes by Tag 0A54, and in degrees `≥ 3` the scheme `W`, open in the
separated `X_n`, is in Situation 0A52 and Tag 0A53 applies.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_of_three_le`: **Tag 03RT**, `H^q(X, F) = 0` for
  every `q ≥ 3`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_two_of_isAffine`: **Tag 03RT**, `H^2(X, F) = 0`
  when `X` is affine.
* `Stacks.EtaleCohomology.subsingleton_h'_opensToSite_iSup_of_three_le`: the Mayer--Vietoris
  induction over a finite union of affine opens.

## Implementation notes

The hypotheses are those of Situation 0A52 (`Stacks.EtaleCohomology.TorsionSheafSituation`)
without separatedness: finite type is `LocallyOfFiniteType` with `QuasiCompact` of the structure
morphism, and the dimension bound is `topologicalKrullDim X ≤ 1`. The source says "dimension 1";
the bound `≤ 1` contains that case and is what the proof uses. The coefficients are
`AddCommGrpCat.{max (u + 1) v}` for every `v` and the `Ext` universe `w` is arbitrary, as in
Theorem 03SC.

The Mayer--Vietoris sequence of Tag 0A50 is available for cohomology *over the open subschemes*,
read as objects of the one-universe model `Stacks.EtaleCohomology.MayerVietoris.Site` of the small
étale site, at coefficients `AddCommGrpCat.{u + 1}`. The induction is therefore run there for a
sheaf at those coefficients, and the vanishing over an open `W` is obtained from the vanishing of
the global cohomology of the restriction of the sheaf to `W` on Mathlib's site
(`OpensAcyclicity.subsingleton_opensCohomology_of_subsingleton_H_smallEtale`), where Theorem 03SC
is stated. For an open `W` of an affine open `V`, the cohomology over `W` is first
read on the site of `V` by Tag 03YU (`subsingleton_h'_image_of_subsingleton_h'_opensRestrict`) so
that Tags 0A5A and 0A54 on `V` apply. The general coefficient universe is reached as in
`Stacks.EtaleCohomology.curveStatements_partial_of_torsionSheafProperty`: a sheaf at
`AddCommGrpCat.{max (u + 1) v}` is the filtered colimit of universe lifts of torsion subsheaves at
`AddCommGrpCat.{u + 1}`, and cohomology of the noetherian scheme `X` commutes with filtered
colimits (Tag 03Q5).

## References

* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology

universe w v u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section Model

variable {X : Scheme.{u}} (V : X.Opens) (W : V.toScheme.Opens)

/-- The open subscheme `W` of the open subscheme `V`, carried into the small étale site of `X`
by composition with the inclusion of `V`, is the image of `W` in `X` read as an object there. -/
def opensInclusionImageIso :
    (ConstantTransport.opensInclusion X V).obj ((MayerVietoris.opensToSite V).obj W) ≅
      (MayerVietoris.opensToSite X).obj (V.ι ''ᵁ W) :=
  (AsSmall.up : X.Etale ⥤ MayerVietoris.Site X).mapIso
    (MorphismProperty.Over.isoMk (V.ι.isoImage W) (V.ι.isoImage_hom_ι W))

/-- Cohomology over an open subscheme of an open subscheme `V` of `X`, computed on the small
étale site of `V` for the restriction of `F`, is the cohomology of `F` over its image in `X`. -/
theorem subsingleton_h'_image_of_subsingleton_h'_opensRestrict
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H'.{u + 1} ((OpensAcyclicity.opensRestrict X V).obj F) q
      ((MayerVietoris.opensToSite V).obj W))) :
    Subsingleton (Sheaf.H'.{u + 1} F q ((MayerVietoris.opensToSite X).obj (V.ι ''ᵁ W))) := by
  have : ∀ P : (MayerVietoris.Site V.toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ConstantTransport.opensInclusion X V).op.HasPointwiseRightKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  let e : Sheaf.H'.{u + 1} ((OpensAcyclicity.opensRestrict X V).obj F) q
        ((MayerVietoris.opensToSite V).obj W) ≅
      Sheaf.H'.{u + 1} F q ((MayerVietoris.opensToSite X).obj (V.ι ''ᵁ W)) :=
    (Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
        (MayerVietoris.topology V.toScheme) (MayerVietoris.topology X)
        (ConstantTransport.opensInclusion X V) ((MayerVietoris.opensToSite V).obj W) q).app F ≪≫
      (F.cohomologyPresheaf q).mapIso (opensInclusionImageIso V W).op.symm
  exact e.symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Model

section Succ

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [LocallyOfFiniteType π] (hdim : topologicalKrullDim X ≤ 1)
  (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G)

/-- An affine open subscheme of a finite type scheme of dimension at most one over `k`, with the
restriction of a torsion abelian sheaf to it, is an instance of Situation 0A52. -/
def TorsionSheafSituation.ofIsAffineOpen (V : X.Opens) (hV : IsAffineOpen V) :
    TorsionSheafSituation.{u, 0} :=
  have : IsAffine V := hV
  have : IsAffineHom (V.ι ≫ π) := isAffineHom_of_isAffine _
  have : IsSeparated (V.ι ≫ π) := IsSeparated.of_isAffineHom _
  have : QuasiCompact (V.ι ≫ π) := (quasiCompact_iff_compactSpace _).2 inferInstance
  { k := k
    X := V
    structureMorphism := V.ι ≫ π
    dimension_le_one := (topologicalKrullDim_subspace_le X (V : Set X)).trans hdim
    F := (OpensAcyclicity.smallEtaleOpensRestrict X V).obj G
    isTorsion := Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ G hG }

/-- An open subscheme `W` of an affine open subscheme `V` of a finite type scheme of dimension at
most one over `k`, with the restriction of a torsion abelian sheaf to it, is an instance of
Situation 0A52: `W` is separated, being open in the affine `V`. -/
def TorsionSheafSituation.ofLeIsAffineOpen (V : X.Opens) (hV : IsAffineOpen V)
    (W : V.toScheme.Opens) : TorsionSheafSituation.{u, 0} :=
  have : IsAffine V := hV
  have : IsAffineHom (V.ι ≫ π) := isAffineHom_of_isAffine _
  have : IsSeparated (V.ι ≫ π) := IsSeparated.of_isAffineHom _
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ π)
  have : IsNoetherian V := ⟨⟩
  have : CompactSpace W := isCompact_iff_compactSpace.1
    (TopologicalSpace.NoetherianSpace.isCompact (W : Set V))
  have : QuasiCompact (W.ι ≫ V.ι ≫ π) := (quasiCompact_iff_compactSpace _).2 ‹_›
  { k := k
    X := W
    structureMorphism := W.ι ≫ V.ι ≫ π
    dimension_le_one := ((topologicalKrullDim_subspace_le V (W : Set V)).trans
      (topologicalKrullDim_subspace_le X (V : Set X))).trans hdim
    F := (OpensAcyclicity.smallEtaleOpensRestrict V W).obj
      ((OpensAcyclicity.smallEtaleOpensRestrict X V).obj G)
    isTorsion := Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ _
      (Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ G hG) }

include π hdim hG

/-- The cohomology of a torsion abelian sheaf over an affine open vanishes above degree one, read
over the open subscheme in the one-universe model of the site. -/
theorem subsingleton_h'_opensToSite_of_isAffineOpen (V : X.Opens) (hV : IsAffineOpen V)
    (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H'.{u + 1} ((MayerVietoris.mayerVietorisRestrict X).obj G) q
      ((MayerVietoris.opensToSite X).obj V)) := by
  have : IsAffine V := hV
  exact OpensAcyclicity.subsingleton_opensCohomology_of_subsingleton_H_smallEtale X V G q
    ((TorsionSheafSituation.ofIsAffineOpen π hdim G hG V hV).isAffineVanishingAboveDegreeOne.{u +
      1, 0, u} this q hq)

/-- The cohomology of a torsion abelian sheaf over an open contained in an affine open vanishes
above degree one. In degree two this is the surjectivity of `H²(V, F) → H²(W, F)` of Tag 0A5A on
the affine `V`, whose source vanishes; above degree two it is Tag 0A53 on `W`, which is
separated. -/
theorem subsingleton_h'_opensToSite_of_le_isAffineOpen (V : X.Opens) (hV : IsAffineOpen V)
    (W : X.Opens) (hWV : W ≤ V) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H'.{u + 1} ((MayerVietoris.mayerVietorisRestrict X).obj G) q
      ((MayerVietoris.opensToSite X).obj W)) := by
  have : IsAffine V := hV
  let S := TorsionSheafSituation.ofIsAffineOpen π hdim G hG V hV
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  have hW : V.ι ''ᵁ W' = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hWV
  rw [← hW]
  apply subsingleton_h'_image_of_subsingleton_h'_opensRestrict
  refine OpensAcyclicity.subsingleton_opensCohomology_of_subsingleton_H_smallEtale V W' S.F q ?_
  obtain rfl | hq2 : q = 2 ∨ 2 < q := by omega
  · have := S.isAffineVanishingAboveDegreeOne.{u + 1, 0, u} this 2 (by omega)
    have hinv := (S.isDegreeTwoOpenRestrictionSurjective.{u + 1, 0, u} W').subsingleton
    exact (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} W'.ι).app S.F) 2).1 hinv
  · exact (TorsionSheafSituation.ofLeIsAffineOpen π hdim G hG V hV
      W').isVanishingAboveDegreeTwo.{u + 1, 0, u} q hq2

/-- **The Mayer--Vietoris induction.** Over the union of finitely many affine opens, the
cohomology of a torsion abelian sheaf vanishes in every degree at least three.

Adding an affine open `V` to a union `U` of affine opens, the window
`H^{q-1}(U ∩ V) ⟶ H^q(U ∪ V) ⟶ H^q(U) ⊕ H^q(V)` of the Mayer--Vietoris sequence has vanishing
ends: `U ∩ V` lies in the affine `V`, so its cohomology vanishes above degree one. -/
theorem subsingleton_h'_opensToSite_iSup_of_three_le (t : Finset X.affineOpens) (q : ℕ)
    (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H'.{u + 1} ((MayerVietoris.mayerVietorisRestrict X).obj G) q
      ((MayerVietoris.opensToSite X).obj (⨆ i ∈ t, (i : X.Opens)))) := by
  classical
  induction t using Finset.induction_on generalizing q with
  | empty =>
    simpa using subsingleton_h'_opensToSite_of_isAffineOpen π hdim G hG ⊥ (isAffineOpen_bot X)
      q (by omega)
  | @insert a t _ ih =>
    rw [Finset.iSup_insert, sup_comm]
    obtain ⟨n₀, rfl⟩ : ∃ n₀, n₀ + 1 = q := ⟨q - 1, by omega⟩
    exact MayerVietoris.subsingleton_cohomologySup_of_subsingleton _ _ _ n₀ (n₀ + 1) rfl
      (subsingleton_h'_opensToSite_of_le_isAffineOpen π hdim G hG a a.2 _ inf_le_right n₀
        (by omega))
      (ih _ hq) (subsingleton_h'_opensToSite_of_isAffineOpen π hdim G hG a a.2 _ (by omega))

/-- The first statement of Tag 03RT at the coefficients `AddCommGrpCat.{u + 1}`: the étale
cohomology of a torsion abelian sheaf on a finite type scheme of dimension at most one over an
algebraically closed field vanishes in every degree at least three. The scheme is the union of
finitely many affine opens, so this is `subsingleton_h'_opensToSite_iSup_of_three_le` over `⊤`,
which is terminal, carried from the one-universe model to Mathlib's small étale site. -/
@[sga "4½ Arcata 3.3.6" "more general"]
theorem subsingleton_sheafH_of_three_le_succ [QuasiCompact π]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{w} G q) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨s, hs, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp
    (by simpa using isCompact_univ)
  have htop : (⨆ i ∈ hs.toFinset, (i : X.Opens)) = ⊤ := by
    simp only [← Finset.mem_coe, hs.coe_toFinset, ← e]
  have h := subsingleton_h'_opensToSite_iSup_of_three_le π hdim G hG hs.toFinset q hq
  rw [htop] at h
  have hH : Subsingleton (Sheaf.H.{u + 1} ((MayerVietoris.mayerVietorisRestrict X).obj G) q) :=
    (MayerVietoris.cohomologyTopIsoH X _ q).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  exact DenseSubsiteSheaf.subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
    (MayerVietoris.topology X) X.smallEtaleTopology
    (AsSmall.down : MayerVietoris.Site X ⥤ X.Etale) (MayerVietoris.selfIsTerminal X)
    (MayerVietoris.isTerminalAsSmallDownSelf X) G q hH

end Succ

section Max

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include π hdim hF

/-- **Stacks Project, Tag 03RT.** Let `X` be a scheme of finite type and of dimension at most one
over an algebraically closed field `k`, and let `F` be a torsion abelian sheaf on `X_étale`. Then
`H^q_étale(X, F) = 0` for every `q ≥ 3`.

No separatedness is assumed. The source's "dimension 1" is the case of equality of the bound
`topologicalKrullDim X ≤ 1`. -/
@[stacks 03RT "H^q(X, F) = 0 for q ≥ 3",
  sga "4 XVII 5.2.8.1" "special case",
  sga "4½ Arcata 3.3.6" "more general"]
theorem subsingleton_sheafH_of_three_le (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  have hw := ‹HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})›
  have hmax : HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    IsGrothendieckAbelian.hasExt _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsNoetherian X := ⟨⟩
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ := exists_isColimit_etaleUlift_mono F
  choose G hG using fun j ↦ (hD j).2
  have he : ∀ j, (etaleUlift.{v} X).obj (G j) ≅ D.obj j := fun j ↦ (hG j).some
  have hmono : ∀ j, Mono (ι.app j) := fun j ↦ (hD j).1
  have hGt : ∀ j, Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (G j) := fun j ↦
    torsionSheafProperty_of_etaleUlift
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_mono ((he j).hom ≫ ι.app j) hF)
  exact subsingleton_sheafH_chgUniv.{max (u + 1) v, w, v, u} hmax hw q
    (subsingleton_sheafH_of_isColimit_max hc q fun j ↦
      subsingleton_sheafH_of_etaleUlift_iso (he j) q
        (subsingleton_sheafH_of_three_le_succ π hdim (G j) (hGt j) q hq))

/-- **Stacks Project, Tag 03RT.** Let `X` be an affine scheme of finite type and of dimension at
most one over an algebraically closed field `k`, and let `F` be a torsion abelian sheaf on
`X_étale`. Then `H^2_étale(X, F) = 0`.

An affine scheme is separated over `k`, so this is Theorem 03SC (2), Tag 0A54. -/
@[stacks 03RT "H^2(X, F) = 0 if X is affine", sga "4½ Arcata 3.3.6" "(ii), degree q=2"]
theorem subsingleton_sheafH_two_of_isAffine [IsAffine X] : Subsingleton (Sheaf.H.{w} F 2) :=
  have : IsAffineHom π := isAffineHom_of_isAffine _
  have : IsSeparated π := IsSeparated.of_isAffineHom _
  (TorsionSheafSituation.mk k X π hdim F hF).isAffineVanishingAboveDegreeOne.{w, v, u}
    ‹IsAffine X› 2 (by omega)

end Max

end Stacks.EtaleCohomology
