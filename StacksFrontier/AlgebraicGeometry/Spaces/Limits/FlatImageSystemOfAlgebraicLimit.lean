module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximationOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitBridgeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.TailSystemOfAlgebraicLimit

/-!
# Stacks 0CPC with no bound on the index type

In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated over `B`,
let `X = lim X_i` and `Y = lim Y_i` be the limit descriptions by scheme-theoretic images attached
to two diagrams as in Stacks 0CP8 (Stacks 0CP9), and let `(f_i)_{i ≥ i₀}` be a morphism of these
inverse systems with limit `f` (Stacks 0CPA). Stacks 0CPC asserts that if `f` is flat and of
finite presentation, then for all sufficiently large `i₃` the morphism `f_{i₃}` is flat,
`X = Y ×_{Y_{i₃}} X_{i₃}`, and `X_i = Y_i ×_{Y_{i₃}} X_{i₃}` for every `i ≥ i₃`. Here no bound is
put on the size of the index type.

The proof is that of `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback`:
by Stacks 07SK and 08K0 the morphism `f` is the base change of a flat morphism `u : U ⟶ Y_n` of
finite presentation, the base changes `U_l = Y_l ×_{Y_n} U` form a second inverse system with
limit `X`, and the image system of `X` is eventually isomorphic to it over `(Y_l)`, the
comparison maps being built and shown inverse by the two halves of Stacks 0CP4. Each of these
steps is applied in its form for inverse systems with limit bridges, which the image systems
and the system `(U_l)` have because their limit projections are scheme-theoretically dominant.

## Main results

* `AlgebraicGeometry.Space.exists_isFlat_of_isPullback_of_hasChartLimitBridges`: **Stacks 08K0**,
  flatness of the morphism, for an inverse system with limit bridges.
* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_flat_model_of_algebraicLimit`: a
  flat morphism of finite presentation is the base change of a flat morphism of finite
  presentation over a stage of the image system of its target.
* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback_of_algebraicLimit`:
  **Stacks 0CPC**.

## Implementation notes

The form carrying the bound `#I < B.cutoff.ord.cof` is
`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback`; the objects of the
comparison, `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.FlatComparison`, are those of that
proof.

## References

* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-! ### Stacks 08K0 along a system with limit bridges -/

/-- **Stacks 08K0**, flatness of the morphism, for an inverse system with limit bridges. Let
`(Y_j)` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms and limit `Y`, whose chart systems along étale affine points have limit bridges, and
let `f₀ : X₀ ⟶ Y_m` be a morphism locally of finite presentation from a quasi-compact algebraic
space to a quasi-compact quasi-separated member of the system. If the base change `f : X ⟶ Y`
of `f₀` to the limit is flat, then the base change of `f₀` to some later member `Y_j` is flat.
No bound is put on the size of the index category: this is the case of flatness of
`AlgebraicGeometry.Space.exists_holdsOnEveryEtaleChart_of_isPullback_of_hasChartLimitBridges`,
with Stacks 04AI for the affine schemes charting the members. -/
theorem exists_isFlat_of_isPullback_of_hasChartLimitBridges {hZ : B.Contains (⊤_ Scheme.{u})}
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (Ys : J ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (bridges : HasChartLimitBridges Ys)
    {c : Cone Ys} (hc : IsLimit c) (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j))
    (affYs : ∀ {j k : J} (a : j ⟶ k), IsAffineHom B S hS (Ys.map a)) {m : J}
    (qcYm : IsQuasiCompactSpace B S hS (Ys.obj m))
    (qsYm : IsAbsolutelyQuasiSeparated B S hS hZ (Ys.obj m))
    {X₀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX₀ : IsAlgebraicSpace B S hS X₀)
    (qcX₀ : IsQuasiCompactSpace B S hS X₀) (f₀ : X₀ ⟶ Ys.obj m)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    {q : X ⟶ X₀} {f : X ⟶ c.pt} (sq : IsPullback q f f₀ (c.π.app m))
    (flat : IsFlat B S hS f) :
    ∃ (j : J) (a : j ⟶ m),
      ∀ {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q' : X' ⟶ X₀) (f' : X' ⟶ Ys.obj j),
        IsPullback q' f' f₀ (Ys.map a) → IsFlat B S hS f' := by
  have : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_holdsOnEveryEtaleChart_of_isPullback_of_hasChartLimitBridges (hZ := hZ)
    (@Flat.{u}) Flat.isEtaleLocalOnSourceAndTarget Ys bridges hc algYs affYs qcYm qsYm algX₀
    qcX₀ f₀ fp sq ?_ flat
  intro Ds cs hcs haff k₀ X₀' Y₀' φ hk₀ hX₀ hY₀ hφ hlim
  have : ∀ {j k : Over m} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (Ds.map g) := haff
  have : CompactSpace (Ds.obj k₀) := Scheme.compactSpace_of_isAffine _
  have : CompactSpace X₀'.left := Scheme.compactSpace_of_isAffine _
  have : CompactSpace Y₀'.left := Scheme.compactSpace_of_isAffine _
  exact exists_flat_baseChange_of_limitBaseChange Ds cs k₀ X₀' Y₀' φ hcs

namespace GoodDiagram

namespace SystemMorphism

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt} {pY : Y ⟶ D.limitCone.pt}

/-- A morphism `f_j : X_j ⟶ Y_j` of tail systems is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_maps_app {GX : GoodDiagram B S hS hZ D pX}
    {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y} {i₀ : I} {leX : GX.index ≤ i₀}
    {leY : GY.index ≤ i₀} (F : SystemMorphism GX GY f i₀ leX leY) (p : Over (op i₀)) :
    IsLocallyOfFinitePresentation B S hS (F.maps.app p) :=
  isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS
    (tailSystem_isAlgebraicSpace GX leX p) (tailSystem_isAlgebraicSpace GY leY p) _
    (tailSystem_isLocallyNoetherian GY leY p)
    (isLocallyOfFiniteType_of_comp B S hS (tailSystem_isAlgebraicSpace GX leX p)
      (tailSystem_isAlgebraicSpace GY leY p) (D.system_isAlgebraicSpace p.left.unop)
      (F.maps.app p) (tailBase GY leY p)
      (by rw [F.over_base p]; exact isLocallyOfFiniteType_tailBase GX leX p))

/-- The base changes `U_l = Y_l ×_{Y_n} U` of a finitely presented morphism `u : U ⟶ Y_n` are
finitely presented over `Y_l`, quasi-compact and absolutely quasi-separated. -/
private theorem baseChange_tailSystem_props {GY : GoodDiagram B S hS hZ D pY} {i₀ : I}
    {leY : GY.index ≤ i₀} (algY : IsAlgebraicSpace B S hS Y) (qsY : IsQuasiSeparated B S hS pY)
    {n : Over (op i₀)} {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algU : IsAlgebraicSpace B S hS U)
    (u : U ⟶ (tailSystem GY leY).obj n) (fpU : IsFinitePresentation B S hS u) (l : Over n) :
    IsFinitePresentation B S hS (pullback.fst ((tailSystem GY leY).map l.hom) u) ∧
      IsQuasiCompactSpace B S hS ((baseChangeSystem (tailSystem GY leY) n u).obj l) ∧
      IsAbsolutelyQuasiSeparated B S hS hZ ((baseChangeSystem (tailSystem GY leY) n u).obj l) := by
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have aUs : IsAlgebraicSpace B S hS ((baseChangeSystem (tailSystem GY leY) n u).obj l) :=
    isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr n)
  have fp := isFinitePresentation_of_isPullback B S hS aUs algU (aYr _) (aYr n)
    (IsPullback.of_hasPullback ((tailSystem GY leY).map l.hom) u).flip fpU
  exact ⟨fp, isQuasiCompactSpace_of_isFinitePresentation B S hS _ (aYr _)
    (tailSystem_isQuasiCompactSpace GY leY _) fp,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ aUs
      (tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GY leY algY qsY _) fp.2.2⟩

/-- The transition morphisms of the system of base changes `U_l = Y_l ×_{Y_n} U` are affine. -/
private theorem isAffineHom_baseChangeSystem_map_tail (GY : GoodDiagram B S hS hZ D pY) {i₀ : I}
    (leY : GY.index ≤ i₀) {n : Over (op i₀)} {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u : U ⟶ (tailSystem GY leY).obj n) {l l' : Over n} (a : l ⟶ l') :
    IsAffineHom B S hS ((baseChangeSystem (tailSystem GY leY) n u).map a) :=
  isAffineHom_of_isPullback (isPullback_baseChangeSystem_map (tailSystem GY leY) n u a).flip
    (tailSystem_map_isAffineHom GY leY _)

/-- **The first half of the proof of Stacks 0CPC**, with no bound on the index type. A flat
morphism `f : X ⟶ Y` of finite presentation is the base change, along a projection `Y ⟶ Y_n` of
the image system of `Y`, of a flat morphism `u : U ⟶ Y_n` of finite presentation: Stacks 07SK
descends `f` to some stage, and Stacks 08K0 makes it flat after increasing the stage, both in
their forms for inverse systems with limit bridges. -/
theorem exists_flat_model_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsY : IsQuasiSeparated B S hS pY)
    (GY : GoodDiagram B S hS hZ D pY) {i₀ : I} (leY : GY.index ≤ i₀) (f : X ⟶ Y)
    (flat : IsFlat B S hS f) (fp : IsFinitePresentation B S hS f) :
    ∃ (n : Over (op i₀)) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B S hS U) (u : U ⟶ (tailSystem GY leY).obj n) (toU : X ⟶ U),
      IsFlat B S hS u ∧ IsFinitePresentation B S hS u ∧
        IsPullback toU f u ((tailCone GY leY).π.app n) := by
  classical
  let Yr := tailSystem GY leY
  let cY := tailCone GY leY
  have hcY : IsLimit cY := isLimit_tailCone_of_algebraicLimit GY leY algY
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GY leY algY qsY
  have afYr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Yr.map a) :=
    fun a => tailSystem_map_isAffineHom GY leY a
  have algL : IsAlgebraicSpace B S hS (limit Yr) :=
    isAlgebraicSpace_limit_tailSystem_of_algebraicLimit GY leY algY
  -- Step 1 (Stacks 07SK): `f` is the base change of a morphism `u : U ⟶ Y_m` of finite
  -- presentation along the projection `Y ⟶ Y_m`.
  let eY : Y ≅ limit Yr := hcY.conePointUniqueUpToIso (limit.isLimit Yr)
  have heY : ∀ j, eY.hom ≫ limit.π Yr j = cY.π.app j :=
    fun j => hcY.conePointUniqueUpToIso_hom_comp (limit.isLimit Yr) j
  obtain ⟨m, Uo, algU, fpU, ⟨φ⟩⟩ := exists_model_of_finitePresentation_of_limitBridges B S hS hZ
    Yr algL (tailSystem_hasAllChartLimitBridges GY leY algY qsY)
    (fun j => isAffineHom_π_of_isAlgebraicSpace B S hS Yr afYr (limit.isLimit Yr) algL j (aYr j))
    aYr afYr qcYr qsYr (Over.mk (f ≫ eY.hom)) algX
    (isFinitePresentation_comp_iso algX algY algL f eY fp)
  let U := Uo.left
  let u : U ⟶ Yr.obj m := Uo.hom
  let toU : X ⟶ U := φ.hom.left ≫ pullback.fst _ _
  have sqU : IsPullback toU f u (cY.π.app m) := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback u (limit.π Yr m))
      ((Over.forget _).mapIso φ.symm) (Iso.refl _) eY.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [toU]
      rfl
    · have hw : φ.inv.left ≫ f ≫ eY.hom = pullback.snd u (limit.π Yr m) := Over.w φ.inv
      rw [← hw]
      simp
    · simp
    · simp [← heY]
  -- Step 2 (Stacks 08K0): after increasing `m`, the morphism `u` is flat.
  have qcU : IsQuasiCompactSpace B S hS U :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS u (aYr m) (qcYr m) fpU
  obtain ⟨n, a, flatA⟩ := exists_isFlat_of_isPullback_of_hasChartLimitBridges Yr
    (tailSystem_hasChartLimitBridges GY leY algY) hcY aYr afYr (qcYr m) (qsYr m) algU qcU u
    fpU.1 sqU flat
  have sqR : IsPullback (pullback.snd (Yr.map a) u) (pullback.fst (Yr.map a) u) u (Yr.map a) :=
    (IsPullback.of_hasPullback (Yr.map a) u).flip
  have algP : IsAlgebraicSpace B S hS (pullback (Yr.map a) u) :=
    isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr _)
  refine ⟨n, pullback (Yr.map a) u, algP, pullback.fst _ _,
    pullback.lift (f ≫ cY.π.app n) toU ?_, flatA _ _ sqR,
    isFinitePresentation_of_isPullback B S hS algP algU (aYr _) (aYr _) sqR fpU, ?_⟩
  · rw [Category.assoc, cY.w a]
    exact sqU.w.symm
  · refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) sqR
    rw [pullback.lift_snd, cY.w a]
    exact sqU

section Comparison

variable {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
  {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}

/-- The objects of `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.FlatComparison` exist
for a flat morphism of finite presentation, with no bound on the index type. -/
theorem nonempty_flatComparison_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (F : SystemMorphism GX GY f i₀ leX leY)
    (flat : IsFlat B S hS f) (fp : IsFinitePresentation B S hS f) :
    Nonempty (FlatComparison F) := by
  classical
  let Xr := tailSystem GX leX
  let Yr := tailSystem GY leY
  let cX := tailCone GX leX
  let cY := tailCone GY leY
  have hcY : IsLimit cY := isLimit_tailCone_of_algebraicLimit GY leY algY
  have aXr := tailSystem_isAlgebraicSpace GX leX
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GY leY algY qsY
  have afYr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Yr.map a) :=
    fun a => tailSystem_map_isAffineHom GY leY a
  have hind : ∀ j, cX.π.app j ≫ F.maps.app j = f ≫ cY.π.app j := F.induces
  obtain ⟨n, U, algU, u, toU, flatU, fpU, sqU⟩ :=
    exists_flat_model_of_algebraicLimit algX algY qsY GY leY f flat fp
  -- Step 3 (Stacks 0CP4): the morphism `X ⟶ U` is defined over a stage `X_p ⟶ U`.
  obtain ⟨j0, t, p, a0, hp, ht1, ht2⟩ := exists_stage_map_of_limitBridge B S hS hZ
    Xr cX (isLimit_tailCone_of_algebraicLimit GX leX algX)
    (tailSystem_hasChartLimitBridges GX leX algX) aXr (tailSystem_isQuasiCompactSpace GX leX)
    (tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GX leX algX qsX)
    (fun a => tailSystem_map_isAffineHom GX leX a) algU (aYr n) u fpU.1 toU n (F.maps.app n)
    (by rw [sqU.w, hind]) algX
  let t₀ : Xr.obj p ⟶ U := Xr.map a0 ≫ t
  have ht₀lim : cX.π.app p ≫ t₀ = toU := ht1
  have ht₀u : t₀ ≫ u = Xr.map hp ≫ F.maps.app n := ht2
  clear ht1 ht2
  -- Step 4: the system of base changes `U_l = Y_l ×_{Y_n} U`, whose limit is `X`.
  have hcU : IsLimit (baseChangeCone Yr n u cY) := isLimitBaseChangeCone Yr n u hcY
  let e : X ≅ pullback (cY.π.app n) u := sqU.flip.isoPullback
  have hefst : e.inv ≫ f = pullback.fst (cY.π.app n) u := by
    rw [← sqU.flip.isoPullback_hom_fst, Iso.inv_hom_id_assoc]
  have aUs : ∀ l, IsAlgebraicSpace B S hS ((baseChangeSystem Yr n u).obj l) :=
    fun l => isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr n)
  have props := baseChange_tailSystem_props algY qsY algU u fpU
  have afUs : ∀ {l l' : Over n} (a : l ⟶ l'),
      IsAffineHom B S hS ((baseChangeSystem Yr n u).map a) :=
    fun a => isAffineHom_baseChangeSystem_map_tail GY leY u a
  -- Step 5 (Stacks 0CP4): the morphism `X ⟶ X_p` is defined over a stage `U_l ⟶ X_p`, over
  -- `Y_p`. The morphism `f_p` is of finite type with locally Noetherian target.
  let pU : Over n := Over.mk hp
  obtain ⟨q0, s', l0, b1, b2, hs1, hs2⟩ := exists_stage_map_of_limitBridge B S hS hZ
    (baseChangeSystem Yr n u) (baseChangeCone Yr n u cY) hcU
    (baseChangeSystem_hasChartLimitBridges Yr n u hcY aYr afYr algY algU flatU
      (isQuasiCompact_tailCone_π_of_algebraicLimit GY leY)
      (schemeTheoreticImage_tailCone_π GY leY))
    aUs (fun l => (props l).2.1) (fun l => (props l).2.2) afUs (aXr p) (aYr p) (F.maps.app p)
    (isLocallyOfFinitePresentation_maps_app F p)
    (e.inv ≫ cX.π.app p) pU (pullback.fst (Yr.map pU.hom) u)
    (by
      rw [Category.assoc, hind, ← Category.assoc, hefst, baseChangeCone_π_fst]
      rfl)
    (isAlgebraicSpace_of_iso B S hS e algX)
  let s₀ : (baseChangeSystem Yr n u).obj l0 ⟶ Xr.obj p := (baseChangeSystem Yr n u).map b1 ≫ s'
  have hs₀lim : (baseChangeCone Yr n u cY).π.app l0 ≫ s₀ = e.inv ≫ cX.π.app p := hs1
  have hs₀F : s₀ ≫ F.maps.app p =
      (baseChangeSystem Yr n u).map b2 ≫ pullback.fst (Yr.map pU.hom) u := hs2
  clear hs1 hs2
  refine ⟨⟨n, U, algU, u, toU, flatU, fpU, sqU, p, hp, t₀, ht₀lim, ht₀u, l0, b2.left, s₀,
    hs₀lim, ?_⟩⟩
  rw [hs₀F, baseChangeSystem_map_fst]

namespace FlatComparison

variable {F : SystemMorphism GX GY f i₀ leX leY} (M : FlatComparison F)

/-- **Density**, with no bound on the index type. The scheme-theoretic image of `X ⟶ U_l` is
all of `U_l`: it is the base change of `Y ⟶ Y_l`, whose image is all of `Y_l`, along the flat
morphism `U_l ⟶ Y_l` (Stacks 089E). -/
lemma schemeTheoreticImage_d_of_algebraicLimit (algY : IsAlgebraicSpace B S hS Y)
    (l : Over M.n) : schemeTheoreticImageSubfunctor B S hS (M.d l) = ⊤ := by
  rw [← (M.isPullback_d l).flip.isoPullback_hom_snd, schemeTheoreticImageSubfunctor_comp_of_epi,
    schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS (M.pr l)
      ((tailCone GY leY).π.app l.left) (M.isAlgebraicSpace_Us l)
      (tailSystem_isAlgebraicSpace GY leY _) algY (M.isFlat_pr l)
      (isQuasiCompact_tailCone_π_of_algebraicLimit GY leY _),
    schemeTheoreticImage_tailCone_π]
  rfl

/-- The morphism `q_l : U_l ⟶ B_l ×_{B_{i₁}} W` factors through the scheme-theoretic image
`X_l`. -/
lemma range_q_le_of_algebraicLimit (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (c : l ⟶ M.l₀) :
    Subfunctor.range (M.q l c) ≤ stageImage GX ((Over.map (homOfLE leX).op).obj l.left) := by
  have hZc : IsClosedSubspace B S hS
      ((stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).preimage (M.q l c)) :=
    isClosedSubspace_preimage B S hS (M.q l c) _ (isAlgebraicSpace_stageTarget GX _)
      (M.isAlgebraicSpace_Us l) (isClosedSubspace_stageImage GX _)
  have hle : Subfunctor.range (M.d l) ≤
      (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).preimage (M.q l c) := by
    rintro U x ⟨y, rfl⟩
    have hy : (M.q l c).app U ((M.d l).app U y) =
        (stageMap GX ((Over.map (homOfLE leX).op).obj l.left)).app U y := by
      simpa using congrArg (fun g => g.app U y) (M.d_q l c)
    show (M.q l c).app U ((M.d l).app U y) ∈ (stageImage GX _).obj U
    rw [hy]
    exact range_le_schemeTheoreticImageSubfunctor B S hS _ U ⟨_, rfl⟩
  have htop := schemeTheoreticImageSubfunctor_le B S hS (M.d l) hZc hle
  rw [M.schemeTheoreticImage_d_of_algebraicLimit algY l, top_le_iff] at htop
  exact (Subfunctor.preimage_eq_top_iff _ _).1 htop

/-- The comparison map `U_l ⟶ X_l`, with no bound on the index type: the morphism `q_l` factors
through the scheme-theoretic image `X_l`, because `X ⟶ U_l` is scheme-theoretically dense. -/
noncomputable def backOfAlgebraicLimit (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (c : l ⟶ M.l₀) : M.Us.obj l ⟶ (tailSystem GX leX).obj l.left :=
  Subfunctor.lift (M.q l c) (M.range_q_le_of_algebraicLimit algY l c)

/-- The comparison map `U_l ⟶ X_l`, followed by the inclusion of `X_l`, is `q_l`. -/
@[reassoc (attr := simp)]
lemma backOfAlgebraicLimit_ι (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (c : l ⟶ M.l₀) :
    M.backOfAlgebraicLimit algY l c ≫
        (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).ι = M.q l c :=
  Subfunctor.lift_ι _ _

/-- The comparison map `U_l ⟶ X_l`, followed by the transition morphism `X_l ⟶ X_p`, is
`s_l`. -/
lemma backOfAlgebraicLimit_map (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (c : l ⟶ M.l₀) (w : l.left ⟶ M.p) :
    M.backOfAlgebraicLimit algY l c ≫ (tailSystem GX leX).map w = M.s l c := by
  refine (cancel_mono (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · have h2 : M.backOfAlgebraicLimit algY l c ≫ tailBase GX leX l.left =
        M.pr l ≫ tailBase GY leY l.left := by
      rw [show tailBase GX leX l.left = (stageImage GX _).ι ≫ pullback.fst _ _ from rfl,
        ← Category.assoc, backOfAlgebraicLimit_ι, q_fst]
    calc ((M.backOfAlgebraicLimit algY l c ≫ (tailSystem GX leX).map w) ≫
          (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι) ≫ pullback.fst _ _
        = M.backOfAlgebraicLimit algY l c ≫
            ((tailSystem GX leX).map w ≫ tailBase GX leX M.p) := by
          simp only [Category.assoc]
      _ = M.pr l ≫ tailBase GY leY l.left ≫ D.system.map w.left := by
          rw [tailSystem_map_tailBase GX leX w, ← Category.assoc, h2, Category.assoc]
      _ = M.s l c ≫ tailBase GX leX M.p := (M.s_tailBase l c w).symm
      _ = _ := by simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, tailSystem_map_ι_snd, backOfAlgebraicLimit_ι_assoc, q_snd]
    simp only [Category.assoc]

/-- The comparison map `U_l ⟶ X_l`, followed by `f_l : X_l ⟶ Y_l`, is the projection
`U_l ⟶ Y_l`. -/
lemma backOfAlgebraicLimit_F (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (c : l ⟶ M.l₀) :
    M.backOfAlgebraicLimit algY l c ≫ F.maps.app l.left = M.pr l := by
  refine (cancel_mono (stageImage GY ((Over.map (homOfLE leY).op).obj l.left)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, show (stageImage GY _).ι ≫ pullback.fst _ _ =
      tailBase GY leY l.left from rfl, maps_tailBase, show tailBase GX leX l.left =
      (stageImage GX _).ι ≫ pullback.fst _ _ from rfl, backOfAlgebraicLimit_ι_assoc, q_fst]
    rfl
  · let w : l.left ⟶ M.p := c.left ≫ M.c₀
    rw [Category.assoc, Category.assoc, ← tailSystem_map_ι_snd GY leY w,
      ← Category.assoc (F.maps.app l.left), ← F.maps.naturality, Category.assoc,
      ← Category.assoc (M.backOfAlgebraicLimit algY l c), M.backOfAlgebraicLimit_map algY l c w,
      ← Category.assoc, M.s_F l c w, Category.assoc, tailSystem_map_ι_snd]
    simp only [Category.assoc]

/-- If `T_l ≫ s_l` is the transition morphism `X_l ⟶ X_p`, then `T_l : X_l ⟶ U_l` followed by
the comparison map `U_l ⟶ X_l` is the identity. -/
lemma T_backOfAlgebraicLimit (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (b : l ⟶ M.pU) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p)
    (h : M.T l b ≫ M.s l c = (tailSystem GX leX).map w) :
    M.T l b ≫ M.backOfAlgebraicLimit algY l c = 𝟙 _ := by
  refine (cancel_mono (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, backOfAlgebraicLimit_ι_assoc, q_fst, ← Category.assoc,
      T_pr, maps_tailBase, Category.id_comp]
  · rw [Category.assoc, Category.assoc, backOfAlgebraicLimit_ι_assoc, q_snd, ← Category.assoc, h,
      tailSystem_map_ι_snd, Category.id_comp]

/-- If `s_l ≫ t₀` is the projection `U_l ⟶ U`, then the comparison map `U_l ⟶ X_l` followed by
`T_l : X_l ⟶ U_l` is the identity. -/
lemma backOfAlgebraicLimit_T (algY : IsAlgebraicSpace B S hS Y) (l : Over M.n)
    (b : l ⟶ M.pU) (c : l ⟶ M.l₀)
    (h : M.s l c ≫ M.t₀ = pullback.snd ((tailSystem GY leY).map l.hom) M.u) :
    M.backOfAlgebraicLimit algY l c ≫ M.T l b = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, T_pr, backOfAlgebraicLimit_F, Category.id_comp]
  · rw [Category.assoc, T_snd, ← Category.assoc, backOfAlgebraicLimit_map, h, Category.id_comp]

/-- **The comparison maps are eventually inverse**, with no bound on the index type. At every
sufficiently late stage `l`, the composite `X_l ⟶ U_l ⟶ X_p` is the transition morphism and
`U_l ⟶ X_p ⟶ U` is the projection; both hold at one stage by the injectivity half of Stacks
0CP4, applied to the systems `X_l` and `U_l` in its form with limit bridges, and then at every
later stage. -/
lemma exists_eventually_inverse_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) :
    ∃ (l₂ : Over M.n) (b : l₂ ⟶ M.pU) (c : l₂ ⟶ M.l₀), ∀ (l : Over M.n) (a : l ⟶ l₂),
      M.T l (a ≫ b) ≫ M.s l (a ≫ c) = (tailSystem GX leX).map ((a ≫ c).left ≫ M.c₀) ∧
      M.s l (a ≫ c) ≫ M.t₀ = pullback.snd ((tailSystem GY leY).map l.hom) M.u := by
  classical
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have aXr := tailSystem_isAlgebraicSpace GX leX
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GY leY algY qsY
  have props := baseChange_tailSystem_props algY qsY M.algU M.u M.fp
  -- A common refinement of the two stages.
  let l₀' : Over M.n := IsCofiltered.min M.l₀ M.pU
  let c0 : l₀' ⟶ M.l₀ := IsCofiltered.minToLeft _ _
  let b0 : l₀' ⟶ M.pU := IsCofiltered.minToRight _ _
  let w0 : l₀'.left ⟶ M.p := c0.left ≫ M.c₀
  -- The first identity, by the injectivity half of Stacks 0CP4 for the system `X_l`.
  obtain ⟨kk, e2, heq⟩ := exists_stage_eq_of_limitBridge B S hS hZ
    (tailSystem GX leX) (tailCone GX leX) (isLimit_tailCone_of_algebraicLimit GX leX algX)
    (tailSystem_hasChartLimitBridges GX leX algX) aXr (tailSystem_isQuasiCompactSpace GX leX)
    (tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit GX leX algX qsX)
    (fun a => tailSystem_map_isAffineHom GX leX a) (aXr M.p) (aYr M.p) (F.maps.app M.p)
    (isLocallyOfFinitePresentation_maps_app F M.p)
    l₀'.left (M.T l₀' b0 ≫ M.s l₀' c0) ((tailSystem GX leX).map w0)
    (by rw [← Category.assoc, M.π_T, M.d_s, (tailCone GX leX).w])
    (by rw [Category.assoc, M.s_F l₀' c0 w0, ← Category.assoc, T_pr, F.maps.naturality]) algX
  let l₁ : Over M.n := Over.mk (e2 ≫ l₀'.hom)
  let a1 : l₁ ⟶ l₀' := Over.homMk e2
  have hi : ∀ (l : Over M.n) (a : l ⟶ l₁) (b : l ⟶ M.pU) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p),
      M.T l b ≫ M.s l c = (tailSystem GX leX).map w := by
    intro l a b c w
    rw [← M.s_map (a ≫ a1) c c0, ← Category.assoc, M.T_map (a ≫ a1) b b0, Category.assoc,
      show (a ≫ a1).left = a.left ≫ e2 from rfl, Functor.map_comp, Category.assoc, heq,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Subsingleton.elim ((a.left ≫ e2) ≫ w0) w]
  -- The second identity, by the injectivity half of Stacks 0CP4 for the system `U_l`.
  let c1 : l₁ ⟶ M.l₀ := a1 ≫ c0
  obtain ⟨l₂, a2, heq2⟩ := exists_stage_eq_of_limitBridge B S hS hZ M.Us M.cU
    (isLimitBaseChangeCone (tailSystem GY leY) M.n M.u
      (isLimit_tailCone_of_algebraicLimit GY leY algY))
    (baseChangeSystem_hasChartLimitBridges (tailSystem GY leY) M.n M.u
      (isLimit_tailCone_of_algebraicLimit GY leY algY) aYr
      (fun a => tailSystem_map_isAffineHom GY leY a) algY M.algU M.flat
      (isQuasiCompact_tailCone_π_of_algebraicLimit GY leY)
      (schemeTheoreticImage_tailCone_π GY leY))
    M.isAlgebraicSpace_Us
    (fun l => (props l).2.1) (fun l => (props l).2.2)
    (fun a => isAffineHom_baseChangeSystem_map_tail GY leY M.u a)
    M.algU (aYr M.n) M.u M.fp.1 l₁ (M.s l₁ c1 ≫ M.t₀) (pullback.snd _ _)
    (by
      have h1 : M.cU.π.app l₁ ≫ M.s l₁ c1 = M.e.inv ≫ (tailCone GX leX).π.app M.p := by
        rw [← M.d_s l₁ c1]
        simp only [d, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, h1, Category.assoc, M.t₀_lim, e_inv_toU, baseChangeCone_π_snd])
    (by
      rw [Category.assoc, M.t₀_u, F.maps.naturality, ← Category.assoc,
        M.s_F l₁ c1 (c1.left ≫ M.c₀), Category.assoc, ← Functor.map_comp, ← pullback.condition,
        Subsingleton.elim ((c1.left ≫ M.c₀) ≫ M.hp) l₁.hom])
    (isAlgebraicSpace_of_iso B S hS M.e algX)
  refine ⟨l₂, a2 ≫ a1 ≫ b0, a2 ≫ c1, fun l a => ⟨hi l (a ≫ a2) _ _ _, ?_⟩⟩
  rw [← M.s_map (a ≫ a2) (a ≫ a2 ≫ c1) c1, Functor.map_comp, Category.assoc, Category.assoc,
    heq2, baseChangeSystem_map_snd, baseChangeSystem_map_snd]

end FlatComparison

end Comparison

/-- **Stacks 0CPC.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces
quasi-separated over `B`, let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and `Y`, and
let `(f_i)_{i ≥ i₀}` be a morphism of the inverse systems of scheme-theoretic images
`X = lim X_i` and `Y = lim Y_i` whose limit is `f`, as in Stacks 0CPA. If `f` is flat and of
finite presentation, then there is a stage `i₃ ≥ i₀` such that for every `k ≥ i₃` the morphism
`f_k` is flat, `X = Y ×_{Y_k} X_k`, and `X_i = Y_i ×_{Y_k} X_k` for every `i ≥ k`. No bound is
put on the size of the index type. -/
theorem exists_isFlat_isPullback_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}
    (F : SystemMorphism GX GY f i₀ leX leY)
    (flat : IsFlat B S hS f) (fp : IsFinitePresentation B S hS f) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ k : Over (op i₀), i₃ ≤ k.left.unop →
      IsFlat B S hS (F.maps.app k) ∧
      IsPullback ((imageCone GX).π.app ((Over.map (homOfLE leX).op).obj k)) f
        (F.maps.app k) ((imageCone GY).π.app ((Over.map (homOfLE leY).op).obj k)) ∧
      ∀ (j : Over (op i₀)) (a : j ⟶ k),
        IsPullback ((imageSystem GX).map ((Over.map (homOfLE leX).op).map a)) (F.maps.app j)
          (F.maps.app k) ((imageSystem GY).map ((Over.map (homOfLE leY).op).map a)) := by
  obtain ⟨M⟩ := nonempty_flatComparison_of_algebraicLimit algX algY qsX qsY F flat fp
  obtain ⟨l₂, b, c, hinv⟩ := M.exists_eventually_inverse_of_algebraicLimit algX algY qsX qsY
  -- At every stage `l` above `l₂`, the comparison maps are mutually inverse isomorphisms
  -- `U_l ≅ X_l` over `Y_l`.
  let Φ : ∀ (l : Over M.n), (l ⟶ l₂) → (M.Us.obj l ≅ (tailSystem GX leX).obj l.left) :=
    fun l a =>
      { hom := M.backOfAlgebraicLimit algY l (a ≫ c)
        inv := M.T l (a ≫ b)
        hom_inv_id := M.backOfAlgebraicLimit_T algY l (a ≫ b) (a ≫ c) (hinv l a).2
        inv_hom_id := M.T_backOfAlgebraicLimit algY l (a ≫ b) (a ≫ c) _ (hinv l a).1 }
  have hΦF : ∀ (l : Over M.n) (a : l ⟶ l₂), (Φ l a).hom ≫ F.maps.app l.left = M.pr l :=
    fun l a => M.backOfAlgebraicLimit_F algY l (a ≫ c)
  have hΦnat : ∀ {l l' : Over M.n} (a : l ⟶ l') (h : l ⟶ l₂) (h' : l' ⟶ l₂),
      M.Us.map a ≫ (Φ l' h').hom = (Φ l h).hom ≫ (tailSystem GX leX).map a.left := by
    intro l l' a h h'
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
    exact M.T_map a _ _
  refine ⟨l₂.left.left.unop, leOfHom l₂.left.hom.unop, fun k hk => ?_⟩
  let hkl : k ⟶ l₂.left := Over.homMk (homOfLE hk).op (Subsingleton.elim _ _)
  let lk : Over M.n := Over.mk (hkl ≫ l₂.hom)
  let ak : lk ⟶ l₂ := Over.homMk hkl
  have algUk := M.isAlgebraicSpace_Us lk
  refine ⟨?_, ?_, fun j a => ?_⟩
  · have hF : F.maps.app k = (Φ lk ak).inv ≫ M.pr lk := (M.T_pr lk (ak ≫ b)).symm
    rw [hF]
    have := Iso.isIso_inv (Φ lk ak)
    exact isFlat_comp B S hS (tailSystem_isAlgebraicSpace GX leX k) algUk
      (tailSystem_isAlgebraicSpace GY leY k) _ _ (isFlat_of_isIso _ algUk) (M.isFlat_pr lk)
  · refine IsPullback.of_iso (M.isPullback_d lk) (Iso.refl _) (Φ lk ak) (Iso.refl _)
      (Iso.refl _) ?_ ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    · rw [Iso.refl_hom, Category.id_comp, ← M.π_T lk (ak ≫ b), Category.assoc]
      show _ ≫ (Φ lk ak).inv ≫ (Φ lk ak).hom = _
      rw [Iso.inv_hom_id, Category.comp_id]
      rfl
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lk ak).symm
  · let lj : Over M.n := Over.mk (a ≫ lk.hom)
    let aj : lj ⟶ lk := Over.homMk a
    refine IsPullback.of_iso
      (isPullback_baseChangeSystem_map (tailSystem GY leY) M.n M.u aj)
      (Φ lj (aj ≫ ak)) (Φ lk ak) (Iso.refl _) (Iso.refl _) (hΦnat aj (aj ≫ ak) ak) ?_ ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lj (aj ≫ ak)).symm
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lk ak).symm

end SystemMorphism

end GoodDiagram

end AlgebraicGeometry.Space

end
