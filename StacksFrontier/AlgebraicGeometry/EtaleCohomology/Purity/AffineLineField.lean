module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SeparableExtensionHigherBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.CurveHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.CoverDense
public import StacksFrontier.AlgebraicGeometry.AffineUniversalHomeo.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFundamentalExactSequence
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of `𝐆_m ⊆ 𝐀¹` over an arbitrary field

Let `k` be a field and `j : 𝐆_m ⟶ 𝐀¹_k` the inclusion of the punctured affine line. For an
abelian sheaf `G` on `𝐆_m` killed by an integer `n` invertible in `k`, `R^q j_* G = 0` for every
`q ≥ 2`.

The proof descends the vanishing over an algebraically closed field
(`Stacks.EtaleCohomology.isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one`, from
[Stacks, Tag 03SC]) in two steps. From a separably closed field `K` to its algebraic closure `L`
the base change `Y_L ⟶ Y` is a universal homeomorphism, along which higher direct images are
computed (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism`).
From `k` to its separable closure, higher direct images commute with base change
(`Stacks.EtaleCohomology.SeparableBaseChange.isIso_higherBaseChangeMapAb`, from [Stacks, Tag
0EYM]), and inverse image along the surjective `𝐀¹_{k^{sep}} ⟶ 𝐀¹_k` detects zero sheaves.

## Main results

* `Stacks.EtaleCohomology.Purity.affineLineTorsionVanishing`: **`R^q j_* G = 0` for `q ≥ 2`**,
  i.e. `Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing k`, for every field `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [-instance] CategoryTheory.catToReflQuiver

/-- **Inverse image along a surjective morphism detects zero sheaves.** -/
theorem isZero_of_isZero_smallEtalePullbackAb {T' T : Scheme.{u}} (π : T' ⟶ T) [Surjective π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (h : IsZero ((smallEtalePullbackAb π).obj F)) : IsZero F := by
  have := mono_smallEtaleUnitAb_of_surjective π F
  exact IsZero.of_mono ((smallEtaleAdjunctionAb π).unit.app F)
    (Functor.map_isZero (smallEtalePushforwardAb π) h)

/-- Inverse image preserves being killed by `n`. -/
theorem nsmul_id_smallEtalePullbackAb {T' T : Scheme.{u}} (π : T' ⟶ T)
    {G : Sheaf (smallEtaleTopology T) Ab.{u + 1}} {n : ℕ} (hG : n • 𝟙 G = 0) :
    n • 𝟙 ((smallEtalePullbackAb π).obj G) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]

/-- A sheaf killed by a positive integer is a torsion sheaf. -/
theorem torsionSheafProperty_of_nsmul_id {Y : Scheme.{u}}
    {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {n : ℕ} (hn : 0 < n) (hG : n • 𝟙 G = 0) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G := fun V x =>
  ⟨⊤, Y.smallEtaleTopology.top_mem _, fun W f _ => ⟨n, hn, by
    have h1 := (sheafToPresheaf _ _).map_nsmul (f := 𝟙 G) (n := n)
    rw [hG, Functor.map_zero, CategoryTheory.Functor.map_id] at h1
    have := congrArg (fun g => (g.app (op W)).hom (G.obj.map f.op x)) h1
    simpa [NatTrans.app_nsmul, AddCommGrpCat.hom_nsmul] using this.symm⟩⟩

/-- A base change of a universal homeomorphism is a universal homeomorphism. -/
theorem universalHomeomorphism_pullback_snd {X Y S : Scheme.{u}} (s : X ⟶ S) (π : Y ⟶ S)
    [hs : UniversalHomeomorphism s] : UniversalHomeomorphism (pullback.snd s π) :=
  ⟨MorphismProperty.universally_isStableUnderBaseChange _ |>.of_isPullback
    (IsPullback.of_hasPullback s π) hs.1⟩

/-- `Spec L ⟶ Spec K` is a universal homeomorphism for the algebraic closure `L` of a separably
closed field `K`. -/
theorem universalHomeomorphism_spec_algebraicClosure (K : Type u) [Field K] [IsSepClosed K] :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := by
  have : ExpChar K (ringExpChar K) := inferInstance
  refine universalHomeomorphism_specMap_of_pow_mem_range (k := K)
    (algebraMap K (AlgebraicClosure K)) (ringExpChar K) ?_
    fun s => IsPurelyInseparable.pow_mem K (ringExpChar K) s
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]
  exact bot_le

/-- **`R^r h_* G = 0` for `r ≥ 2` over a separably closed field**, for an affine `h : Y ⟶ X` over
`K` with `Y` locally of finite type and of dimension at most one over `K`, and `G` killed by a
positive integer. Base change to the algebraic closure `L` of `K` is a universal homeomorphism,
which computes higher direct images, and over `L` this is Stacks 03SC. -/
theorem isZero_rightDerived_pushforward_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of K)) (h : Y ⟶ X) [IsAffineHom h]
    [LocallyOfFiniteType (h ≫ πX)] (hdim : topologicalKrullDim Y ≤ 1)
    (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) {n : ℕ} (hn : 0 < n) (hG : n • 𝟙 G = 0)
    (r : ℕ) (hr : 2 ≤ r) : IsZero (((smallEtalePushforwardAb h).rightDerived r).obj G) := by
  let L := AlgebraicClosure K
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have := universalHomeomorphism_spec_algebraicClosure K
  let f' := pullback.snd s πX
  let e' := pullback.snd s (h ≫ πX)
  let h' := SeparableBaseChange.baseChangeMap πX h s
  have : UniversalHomeomorphism f' := universalHomeomorphism_pullback_snd s πX
  have : UniversalHomeomorphism e' := universalHomeomorphism_pullback_snd s (h ≫ πX)
  have sq := SeparableBaseChange.isPullback_baseChangeMap πX h s
  have : IsAffineHom h' := MorphismProperty.of_isPullback sq.flip inferInstance
  have hdim' : topologicalKrullDim (Limits.pullback s (h ≫ πX) : Scheme.{u}) ≤ 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (isHomeomorph_base_of_universalHomeomorphism e')).le.trans hdim
  have hz : IsZero (((smallEtalePushforwardAb h').rightDerived r).obj
      ((smallEtalePullbackAb e').obj G)) :=
    isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one L h' (pullback.fst s (h ≫ πX))
      hdim' _ (torsionSheafProperty_of_nsmul_id hn (nsmul_id_smallEtalePullbackAb e' hG)) r hr
  have := isEquivalence_smallEtalePushforwardAb_of_universalHomeomorphism f'
  have hb := isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism e' h (𝟙 X) rfl (e' ≫ h)
    (by simp) r G
  refine isZero_of_isZero_smallEtalePullbackAb (𝟙 X) _ ?_
  refine IsZero.of_iso ?_ (@asIso _ _ _ _ _ hb)
  rw [show e' ≫ h = h' ≫ f' from sq.w.symm]
  exact (Functor.map_isZero (smallEtalePushforwardAb f') hz).of_iso
    ((Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbCompIso h' f').symm r).app _ ≪≫
      ((smallEtalePushforwardAb h').rightDerivedCompIso (smallEtalePushforwardAb f') r).app _)

/-- **`R^q j_* G = 0` for `q ≥ 2` along `j : 𝐆_m ⟶ 𝐀¹_k`, over any field `k`**, for every abelian
sheaf `G` on `𝐆_m` killed by an integer invertible in `k`. Over the separable closure `K` of `k`
the higher direct images are the inverse images of those over `k`
(`Stacks.EtaleCohomology.SeparableBaseChange.isIso_higherBaseChangeMapAb`), they vanish over `K`
(`Stacks.EtaleCohomology.Purity.isZero_rightDerived_pushforward_of_isSepClosed`), and inverse image
along the surjective `𝐀¹_K ⟶ 𝐀¹_k` detects zero sheaves. -/
@[sga "4 XIX 3.2" "special case"]
theorem affineLineTorsionVanishing (k : Type u) [Field k] : AffineLineTorsionVanishing k := by
  intro G n hn _ hG q hq
  let K := SeparableClosure k
  let sK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let πX := affineLine k ↘ Spec (.of k)
  let j := (punctured k).ι
  have : IsSeparated j := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have := AlgebraicGeometry.surjective_specMap_algebraMap_field k K
  have : Surjective (pullback.snd sK πX) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback sK πX) inferInstance
  have hb := SeparableBaseChange.isIso_higherBaseChangeMapAb k K πX j G q
  let h := SeparableBaseChange.baseChangeMap πX j sK
  have sq := SeparableBaseChange.isPullback_baseChangeMap πX j sK
  have : IsOpenImmersion h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsAffineHom j := isAffineHom_of_isAffine _
  have : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : LocallyOfFiniteType (h ≫ pullback.fst sK πX) := by
    rw [show h ≫ pullback.fst sK πX = pullback.fst sK (j ≫ πX) by simp [h]]
    infer_instance
  have hdimX : topologicalKrullDim (Limits.pullback sK πX : Scheme.{u}) ≤ 1 :=
    SmoothBaseChange.topologicalKrullDim_le_one_of_affineLine (IsPullback.id_horiz πX)
      (IsPullback.of_hasPullback sK πX).flip
  have hdim : topologicalKrullDim (Limits.pullback sK (j ≫ πX) : Scheme.{u}) ≤ 1 :=
    (SmoothBaseChange.topologicalKrullDim_le_of_etale h).trans hdimX
  refine isZero_of_isZero_smallEtalePullbackAb (pullback.snd sK πX) _ ?_
  refine IsZero.of_iso ?_ (@asIso _ _ _ _ _ hb)
  exact isZero_rightDerived_pushforward_of_isSepClosed K (pullback.fst sK πX) h hdim _ hn
    (nsmul_id_smallEtalePullbackAb _ hG) q hq

end Stacks.EtaleCohomology.Purity
