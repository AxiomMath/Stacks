module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ClosedPointNeighborhoodsOfDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ResolutionTransferAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SchemeNormalizedBlowupBridge

/-!
# Lifting sequences of blowups at closed points from étale neighbourhoods to the whole space

Let `X` be a locally Noetherian decent algebraic space over a scheme `S`, with pairwise distinct
closed points `x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` as in
Section 0BH9 of the Stacks project. A sequence of blowups of the scheme `Uᵢ` at closed points
lying over `uᵢ` lifts, one blowing up at a time, to a sequence of blowings up of algebraic spaces
over `X` at closed points lying over `xᵢ`, whose base change to `Uᵢ` is the given sequence and
whose base change to every étale `P ⟶ X` missing `xᵢ` is unchanged. Doing this for each `i` in
turn produces a single sequence of blowings up of `X` at closed points lying over
`{x₁, …, xₙ}` whose base change to each `Uᵢ` is the `i`th given sequence.

This is the direction "from the `Uᵢ` to `X`" of Stacks 0BHF, in the form in which the proofs of
Stacks 0BHG and 0BHH use it.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_isLocallyNoetherian`: a closed subspace of
  a locally Noetherian algebraic space is of finite presentation.
* `AlgebraicGeometry.Space.exists_iso_pullback_comp_of_isBlowupAtClosedPoint` and
  `AlgebraicGeometry.Space.exists_iso_pullback_comp_blowUp`: a blowing up at a closed point does
  not change the base change along an étale morphism missing the centre, and base changes along
  an étale chart with a single point over the centre to the blowup of the chart's scheme.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_lift_isBlowupAtClosedPoint`: one
  step of the lifting.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_lift_pointBlowupChain`: one whole
  sequence over one neighbourhood.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupFactorization_stageRep`: all
  the neighbourhoods together.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Blowing up a locally Noetherian algebraic space -/

/-- **A closed subspace of a locally Noetherian algebraic space is of finite presentation**: on a
locally Noetherian surjective étale chart every sheaf of ideals is finitely generated over the
affine opens, which is Stacks 084Q. -/
theorem isFinitePresentation_ι_of_isLocallyNoetherian {X : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z : ClosedSubspaces B S hS X.obj) : IsFinitePresentation B S hS Z.1.ι := by
  obtain ⟨V, b, hbs, hbe, hV⟩ := hX
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hV
  refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) (X := X)
    (ObjectProperty.homMk Z.1.ι) Z.2.2 hbe hbs).2 fun A => ?_
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, A) :=
    IsLocallyNoetherian.component_noetherian A
  exact IsNoetherian.noetherian _

/-- **The blowing up of a locally Noetherian algebraic space is locally Noetherian**: the centre
is of finite presentation, so the blowing up is proper (Stacks 085Z), in particular locally of
finite type. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {Z : ClosedSubspaces B S hS X.obj} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) :
    HasEtaleLocalProperty B S hS X'.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X'.property
    X.property _ (isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z b
      (isFinitePresentation_ι_of_isLocallyNoetherian hX Z) hb).2.1.1 hX

/-! ### A blowing up at a closed point under étale base change -/

/-- **Away from the centre a blowing up at a closed point does not change the base change.** If
no point of `Z ×_X P` lies over the centre `z` of the blowing up `g : Z' ⟶ Z`, then
`Z' ×_X P = Z ×_X P` over `P`. -/
theorem exists_iso_pullback_comp_of_isBlowupAtClosedPoint
    {X Z Z' : AlgebraicSpaces B S hS} (f : Z ⟶ X) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {g : Z' ⟶ Z}
    (hg : IsBlowupAtClosedPoint B S hS z hz g)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (a : P ⟶ X.obj)
    (ha : IsEtale B S hS a)
    (hfib : ∀ t, pointsMap B S hS _ (pullback.fst f.hom a) t ≠ z) :
    ∃ e : pullback (g.hom ≫ f.hom) a ≅ pullback f.hom a,
      e.hom ≫ pullback.snd f.hom a = pullback.snd (g.hom ≫ f.hom) a := by
  let T : AlgebraicSpaces B S hS :=
    ⟨pullback f.hom a, isAlgebraicSpace_pullback B S hS f.hom a Z.property hP X.property⟩
  let φ : T ⟶ Z := ObjectProperty.homMk (pullback.fst f.hom a)
  have hφ : IsEtale B S hS φ.hom := isEtale_pullback_fst B S hS Z.property X.property hP _ _ ha
  have hqb : IsIso (ObjectProperty.homMk (pullback.fst φ.hom g.hom) :
      AlgebraicSpaces.fiberProduct B S hS φ g ⟶ T) :=
    isIso_of_isPullback_of_isBlowupAtClosedPoint_of_isEtale hφ
      (Set.eq_empty_of_forall_notMem fun t ht => hfib t ht) hg
      (AlgebraicSpaces.isPullback_fiberProduct B S hS φ g)
  have hiso : IsIso (pullback.fst φ.hom g.hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      (ObjectProperty.homMk (pullback.fst φ.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS φ g ⟶ T)))
  refine ⟨(pullbackRightPullbackFstIso f.hom a g.hom).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.fst φ.hom g.hom), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  show _ ≫ _ ≫ pullback.fst (pullback.fst f.hom a) g.hom ≫ pullback.snd f.hom a = _
  rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_snd]

/-- The composite of an inverse isomorphism with the base change of `f` along an étale `a` is
étale. -/
private theorem isEtale_inv_comp_pullback_fst {X Z : AlgebraicSpaces B S hS} (f : Z ⟶ X)
    {P F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (a : P ⟶ X.obj)
    (ha : IsEtale B S hS a) (e : pullback f.hom a ≅ F) :
    IsEtale B S hS (e.inv ≫ pullback.fst f.hom a) :=
  isEtale_comp B S hS (isEtale_of_iso B S hS e.symm)
    (isEtale_pullback_fst B S hS Z.property X.property hP _ _ ha)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **At the centre a blowing up at a closed point base changes to the blowup of the scheme
representing the base change.** If `Z ×_X V ≅ h_W` over `V` for a locally Noetherian scheme `W`,
and the closed point `w` of `W` is the only point over the centre `z` of the blowing up
`g : Z' ⟶ Z`, then `Z' ×_X V` is represented by the blowup of `W` at `w`, over `V`. -/
theorem exists_iso_pullback_comp_blowUp
    {X Z Z' : AlgebraicSpaces B S hS} (f : Z ⟶ X) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {g : Z' ⟶ Z}
    (hg : IsBlowupAtClosedPoint B S hS z hz g)
    {V W : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X.obj) (ha : IsEtale B S hS a)
    (q : W ⟶ V) (φ : pullback f.hom a ≅ yoneda.obj W)
    (hφ : φ.hom ≫ yoneda.map q = pullback.snd f.hom a)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _))
    (hfib : pointsMap B S hS _ (φ.inv ≫ pullback.fst f.hom a) ⁻¹' {z} =
      {schemeSpacePoint W w}) :
    ∃ (N : BigFppfOver B S hS) (q' : N ⟶ W) (e : pullback (g.hom ≫ f.hom) a ≅ yoneda.obj N)
      (ψ : (BigFppfOver.toScheme B S hS).obj N ≅
        AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _))),
      e.hom ≫ yoneda.map (q' ≫ q) = pullback.snd (g.hom ≫ f.hom) a ∧
        (BigFppfOver.toScheme B S hS).map q' = ψ.hom ≫ AlgebraicGeometry.blowUpToBase _ := by
  let φ' : schemeSpace W ⟶ Z := ObjectProperty.homMk (φ.inv ≫ pullback.fst f.hom a)
  have hφ' : IsEtale B S hS φ'.hom :=
    isEtale_inv_comp_pullback_fst f (isAlgebraicSpace_yoneda B S hS V) a ha φ
  have hBU : IsBlowupAtClosedPoint B S hS (schemeSpacePoint W w)
      (isClosed_singleton_schemeSpacePoint W hw)
      (ObjectProperty.homMk (pullback.fst φ'.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS φ' g ⟶ schemeSpace W) :=
    isBlowupAtClosedPoint_of_isPullback_of_isEtale hφ'
      (isClosed_singleton_schemeSpacePoint W hw) hfib hg
      (AlgebraicSpaces.isPullback_fiberProduct B S hS φ' g)
  obtain ⟨N, q', e₀, ψ, he₀, hq'⟩ := exists_iso_schemeSpace_blowUp_of_isBlowupAtClosedPoint W hw hBU
  -- the square exhibiting `Z' ×_X V` as `Z' ×_Z h_W`
  let l : pullback (g.hom ≫ f.hom) a ⟶ pullback f.hom a :=
    pullback.lift (pullback.fst _ _ ≫ g.hom) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  have hsq₁ : IsPullback (pullback.fst (g.hom ≫ f.hom) a) l g.hom (pullback.fst f.hom a) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f.hom a)
    have hl : l ≫ pullback.snd f.hom a = pullback.snd (g.hom ≫ f.hom) a := pullback.lift_snd _ _ _
    rw [hl]
    exact IsPullback.of_hasPullback (g.hom ≫ f.hom) a
  have hsq₂ : IsPullback (pullback.fst (g.hom ≫ f.hom) a) (l ≫ φ.hom) g.hom φ'.hom := by
    refine IsPullback.of_iso hsq₁ (Iso.refl _) (Iso.refl _) φ (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · show pullback.fst f.hom a ≫ 𝟙 _ = φ.hom ≫ φ.inv ≫ pullback.fst f.hom a
      simp
  let ε := (IsPullback.of_hasPullback φ'.hom g.hom).isoIsPullback _ _ hsq₂.flip
  let e₀' : pullback φ'.hom g.hom ≅ yoneda.obj N := (ObjectProperty.ι _).mapIso e₀
  refine ⟨N, q', ε.symm ≪≫ e₀', ψ, ?_, hq'⟩
  have h2 : e₀'.hom ≫ yoneda.map q' = pullback.fst φ'.hom g.hom :=
    congrArg (fun k => k.hom) he₀
  have h3 : ε.inv ≫ pullback.fst φ'.hom g.hom = l ≫ φ.hom :=
    IsPullback.isoIsPullback_inv_fst _ _ _ _
  rw [Iso.trans_hom, Functor.map_comp, Iso.symm_hom, Category.assoc, ← Category.assoc e₀'.hom,
    h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ yoneda.map q) h3).trans
    ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) hφ).trans (pullback.lift_snd _ _ _))))

/-- The blowup of a scheme at a closed point, transported along an isomorphism of schemes. -/
theorem exists_blowUp_vanishingIdeal_iso_of_iso {Z W : Scheme.{u}} (e : Z ≅ W) (z : Z)
    (hz : IsClosed ({z} : Set Z)) (hz' : IsClosed ({e.hom z} : Set W)) :
    ∃ d : AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)) ≅
        AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{e.hom z}, hz'⟩ : Closeds W)),
      d.hom ≫ AlgebraicGeometry.blowUpToBase _ = AlgebraicGeometry.blowUpToBase _ ≫ e.hom := by
  set J : W.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{e.hom z}, hz'⟩ : Closeds W) with hJ
  obtain ⟨_, hideal⟩ :=
    AlgebraicGeometry.vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom z) hz' z rfl
  have key : ∀ K : Z.IdealSheafData, K = J.comap e.hom →
      ∃ d : AlgebraicGeometry.blowUp K ≅ AlgebraicGeometry.blowUp J,
        d.hom ≫ AlgebraicGeometry.blowUpToBase J = AlgebraicGeometry.blowUpToBase K ≫ e.hom := by
    intro K hK
    cases hK
    exact AlgebraicGeometry.exists_blowUp_iso_comap_of_isIso e.hom J
  exact key _ hideal.symm

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **One blowing up of the `i`th neighbourhood at a point over `uᵢ` lifts to `A`.** If the base
change of `g : A ⟶ X` to the `i`th neighbourhood is represented by the scheme `Z` and `x` is a
closed point of `Z` over `uᵢ`, then there is a blowing up `g₁ : A' ⟶ A` at a closed point of `A`
over `xᵢ` such that the base change of `g₁ ≫ g` to the `i`th neighbourhood is represented by the
blowup of `Z` at `x`, while over every étale `P ⟶ X` none of whose points maps to `xᵢ` the base
change of `g₁ ≫ g` is that of `g`; and `A'` is again locally Noetherian. -/
theorem exists_lift_isBlowupAtClosedPoint (i : Fin n) {A : AlgebraicSpaces B S hS}
    (g : A ⟶ D.space)
    (hAnoeth : HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {Z : Over (D.neighborhoodScheme i)} (hZ : D.StageRep i g Z) (x : Z.left)
    (hx : IsClosed ({x} : Set Z.left)) (hxu : Z.hom x = (D.neighborhood i).point) :
    ∃ (A' : AlgebraicSpaces B S hS) (g₁ : A' ⟶ A) (z : points B S hS A.obj)
      (hz : IsClosed ({z} : Set (points B S hS A.obj))),
      IsBlowupAtClosedPoint B S hS z hz g₁ ∧ pointsMap B S hS A.obj g.hom z = D.point i ∧
        HasEtaleLocalProperty B S hS A'.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
        D.StageRep i (g₁ ≫ g) (Over.mk (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds Z.left)) ≫ Z.hom)) ∧
        ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
          (c : P ⟶ D.space.obj), IsEtale B S hS c →
            (∀ p, pointsMap B S hS P c p ≠ D.point i) →
            ∃ e : pullback (g₁.hom ≫ g.hom) c ≅ pullback g.hom c,
              e.hom ≫ pullback.snd g.hom c = pullback.snd (g₁.hom ≫ g.hom) c := by
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hZ
  set φ := D.toSpaceHom i
  -- the point of `W` corresponding to the centre
  obtain ⟨w, rfl⟩ : ∃ w, θ.hom w = x := ⟨θ.inv x, by simp⟩
  have hw : IsClosed ({w} : Set ((BigFppfOver.toScheme B S hS).obj W)) := by
    have h := θ.inv.isClosedEmbedding.isClosedMap _ hx
    have hww : θ.inv (θ.hom w) = w := by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    rwa [Set.image_singleton, hww] at h
  have hWv : (BigFppfOver.toScheme B S hS).map q w = (D.neighborhood i).point := by
    rw [← hθ, Scheme.Hom.comp_apply]
    exact hxu
  -- the corresponding point of the base change and of `A`
  set t := pointsMap B S hS _ Φ.inv (schemeSpacePoint W w) with htdef
  have ht : IsClosed ({t} : Set (points B S hS (pullback g.hom φ.hom))) := by
    have hpre : ({t} : Set (points B S hS (pullback g.hom φ.hom))) =
        pointsMap B S hS _ Φ.hom ⁻¹' {schemeSpacePoint W w} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rw [htdef, ← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id]
        rfl
      · intro hy
        rw [htdef, ← hy, ← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id]
        rfl
    rw [hpre]
    exact (isClosed_singleton_schemeSpacePoint W hw).preimage (continuous_pointsMap B S hS Φ.hom)
  have htv : pointsMap B S hS _ (pullback.snd g.hom φ.hom) t = D.neighborhoodPoint i := by
    have hcomp : Φ.inv ≫ pullback.snd g.hom φ.hom = yoneda.map q :=
      (congrArg (Φ.inv ≫ ·) hΦ).symm.trans (Iso.inv_hom_id_assoc Φ _)
    have h1 : pointsMap B S hS (yoneda.obj W) (yoneda.map q) (schemeSpacePoint W w) =
        schemeSpacePoint _ ((BigFppfOver.toScheme B S hS).map q w) := by
      have := congrFun (pointsMap_yoneda_map_eq B S hS q) (schemeSpacePoint W w)
      simpa using this
    rw [htdef, ← pointsMap_comp_apply, hcomp]
    exact h1.trans (by rw [hWv, D.neighborhoodPoint_eq_schemeSpacePoint])
  have htx : pointsMap B S hS A.obj g.hom
      (pointsMap B S hS _ (pullback.fst g.hom φ.hom) t) = D.point i := by
    rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply, htv]
    exact D.pointsMap_toSpaceHom_neighborhoodPoint i
  set z := pointsMap B S hS _ (pullback.fst g.hom φ.hom) t with hzdef
  have hz : IsClosed ({z} : Set (points B S hS A.obj)) :=
    isClosed_singleton_pointsMap_fst_of_isIso_fromPreimage (D.neighborhoodSpace i).property
      D.space.property A.property φ.hom (D.neighborhood i).etale_toSpace g.hom
      (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i)
      (D.range_pointsMap_ι_pointSubspace i) (D.isClosed_point i) ht htx
  -- the blowing up of `A` at `z`
  obtain ⟨A', b, hb, -⟩ :=
    exists_isBlowupAlong_of_isLocallyNoetherian hAnoeth (closedPointSubspace B S hS z hz)
  have hg₁ : IsBlowupAtClosedPoint B S hS z hz b := isBlowupAtClosedPoint_of_isBlowupAlong hb
  have hWnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) := by
    exact (exists_atlas_iff_forall_etale B S hS A.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) A.property).mp hAnoeth W
      (Φ.inv ≫ pullback.fst g.hom φ.hom)
      (presheaf_etale_of_isEtale B S hS (isEtale_inv_comp_pullback_fst g
        (D.neighborhoodSpace i).property φ.hom (D.neighborhood i).etale_toSpace Φ))
  refine ⟨A', b, z, hz, hg₁, htx, hasEtaleLocalProperty_isLocallyNoetherian_of_isBlowupAlong
    hAnoeth hb, ?_, ?_⟩
  · -- the base change to the `i`th neighbourhood
    have hfib : pointsMap B S hS _ (Φ.inv ≫ pullback.fst g.hom φ.hom) ⁻¹' {z} =
        {schemeSpacePoint W w} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, pointsMap_comp_apply]
      constructor
      · intro hy
        have h1 := pointsMap_fst_injOn_of_isIso_fromPreimage φ.hom g.hom (D.pointSubspace i)
          (D.isIso_fromPreimage_pointSubspace i) (D.range_pointsMap_ι_pointSubspace i)
          htx hy.symm
        have h2 := congrArg (pointsMap B S hS _ Φ.hom) h1
        rw [htdef, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Iso.inv_hom_id,
          pointsMap_id] at h2
        exact h2.symm
      · intro hy
        rw [hy]
    obtain ⟨N, q', e', ψ, he', hq'⟩ := exists_iso_pullback_comp_blowUp g hg₁ φ.hom
      (D.neighborhood i).etale_toSpace q Φ hΦ hw hfib
    obtain ⟨m, hm⟩ := exists_blowUp_vanishingIdeal_iso_of_iso θ w hw hx
    refine ⟨N, q' ≫ q, e', ψ ≪≫ m, ?_, ?_⟩
    · show e'.hom ≫ yoneda.map (q' ≫ q) = pullback.snd (b.hom ≫ g.hom) φ.hom
      exact he'
    · simp only [Iso.trans_hom, Category.assoc, Functor.map_comp, Over.mk_hom]
      rw [← Category.assoc m.hom, hm, Category.assoc, hθ, ← Category.assoc, hq']
  · intro P hP c hc hcx
    refine exists_iso_pullback_comp_of_isBlowupAtClosedPoint g hg₁ hP c hc
      fun p hp => hcx (pointsMap B S hS _ (pullback.snd g.hom c) p) ?_
    rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, hp, hzdef, htx]

/-- **The lifting of a sequence of blowups of the `i`th neighbourhood at closed points over
`uᵢ`.** Starting from `g₀ : A₀ ⟶ X`, a sequence of blowings up at closed points over
`{x₁, …, xₙ}` with locally Noetherian source whose base change to the `i`th neighbourhood is the
neighbourhood itself, a sequence of blowups of the neighbourhood at closed points over `uᵢ`
ending in `f : Y ⟶ Uᵢ` lifts to such a `g : A ⟶ X` whose base change to the `i`th neighbourhood is
`f` and whose base change to every étale `P ⟶ X` missing `xᵢ` is that of `g₀`. -/
theorem exists_lift_pointBlowupChain (i : Fin n) {A₀ : AlgebraicSpaces B S hS}
    {g₀ : A₀ ⟶ D.space}
    (hA₀ : HasEtaleLocalProperty B S hS A₀.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hF₀ : Nonempty (BlowupFactorization B S hS (Set.range D.point) g₀))
    (hrep : D.StageRep i g₀ (Over.mk (𝟙 _))) {Y : Scheme.{u}} {f : Y ⟶ D.neighborhoodScheme i}
    (hchain : Stacks.ResolutionOfSurfaces.PointBlowupChain (D.neighborhoodScheme i)
      {(D.neighborhood i).point} Y f) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space),
      HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
      Nonempty (BlowupFactorization B S hS (Set.range D.point) g) ∧ D.StageRep i g (Over.mk f) ∧
        ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
          (c : P ⟶ D.space.obj), IsEtale B S hS c →
            (∀ p, pointsMap B S hS P c p ≠ D.point i) →
            ∃ e : pullback g.hom c ≅ pullback g₀.hom c,
              e.hom ≫ pullback.snd g₀.hom c = pullback.snd g.hom c := by
  induction hchain with
  | refl =>
    exact ⟨A₀, g₀, hA₀, hF₀, hrep, fun _ c _ _ => ⟨Iso.refl _, Category.id_comp _⟩⟩
  | @step W h hh w hw hwT ih =>
    obtain ⟨A, g, hAn, ⟨F⟩, hArep, hApres⟩ := ih
    obtain ⟨A', g₁, z, hz, hg₁, hzx, hA'n, hrep', hpres'⟩ :=
      D.exists_lift_isBlowupAtClosedPoint i g hAn (Z := Over.mk h) hArep w hw hwT
    refine ⟨A', g₁ ≫ g, hA'n, ⟨F.comp (BlowupFactorization.ofBlowup _ hg₁ ⟨i, hzx.symm⟩)⟩,
      hrep', ?_⟩
    intro P hP c hc hcx
    obtain ⟨e₁, he₁⟩ := hpres' hP c hc hcx
    obtain ⟨e₂, he₂⟩ := hApres hP c hc hcx
    exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]; rfl⟩

/-- **The lifting of sequences of blowups of all the neighbourhoods.** Given, for each `i`, a
sequence of blowups `fᵢ : Yᵢ ⟶ Uᵢ` of the `i`th neighbourhood at closed points over `uᵢ`, there is
a sequence of blowings up `g : A ⟶ X` at closed points over `{x₁, …, xₙ}` whose base change to the
`i`th neighbourhood is `fᵢ` for every `i`, and which is an isomorphism over
`X ∖ {x₁, …, xₙ}`. This is the direction "from the `Uᵢ` to `X`" of Stacks 0BHF. -/
theorem exists_blowupFactorization_stageRep
    (hX : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {Y : Fin n → Scheme.{u}} (f : ∀ i, Y i ⟶ D.neighborhoodScheme i)
    (hf : ∀ i, Stacks.ResolutionOfSurfaces.PointBlowupChain (D.neighborhoodScheme i)
      {(D.neighborhood i).point} (Y i) (f i)) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space),
      Nonempty (BlowupFactorization B S hS (Set.range D.point) g) ∧
        (∀ i, D.StageRep i g (Over.mk (f i))) ∧
        IsIso (pullback.snd g.hom D.openAwayFromPoints.ι) := by
  classical
  have hidp : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : P ⟶ D.space.obj),
      IsIso (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom c) :=
    fun c => (IsPullback.of_hasPullback _ c).isIso_snd_of_isIso
  have hrep₀ : ∀ k, D.StageRep k (𝟙 D.space) (Over.mk (𝟙 _)) := fun k =>
    ⟨(D.neighborhood k).scheme, 𝟙 _, @asIso _ _ _ _
      (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom (D.toSpaceHom k).hom) (hidp _),
      Iso.refl _, by simp only [CategoryTheory.Functor.map_id, Category.comp_id]; rfl, by simp⟩
  have hNo := D.isOpenSubspace_openAwayFromPoints
  have claim : ∀ s : Finset (Fin n), ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space),
      HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
      Nonempty (BlowupFactorization B S hS (Set.range D.point) g) ∧
        (∀ k, D.StageRep k g (if k ∈ s then Over.mk (f k) else Over.mk (𝟙 _))) ∧
        IsIso (pullback.snd g.hom D.openAwayFromPoints.ι) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨_, 𝟙 D.space, hX, ⟨BlowupFactorization.ofIso _ (Iso.refl _)⟩,
        fun k => by simpa using hrep₀ k, hidp _⟩
    | @insert i s hi ih =>
      obtain ⟨A₀, g₀, hA₀, hF₀, hrep, hiso₀⟩ := ih
      have hrepi : D.StageRep i g₀ (Over.mk (𝟙 _)) := by simpa [hi] using hrep i
      obtain ⟨A, g, hA, hF, hrepi', hpres⟩ :=
        D.exists_lift_pointBlowupChain i hA₀ hF₀ hrepi (hf i)
      refine ⟨A, g, hA, hF, fun k => ?_, ?_⟩
      · by_cases hk : k = i
        · subst hk
          simpa using hrepi'
        · obtain ⟨e, he⟩ := hpres (D.neighborhoodSpace k).property (D.toSpaceHom k).hom
            (D.neighborhood k).etale_toSpace (fun p hp => D.map_ne_point k i hk p hp)
          have h := D.stageRep_of_iso k e he (hrep k)
          simpa [Finset.mem_insert, hk] using h
      · obtain ⟨e, he⟩ := hpres hNo.1 D.openAwayFromPoints.ι (isEtale_ι_of_isOpenSubspace hNo)
          (by
            intro p hp
            have hmem : D.point i ∈ Set.range
                (pointsMap B S hS _ D.openAwayFromPoints.ι) := ⟨p, hp⟩
            rw [D.range_pointsMap_ι_openAwayFromPoints] at hmem
            exact hmem ⟨i, rfl⟩)
        rw [← he]
        infer_instance
  obtain ⟨A, g, -, hF, hrep, hiso⟩ := claim Finset.univ
  exact ⟨A, g, hF, fun k => by simpa using hrep k, hiso⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
