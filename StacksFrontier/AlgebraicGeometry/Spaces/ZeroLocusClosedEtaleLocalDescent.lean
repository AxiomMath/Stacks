module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartZeroLocusEndgame
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent

/-!
# Closedness of the vanishing subfunctor is étale local on the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `u : ℱ ⟶ 𝒢` be a
map of quasi-coherent `𝒪_X`-modules, as in Stacks 083F.  Its vanishing locus
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` is a subfunctor of `Y`.  If every
point of `Y` has an étale neighbourhood `Y' ⟶ Y` over which the vanishing subfunctor of the
base-changed situation is a closed subspace, then the vanishing subfunctor of `Y` is a closed
subspace of `Y`.  Together with a dévissage this gives the closed-immersion clause of
Stacks 0CWC.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_zeroSubfunctor`: the vanishing subfunctor
  is a sheaf for the big fppf topology.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor_baseChangeTarget`: the vanishing
  subfunctor of the situation base changed along `b : Y' ⟶ Y` is the preimage of the
  vanishing subfunctor along `b`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_etaleLocalOnBase`:
  closedness of the vanishing subfunctor is étale local on the base.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusClosedEtaleLocalOnBase`: the predicate
  `AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusClosedEtaleLocalOnBase` holds.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor`: the
  closed-immersion clause of Stacks 0CWC, given a dévissage and the étale-local descent.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_devissage`: the
  closed-immersion clause of Stacks 0CWC, given a dévissage.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Restricting the test scheme a section names -/

/-- A morphism `q : c ⟶ a` of the site carries the test scheme named by a section of `Y` over
`a` to the test scheme named by its restriction along `q`. -/
def zeroTestHom (D : ModuleMapSituation.{u, u} B S hS) {a c : BigFppfOver B S hS} (q : c ⟶ a)
    (s : D.Y.1.obj (op a)) :
    D.zeroTest c (D.Y.1.map q.op s) ⟶ D.zeroTest a s :=
  CostructuredArrow.homMk q (by
    apply ObjectProperty.hom_ext
    change yoneda.map q ≫ yonedaEquiv.symm s = yonedaEquiv.symm (D.Y.1.map q.op s)
    apply yonedaEquiv.injective
    simpa using (yonedaEquiv_naturality (yonedaEquiv.symm s) q).symm)

/-- The underlying morphism of `zeroTestHom q s` is `q`. -/
@[simp]
theorem zeroTestHom_left (D : ModuleMapSituation.{u, u} B S hS) {a c : BigFppfOver B S hS}
    (q : c ⟶ a) (s : D.Y.1.obj (op a)) : (D.zeroTestHom q s).left = q :=
  rfl

/-! ### The vanishing subfunctor is a sheaf -/

/-- **Vanishing at a test scheme is local on the big fppf site.**  If the arrows of the site
along which the base change of `u` vanishes at the restricted test scheme form a covering sieve,
then the base change of `u` vanishes at the test scheme itself. -/
theorem isZeroAt_zeroTest_of_sieveOfSection_mem (D : ModuleMapSituation.{u, u} B S hS)
    {a : BigFppfOver B S hS} (s : D.Y.1.obj (op a))
    (hs : D.zeroSubfunctor.sieveOfSection s ∈ BigFppfOver.topology B S hS a) :
    D.IsZeroAt (modulePullbackSystem B S hS) (D.zeroTest a s) := by
  classical
  choose c q hq hflat hlfp hx using fun x : (BigFppfOver.toScheme B S hS).obj a =>
    BigFppfOver.exists_mem_of_mem_topology B S hS hs x
  set T : D.SchemesOver := D.zeroTest a s with hT
  set T' : (BigFppfOver.toScheme B S hS).obj a → D.SchemesOver :=
    fun x => D.zeroTest (c x) (D.Y.1.map (q x).op s) with hT'
  set g : ∀ x, T' x ⟶ T := fun x => D.zeroTestHom (q x) s with hg
  have hpre : Presieve.ofArrows T' g ∈
      (Scheme.fpqcPrecoverage.comap (testSchemeFunctor D.Y)).coverings T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ?_
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x => ⟨x, hx x⟩, fun x => ⟨hflat x, hlfp x⟩⟩
  have hsieve : Sieve.generate (Presieve.ofArrows T' g) ∈ fpqcTopology D.Y T :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsub : ∀ W : (D.SchemesOver)ᵒᵖ,
      Subsingleton ((D.zeroFunctor (modulePullbackSystem B S hS)).obj W) :=
    fun W => D.zeroFunctor_obj_subsingleton (modulePullbackSystem B S hS) W.unop
  refine (D.nonempty_zeroFunctor_obj_iff (modulePullbackSystem B S hS) T).1
    ((Presheaf.isSheaf_iff_nonempty_of_subsingleton _ _).1
      D.isSheaf_zeroFunctor T _ hsieve ?_)
  rintro T'' k ⟨Z, k₁, k₂, ⟨x⟩, rfl⟩
  refine (D.nonempty_zeroFunctor_obj_iff (modulePullbackSystem B S hS) T'').2 ?_
  exact D.isZeroAt_of_hom (modulePullbackSystem B S hS) k₁ (hq x)

/-- **The vanishing subfunctor of the base is a sheaf for the big fppf topology.** -/
theorem isSheaf_zeroSubfunctor (D : ModuleMapSituation.{u, u} B S hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.zeroSubfunctor.toFunctor := by
  have hY := (isSheaf_iff_isSheaf_of_type _ _).1 D.Y.2.isSheaf
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hY]
  intro U s hU
  exact D.isZeroAt_zeroTest_of_sieveOfSection_mem s hU

/-! ### The vanishing subfunctor under base change of the target -/

/-- For `b : Y' ⟶ Y`, a section `x` of `Y'` lies in the vanishing subfunctor of
`D.baseChangeTarget b` if and only if its image under `b` lies in the vanishing subfunctor of
`Y`. -/
theorem mem_zeroSubfunctor_baseChangeTarget_iff (D : ModuleMapSituation.{u, u} B S hS)
    {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ D.Y) (a : BigFppfOver B S hS)
    (x : Y'.1.obj (op a)) :
    x ∈ (D.baseChangeTarget b).zeroSubfunctor.obj (op a) ↔
      b.hom.app (op a) x ∈ D.zeroSubfunctor.obj (op a) := by
  have hhom : ((D.baseChangeTarget b).zeroTest a x).hom ≫ b =
      (D.zeroTest a (b.hom.app (op a) x)).hom := by
    apply ObjectProperty.hom_ext
    change yonedaEquiv.symm x ≫ b.hom = yonedaEquiv.symm (b.hom.app (op a) x)
    apply yonedaEquiv.injective
    simp [yonedaEquiv_comp]
  have hobj : (D.overTarget b).obj ((D.baseChangeTarget b).zeroTest a x) =
      D.zeroTest a (b.hom.app (op a) x) :=
    congrArg CostructuredArrow.mk hhom
  rw [mem_zeroSubfunctor_iff, mem_zeroSubfunctor_iff,
    D.isZeroAt_baseChangeTarget_iff b ((D.baseChangeTarget b).zeroTest a x), hobj]

/-- **The vanishing subfunctor of the base-changed situation is the preimage of the vanishing
subfunctor.**  For `b : Y' ⟶ Y` the vanishing subfunctor of `D.baseChangeTarget b`, a subfunctor
of `Y'`, is the preimage along `b` of the vanishing subfunctor of `Y`. -/
theorem zeroSubfunctor_baseChangeTarget (D : ModuleMapSituation.{u, u} B S hS)
    {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ D.Y) :
    (D.baseChangeTarget b).zeroSubfunctor = D.zeroSubfunctor.preimage b.hom := by
  ext U x
  obtain ⟨a⟩ := U
  rw [Subfunctor.preimage_obj, Set.mem_preimage]
  exact D.mem_zeroSubfunctor_baseChangeTarget_iff b a x

/-! ### The descent step -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_zeroLocusClosedEtaleLocalDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_zeroLocusClosedEtaleLocalDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Being represented by a morphism of the site with `Q` is read off the base change along any
one of two equal morphisms. -/
private theorem presheaf_pullback_snd_congr {Q : MorphismProperty Scheme.{u}}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {g g' : Z ⟶ Y} (hg : g = g')
    (h : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g') := by
  subst hg
  exact h

/-- A base change of a morphism of presheaves which is itself representable with `Q` passes `Q`
on to the base change along a morphism out of a representable which factors through it. -/
private theorem presheaf_pullback_snd_of_factor {Q : MorphismProperty Scheme.{u}}
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {m : Z ⟶ W} {w : W ⟶ Y}
    {t : Z ⟶ X} (sq : IsPullback t m f w) {a : BigFppfOver B S hS} (k : yoneda.obj a ⟶ W)
    (hm : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf m) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (k ≫ w)) := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (Q.inverseImage (BigFppfOver.toScheme B S hS)) (F := yoneda (C := BigFppfOver B S hS))
  have _hri : MorphismProperty.RespectsIso
      ((Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf) := hbc.respectsIso
  have h1 : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd m k) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback m k) hm
  have sqA : IsPullback (pullback.fst m k ≫ t) (pullback.snd m k) f (k ≫ w) :=
    (IsPullback.of_hasPullback m k).paste_horiz sq
  have he : (sqA.isoIsPullback _ _ (IsPullback.of_hasPullback f (k ≫ w))).hom ≫
      pullback.snd f (k ≫ w) = pullback.snd m k :=
    sqA.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f (k ≫ w))
  rw [← he] at h1
  exact (MorphismProperty.cancel_left_of_respectsIso _
    (sqA.isoIsPullback _ _ (IsPullback.of_hasPullback f (k ≫ w))).hom _).mp h1

/-- **Closedness of the vanishing subfunctor is étale local on the base.**  If every point of
the base `Y` has an étale neighbourhood `b : Y' ⟶ Y` over which the vanishing subfunctor of the
base-changed situation is a closed subspace of `Y'`, then the vanishing subfunctor of `Y` is a
closed subspace of `Y`. -/
theorem isClosedSubspace_zeroSubfunctor_of_etaleLocalOnBase
    (D : ModuleMapSituation.{u, u} B S hS)
    (hloc : ∀ y : points B S hS D.Y.1,
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ D.Y),
        IsEtale B S hS b.hom ∧
        y ∈ Set.range (pointsMap B S hS Y'.1 b.hom) ∧
        IsClosedSubspace B S hS (D.baseChangeTarget b).zeroSubfunctor) :
    IsClosedSubspace B S hS D.zeroSubfunctor := by
  classical
  have hci : IsClosedImmersion B S hS D.zeroSubfunctor.ι := by
    have _hri : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ _
    refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _
      D.zeroSubfunctor.ι).2 ?_
    intro a h
    have step : ∀ x : (BigFppfOver.toScheme B S hS).obj a,
        ∃ (Zx : BigFppfOver B S hS) (qx : Zx ⟶ a) (kx : yoneda.obj Zx ⟶ D.Y.1),
          _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map qx) ∧
          x ∈ Set.range ((BigFppfOver.toScheme B S hS).map qx).base ∧
          yoneda.map qx ≫ h = kx ∧
          ∀ {b' : BigFppfOver B S hS} (e : b' ⟶ Zx),
            IsClosedImmersion B S hS
              (pullback.snd D.zeroSubfunctor.ι (yoneda.map e ≫ kx)) := by
      intro x
      obtain ⟨Y', b, hbet, hyb, hbclosed⟩ :=
        hloc (pointsMap B S hS (yoneda.obj a) h ((pointsEquivScheme B S hS a).symm x))
      obtain ⟨W, p, hpsurj, hpet⟩ := Y'.2.exists_atlas
      have hket : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (p ≫ b.hom) := hbet W p hpet
      refine ⟨hket.rep.pullback h, hket.rep.snd h,
        hket.rep.fst h ≫ p ≫ b.hom, hket.property_snd h, ?_, ?_, ?_⟩
      · obtain ⟨z, hz⟩ := hyb
        obtain ⟨α, hα⟩ := (surjective_iff_surjective_pointsMap B S hS Y'.1 Y'.2 W p).1 hpsurj z
        have hcompat : pointsMap B S hS (yoneda.obj W) (p ≫ b.hom) α =
            pointsMap B S hS (yoneda.obj a) h ((pointsEquivScheme B S hS a).symm x) := by
          rw [pointsMap_comp, Function.comp_apply, hα, hz]
        obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS (hket.rep.isPullback h) α
          ((pointsEquivScheme B S hS a).symm x) hcompat
        have hinv : pointsToScheme B S hS a ((pointsEquivScheme B S hS a).symm x) = x :=
          (pointsEquivScheme B S hS a).apply_symm_apply x
        have hts := pointsToScheme_pointsMap_yoneda B S hS (hket.rep.snd h) w
        rw [hw] at hts
        exact ⟨pointsToScheme B S hS (hket.rep.pullback h) w, hts.symm.trans hinv⟩
      · exact (hket.rep.isPullback h).w.symm
      · intro b' e
        have hpb := Subfunctor.isPullback_preimage b.hom D.zeroSubfunctor
        have hm : IsClosedImmersion B S hS (D.zeroSubfunctor.preimage b.hom).ι := by
          rw [← D.zeroSubfunctor_baseChangeTarget b]
          exact hbclosed.2
        refine presheaf_pullback_snd_congr D.zeroSubfunctor.ι (by simp)
          (presheaf_pullback_snd_of_factor hpb (yoneda.map e ≫ hket.rep.fst h ≫ p) hm)
    choose Zx qx kx hqet hqx hqfac hqclosed using step
    have hsieve : Sieve.ofArrows Zx qx ∈ BigFppfOver.topology B S hS a :=
      sieve_ofArrows_mem_topology_of_etale B hS Zx qx
        (fun t => by obtain ⟨z, hz⟩ := hqx t; exact ⟨t, z, hz⟩) hqet
    refine FormalSpace.isEffectiveDescentAlongCoveringSieve_isClosedImmersion B S hS
      D.zeroSubfunctor.ι D.isSheaf_zeroSubfunctor D.Y.2.isSheaf h _ hsieve ?_
    rintro b' q ⟨Z, e, q', ⟨x⟩, rfl⟩
    refine presheaf_pullback_snd_congr D.zeroSubfunctor.ι ?_ (hqclosed x e)
    rw [Functor.map_comp, Category.assoc, hqfac x]
  exact ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS D.zeroSubfunctor.ι hci.rep D.Y.2,
    hci⟩

/-- **Closedness of the vanishing subfunctor of Stacks 083F is étale local on the base**: the
predicate `AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusClosedEtaleLocalOnBase` holds. -/
theorem zeroLocusClosedEtaleLocalOnBase (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : ZeroLocusClosedEtaleLocalOnBase B S hS :=
  fun D hloc => D.isClosedSubspace_zeroSubfunctor_of_etaleLocalOnBase hloc

/-! ### Stacks 0CWC -/

/-- **Stacks 0CWC, the closed-immersion clause, given a dévissage and the étale-local
descent.**  In the situation of Stacks 083F, assume that `f` is of finite presentation and that
`𝒢` is of finite presentation, flat over `Y`, and pure relative to `Y`.  Given the dévissage
`hdev` and the étale-local descent `hdesc`, the vanishing subfunctor
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` is a closed subspace of `Y`; by
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_exists_factor_zeroSubfunctor` it
represents `F_zero`. -/
theorem isClosedSubspace_zeroSubfunctor (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y))
    (hdev : DevissageInput B S hS)
    (hdesc : ZeroLocusClosedEtaleLocalOnBase B S hS) :
    IsClosedSubspace B S hS D.zeroSubfunctor := by
  have h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS :=
    weaklyAssociatedSubsetRelativeInput B S hS
  refine hdesc D fun y => ?_
  obtain ⟨V, b, hVaff, hbet, hy, W, g, hF, hG, α, hWaff, hgflat, htri, hGass, hproj⟩ :=
    hdev D hf hGfp hGflat hft hdec hGft hpure y
  have hGft' : SheafOfModules.IsFiniteTypeOnSite (D.baseChangeTarget b).G :=
    isFiniteTypeOnSite_modulePullback B S hS (D.baseChangeTargetProjection b) D.G hGft
  have :
      ((modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.G).IsQuasicoherentOnSite :=
    D.isQuasicoherentOnSite_baseChangeTargetG b
  have hGflat' : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS
      (D.baseChangeTarget b).X.2 (D.baseChangeTarget b).f.hom (D.baseChangeTarget b).G :=
    isFlatOver_modulePullback B S hS (D.isPullback_baseChangeTargetSpace b) D.G hGflat
  have hflt' : IsLocallyOfFiniteType B S hS (D.baseChangeTarget b).f.hom :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (D.isPullback_baseChangeTargetSpace b) hft.1
  have hfqs' : IsQuasiSeparated B S hS (D.baseChangeTarget b).f.hom :=
    (isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback
      (D.isPullback_baseChangeTargetSpace b) hf.2.2
  have hgqc : IsQuasiCompact B S hS g.hom :=
    isQuasiCompact_of_comp_eq_schemeSpaceMap B S hS hVaff hWaff g (D.baseChangeTarget b).f
      hfqs' α htri
  have hgqs : IsQuasiSeparated B S hS g.hom :=
    isQuasiSeparated_of_comp_eq_schemeSpaceMap B S hS hVaff hWaff g (D.baseChangeTarget b).f
      α htri
  refine ⟨schemeSpace V, b, hbet, hy, ?_⟩
  rw [zeroSubfunctor_pullbackSituation_eq_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs
      (D.baseChangeTarget b) g hF hG h0CVL hgflat hgqc hgqs hflt' hGft' hGflat' hGass]
  exact affineChartZeroLocusClosed B S hS (D.baseChangeTarget b) V W hVaff hWaff rfl g hF hG α
    hgflat hGft' hGflat' (by simpa using htri) hproj

/-- **Stacks 0CWC, the closed-immersion clause, given a dévissage.**  In the situation of
Stacks 083F, assume that `f` is of finite presentation and that `𝒢` is of finite presentation,
flat over `Y`, and pure relative to `Y`.  Given the dévissage `hdev`, the vanishing subfunctor
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` is a closed subspace of `Y`. -/
theorem isClosedSubspace_zeroSubfunctor_of_devissage (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y))
    (hdev : DevissageInput B S hS) :
    IsClosedSubspace B S hS D.zeroSubfunctor :=
  D.isClosedSubspace_zeroSubfunctor hf hGfp hGft hGflat hft hdec hpure hdev
    (zeroLocusClosedEtaleLocalOnBase B S hS)

end ModuleMapSituation

end AlgebraicGeometry.Space

end

