module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.TrivialOfFreeStalk
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowUpLocalTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FlatCoverCriteria
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.PushforwardTrivialOffCentre

/-!
# A module on the blowup of a closed point which is trivial off the centre and near it

Let `W` be a locally Noetherian normal scheme, `w ∈ W` a closed point with `dim 𝒪_{W,w} ≥ 2`, `I`
an ideal sheaf with support `{w}` and `b : W' ⟶ W` the blowup in `I`, with `𝒪_W = b_*𝒪_{W'}`. Let
`A ≅ 𝒪_{W,w}` and `h : Bl(A) ⟶ W'` the base change of `b` along `Spec A ⟶ W`. A quasi-coherent
`𝒪_{W'}`-module `L` which is trivial over `b⁻¹(W ∖ {w})` and whose pullback along `h` is trivial
is trivial: the counit `b^*b_*L ⟶ L` is an isomorphism (flat base change of the counit along the
two flat morphisms, whose images cover `W'`), and `b_*L ≅ 𝒪_W` by Hartogs' extension, `b_*L`
being trivial off `w` with stalk at `w` free of rank one (flat base change of `b_*`). This is the
last step of the stage lemma in the proof of the second sentence of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.exists_of_isPullback`: points of a cartesian square.
* `AlgebraicGeometry.DualizingDivisor.nonempty_iso_unit_of_pullback_iso_of_blowUp`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.DualizingDivisor

/-- **Points of a cartesian square of schemes**: two points with the same image have a common
preimage. -/
theorem exists_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (H : IsPullback fst snd f g) (x : X) (y : Y) (h : f x = g y) :
    ∃ p, fst p = x ∧ snd p = y := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨H.isoPullback.inv z, ?_, ?_⟩
  · rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  · rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]

open BlowUpDualizing

variable {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W] {w : W}
  (I : W.IdealSheafData) (hI : (I.support : Set W) = {w})
  (hO : IsIso (blowUpToBase I).toLRSHom.toHom.c)
  (A : Type u) [CommRing A] [IsLocalRing A] (hA : ringKrullDim A = 2)
  (e : A ≃+* W.presheaf.stalk w) (h : blowUpScheme A ⟶ blowUp I)
  (sq : IsPullback (blowUpToBase (centre A)) h (specToOfRingEquivStalk A w e) (blowUpToBase I))
  [Flat h] [QuasiCompact (blowUpToBase I)] [QuasiSeparated (blowUpToBase I)]

/-- A point outside the open complement of the support of `J` is the closed point `v`. -/
private theorem eq_of_notMem_compl_support {V : Scheme.{u}} {J : V.IdealSheafData} {v : V}
    (hJ : (J.support : Set V) = {v}) {x : V} (hx : x ∉ J.support.compl) : x = v := by
  have : x ∈ (J.support : Set V) := by
    by_contra hn
    exact hx hn
  rwa [hJ] at this

include hI sq in
/-- The open `b⁻¹(W ∖ {w})` and the image of `h` cover the blowup. -/
theorem mem_range_or_mem_range_of_isPullback (x : blowUp I) :
    x ∈ Set.range (blowUpToBase I ⁻¹ᵁ I.support.compl).ι ∨ x ∈ Set.range h := by
  by_cases hx : blowUpToBase I x ∈ I.support.compl
  · left
    rwa [Scheme.Opens.range_ι]
  · right
    obtain ⟨p, -, hp⟩ := exists_of_isPullback sq _ x
      ((specToOfRingEquivStalk_closedPoint A w e).trans (eq_of_notMem_compl_support hI hx).symm)
    exact ⟨p, hp⟩

include hI hO hA sq in
/-- **A module on the blowup of a closed point, trivial off the centre and after base change to
the local ring at the point, is trivial.** -/
theorem nonempty_iso_unit_of_pullback_iso_of_blowUp (L : (blowUp I).Modules)
    [L.IsQuasicoherent]
    (eU : (Scheme.Modules.pullback (blowUpToBase I ⁻¹ᵁ I.support.compl).ι).obj L ≅
      SheafOfModules.unit _)
    (eh : (Scheme.Modules.pullback h).obj L ≅ SheafOfModules.unit _) :
    Nonempty (L ≅ SheafOfModules.unit (blowUp I).ringCatSheaf) := by
  classical
  set b := blowUpToBase I
  set U : W.Opens := I.support.compl
  have hunit := VectorBundleCodimensionOne.isIso_unit_app_unit_of_isIso_c b hO
  have sqU : IsPullback (b ⁻¹ᵁ U).ι (b ∣_ U) b U.ι := (isPullback_morphismRestrict b U).flip
  have hunitU := VectorBundleCodimensionOne.isIso_unit_app_unit_of_isPullback sqU hunit
  have hunitA := VectorBundleCodimensionOne.isIso_unit_app_unit_of_isPullback sq.flip hunit
  let fr : ∀ (Z : Scheme.{u}), SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.free PUnit :=
    fun Z =>
      (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit Z.ringCatSheaf)).symm
  let g := specToOfRingEquivStalk A w e
  have hfac : W.fromSpecStalk w =
      Spec.map (CommRingCat.ofHom (e : A →+* W.presheaf.stalk w)) ≫ g := by
    show _ = Spec.map _ ≫ (Spec.map _ ≫ W.fromSpecStalk w)
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.comp_symm,
      CommRingCat.ofHom_id]
    exact (Category.id_comp _).symm.trans
      (congrArg (· ≫ W.fromSpecStalk w) (Spec.map_id (W.presheaf.stalk w)).symm)
  let ε := (Scheme.Modules.pullbackPushforwardAdjunction b).counit.app L
  have hε : IsIso ε := isIso_of_isIso_pullback_map_of_cover (b ⁻¹ᵁ U).ι h
    (mem_range_or_mem_range_of_isPullback I hI A e h sq) ε
    (VectorBundleCodimensionOne.isIso_pullback_map_counit_of_isPullback sqU L
      (VectorBundleCodimensionOne.isIso_counit_app_of_iso_free (b ∣_ U) hunitU _ PUnit
        (eU ≪≫ fr _)))
    (VectorBundleCodimensionOne.isIso_pullback_map_counit_of_isPullback sq.flip L
      (VectorBundleCodimensionOne.isIso_counit_app_of_iso_free _ hunitA _ PUnit (eh ≪≫ fr _)))
  let M := (Scheme.Modules.pushforward b).obj L
  have : M.IsQuasicoherent := ProperCoherentFiniteType.isQuasicoherent_pushforward b L ‹_›
  obtain ⟨eMU⟩ := nonempty_pullback_pushforward_iso_unit b U L
    (eU ≪≫ (Scheme.Modules.pullbackUnitIso _).symm)
  let bA := blowUpToBase (centre A)
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    sq.flip L
  let eg : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit _ :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.flip.w).app L) ≪≫
      (Scheme.Modules.pushforward bA).mapIso (eh ≪≫ (Scheme.Modules.pullbackUnitIso bA).symm) ≪≫
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction bA).unit.app
        (SheafOfModules.unit _))).symm
  let eφ : (Scheme.Modules.pullback (W.fromSpecStalk w)).obj M ≅ SheafOfModules.unit _ :=
    (Scheme.Modules.pullbackCongr hfac).app M ≪≫
      ((Scheme.Modules.pullbackComp _ g).app M).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eg ≪≫ Scheme.Modules.pullbackUnitIso _
  obtain ⟨ew⟩ := nonempty_stalk_linearEquiv_of_pullback_fromSpecStalk_iso M w eφ
  have hdim : (2 : ℕ∞) ≤ ringKrullDim (W.presheaf.stalk w) := by
    rw [← ringKrullDim_eq_of_ringEquiv e, hA]
    rfl
  obtain ⟨eM⟩ := nonempty_iso_unit_of_pullback_iso_of_stalk M U w
    (fun _ hx => eq_of_notMem_compl_support hI hx) hdim eMU ⟨ew⟩
  exact ⟨(asIso ε).symm ≪≫ (Scheme.Modules.pullback b).mapIso eM ≪≫
    Scheme.Modules.pullbackUnitIso b⟩

end AlgebraicGeometry.DualizingDivisor

end
