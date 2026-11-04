module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusClosed0BF0
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# Locality of the descent condition

Let `f : X ⟶ S` be a morphism of schemes and `E` a sheaf of modules on `X`. The descent
condition `AlgebraicGeometry.DescendsFromBase f E g` asks that the pullback of `E` to the base
change `X ×_S T` along `g : T ⟶ S` come from a finite locally free module on `T`. This file
proves the formal properties of that condition which make it a candidate for representability by
a subscheme of `S`, as in [Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP): it is
stable under precomposition, independent of the chosen fibre product, trivialised over an affine
open cover of `T`, and — for `f` flat and proper with `𝒪 = f_*𝒪` universally and `E` finite
locally free — local on `T`.

## Main results

* `AlgebraicGeometry.DescendsFromBase.precomp`: the condition is stable under precomposition.
* `AlgebraicGeometry.descendsFromBase_iff_of_isPullback`: the condition may be read off any
  cartesian square, not only Mathlib's chosen pullback.
* `AlgebraicGeometry.DescendsFromBase.exists_affine_cover_iso_free`: when the condition holds,
  the pulled-back module is free of finite rank over the members of an affine open cover of `T`.
* `AlgebraicGeometry.descendsFromBase_of_iSup_eq_top`: the condition is local on `T`.
* `AlgebraicGeometry.exists_pullback_iso_of_comp_eq`: the condition transported along a map of
  squares, from which the first two results follow.
* `AlgebraicGeometry.exists_affine_cover_pullback_iso_free`: a finite locally free module on a
  scheme is free of finite rank over the members of an affine open cover.
* `AlgebraicGeometry.isIso_stalk_counit_of_iso_free`: the counit of the projection of a base
  change is invertible on the stalks over a flat chart on which the module is free.

## Implementation notes

Locality is proved through the counit `ε : p^* p_* F ⟶ F` of the adjunction for the projection
`p : X ×_S T ⟶ T`, where `F` is the pullback of `E`. Over an open `W` of `T` on which `F` is free
of finite rank, the base change of `ε` to `X ×_S W` is the counit of the base-changed family at a
free module of finite rank, invertible because `𝒪_W = p_*𝒪` there; flat base change in degree
zero identifies the two, so `ε` is invertible on the stalks over `W`. Once `ε` is invertible, `F`
is the pullback of `p_* F`, which is finite locally free by fpqc descent along the flat
surjection `p`; surjectivity of `p` comes from `𝒪_T = p_*𝒪` and properness.

All manipulations of pullbacks are made with `AlgebraicGeometry.Scheme.Modules.pullback`, which
is the functor `RingedSpaceModuleAdjunction.modulePullback` of the statements by definition.

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- The pullback of a free sheaf of modules along a morphism of schemes is the free sheaf on the
same index type. -/
noncomputable def schemeModulesPullbackObjFreeIso {Y Z : Scheme.{u}} (a : Y ⟶ Z) (I : Type u) :
    (Scheme.Modules.pullback a).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).isRightAdjoint
  haveI : (Opens.map a.base).Final := Stacks.Topology.final_opensMap _
  SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom I

/-- **Transport of an identification of pullbacks along a map of squares.** If
`p^* N ≅ q^* E` for `q : X₁ ⟶ X`, `p : X₁ ⟶ T`, and `φ : X₂ ⟶ X₁` satisfies `φ ≫ q = q'` and
`φ ≫ p = p' ≫ h`, then `p'^* (h^* N) ≅ q'^* E`. -/
theorem nonempty_pullback_iso_of_comp_eq {X X₁ X₂ T T' : Scheme.{u}} {q : X₁ ⟶ X}
    {p : X₁ ⟶ T} {q' : X₂ ⟶ X} {p' : X₂ ⟶ T'} (h : T' ⟶ T) (φ : X₂ ⟶ X₁) (hq : φ ≫ q = q')
    (hp : φ ≫ p = p' ≫ h) {E : X.Modules} {N : T.Modules}
    (e : (Scheme.Modules.pullback p).obj N ≅ (Scheme.Modules.pullback q).obj E) :
    Nonempty ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback q').obj E) :=
  ⟨(Scheme.Modules.pullbackComp p' h).app N ≪≫
    (Scheme.Modules.pullbackCongr hp.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ p).app N).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso e ≪≫
    (Scheme.Modules.pullbackComp φ q).app E ≪≫
    (Scheme.Modules.pullbackCongr hq).app E⟩

/-- **The descent condition along a map of squares.** If the pullback of `E` along `q` is the
pullback along `p` of a finite locally free module on `T`, and `φ : X₂ ⟶ X₁` satisfies
`φ ≫ q = q'` and `φ ≫ p = p' ≫ h`, then the pullback of `E` along `q'` is the pullback along `p'`
of a finite locally free module on `T'`, namely the pullback along `h` of the given one. -/
theorem exists_pullback_iso_of_comp_eq {X X₁ X₂ T T' : Scheme.{u}}
    {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {q : X₁ ⟶ X}
    {p : X₁ ⟶ T} {q' : X₂ ⟶ X} {p' : X₂ ⟶ T'} (h : T' ⟶ T) (φ : X₂ ⟶ X₁) (hq : φ ≫ q = q')
    (hp : φ ≫ p = p' ≫ h)
    (H : ∃ N : SheafOfModules.{u} (structureSheafRing T.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback p.toLRSHom.toShHom).obj N ≅
          (modulePullback q.toLRSHom.toShHom).obj E)) :
    ∃ N : SheafOfModules.{u} (structureSheafRing T'.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback p'.toLRSHom.toShHom).obj N ≅
          (modulePullback q'.toLRSHom.toShHom).obj E) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := H
  exact ⟨(Scheme.Modules.pullback h).obj N,
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme h N hN,
    nonempty_pullback_iso_of_comp_eq (E := E) h φ hq hp e⟩

/-- The base change along `h ≫ g` maps to the base change along `g` over `h`, and the resulting
square is cartesian. -/
private theorem exists_pullback_map_precomp {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (h : T' ⟶ T) : ∃ φ : pullback f (h ≫ g) ⟶ pullback f g,
      φ ≫ pullback.fst f g = pullback.fst f (h ≫ g) ∧
      φ ≫ pullback.snd f g = pullback.snd f (h ≫ g) ≫ h ∧
      IsPullback φ (pullback.snd f (h ≫ g)) (pullback.snd f g) h := by
  refine ⟨pullback.lift (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g) ≫ h)
    (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f g)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback f (h ≫ g)

/-- **The descent condition is stable under precomposition.** If `E` descends along `g`, it
descends along `h ≫ g`: the base change `X ×_S T'` maps to `X ×_S T` over `h`, and the pullback
along `h` of the module on `T` witnesses the condition on `T'`. -/
theorem DescendsFromBase.precomp {X S : Scheme.{u}} {f : X ⟶ S}
    {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {T T' : Scheme.{u}}
    (h : T' ⟶ T) {g : T ⟶ S} (hg : DescendsFromBase f E g) : DescendsFromBase f E (h ≫ g) :=
  let ⟨_, hq, hp, _⟩ := exists_pullback_map_precomp f g h
  exists_pullback_iso_of_comp_eq h _ hq hp hg

/-- **The descent condition does not depend on the chosen fibre product.** For any cartesian
square with projections `q : X' ⟶ X` and `p : X' ⟶ T`, `E` descends along `g` exactly when the
pullback of `E` along `q` is the pullback along `p` of a finite locally free module on `T`. -/
theorem descendsFromBase_iff_of_isPullback {X S : Scheme.{u}} {f : X ⟶ S}
    {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {T X' : Scheme.{u}}
    {g : T ⟶ S} {q : X' ⟶ X} {p : X' ⟶ T} (H : IsPullback q p f g) :
    DescendsFromBase f E g ↔
      ∃ N : SheafOfModules.{u} (structureSheafRing T.toRingedSpace),
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
          Nonempty ((modulePullback p.toLRSHom.toShHom).obj N ≅
            (modulePullback q.toLRSHom.toShHom).obj E) :=
  ⟨fun hg ↦ exists_pullback_iso_of_comp_eq (𝟙 T) H.isoPullback.hom H.isoPullback_hom_fst
      (by rw [H.isoPullback_hom_snd, Category.comp_id]) hg,
    fun hg ↦ exists_pullback_iso_of_comp_eq (𝟙 T) H.isoPullback.inv H.isoPullback_inv_fst
      (by rw [H.isoPullback_inv_snd, Category.comp_id]) hg⟩

/-- A finite locally free module on a scheme is free of finite rank over the members of an affine
open cover, in the form of an isomorphism of its pullback along the inclusion of each member with
a free module of finite rank. -/
theorem exists_affine_cover_pullback_iso_free {T : Scheme.{u}} (N : T.Modules)
    (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ V : T → T.Opens, (∀ t, t ∈ V t) ∧ ∀ t, IsAffineOpen (V t) ∧ ∃ m : ℕ,
      Nonempty ((Scheme.Modules.pullback (V t).ι).obj N ≅
        SheafOfModules.free (ULift.{u} (Fin m))) := by
  choose U hU I hI eU using (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators N).2 hN
  choose V hV htV hVU using fun t : T ↦ exists_isAffineOpen_mem_and_subset (hU t)
  refine ⟨V, htV, fun t ↦ ⟨hV t, ?_⟩⟩
  obtain ⟨m, ⟨σ⟩⟩ := Finite.exists_equiv_fin (I t)
  have hle : V t ≤ U t := hVU t
  exact ⟨m, ⟨(Scheme.Modules.pullbackCongr (T.homOfLE_ι hle).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp (T.homOfLE hle) (U t).ι).app N).symm ≪≫
    (Scheme.Modules.pullback (T.homOfLE hle)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback (U t).ι).app N).symm ≪≫ (eU t).some) ≪≫
    schemeModulesPullbackObjFreeIso (T.homOfLE hle) (I t) ≪≫
    SheafOfModules.freeFunctor.mapIso (σ.trans Equiv.ulift.symm).toIso⟩⟩

/-- **A module satisfying the descent condition is trivialised over an affine open cover.** If
`E` descends along `g : T ⟶ S`, there are affine opens `V k` covering `T` such that the pullback
of `E` to each base change `X ×_S V k` is free of finite rank: the finite locally free module on
`T` witnessing the condition is free of finite rank over the members of an affine open cover, and
its pullback to `X ×_S V k` is the pullback of `E`. -/
theorem DescendsFromBase.exists_affine_cover_iso_free {X S : Scheme.{u}} {f : X ⟶ S}
    {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {T : Scheme.{u}}
    {g : T ⟶ S} (hg : DescendsFromBase f E g) :
    ∃ (κ : Type u) (V : κ → T.Opens), (⨆ k, V k) = ⊤ ∧ ∀ k, IsAffineOpen (V k) ∧ ∃ m : ℕ,
      Nonempty ((modulePullback (pullback.fst f ((V k).ι ≫ g)).toLRSHom.toShHom).obj E ≅
        SheafOfModules.free (ULift.{u} (Fin m))) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hg
  obtain ⟨V, htV, hV⟩ := exists_affine_cover_pullback_iso_free (T := T) N hN
  refine ⟨T, V, eq_top_iff.2 fun t _ ↦ Opens.mem_iSup.2 ⟨t, htV t⟩, fun t ↦ ⟨(hV t).1, ?_⟩⟩
  obtain ⟨m, ⟨e₁⟩⟩ := (hV t).2
  obtain ⟨φ, hq, hp, -⟩ := exists_pullback_map_precomp f g (V t).ι
  obtain ⟨e₂⟩ := nonempty_pullback_iso_of_comp_eq (E := E) (V t).ι φ hq hp e
  exact ⟨m, ⟨e₂.symm ≪≫ (Scheme.Modules.pullback (pullback.snd f ((V t).ι ≫ g))).mapIso e₁ ≪≫
    schemeModulesPullbackObjFreeIso _ _⟩⟩

/-- Invertibility of the comparison `𝒪_Y ⟶ a_* 𝒪_X` of sheaves of `RingCat`-valued rings that
`RingedSpaceModuleAdjunction.structureSheafHom` records implies invertibility of the comparison
`a.c` of sheaves of commutative rings: the two agree section by section. -/
theorem isIso_c_of_isIso_structureSheafHom {X Y : Scheme.{u}} (a : X ⟶ Y)
    (h : IsIso (structureSheafHom a.toLRSHom.toShHom)) : IsIso a.toLRSHom.toHom.c := by
  have h₁ : IsIso ((sheafToPresheaf _ _).map (structureSheafHom a.toLRSHom.toShHom)) :=
    inferInstance
  change IsIso (Functor.whiskerRight a.toLRSHom.toHom.c (forget₂ CommRingCat RingCat)) at h₁
  rw [NatTrans.isIso_iff_isIso_app] at h₁ ⊢
  intro U
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ((ConcreteCategory.isIso_iff_bijective
      ((forget₂ CommRingCat RingCat).map (a.toLRSHom.toHom.c.app U))).1 (h₁ U))

/-- **The counit is invertible on the stalks over a flat chart trivialising the module.** Let
`p : X ×_S T ⟶ T` and `q : X ×_S T ⟶ X` be the projections, and let `j : W ⟶ T` be flat with
`j ≫ g = j'`, such that `𝒪_W = p'_* 𝒪` for the base change `p' : X ×_S W ⟶ W` and the pullback of
`E` to `X ×_S W` is free of finite rank. Then the counit `p^* p_* (q^* E) ⟶ q^* E` is invertible
on the stalk at every point of `X ×_S T` lying over the image of `j`.

The pullback of the counit to `X ×_S W` is the counit of `p'` at a free module of finite rank by
flat base change in degree zero, and that counit is invertible because the unit is invertible at
`𝒪_W`. -/
theorem isIso_stalk_counit_of_iso_free {X S T W : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact (pullback.snd f g)] [QuasiSeparated (pullback.snd f g)] (E : X.Modules)
    [((Scheme.Modules.pullback (pullback.fst f g)).obj E).IsQuasicoherent]
    (j : W ⟶ T) [Flat j] (j' : W ⟶ S) (hj : j ≫ g = j')
    (hO : IsIso (pullback.snd f j').toLRSHom.toHom.c) (I : Type u) [Finite I]
    (e : (Scheme.Modules.pullback (pullback.fst f j')).obj E ≅ SheafOfModules.free I)
    (x : ↥(pullback f g)) (w : W) (hx : pullback.snd f g x = j w) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (pullback f g).ringCatSheaf.obj).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f g)).counit.app
          ((Scheme.Modules.pullback (pullback.fst f g)).obj E)).val)) := by
  subst hj
  obtain ⟨k, hk, -, H⟩ := exists_pullback_map_precomp f g j
  have : Flat k := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  let e' : (Scheme.Modules.pullback k).obj
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E) ≅ SheafOfModules.free I :=
    (Scheme.Modules.pullbackComp k (pullback.fst f g)).app E ≪≫
      (Scheme.Modules.pullbackCongr hk).app E ≪≫ e
  have hc := VectorBundleCodimensionOne.isIso_counit_app_of_iso_free (pullback.snd f (j ≫ g))
    (VectorBundleCodimensionOne.isIso_unit_app_unit_of_isIso_c (pullback.snd f (j ≫ g)) hO) _ I e'
  have hp := VectorBundleCodimensionOne.isIso_pullback_map_counit_of_isPullback H _ hc
  obtain ⟨z, hz, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f g) (g := j) x w hx
  have hy : k (H.isoPullback.inv z) = x := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz]
  have := VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map k _ hp
    (H.isoPullback.inv z)
  rwa [hy] at this

/-- **The descent condition is local on the base change.** Let `f : X ⟶ S` be flat and proper
with `𝒪_T = (X ×_S T ⟶ T)_* 𝒪` for every base change, and let `E` be finite locally free on `X`.
If `E` descends along `(V k).ι ≫ g` for the members `V k` of an open cover of `T`, then it
descends along `g`.

By `DescendsFromBase.exists_affine_cover_iso_free` the pullback of `E` is free of finite rank
over a refinement of the cover, so the counit `p^* p_* F ⟶ F` at the pullback `F` of `E` is
invertible on every stalk (`isIso_stalk_counit_of_iso_free`); then `F` is the pullback of the
finite locally free module `p_* F`, by fpqc descent along the flat surjection `p`. -/
theorem descendsFromBase_of_iSup_eq_top {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    {T : Scheme.{u}} (g : T ⟶ S) {κ : Type u} (V : κ → T.Opens) (hV : (⨆ k, V k) = ⊤)
    (h : ∀ k, DescendsFromBase f E ((V k).ι ≫ g)) : DescendsFromBase f E g := by
  let p := pullback.snd f g
  let q := pullback.fst f g
  let F : (pullback f g).Modules := (Scheme.Modules.pullback q).obj E
  have hF : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme q E (by assumption)
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have hε : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p).counit.app F) := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun x ↦ ?_
    obtain ⟨k₀, hk₀⟩ := Opens.mem_iSup.1 (show p x ∈ ⨆ k, V k by rw [hV]; trivial)
    obtain ⟨κ', V', hV', hfree⟩ := (h k₀).exists_affine_cover_iso_free
    let t₀ : (V k₀).toScheme := ⟨p x, hk₀⟩
    obtain ⟨k₁, hk₁⟩ := Opens.mem_iSup.1 (show t₀ ∈ ⨆ k, V' k by rw [hV']; trivial)
    obtain ⟨m, ⟨e⟩⟩ := (hfree k₁).2
    exact isIso_stalk_counit_of_iso_free f g E ((V' k₁).ι ≫ (V k₀).ι)
      ((V' k₁).ι ≫ (V k₀).ι ≫ g) (Category.assoc _ _ _)
      (isIso_c_of_isIso_structureSheafHom _ (hO _)) (ULift (Fin m)) e x ⟨t₀, hk₁⟩ rfl
  have : Surjective p := VectorBundleCodimensionOne.surjective_of_isIso_cMap p
    (isIso_c_of_isIso_structureSheafHom _ (hO g))
  exact VectorBundleCodimensionOne.exists_isFiniteLocallyFree_pullback_iso_of_isIso_counit p F hε

end AlgebraicGeometry

end
