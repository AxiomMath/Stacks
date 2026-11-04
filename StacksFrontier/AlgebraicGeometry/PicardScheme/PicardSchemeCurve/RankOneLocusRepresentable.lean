module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusHilbert
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RigidifiedPicardSeparated
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme

/-!
# The rank-one locus is represented by an open subscheme of the Hilbert scheme

This file proves [Stacks, Tag 0B9X]. Let `k` be a field, `X` a smooth projective
curve of genus `g` over `k` with a `k`-rational point `σ`, and `H` a scheme representing
`Hilb^g_{X/k}` (the data of [Stacks, Tag 0B9I] (1)). The universal element
`ℒ_H ∈ Pic_{X/k, σ}(H)` (`AlgebraicGeometry.RigidifiedPicard.universalClass`) defines
`h_H ⟶ Pic_{X/k, σ}`, and `W ⊆ H` is the open of [Stacks, Tag 0B9V] over which `ℒ_H` lies in
the subfunctor `F`. The statement is that `h_W ⟶ F`, `m ↦ m^*ℒ_H`, is bijective on `T`-points
for every `k`-scheme `T`.

## Main results

* `AlgebraicGeometry.RigidifiedPicard.rankOneLocus_representable_by_open_of_hilbert`:
  [Stacks, Tag 0B9X], with the two named arguments of
  `rankOneLocus_isSubfunctor_and_representable` ([Stacks, Tag 0B9V]): `hPerfBC`
  ([Stacks, Tag 0A1H]) and `hRankOpen` (description (2) of [Stacks, Tag 0BDK] for
  arbitrary morphisms). `H` representing `Hilb^g_{X/k}` is data, as in
  [Stacks, Tag 0B9J].
* `AlgebraicGeometry.RigidifiedPicard.eq_of_map_universalClass_eq`: injectivity of
  `m ↦ m^*ℒ_H`.
* `AlgebraicGeometry.RigidifiedPicard.exists_map_universalClass_eq`: surjectivity of
  `m ↦ m^*ℒ_H` onto `F(T)`.
* `AlgebraicGeometry.RigidifiedPicard.nonempty_unit_iso_derivedPushforward_pullback`: after base
  change to a `T'` over which the invertible module `𝒩` with `Rf_{T,*}ℒ ≅ 𝒩[0]` becomes trivial,
  `Rf_{T',*}ℒ_{T'} ≅ 𝒪_{T'}[0]` ([Stacks, Tag 0B91] (1)).
* `AlgebraicGeometry.RigidifiedPicard.eq_zeroScheme_of_isGenerator`: a degree-`g` divisor `E` with
  `𝒪(E) ≅ ℒ` is the zero scheme of any generator of `ℒ`.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open RingedSpaceModuleAdjunction (modulePullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- **After a base change trivialising `𝒩`, the derived pushforward is the structure sheaf**:
if `Rf_{T,*}ℒ ≅ 𝒩[0]` with `𝒩` invertible and `g^*𝒩 ≅ 𝒪_{T'}` for `g : T' ⟶ T`, then
`𝒪_{T'}[0] ≅ Rf_{T',*}(ℒ_{T'}[0])`. -/
theorem nonempty_unit_iso_derivedPushforward_pullback
    (_hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] {T T' : Over (Spec (.of k))}
    (g : T' ⟶ T) (R : (pullback f T.hom).Modules)
    [SheafOfModules.IsInvertible (pullback f T.hom).sheaf.obj
      (pullback f T.hom).ringCatSheaf.property R]
    (M : T.left.Modules)
    [SheafOfModules.IsInvertible T.left.sheaf.obj T.left.ringCatSheaf.property M]
    (eM : (derivedPushforward (pullback.snd f T.hom).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (pullback f T.hom).Modules 0).obj R) ≅
      (DerivedCategory.singleFunctor T.left.Modules 0).obj M)
    (eu : (Scheme.Modules.pullback g.left).obj M ≅ SheafOfModules.unit T'.left.ringCatSheaf) :
    Nonempty ((DerivedCategory.singleFunctor T'.left.Modules 0).obj
        (SheafOfModules.unit T'.left.ringCatSheaf) ≅
      (derivedPushforward (pullback.snd f T'.hom).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (pullback f T'.hom).Modules 0).obj
          ((modulePullback (baseChangeMap f g).toLRSHom.toShHom).obj R))) := by
  have : IsProper (pullback.snd f T.hom) := inferInstance
  have : Flat (pullback.snd f T.hom) := inferInstance
  have hf : FinitePresentation (pullback.snd f T.hom) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hbc :=
    (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
    _ hf inferInstance inferInstance _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree _ R
      (Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ R))).2 _ _ _
    (Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _ g.left
      (Over.w g).symm)
  exact ⟨(DerivedCategory.singleFunctor T'.left.Modules 0).mapIso eu.symm ≪≫
    (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso g.left.toLRSHom.toShHom M
      (Stacks.Chow.isFlat_of_isInvertible M)).symm ≪≫
    (derivedPullback g.left.toLRSHom.toShHom).mapIso eM.symm ≪≫ @asIso _ _ _ _ _ hbc ≪≫
    (derivedPushforward (pullback.snd f T'.hom).toLRSHom.toShHom).mapIso
      (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso
        (baseChangeMap f g).toLRSHom.toShHom R (Stacks.Chow.isFlat_of_isInvertible R))⟩

/-! ### Local triviality -/

/-- **Finitely many Picard classes are simultaneously trivial near any point.** -/
theorem exists_mem_forall_schemePullbackClass_eq_zero {Y : Scheme.{u}} :
    ∀ (n : ℕ) (N : Fin n → Stacks.Picard.ofScheme Y) (y : Y),
      ∃ U : Y.Opens, y ∈ U ∧ ∀ i, Stacks.Picard.schemePullbackClass U.ι (N i) = 0
  | 0, _, _ => ⟨⊤, trivial, fun i => i.elim0⟩
  | n + 1, N, y => by
    obtain ⟨U, hU, hN⟩ := exists_mem_forall_schemePullbackClass_eq_zero n (fun i => N i.succ) y
    obtain ⟨V, hV, hN0⟩ := Stacks.Picard.exists_mem_schemePullbackClass_eq_zero (N 0) y
    have key : ∀ (W : Y.Opens) (h : U ⊓ V ≤ W) (x : Stacks.Picard.ofScheme Y),
        Stacks.Picard.schemePullbackClass W.ι x = 0 →
          Stacks.Picard.schemePullbackClass (U ⊓ V).ι x = 0 := by
      intro W h x hx
      rw [← Y.homOfLE_ι h, ← Stacks.Picard.schemePullbackClass_comp, hx]
      exact map_zero (Stacks.Picard.schemePullbackClassHom _)
    refine ⟨U ⊓ V, ⟨hU, hV⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact key V inf_le_right _ hN0
    · exact key U inf_le_left _ (hN j)

/-- A module whose Picard class pulls back to zero along `g` has trivial pullback along `g`. -/
theorem nonempty_pullback_iso_unit_of_schemePullbackClass_eq_zero {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (M : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M)
    (h : Stacks.Picard.schemePullbackClass g
      (Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M hM) = 0) :
    Nonempty ((Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y'.ringCatSheaf) := by
  exact (Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _ _).1
    ((Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom M hM).symm.trans h)

/-- Restriction in `Pic_{X/k, σ}` along a composite is the composite of the restrictions. -/
theorem kernelMap_comp {T T' T'' : Over (Spec (.of k))} (g : T'' ⟶ T') (g' : T' ⟶ T)
    (c : kernelAt f σ hσ T) :
    kernelMap f σ hσ (g ≫ g') c = kernelMap f σ hσ g (kernelMap f σ hσ g' c) := by
  apply Subtype.ext
  show Stacks.Picard.schemePullbackClass (baseChangeMap f (g ≫ g')) c.1 =
    Stacks.Picard.schemePullbackClass (baseChangeMap f g)
      (Stacks.Picard.schemePullbackClass (baseChangeMap f g') c.1)
  rw [baseChangeMap_comp, Stacks.Picard.schemePullbackClass_comp]

/-- The `k`-scheme `U` attached to an open `U` of a `k`-scheme `T`. -/
abbrev opensObj (T : Over (Spec (.of k))) (U : T.left.Opens) : Over (Spec (.of k)) :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of an open, as a morphism of `k`-schemes. -/
abbrev opensHom (T : Over (Spec (.of k))) (U : T.left.Opens) : opensObj T U ⟶ T :=
  Over.homMk U.ι

/-- A class differing from `c` by a class pulled back from `T` has the same pullback as `c`
along a base change `g` over which that class becomes trivial. -/
theorem schemePullbackClass_baseChangeMap_eq {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (x c : Stacks.Picard.ofScheme (pullback f T.hom)) (P : Stacks.Picard.ofScheme T.left)
    (hx : x = c + Stacks.Picard.schemePullbackClass (pullback.snd f T.hom) P)
    (hP : Stacks.Picard.schemePullbackClass g.left P = 0) :
    Stacks.Picard.schemePullbackClass (baseChangeMap f g) x =
      Stacks.Picard.schemePullbackClass (baseChangeMap f g) c := by
  have hsnd : baseChangeMap f g ≫ pullback.snd f T.hom = pullback.snd f T'.hom ≫ g.left :=
    pullback.lift_snd _ _ _
  rw [hx, Stacks.Picard.schemePullbackClass_add, Stacks.Picard.schemePullbackClass_comp, hsnd,
    ← Stacks.Picard.schemePullbackClass_comp, hP,
    show Stacks.Picard.schemePullbackClass (pullback.snd f T'.hom) 0 = 0 from
      map_zero (Stacks.Picard.schemePullbackClassHom _), add_zero]

/-- A class whose normalisation is `c` is `c` plus a class pulled back from `T`. -/
theorem eq_add_of_normalize_eq (T : Over (Spec (.of k)))
    (x : Stacks.Picard.ofScheme (pullback f T.hom)) (c : kernelAt f σ hσ T)
    (h : normalize f σ hσ T x = c) :
    x = c.1 + Stacks.Picard.schemePullbackClass (pullback.snd f T.hom)
      (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) x) := by
  have h' := congrArg Subtype.val h
  change x - _ = c.1 at h'
  rw [← h', sub_add_cancel]

include σ hσ in
/-- **A degree-`g` divisor `E` with `𝒪(E) ≅ ℒ` is the zero scheme of any generator of `ℒ`.** It
takes [Stacks, Tag 0A1H] as an argument (`hPerfBC`). -/
theorem eq_zeroScheme_of_isGenerator
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [Smooth f] [IsProper f] {T : Scheme.{u}} (q : T ⟶ Spec (.of k))
    (E : (pullback f q).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hE : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (E.subschemeι ≫ pullback.snd f q) (genus f))
    (L : (pullback f q).Modules)
    [SheafOfModules.IsInvertible (pullback f q).sheaf.obj (pullback f q).ringCatSheaf.property L]
    (e : Stacks.Divisors.divisorSheaf E ≅ L)
    (s : SheafOfModules.unit (pullback f q).ringCatSheaf ⟶ L)
    (hs : PushforwardGenerator.IsGenerator (pullback.snd f q).toLRSHom.toShHom L s) :
    E = zeroScheme (pullback f q) L ((L.unitHomEquiv s).eval (op ⊤)) := by
  let : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  let : SmoothOfRelativeDimension 1 (pullback.snd f q) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f q) inferInstance
  let t : SheafOfModules.unit (pullback f q).ringCatSheaf ⟶ L :=
    (Stacks.Divisors.divisorSheaf E).unitHomEquiv.symm (Stacks.Divisors.canonicalSection' E) ≫ e.hom
  have ht : zeroScheme (pullback f q) L ((L.unitHomEquiv t).eval (op ⊤)) = E := by
    refine (zeroScheme_eq_of_iso e ?_).symm.trans (Stacks.Divisors.zeroScheme_canonicalSection E)
    have h1 : L.unitHomEquiv t =
        SheafOfModules.sectionsMap e.hom (Stacks.Divisors.canonicalSection' E) :=
      (SheafOfModules.unitHomEquiv_comp_apply _ e.hom).trans
        (congrArg (SheafOfModules.sectionsMap e.hom)
          ((Stacks.Divisors.divisorSheaf E).unitHomEquiv.apply_symm_apply
            (Stacks.Divisors.canonicalSection' E)))
    rw [h1]
    rfl
  have := isFiniteLocallyFreeOfRank_zeroScheme_of_isGenerator f σ hσ hPerfBC q L s hs
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((zeroScheme (pullback f q) L ((L.unitHomEquiv t).eval (op ⊤))).subschemeι ≫
        pullback.snd f q) (genus f) := by
    rwa [ht]
  rw [← zeroScheme_eq_of_isGenerator (pullback.snd f q) L s t hs (genus f), ht]

/-- The chosen representative of a Picard class of a scheme is invertible in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
instance isInvertible_picardRepresentative {Y : Scheme.{u}} (c : Stacks.Picard.ofScheme Y) :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (Stacks.Picard.picardRepresentative Y.toRingedSpace c).property

/-- The pullback of a Picard class is the class of the pullback of its representative. -/
theorem schemePullbackClass_eq_picardClass_pullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (c : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass g c =
      Stacks.SheafOfModules.picardClass Y'.presheaf (Stacks.RingedSpace.structureIsSheaf _)
        ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj
          (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj)
        (Stacks.RingedSpace.modulePullback_isInvertible_of _ _
          (Stacks.Picard.picardRepresentative Y.toRingedSpace c).property) := by
  conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative _ c]
  exact Stacks.Picard.pullbackClass_classOf _ _ _

include σ hσ in
/-- **A degree-`g` Hilbert family with the class of `ℒ` is the divisor of a generator of `ℒ`**:
for an invertible `ℒ` on `X_T`, a family `Z` over `T` with `[𝒪(Z)] = [ℒ]` and a generator `s`
of `ℒ` relative to `f_T`, the ideal of `Z` is the zero scheme of `s`. It takes
[Stacks, Tag 0A1H] as an argument (`hPerfBC`). -/
theorem familyIdeal_eq_zeroScheme_of_isGenerator
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [Smooth f] [IsProper f] {T : Over (Spec (.of k))}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)) (R : (pullback f T.hom).Modules)
    [hRa : SheafOfModules.IsInvertible (pullback f T.hom).sheaf.obj
      (pullback f T.hom).ringCatSheaf.property R]
    (hR : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (Stacks.RingedSpace.structureIsSheaf _) R)
    (hcls : familyClass f Z = Stacks.SheafOfModules.picardClass (pullback f T.hom).presheaf
      (Stacks.RingedSpace.structureIsSheaf _) R hR)
    (s : SheafOfModules.unit (pullback f T.hom).ringCatSheaf ⟶ R)
    (hs : PushforwardGenerator.IsGenerator (pullback.snd f T.hom).toLRSHom.toShHom R s) :
    Z.ideal = zeroScheme (pullback f T.hom) R ((R.unitHomEquiv s).eval (op ⊤)) := by
  have hZ : Stacks.Divisors.IsEffectiveCartierDivisor (X := pullback f T.hom) Z.ideal :=
    (isRelativeEffectiveCartierDivisor_hilbertFamily f Z).1
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hcls
  exact eq_zeroScheme_of_isGenerator f σ hσ hPerfBC T.hom Z.ideal Z.isFiniteLocallyFreeOfRank R e
    s hs

/-- The Stacks and the `AlgebraicGeometry` notions of invertibility hold for a module that is
finite locally free of rank one. -/
private theorem isInvertible_of_isFiniteLocallyFreeOfRank_one {Y : Scheme.{u}} (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
      SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := by
  have hMs := (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one
    _ _).2 hM
  exact ⟨hMs,
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hMs⟩

/-- The class of the Hilbert family of `g ≫ m` is the pullback of that of `m`. -/
private theorem familyClass_family_comp [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    {T T' : Over (Spec (.of k))} (m : T ⟶ H) (g : T' ⟶ T) :
    familyClass f (hH.family (g ≫ m)) =
      Stacks.Picard.schemePullbackClass (baseChangeMap f g) (familyClass f (hH.family m)) :=
  (@Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ (baseChangeMap f g)
    (hH.family m).ideal (hH.family (g ≫ m)).ideal
    (isRelativeEffectiveCartierDivisor_hilbertFamily f (hH.family m)).1
    (isRelativeEffectiveCartierDivisor_hilbertFamily f (hH.family (g ≫ m))).1
    (hH.naturality g m)).symm

include hσ in
/-- **The pullback of `[𝒪(Z_m)]` to a base change over which `σ^*[𝒪(Z_m)]` is trivial is the
pullback of `m^*ℒ_H`.** -/
theorem familyClass_comp_eq [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    {T T' : Over (Spec (.of k))} (m : T ⟶ H) (g : T' ⟶ T)
    (hP : Stacks.Picard.schemePullbackClass g.left
      (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) (familyClass f (hH.family m))) = 0) :
    familyClass f (hH.family (g ≫ m)) = Stacks.Picard.schemePullbackClass (baseChangeMap f g)
      ((picardFunctor f σ hσ).map m.op (universalClass f σ hσ hH)).1 := by
  rw [familyClass_family_comp f hH m g]
  exact schemePullbackClass_baseChangeMap_eq f g _ _ _
    (eq_add_of_normalize_eq f σ hσ T _ _ (map_universalClass f σ hσ hH m).symm) hP

include σ hσ in
/-- **Two morphisms into `H` whose families have the class of `q^*ℒ` agree**, over a
`q : T' ⟶ T` along which the invertible module `𝒩` with `Rf_{T,*}ℒ ≅ 𝒩[0]` becomes trivial. It
takes [Stacks, Tag 0A1H] as an argument (`hPerfBC`). -/
theorem eq_of_familyClass_eq
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [Smooth f] [IsProper f] {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f))
    {T T' : Over (Spec (.of k))} (q : T' ⟶ T) (c : Stacks.Picard.ofScheme (pullback f T.hom))
    (M : T.left.Modules)
    [SheafOfModules.IsInvertible T.left.sheaf.obj T.left.ringCatSheaf.property M]
    (eM : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule (pullback.snd f T.hom)
        (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj ≅
      (DerivedCategory.singleFunctor T.left.Modules 0).obj M)
    (eu : (Scheme.Modules.pullback q.left).obj M ≅ SheafOfModules.unit T'.left.ringCatSheaf)
    (n₁ n₂ : T' ⟶ H)
    (h₁ : familyClass f (hH.family n₁) = Stacks.Picard.schemePullbackClass (baseChangeMap f q) c)
    (h₂ : familyClass f (hH.family n₂) = Stacks.Picard.schemePullbackClass (baseChangeMap f q) c) :
    n₁ = n₂ := by
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨s, hs⟩ := PushforwardGenerator.exists_isGenerator _ _
    (nonempty_unit_iso_derivedPushforward_pullback f hPerfBC q _ M eM eu)
  have : SheafOfModules.IsInvertible (pullback f T'.hom).sheaf.obj
      (pullback f T'.hom).ringCatSheaf.property
      ((modulePullback (baseChangeMap f q).toLRSHom.toShHom).obj
        (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ _
      (isInvertible_picardRepresentative _)
  have hcls : ∀ n : T' ⟶ H,
      familyClass f (hH.family n) = Stacks.Picard.schemePullbackClass (baseChangeMap f q) c →
      (hH.family n).ideal = zeroScheme (pullback f T'.hom)
        ((modulePullback (baseChangeMap f q).toLRSHom.toShHom).obj
          (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj)
        ((SheafOfModules.unitHomEquiv _ s).eval (op ⊤)) := fun n hn =>
    familyIdeal_eq_zeroScheme_of_isGenerator f σ hσ hPerfBC (hH.family n)
      ((modulePullback (baseChangeMap f q).toLRSHom.toShHom).obj
        (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj)
      (Stacks.RingedSpace.modulePullback_isInvertible_of _ _
        (Stacks.Picard.picardRepresentative _ _).property)
      (hn.trans (schemePullbackClass_eq_picardClass_pullback _ _)) s hs
  apply hH.family.injective
  ext1
  exact (hcls n₁ h₁).trans (hcls n₂ h₂).symm

include σ hσ in
/-- **`m ↦ m^*ℒ_H` is injective on the morphisms into `W`**: if `m₁^*ℒ_H = m₂^*ℒ_H` lies in
`F(T)`, then `m₁ = m₂`. It takes [Stacks, Tag 0A1H] as an argument (`hPerfBC`). -/
theorem eq_of_map_universalClass_eq
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f))
    {T : Over (Spec (.of k))} (m₁ m₂ : T ⟶ H)
    (hm : (picardFunctor f σ hσ).map m₁.op (universalClass f σ hσ hH) ∈ rankOneLocus f σ hσ T)
    (h : (picardFunctor f σ hσ).map m₁.op (universalClass f σ hσ hH) =
      (picardFunctor f σ hσ).map m₂.op (universalClass f σ hσ hH)) :
    m₁ = m₂ := by
  have : IsProper f := inferInstance
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨M, hM1, ⟨eM⟩⟩ := hm
  obtain ⟨hMs, _⟩ := isInvertible_of_isFiniteLocallyFreeOfRank_one M hM1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨U, htU, hU⟩ := exists_mem_forall_schemePullbackClass_eq_zero 3
    ![Stacks.SheafOfModules.picardClass T.left.presheaf
        (Stacks.RingedSpace.structureIsSheaf _) M hMs,
      Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) (familyClass f (hH.family m₁)),
      Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) (familyClass f (hH.family m₂))] t
  refine ⟨U, htU, ?_⟩
  obtain ⟨eu⟩ := nonempty_pullback_iso_unit_of_schemePullbackClass_eq_zero U.ι M hMs (hU 0)
  have hcl₁ := familyClass_comp_eq f σ hσ hH m₁ (opensHom T U) (hU 1)
  have hcl₂ := familyClass_comp_eq f σ hσ hH m₂ (opensHom T U) (hU 2)
  rw [← h] at hcl₂
  exact congrArg CommaMorphism.left (eq_of_familyClass_eq f σ hσ hPerfBC hH (opensHom T U) _ M eM
    eu _ _ hcl₁ hcl₂)

include σ hσ in
/-- **The class of the divisor of a generator of `g^*ℒ` is `g^*[ℒ]`.** It takes
[Stacks, Tag 0A1H] as an argument (`hPerfBC`). -/
theorem familyClass_zeroScheme_eq
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [Smooth f] [IsProper f] {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (c : Stacks.Picard.ofScheme (pullback f T.hom))
    [SheafOfModules.IsInvertible (pullback f T'.hom).sheaf.obj
      (pullback f T'.hom).ringCatSheaf.property
      ((modulePullback (baseChangeMap f g).toLRSHom.toShHom).obj
        (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj)]
    (s : SheafOfModules.unit (pullback f T'.hom).ringCatSheaf ⟶
      (modulePullback (baseChangeMap f g).toLRSHom.toShHom).obj
        (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c).obj)
    (hs : PushforwardGenerator.IsGenerator (pullback.snd f T'.hom).toLRSHom.toShHom _ s) :
    familyClass f (⟨zeroScheme (pullback f T'.hom) _
          ((SheafOfModules.unitHomEquiv _ s).eval (op ⊤)),
        isFiniteLocallyFreeOfRank_zeroScheme_of_isGenerator f σ hσ hPerfBC T'.hom _ s hs⟩ :
        Stacks.Hilbert.HilbertFamily (Over.mk f) T' (genus f)) =
      Stacks.Picard.schemePullbackClass (baseChangeMap f g) c := by
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection _ _ _).1
    (isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator f σ hσ hPerfBC T'.hom _ s hs).1.1
  refine Eq.trans ?_ (schemePullbackClass_eq_picardClass_pullback _ _).symm
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    ⟨(invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg).symm⟩

include σ hσ in
/-- **Every element of `F(T)` is `m^*ℒ_H` for some `m : T ⟶ H`.** It takes [Stacks, Tag 0A1H] as
an argument (`hPerfBC`). -/
theorem exists_map_universalClass_eq
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f))
    {T : Over (Spec (.of k))} (c : (picardFunctor f σ hσ).obj (op T))
    (hc : c ∈ rankOneLocus f σ hσ T) :
    ∃ m : T ⟶ H, (picardFunctor f σ hσ).map m.op (universalClass f σ hσ hH) = c := by
  classical
  have : IsProper f := inferInstance
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨M, hM1, ⟨eM⟩⟩ := hc
  obtain ⟨hMs, _⟩ := isInvertible_of_isFiniteLocallyFreeOfRank_one M hM1
  choose U hU hzero using fun t : T.left => Stacks.Picard.exists_mem_schemePullbackClass_eq_zero
    (Stacks.SheafOfModules.picardClass T.left.presheaf
      (Stacks.RingedSpace.structureIsSheaf _) M hMs) t
  have hcov : TopologicalSpace.IsOpenCover U :=
    .mk (top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩)
  let 𝒰 := Scheme.openCoverOfIsOpenCover T.left U hcov
  have heu : ∀ {W : Over (Spec (.of k))} (i : 𝒰.I₀) (p : W ⟶ coverObj T 𝒰 i),
      Nonempty ((Scheme.Modules.pullback (p ≫ coverHom T 𝒰 i).left).obj M ≅
        SheafOfModules.unit W.left.ringCatSheaf) := by
    intro W i p
    exact nonempty_pullback_iso_unit_of_schemePullbackClass_eq_zero _ M hMs
      ((Stacks.Picard.schemePullbackClass_comp p.left (U i).ι _).symm.trans
      ((congrArg (Stacks.Picard.schemePullbackClass p.left) (hzero i)).trans
        (map_zero (Stacks.Picard.schemePullbackClassHom p.left))))
  set Rr := Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
    (c : kernelAt f σ hσ T).1
  have hgen : ∀ i : 𝒰.I₀, ∃ s, PushforwardGenerator.IsGenerator
      (pullback.snd f (coverObj T 𝒰 i).hom).toLRSHom.toShHom
      ((modulePullback (baseChangeMap f (coverHom T 𝒰 i)).toLRSHom.toShHom).obj Rr.obj) s := by
    intro i
    obtain ⟨eu⟩ := heu i (𝟙 _)
    rw [Category.id_comp] at eu
    exact PushforwardGenerator.exists_isGenerator _ _
      (nonempty_unit_iso_derivedPushforward_pullback f hPerfBC (coverHom T 𝒰 i) Rr.obj M eM eu)
  choose s hs using hgen
  have hRi : ∀ i : 𝒰.I₀, SheafOfModules.IsInvertible (pullback f (coverObj T 𝒰 i).hom).sheaf.obj
      (pullback f (coverObj T 𝒰 i).hom).ringCatSheaf.property
      ((modulePullback (baseChangeMap f (coverHom T 𝒰 i)).toLRSHom.toShHom).obj Rr.obj) :=
    fun i => Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ _
      (isInvertible_picardRepresentative _)
  obtain ⟨m, hmdef⟩ : ∃ m : ∀ i : 𝒰.I₀, coverObj T 𝒰 i ⟶ H, ∀ i, hH.family (m i) =
      ⟨zeroScheme (pullback f (coverObj T 𝒰 i).hom) _
        ((SheafOfModules.unitHomEquiv _ (s i)).eval (op ⊤)),
        isFiniteLocallyFreeOfRank_zeroScheme_of_isGenerator f σ hσ hPerfBC _ _ (s i) (hs i)⟩ :=
    ⟨fun i => hH.family.symm _, fun i => Equiv.apply_symm_apply _ _⟩
  have hmcls : ∀ i, familyClass f (hH.family (m i)) =
      Stacks.Picard.schemePullbackClass (baseChangeMap f (coverHom T 𝒰 i)) c.1 := by
    intro i
    rw [hmdef i]
    exact familyClass_zeroScheme_eq f σ hσ hPerfBC (coverHom T 𝒰 i) c.1 (s i) (hs i)
  have hcomp : ∀ (i : 𝒰.I₀) {W : Over (Spec (.of k))} (p : W ⟶ coverObj T 𝒰 i),
      familyClass f (hH.family (p ≫ m i)) =
        Stacks.Picard.schemePullbackClass (baseChangeMap f (p ≫ coverHom T 𝒰 i)) c.1 := by
    intro i W p
    rw [baseChangeMap_comp, ← Stacks.Picard.schemePullbackClass_comp, ← hmcls i]
    exact familyClass_family_comp f hH (m i) p
  have hglue : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (m i).left =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (m j).left := by
    intro i j
    obtain ⟨eu⟩ := heu i (coverOverlapFst T 𝒰 i j)
    have h₂ := hcomp j (coverOverlapSnd T 𝒰 i j)
    rw [← coverOverlap_condition] at h₂
    exact congrArg CommaMorphism.left (eq_of_familyClass_eq f σ hσ hPerfBC hH
      (coverOverlapFst T 𝒰 i j ≫ coverHom T 𝒰 i) c.1 M eM eu _ _
      (hcomp i (coverOverlapFst T 𝒰 i j)) h₂)
  obtain ⟨mm, hmi⟩ : ∃ mm : T ⟶ H, ∀ i, coverHom T 𝒰 i ≫ mm = m i := by
    let mleft := 𝒰.glueMorphisms (fun i => (m i).left) hglue
    have hmleft : mleft ≫ H.hom = T.hom := by
      refine 𝒰.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Over.w (m i)]
      rfl
    exact ⟨Over.homMk mleft hmleft, fun i =>
      Over.OverMorphism.ext (Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue i)⟩
  refine ⟨mm, ?_⟩
  let c' : kernelAt f σ hσ T := c
  let x : kernelAt f σ hσ T := kernelMap f σ hσ mm (universalClass f σ hσ hH)
  have key : x - c' = 0 := by
    refine eq_zero_of_forall_kernelMap_coverHom_eq_zero f σ hσ T 𝒰 _ fun i => ?_
    have e1 : kernelMap f σ hσ (coverHom T 𝒰 i) x =
        kernelMap f σ hσ (m i) (universalClass f σ hσ hH) :=
      (kernelMap_comp f σ hσ _ _ _).symm.trans
        (congrArg (fun g => kernelMap f σ hσ g (universalClass f σ hσ hH)) (hmi i))
    have e2 : kernelMap f σ hσ (m i) (universalClass f σ hσ hH) =
        kernelMap f σ hσ (coverHom T 𝒰 i) c' :=
      (map_universalClass f σ hσ hH (m i)).trans
        ((congrArg (normalize f σ hσ _) (hmcls i)).trans
          ((kernelMap_normalize f σ hσ _ _).symm.trans
            (congrArg (kernelMap f σ hσ (coverHom T 𝒰 i)) (normalize_coe f σ hσ T c'))))
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (e1.trans e2))
  exact sub_eq_zero.1 key

include σ hσ in
/-- **[Stacks, Tag 0B9X], with [Stacks, Tag 0A1H] (`hPerfBC`) and description (2) of
[Stacks, Tag 0BDK] for arbitrary morphisms (`hRankOpen`) as arguments.** Let `k` be a field, `X` a
smooth projective curve of genus `g = genus f` over `k` with a `k`-rational point `σ`, and `H` a
scheme representing `Hilb^g_{X/k}` (the data of [Stacks, Tag 0B9I] (1)). Then the subfunctor
`F ⊆ Pic_{X/k, σ}` of [Stacks, Tag 0B9V] (`rankOneLocus`) is represented by an open subscheme
`W ⊆ H`: for every `k`-scheme `T`, `m ↦ m^*ℒ_H` is a bijection from the `k`-morphisms
`T ⟶ H` factoring through `W` onto `F(T)`, where `ℒ_H ∈ Pic_{X/k, σ}(H)` is the universal
element (`universalClass`). The bijections are natural in `T`, being given by pullback of one
element. Here `W` is the open of [Stacks, Tag 0B9S] for `ℒ_H` (`rankOneOpen`). -/
theorem rankOneLocus_representable_by_open_of_hilbert
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f)) :
    ∃ W : H.left.Opens, ∀ T : Over (Spec (.of k)),
      ∃ e : {m : T ⟶ H // ∃ h : T.left ⟶ W.toScheme, h ≫ W.ι = m.left} ≃ rankOneLocus f σ hσ T,
        ∀ m, (e m : (picardFunctor f σ hσ).obj (op T)) =
          (picardFunctor f σ hσ).map m.1.op (universalClass f σ hσ hH) := by
  have : IsProper f := inferInstance
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  refine ⟨rankOneOpen f σ hσ H (universalClass f σ hσ hH), fun T => ?_⟩
  let Φ : {m : T ⟶ H // ∃ h : T.left ⟶ (rankOneOpen f σ hσ H (universalClass f σ hσ hH)).toScheme,
      h ≫ (rankOneOpen f σ hσ H (universalClass f σ hσ hH)).ι = m.left} →
      rankOneLocus f σ hσ T := fun m =>
    ⟨_, (map_mem_rankOneLocus_iff f σ hσ hPerfBC hRankOpen H (universalClass f σ hσ hH) m.1).2 m.2⟩
  have hinj : Function.Injective Φ := fun m₁ m₂ h =>
    Subtype.ext (eq_of_map_universalClass_eq f σ hσ hPerfBC hH m₁.1 m₂.1 (Φ m₁).2
      (congrArg Subtype.val h))
  have hsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨m, hm⟩ := exists_map_universalClass_eq f σ hσ hPerfBC hH c.1 c.2
    refine ⟨⟨m, (map_mem_rankOneLocus_iff f σ hσ hPerfBC hRankOpen H (universalClass f σ hσ hH) m).1
      (hm ▸ c.2)⟩, Subtype.ext hm⟩
  exact ⟨Equiv.ofBijective Φ ⟨hinj, hsurj⟩, fun m => rfl⟩

end AlgebraicGeometry.RigidifiedPicard

end
