module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DirectImageAdequacy
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Parasitic

/-!
# Direct images of parasitic adequate modules

Let `f : T ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `𝓕` be a
parasitic adequate `𝒪_T`-module on a big `τ`-site over `T`. [Stacks, Tag 06ZP] asserts that the
direct image `f_*𝓕` and every higher direct image `R^i f_*𝓕` are parasitic adequate
`𝒪_S`-modules on a big `τ`-site over `S`.

## Main definitions

* `Stacks.Adequate.ambientBaseChange` — the base change functor `V ↦ V ×_S T` between the
  localizations of one ambient big site at `S` and at `T`, and
  `Stacks.Adequate.ambientBaseChangeFst` its first projection.

## Main results

* `Stacks.Adequate.isAdequate_and_isParasitic_directImage_ofAmbient` — **[Stacks, Tag 06ZP]**,
  for every one of the five topologies `τ`, with `(Sch/S)_τ` and `(Sch/T)_τ` the localizations of
  one ambient big site, as in the source.
* `Stacks.Adequate.isAdequate_and_isParasitic_directImage` — the same for arbitrary chosen big
  sites over `S` and over `T`, along any functor which is base change along `f`.
* `Stacks.Adequate.isBaseChangeAlong_ambientBaseChange` — the base change functor between two
  localizations of one ambient big site is base change along `f`.
* `Stacks.Adequate.isParasitic_directImage` — the direct image of a parasitic module is
  parasitic.
* `Stacks.Adequate.isParasitic_higherDirectImage` — every higher direct image of a parasitic
  adequate module along a quasi-compact and quasi-separated morphism is parasitic.
* `Stacks.Adequate.subsingleton_higherDirectImage_obj_of_isAffine` — `R^i f_*𝓕` has no sections
  over an affine object of the site flat over `S`.

## Implementation notes

The source's proof is: the direct images are adequate by [Stacks, Tag 06VR], so by
[Stacks, Tag 06ZM] it suffices to see that their sections vanish over the members of an affine
open covering of `S`; and they do. Adequacy is `Stacks.Adequate.isAdequate_directImage` and
`Stacks.Adequate.isAdequate_higherDirectImage`. Parasiticity of `f_*𝓕` is immediate, as
`(f_*𝓕)(V) = 𝓕(V ×_S T)` and `V ×_S T` is flat over `T` when `V` is flat over `S`. For
`R^i f_*𝓕` the reduction is the implication (5) ⇒ (2) of Tag 06ZM,
`Stacks.Adequate.isParasitic_of_isAffine_cover`, applied to the covering of `S` by its affine
opens, and the vanishing over an affine `U = Spec A` flat over `S` is computed with the
machinery of Tag 06VR:

* the sections of `R^i f_*𝓕` over `U` are those of the presheaf `V ↦ H^i(V ×_S T, 𝓕)` over
  `U`, because the sheafification of a presheaf whose affine-section functors are adequate does
  not change its affine sections (`Stacks.Adequate.affineSectionsMap_isIso`, the argument of
  [Stacks, Tag 06VP]);
* `H^i(U ×_S T, 𝓕)` vanishes by the Mayer–Vietoris induction over the quasi-compact opens of the
  quasi-compact and quasi-separated scheme `U ×_S T`
  (`Stacks.Adequate.prop_rightDerived_openFamilySections`), run with the Serre class of the
  module-valued functors that vanish at the base algebra `A`: on an affine open `W` of
  `U ×_S T` the module `𝓕(W)` vanishes because `W` is flat over `T` and `𝓕` is parasitic, and
  the higher cohomology of `𝓕` over `W` vanishes because `𝓕` is adequate
  ([Stacks, Tag 06VM] (3)).

The direct images are those of Tag 06VR: restriction along a functor `Φ` of the two sites,
with scalars transported along a natural morphism `ν`, where `Stacks.Adequate.IsBaseChangeAlong`
says that `Φ` and `ν` compute base change along `f`. In the source `(Sch/S)_τ` and `(Sch/T)_τ`
are slices of one category `Sch_α`; that is `Stacks.Adequate.BigSite.ofAmbient` at `S` and at
`T`, and there `Φ` is the slice pullback, which is continuous and is base change along `f`, so
the registered statement assumes nothing about the direct image. The general form, for arbitrary
chosen big `τ`-sites over `S` and over `T` and any `Φ` and `ν` which are base change along `f`, is
proved first. Both cover each of the five topologies `Zar`, `étale`, `smooth`, `syntomic` and
`fppf`.

## References

* [Stacks Project, Tag 06ZP](https://stacks.math.columbia.edu/tag/06ZP)
* [Stacks Project, Tag 06VR](https://stacks.math.columbia.edu/tag/06VR)
* [Stacks Project, Tag 06ZM](https://stacks.math.columbia.edu/tag/06ZM)
* [Stacks Project, Tag 07AG](https://stacks.math.columbia.edu/tag/07AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S T : Scheme.{u}} {B : BigSite τ S} {C : BigSite τ T}
  {f : T ⟶ S} {Φ : B.category ⥤ C.category}
  {ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S}

/-- **Flat base change.** If `Φ` computes base change along `f`, then `V ×_S T` is flat over `T`
for every object `V` of the site over `S` which is flat over `S`. -/
public theorem flat_toOver_obj_of_isBaseChangeAlong (hbc : IsBaseChangeAlong B C f Φ ν)
    {V : B.category} (hV : Flat (B.toOver.obj V).hom) : Flat (C.toOver.obj (Φ.obj V)).hom :=
  MorphismProperty.of_isPullback (P := @Flat) (hbc V) hV

variable [Φ.IsContinuous B.topology C.topology]

/-- **The direct image of a parasitic module is parasitic**: `(f_*𝓕)(V) = 𝓕(V ×_S T)`, and
`V ×_S T` is flat over `T` when `V` is flat over `S`. -/
public theorem isParasitic_directImage (hbc : IsBaseChangeAlong B C f Φ ν)
    (F : SheafOfModules.{u} C.structureSheaf) (hpar : IsParasitic T C.toOver F.val) :
    IsParasitic S B.toOver ((directImage.{u, u} B C Φ ν).obj F).val :=
  fun V hV => hpar (Φ.obj V) (flat_toOver_obj_of_isBaseChangeAlong hbc hV)

/-- **The cohomology of a parasitic adequate module over `T ×_S Spec A` vanishes**, for an
affine `Spec A` of the site over `S` which is flat over `S`, read at the base algebra `A` of the
module-valued functors `A' ↦ H^q(T ×_S Spec A', 𝓕)`.

This is the Mayer–Vietoris induction of the proof of [Stacks, Tag 06VR] over the quasi-compact
opens of the quasi-compact and quasi-separated scheme `T ×_S Spec A`, run with the Serre class
of the module-valued functors vanishing at `A`. Over an affine open `W` of `T ×_S Spec A` the
degree-zero term is `𝓕(W)`, which vanishes because `W` is open in `T ×_S Spec A`, hence flat
over `T`, and `𝓕` is parasitic; the higher terms vanish because `𝓕` is adequate. -/
public theorem isZero_evaluation_rightDerived_sectionsAlong_baseChangeFamily
    (hbc : IsBaseChangeAlong B C f Φ ν) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hpar : IsParasitic T C.toOver F.val)
    (A : CommRingCat.{u}) (a : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))
    (ha : Flat (B.toOver.obj ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))).hom) (q : ℕ) :
    IsZero ((PresheafOfModules.evaluation _ (op (baseAlgebraOp B A hA))).obj
      (((sectionsAlong C (baseChangeFamily B C Φ A a)
        (baseChangeFamilyRingMap B C Φ ν A a)).rightDerived q).obj F)) := by
  have := compactSpace_baseChangeBase A a hA hbc
  have := quasiSeparatedSpace_baseChangeBase A a hA hbc
  let E := PresheafOfModules.evaluation (AdequateFunctor.algebraRingDiagramOn
    (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)))
    (op (baseAlgebraOp B A hA))
  have hT : Flat (C.toOver.obj (baseChangeBase B C Φ A a hA)).hom :=
    flat_toOver_obj_of_isBaseChangeAlong hbc ha
  have htop := prop_rightDerived_openFamilySections C (baseChangeFamily B C Φ A a)
    (baseChangeBase B C Φ A a hA) (baseChangeFamilyπ B C Φ A a hA)
    (baseChangeFamilyRingMap B C Φ ν A a) E.kernel F
    (fun U hU k => by
      cases k with
      | zero =>
        refine IsZero.of_iso ?_ (E.mapIso ((Functor.rightDerivedZeroIsoSelf _).app F))
        refine (ModuleCat.isZero_iff_subsingleton).2 (hpar _ ?_)
        change Flat ((openFamilyOpen C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
          (baseChangeFamilyπ B C Φ A a hA) U (baseAlgebraOp B A hA)).ι ≫
            (C.toOver.obj ((baseChangeFamily B C Φ A a).obj (baseAlgebraOp B A hA))).hom)
        exact MorphismProperty.comp_mem @Flat _ _ inferInstance hT
      | succ k =>
        exact E.map_isZero (isZero_rightDerived_openFamilySections_of_isAffineOpen A a hA hbc F
          hF hU (k + 1) k.succ_pos))
    ⊤ (by simpa using isCompact_univ (X := (baseChangeBase B C Φ A a hA).left.obj)) q
  exact IsZero.of_iso htop (E.mapIso ((Functor.rightDerivedIsoOfNatIso
    (openFamilySectionsTopIso C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
      (baseChangeFamilyπ B C Φ A a hA) (baseChangeFamilyRingMap B C Φ ν A a)) q).app F).symm)

/-- **`R^q f_*𝓕` has no sections over an affine `Spec A` of the site flat over `S`**, for a
parasitic adequate `𝓕` and a quasi-compact and quasi-separated `f`.

`R^q f_*𝓕` is the sheafification of the presheaf `V ↦ H^q(V ×_S T, 𝓕)`
(`Stacks.Adequate.higherDirectImageIsoSheafification`), whose affine-section functor over
`Spec A` is adequate by the proof of [Stacks, Tag 06VR]; so the sheafification does not change its
sections over `Spec A` (`Stacks.Adequate.affineSectionsMap_isIso`), and those are
`H^q(T ×_S Spec A, 𝓕) = 0`
(`Stacks.Adequate.isZero_evaluation_rightDerived_sectionsAlong_baseChangeFamily`). -/
public theorem subsingleton_higherDirectImage_obj_affineSpecOver
    (hbc : IsBaseChangeAlong B C f Φ ν) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hpar : IsParasitic T C.toOver F.val)
    (A : CommRingCat.{u}) (a : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))
    (ha : Flat (B.toOver.obj ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))).hom) (q : ℕ) :
    Subsingleton (((higherDirectImage.{u, u} B C Φ ν q).obj F).val.obj
      (op ((affineSpecOver B A a).obj (baseAlgebraOp B A hA)))) := by
  let Pq := ((directImagePresheaf B C Φ ν).rightDerived q).obj F
  have : PreservesFiniteColimits (PresheafOfModules.pushforward.{u} (affineRingMap B A a)) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : (PresheafOfModules.pushforward.{u} (affineRingMap B A a)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (PresheafOfModules.pushforward.{u} (affineRingMap B A a)).Additive := ⟨rfl⟩
  have : (directImagePresheaf B C Φ ν ⋙
      PresheafOfModules.pushforward.{u} (affineRingMap B A a)).Additive := ⟨rfl⟩
  let e : directImagePresheaf B C Φ ν ⋙ PresheafOfModules.pushforward.{u} (affineRingMap B A a) ≅
      sectionsAlong C (baseChangeFamily B C Φ A a) (baseChangeFamilyRingMap B C Φ ν A a) :=
    Iso.refl _
  let eP : presheafAffineSectionFunctor.{u, u} B Pq A a ≅
      ((sectionsAlong C (baseChangeFamily B C Φ A a)
        (baseChangeFamilyRingMap B C Φ ν A a)).rightDerived q).obj F :=
    ((Functor.rightDerivedCompIso (directImagePresheaf B C Φ ν)
      (PresheafOfModules.pushforward.{u} (affineRingMap B A a)) q).app F).symm ≪≫
      (Functor.rightDerivedIsoOfNatIso e q).app F
  obtain ⟨J, hco, hcont, hM⟩ := affineAdequateSheafTopology B A a hA
  have hη := affineSectionsMap_isIso.{u, u} B Pq _ (toSheafification.{u, u} B Pq) inferInstance
    inferInstance A a J hco hcont hM
    ((isAdequate_rightDerived_sectionsAlong_baseChangeFamily hbc hqc hqs F hF A a hA q).of_iso eP)
  let E := PresheafOfModules.evaluation (AdequateFunctor.algebraRingDiagramOn
    (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)))
    (op (baseAlgebraOp B A hA))
  have h₀ : Subsingleton (E.obj (presheafAffineSectionFunctor.{u, u} B Pq A a)) :=
    (ModuleCat.isZero_iff_subsingleton).1
      ((isZero_evaluation_rightDerived_sectionsAlong_baseChangeFamily hbc hqc hqs F hF hpar A a hA
        ha q).of_iso (E.mapIso eP))
  have h₁ : Subsingleton (((sheafification.{u, u} B).obj Pq).val.obj
      (op ((affineSpecOver B A a).obj (baseAlgebraOp B A hA)))) :=
    (ConcreteCategory.bijective_of_isIso (E.map ((PresheafOfModules.pushforward
      (affineRingMap B A a)).map (toSheafification.{u, u} B Pq)))).2.subsingleton
  exact @Function.Surjective.subsingleton _ _ _ h₁
    (ConcreteCategory.bijective_of_isIso ((_root_.SheafOfModules.evaluation B.structureSheaf
      (op ((affineSpecOver B A a).obj (baseAlgebraOp B A hA)))).map
        ((higherDirectImageIsoSheafification B C Φ ν q).app F).inv)).2

/-- **`R^q f_*𝓕` has no sections over an affine object of the site flat over `S`**, for a
parasitic adequate `𝓕` and a quasi-compact and quasi-separated `f`: such an object is the
spectrum `Spec A` of its ring of global functions, read as an affine of the site, and
`Stacks.Adequate.subsingleton_higherDirectImage_obj_affineSpecOver` applies there. -/
public theorem subsingleton_higherDirectImage_obj_of_isAffine
    (hbc : IsBaseChangeAlong B C f Φ ν) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hpar : IsParasitic T C.toOver F.val) (U : B.category) [IsAffine U.left.obj]
    (hU : Flat (B.toOver.obj U).hom) (q : ℕ) :
    Subsingleton (((higherDirectImage.{u, u} B C Φ ν q).obj F).val.obj (op U)) := by
  let A : CommRingCat.{u} := Γ(U.left.obj, ⊤)
  let eU : U.left.obj ≅ Spec A := U.left.obj.isoSpec
  let a : Spec A ⟶ S := eU.inv ≫ U.hom.hom
  have hA : schemeSizeBelow B.cutoff (Spec A) :=
    (Scheme.size_congr eU.symm).trans_lt U.left.property
  let e₀ : (affineSpecOver B A a).obj (op (baseAlgebraInSite B A hA)) ≅ U :=
    Over.isoMk (ObjectProperty.isoMk _ eU.symm) (by
      apply ObjectProperty.hom_ext
      simp [affineSpecOver, a, baseAlgebraInSite]
      rfl)
  have ha :
      Flat (B.toOver.obj ((affineSpecOver B A a).obj (op (baseAlgebraInSite B A hA)))).hom := by
    have hw : (B.toOver.map e₀.hom).left ≫ (B.toOver.obj U).hom =
        (B.toOver.obj ((affineSpecOver B A a).obj (op (baseAlgebraInSite B A hA)))).hom :=
      Over.w (B.toOver.map e₀.hom)
    have : IsIso (B.toOver.map e₀.hom).left := (Over.forget S).map_isIso (B.toOver.map e₀.hom)
    rw [← hw]
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance hU
  exact @Equiv.subsingleton _ _ ((((higherDirectImage.{u, u} B C Φ ν q).obj F).val.presheaf ⋙
    CategoryTheory.forget AddCommGrpCat).mapIso e₀.op).toEquiv
    (subsingleton_higherDirectImage_obj_affineSpecOver hbc hqc hqs F hF hpar A a hA ha q)

/-- **Every higher direct image of a parasitic adequate module is parasitic**, along a
quasi-compact and quasi-separated morphism. `R^q f_*𝓕` is adequate by [Stacks, Tag 06VR] and has
no sections over the affine opens of `S`
(`Stacks.Adequate.subsingleton_higherDirectImage_obj_of_isAffine`), so it is parasitic by the
implication (5) ⇒ (2) of [Stacks, Tag 06ZM], `Stacks.Adequate.isParasitic_of_isAffine_cover`. -/
public theorem isParasitic_higherDirectImage
    (hbc : IsBaseChangeAlong B C f Φ ν) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hpar : IsParasitic T C.toOver F.val) (q : ℕ) :
    IsParasitic S B.toOver ((higherDirectImage.{u, u} B C Φ ν q).obj F).val :=
  isParasitic_of_isAffine_cover B _ (isAdequate_higherDirectImage B C f Φ ν F hF hqc hqs hbc q)
    (fun U : S.affineOpens => B.opensToBig.obj U)
    (fun U => by
      have : IsAffine (B.opensToBig.obj U).left.obj := U.2
      have hι : IsOpenImmersion (B.toOver.obj (B.opensToBig.obj U)).hom :=
        inferInstanceAs (IsOpenImmersion (U : S.Opens).ι)
      exact ⟨hι, U.2, subsingleton_higherDirectImage_obj_of_isAffine hbc hqc hqs F hF hpar _
        inferInstance q⟩)
    (iUnion_range_opensToBig_eq_univ B _ (iSup_affineOpens_eq_top S))

/-- **[Stacks, Tag 06ZP] for an arbitrary base change of chosen big sites.** Let `f : T ⟶ S` be a
quasi-compact and quasi-separated morphism of schemes and let `𝓕` be a parasitic adequate
`𝒪`-module on a chosen big `τ`-site over `T`, for `τ` any of the five topologies `Zar`, `étale`,
`smooth`, `syntomic`, `fppf`. Then the direct image `f_*𝓕` and every higher direct image
`R^i f_*𝓕` are parasitic adequate `𝒪`-modules on a chosen big `τ`-site over `S`.

The direct images are those of [Stacks, Tag 06VR]: `f_*` is restriction along the base-change
functor `Φ` of the two sites with scalars transported along the first projection `ν` of the fibre
squares (`Stacks.Adequate.directImage`), `hbc` says that `Φ` and `ν` are base change along `f`,
and `R^i f_*` is the `i`-th right derived functor of `f_*` (`Stacks.Adequate.higherDirectImage`).
Adequacy is Tag 06VR; parasiticity is `Stacks.Adequate.isParasitic_directImage` and
`Stacks.Adequate.isParasitic_higherDirectImage`. The tag is registered on
`Stacks.Adequate.isAdequate_and_isParasitic_directImage_ofAmbient`, the case of the two
localizations of one ambient big site, where the base change is constructed rather than given. -/
public theorem isAdequate_and_isParasitic_directImage
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hpar : IsParasitic T C.toOver F.val)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) (hbc : IsBaseChangeAlong B C f Φ ν) :
    (IsAdequate B ((directImage.{u, u} B C Φ ν).obj F) ∧
        IsParasitic S B.toOver ((directImage.{u, u} B C Φ ν).obj F).val) ∧
      ∀ i : ℕ, IsAdequate B ((higherDirectImage.{u, u} B C Φ ν i).obj F) ∧
        IsParasitic S B.toOver ((higherDirectImage.{u, u} B C Φ ν i).obj F).val :=
  ⟨⟨isAdequate_directImage B C f Φ ν F hF hqc hqs hbc, isParasitic_directImage hbc F hpar⟩,
    fun i => ⟨isAdequate_higherDirectImage B C f Φ ν F hF hqc hqs hbc i,
      isParasitic_higherDirectImage hbc hqc hqs F hF hpar i⟩⟩

/-! ### The two sites as localizations of one ambient big site -/

/-- The first projection `V ×_S T ⟶ V` of the slice base change along `f : T ⟶ S`, read in
schemes through a functor `G`. This is the natural morphism of schemes that
`Stacks.Adequate.IsBaseChangeAlong` asks for. -/
public def slicePullbackFst {D : Type*} [Category* D] [HasPullbacks D]
    (G : D ⥤ Scheme.{u}) {T S : D} (f : T ⟶ S) :
    Over.pullback f ⋙ Over.post G ⋙ Over.forget (G.obj T) ⟶
      Over.post G ⋙ Over.forget (G.obj S) where
  app V := G.map (pullback.fst V.hom f)
  naturality V W g := by
    change G.map ((Over.pullback f).map g).left ≫ G.map (pullback.fst W.hom f) =
      G.map (pullback.fst V.hom f) ≫ G.map g.left
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (pullback.lift_fst _ _ _)

/-- **The slice base change is base change.** Each component square of
`Stacks.Adequate.slicePullbackFst` is a fibre square, for a functor to schemes preserving
pullbacks. -/
public theorem isPullback_slicePullbackFst {D : Type*} [Category* D] [HasPullbacks D]
    (G : D ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G] {T S : D} (f : T ⟶ S)
    (V : Over S) :
    IsPullback ((slicePullbackFst G f).app V)
      ((Over.post G).obj ((Over.pullback f).obj V)).hom ((Over.post G).obj V).hom (G.map f) :=
  G.map_isPullback (IsPullback.of_hasPullback V.hom f)

section Ambient

variable (𝒮 : AlgebraicGeometry.BigSite.{u} τ) (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮)
  (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮) (f : T ⟶ S)

/-- **The base change functor `V ↦ V ×_S T`** from the localization of an ambient big site `𝒮` at
`S` to its localization at `T`: the slice pullback along `f`, read as a morphism of schemes below
the cutoff of `𝒮`. -/
public def ambientBaseChange :
    (BigSite.ofAmbient 𝒮 S hS).category ⥤ (BigSite.ofAmbient 𝒮 T hT).category :=
  Over.pullback (ObjectProperty.homMk (P := schemeSizeBelow (AlgebraicGeometry.cutoff τ 𝒮))
    (X := ⟨T, hT⟩) (Y := ⟨S, hS⟩) f)

/-- The first projection `V ×_S T ⟶ V` of `Stacks.Adequate.ambientBaseChange`, as a natural
morphism of schemes. -/
public def ambientBaseChangeFst :
    ambientBaseChange 𝒮 hS hT f ⋙ (BigSite.ofAmbient 𝒮 T hT).toOver ⋙ Over.forget T ⟶
      (BigSite.ofAmbient 𝒮 S hS).toOver ⋙ Over.forget S :=
  slicePullbackFst (ObjectProperty.ι (schemeSizeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
    (ObjectProperty.homMk (P := schemeSizeBelow (AlgebraicGeometry.cutoff τ 𝒮))
      (X := ⟨T, hT⟩) (Y := ⟨S, hS⟩) f)

/-- `Stacks.Adequate.ambientBaseChange` is continuous: both topologies are localizations of the
topology of the ambient site (`AlgebraicGeometry.overTopology_eq_siteTopology_over`), and pulling
back along a morphism of a site with fibre products is continuous for the localized
topologies. -/
public instance isContinuous_ambientBaseChange :
    (ambientBaseChange 𝒮 hS hT f).IsContinuous
      (BigSite.ofAmbient 𝒮 S hS).topology (BigSite.ofAmbient 𝒮 T hT).topology := by
  change (Over.pullback _).IsContinuous (AlgebraicGeometry.overTopology τ 𝒮 S hS)
    (AlgebraicGeometry.overTopology τ 𝒮 T hT)
  rw [AlgebraicGeometry.overTopology_eq_siteTopology_over,
    AlgebraicGeometry.overTopology_eq_siteTopology_over]
  infer_instance

/-- **`Stacks.Adequate.ambientBaseChange` is base change along `f`**: with its first projection
`Stacks.Adequate.ambientBaseChangeFst` it is `Stacks.Adequate.IsBaseChangeAlong`, because the
inclusion of the schemes below the cutoff into all schemes preserves fibre products. -/
public theorem isBaseChangeAlong_ambientBaseChange :
    IsBaseChangeAlong (BigSite.ofAmbient 𝒮 S hS) (BigSite.ofAmbient 𝒮 T hT) f
      (ambientBaseChange 𝒮 hS hT f) (ambientBaseChangeFst 𝒮 hS hT f) :=
  fun V => isPullback_slicePullbackFst
    (ObjectProperty.ι (schemeSizeBelow (AlgebraicGeometry.cutoff τ 𝒮))) _ V

/-- **[Stacks, Tag 06ZP].** Let `f : T ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes and let `𝓕` be a parasitic adequate `𝒪_T`-module on `(Sch/T)_τ`, for `τ` any of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. Then the pushforward `f_*𝓕` and every
higher direct image `R^i f_*𝓕` are parasitic adequate `𝒪_S`-modules on `(Sch/S)_τ`.

`(Sch/S)_τ` and `(Sch/T)_τ` are the localizations at `S` and at `T` of one ambient big `τ`-site
`𝒮`, as they are in the source (`Stacks.Adequate.BigSite.ofAmbient`; by
`Stacks.Adequate.BigSite.exists_eq_ofAmbient` every chosen big site is one). `f_*` is the direct
image of [Stacks, Tag 06VR] along the base change `V ↦ V ×_S T`
(`Stacks.Adequate.ambientBaseChange`) with its first projection, and `R^i f_*` is its `i`-th right
derived functor; nothing is assumed about either, since
`Stacks.Adequate.isContinuous_ambientBaseChange` and
`Stacks.Adequate.isBaseChangeAlong_ambientBaseChange` supply what Tag 06VR needs. The proof is
`Stacks.Adequate.isAdequate_and_isParasitic_directImage`. -/
@[stacks 06ZP]
public theorem isAdequate_and_isParasitic_directImage_ofAmbient
    (F : SheafOfModules.{u} (BigSite.ofAmbient 𝒮 T hT).structureSheaf)
    (hF : IsAdequate (BigSite.ofAmbient 𝒮 T hT) F)
    (hpar : IsParasitic T (BigSite.ofAmbient 𝒮 T hT).toOver F.val)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) :
    (IsAdequate (BigSite.ofAmbient 𝒮 S hS)
        ((directImage.{u, u} (BigSite.ofAmbient 𝒮 S hS) (BigSite.ofAmbient 𝒮 T hT)
          (ambientBaseChange 𝒮 hS hT f) (ambientBaseChangeFst 𝒮 hS hT f)).obj F) ∧
      IsParasitic S (BigSite.ofAmbient 𝒮 S hS).toOver
        ((directImage.{u, u} (BigSite.ofAmbient 𝒮 S hS) (BigSite.ofAmbient 𝒮 T hT)
          (ambientBaseChange 𝒮 hS hT f) (ambientBaseChangeFst 𝒮 hS hT f)).obj F).val) ∧
      ∀ i : ℕ, IsAdequate (BigSite.ofAmbient 𝒮 S hS)
          ((higherDirectImage.{u, u} (BigSite.ofAmbient 𝒮 S hS) (BigSite.ofAmbient 𝒮 T hT)
            (ambientBaseChange 𝒮 hS hT f) (ambientBaseChangeFst 𝒮 hS hT f) i).obj F) ∧
        IsParasitic S (BigSite.ofAmbient 𝒮 S hS).toOver
          ((higherDirectImage.{u, u} (BigSite.ofAmbient 𝒮 S hS) (BigSite.ofAmbient 𝒮 T hT)
            (ambientBaseChange 𝒮 hS hT f) (ambientBaseChangeFst 𝒮 hS hT f) i).obj F).val :=
  isAdequate_and_isParasitic_directImage F hF hpar hqc hqs
    (isBaseChangeAlong_ambientBaseChange 𝒮 hS hT f)

end Ambient

end Stacks.Adequate

end
