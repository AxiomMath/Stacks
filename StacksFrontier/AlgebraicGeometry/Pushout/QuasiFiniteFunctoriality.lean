module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.CartesianDiagram
public import StacksFrontier.AlgebraicGeometry.Pushout.Coproduct
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Separated quasi-finite morphisms between pushouts along a closed immersion and an integral map

Let `Y ← Z → X` be the span of a pushout situation of [Stacks Project, Tag 0ECI] and let
`Y' ← Z' → X'` be a span over it whose two squares are cartesian and whose three vertical
morphisms `g, h, f` are separated and locally quasi-finite.  The primed span is again such a
situation (`AlgebraicGeometry.inducedSituation`), so both pushouts exist, and the universal
property gives a morphism `Y' ⨿_{Z'} X' ⟶ Y ⨿_Z X`.  This file shows that this morphism is
separated and locally quasi-finite, and that the two squares

    Y' ⟶ Y' ⨿_{Z'} X' ⟵ X'
    ↓          ↓          ↓
    Y  ⟶  Y ⨿_Z X   ⟵  X

are cartesian.  This is [Stacks Project, Tag 0ECK].

## Main definitions

* `AlgebraicGeometry.pushoutMap` is the induced morphism of pushouts.

## Main results

* `AlgebraicGeometry.pushoutMap_isSeparated`,
  `AlgebraicGeometry.pushoutMap_locallyOfFiniteType` and
  `AlgebraicGeometry.pushoutMap_locallyQuasiFinite` are part (2) of Tag 0ECK.
* `AlgebraicGeometry.pushoutMap_left_isPullback` and
  `AlgebraicGeometry.pushoutMap_right_isPullback` are part (3) of Tag 0ECK.
* `MilnorPatching.finiteType_and_isPushout_of_fibreProduct` is the ring-theoretic heart: a
  comparison map between two ring fibre products whose two sides are of finite type is itself of
  finite type and exhibits both sides as its base changes.

Part (1) of Tag 0ECK — the existence of the two pushouts — is
`AlgebraicGeometry.primedFiber_preimage_subset_affine` in
`StacksFrontier.AlgebraicGeometry.Pushout.CartesianDiagram`, which is what completes the primed
situation; applying `AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral` of
[Stacks Project, Tag 0E25] to the two situations produces the two pushouts.

## Implementation notes

Stacks terminology includes local finite type in "locally quasi-finite", which Mathlib separates
into `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`; both are
concluded.

Everything about the induced morphism over an affine open `U` of `Y ⨿_Z X` and an affine open `V`
of `Y' ⨿_{Z'} X'` above it is read off from one computation: the sections of each pushout over
such an open form a fibre product of rings by [Stacks Project, Tag 0E25], and the comparison
between the two fibre products is the canonical map of Milnor patching, so that
`MilnorPatching.finiteType_and_isPushout_of_fibreProduct` applies.  That lemma is
[Stacks Project, Tag 08KQ] for finite type together with
`MilnorPatching.pullback_baseChange`.  Local finite type is then the affine-local criterion, and
the two cartesian squares follow by testing on affine charts.

Local quasi-finiteness is not affine-local in the same way, so it is proved pointwise from the
criterion that every fibre is discrete.  Over the image of `Y` the fibre is the image of a fibre
of `g`, by part (3); over the open complement of that image the canonical map from `X` is an
isomorphism (`AlgebraicGeometry.pushoutInl_isIso_morphismRestrict`), so the restriction of the
induced morphism is, up to that isomorphism, a restriction of `f`.

Separatedness descends along the surjective universally closed morphism from the coproduct
`Y' ⨿ X'` ([Stacks Project, Tag 09MQ] and
`AlgebraicGeometry.pushoutCoprodDesc_universallyClosed`), because the composite of the induced
morphism with that morphism factors as `coprod.map g f` followed by the coproduct morphism of the
lower pushout, and both of those are separated.

## References

* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace MilnorPatching

/-- **The ring-theoretic heart of [Stacks Project, Tag 0ECK].**  Let `R = B ×_A A'` be a ring
fibre product along a surjection `A' → A`, let `D` and `C'` be algebras over `B` and `A'` whose
base changes to `A` agree, and let `P = D ×_C C'` be the resulting fibre product.  If `D` is of
finite type over `B` and `C'` is of finite type over `A'`, then `P` is of finite type over `R`,
and both `D` and `C'` are the base changes of `P` along `R → B` and `R → A'`.

The finite-type assertion is the first clause of [Stacks Project, Tag 08KQ],
`MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction`, and the two base-change
assertions are `MilnorPatching.pullback_baseChange`.  Both are stated for the literal fibre
product `RingHom.pullback`, so the two abstract fibre products are first identified with the
literal ones by the uniqueness of pullbacks. -/
theorem finiteType_and_isPushout_of_fibreProduct
    {A A' B D C' C R P : CommRingCat.{u}}
    {toBase : B ⟶ A} {surjection : A' ⟶ A} {BtoD : B ⟶ D} {A'toC' : A' ⟶ C'}
    {AtoC : A ⟶ C} {DtoC : D ⟶ C} {C'toC : C' ⟶ C}
    {toB : R ⟶ B} {toA' : R ⟶ A'} {comparison : R ⟶ P} {PtoD : P ⟶ D} {PtoC' : P ⟶ C'}
    (hSource : IsPullback toB toA' toBase surjection)
    (hTarget : IsPullback PtoD PtoC' DtoC C'toC)
    (hD : IsPushout BtoD toBase DtoC AtoC)
    (hC' : IsPushout A'toC' surjection C'toC AtoC)
    (hsurj : Function.Surjective surjection.hom)
    (hw₁ : toB ≫ BtoD = comparison ≫ PtoD) (hw₂ : toA' ≫ A'toC' = comparison ≫ PtoC')
    (hft₁ : BtoD.hom.FiniteType) (hft₂ : A'toC'.hom.FiniteType) :
    comparison.hom.FiniteType ∧ IsPushout comparison toA' PtoC' A'toC' ∧
      IsPushout comparison toB PtoD BtoD := by
  let base : RingFibreProduct.Situation toBase.hom surjection.hom
      (RingHom.ker surjection.hom) := ⟨hsurj, rfl⟩
  let sourceCone := base.pullbackCone
  let sourcePullback := IsPullback.of_isLimit base.pullbackConeIsLimit
  let targetCone := CommRingCat.pullbackCone DtoC C'toC
  let targetLimit := CommRingCat.pullbackConeIsLimit DtoC C'toC
  let targetPullback := IsPullback.of_isLimit targetLimit
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC.hom C'toC.hom :=
    RingHom.codRestrict ((BtoD.hom.comp base.pullbackCone.fst.hom).prod
        (A'toC'.hom.comp base.pullbackCone.snd.hom))
      (RingHom.pullback DtoC.hom C'toC.hom) (fun x ↦ by
        show DtoC.hom (BtoD.hom (base.pullbackCone.fst.hom x)) =
          C'toC.hom (A'toC'.hom (base.pullbackCone.snd.hom x))
        have hd : DtoC.hom.comp BtoD.hom = AtoC.hom.comp toBase.hom :=
          congrArg CommRingCat.Hom.hom hD.w
        have hc : C'toC.hom.comp A'toC'.hom = AtoC.hom.comp surjection.hom :=
          congrArg CommRingCat.Hom.hom hC'.w
        calc
          _ = AtoC.hom (toBase.hom (base.pullbackCone.fst.hom x)) := DFunLike.congr_fun hd _
          _ = AtoC.hom (surjection.hom (base.pullbackCone.snd.hom x)) := congrArg AtoC.hom
            (DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
          _ = _ := (DFunLike.congr_fun hc _).symm)
  have hglue := (MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction
    toBase.hom surjection.hom (RingHom.ker surjection.hom) base BtoD.hom A'toC'.hom AtoC.hom
    DtoC.hom C'toC.hom
    (MilnorPatching.ringPushout_of_isPushout _ _ _ _ hD)
    (MilnorPatching.ringPushout_of_isPushout _ _ _ _ hC')).1
  let eSource := hSource.isoIsPullback _ _ sourcePullback
  let eTarget := hTarget.isoIsPullback _ _ targetPullback
  have hSourceInvFst : eSource.inv ≫ toB = sourceCone.fst :=
    hSource.isoIsPullback_inv_fst _ _ sourcePullback
  have hSourceInvSnd : eSource.inv ≫ toA' = sourceCone.snd :=
    hSource.isoIsPullback_inv_snd _ _ sourcePullback
  have hTargetHomFst : eTarget.hom ≫ targetCone.fst = PtoD :=
    hTarget.isoIsPullback_hom_fst _ _ targetPullback
  have hTargetHomSnd : eTarget.hom ≫ targetCone.snd = PtoC' :=
    hTarget.isoIsPullback_hom_snd _ _ targetPullback
  have hpullfst : sourceCone.fst ≫ BtoD = CommRingCat.ofHom toD' ≫ targetCone.fst := by
    apply CommRingCat.hom_ext
    ext x
    rfl
  have hpullsnd : sourceCone.snd ≫ A'toC' = CommRingCat.ofHom toD' ≫ targetCone.snd := by
    apply CommRingCat.hom_ext
    ext x
    rfl
  have hfst : (eSource.inv ≫ comparison ≫ eTarget.hom) ≫ targetCone.fst =
      CommRingCat.ofHom toD' ≫ targetCone.fst := by
    simp only [Category.assoc]
    rw [hTargetHomFst, ← hw₁, ← Category.assoc, hSourceInvFst]
    exact hpullfst
  have hsnd : (eSource.inv ≫ comparison ≫ eTarget.hom) ≫ targetCone.snd =
      CommRingCat.ofHom toD' ≫ targetCone.snd := by
    simp only [Category.assoc]
    rw [hTargetHomSnd, ← hw₂, ← Category.assoc, hSourceInvSnd]
    exact hpullsnd
  have hfactor : eSource.inv ≫ comparison ≫ eTarget.hom = CommRingCat.ofHom toD' :=
    PullbackCone.IsLimit.hom_ext targetLimit hfst hsnd
  have hcomposite : (eSource.inv ≫ comparison ≫ eTarget.hom).hom.FiniteType := by
    rw [hfactor]
    exact hglue.mpr ⟨hft₁, hft₂⟩
  have hmid := (RingHom.finiteType_respectsIso.cancel_left_isIso eSource.inv
    (comparison ≫ eTarget.hom)).mp hcomposite
  have hp := MilnorPatching.pullback_baseChange base BtoD.hom A'toC'.hom AtoC.hom DtoC.hom
    C'toC.hom hD hC' toD' (fun _ => rfl) (fun _ => rfl)
  have hmap : CommRingCat.ofHom toD' ≫ eTarget.inv = eSource.inv ≫ comparison :=
    (congrArg (fun k => k ≫ eTarget.inv) hfactor).symm.trans (by
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have hTargetFst : targetCone.fst = eTarget.inv ≫ PtoD := by
    rw [← hTargetHomFst, Iso.inv_hom_id_assoc]
  have hTargetSnd : targetCone.snd = eTarget.inv ≫ PtoC' := by
    rw [← hTargetHomSnd, Iso.inv_hom_id_assoc]
  refine ⟨(RingHom.finiteType_respectsIso.cancel_right_isIso comparison eTarget.hom).mp hmid,
    ?_, ?_⟩
  · exact hp.2.of_iso eSource.symm eTarget.symm (Iso.refl _) (Iso.refl _)
      hmap (by
        show sourceCone.snd ≫ 𝟙 _ = eSource.inv ≫ toA'
        simpa only [Category.comp_id] using hSourceInvSnd.symm)
      (by
        show targetCone.snd ≫ 𝟙 _ = eTarget.inv ≫ PtoC'
        simpa only [Category.comp_id] using hTargetSnd)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  · exact hp.1.of_iso eSource.symm eTarget.symm (Iso.refl _) (Iso.refl _)
      hmap (by
        show sourceCone.fst ≫ 𝟙 _ = eSource.inv ≫ toB
        simpa only [Category.comp_id] using hSourceInvFst.symm)
      (by
        show targetCone.fst ≫ 𝟙 _ = eTarget.inv ≫ PtoD
        simpa only [Category.comp_id] using hTargetFst)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

end MilnorPatching

namespace AlgebraicGeometry

/-- A pushout square of the rings of global sections of four affine schemes is a cartesian square
of those schemes. -/
public theorem isPullback_of_isPushout_appTop
    {P X Y S : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine S]
    {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPushout f.appTop g.appTop p.appTop q.appTop) : IsPullback p q f g :=
  (H.op.flip.map Scheme.Spec).of_iso P.isoSpec.symm X.isoSpec.symm
    Y.isoSpec.symm S.isoSpec.symm (Scheme.isoSpec_inv_naturality p)
    (Scheme.isoSpec_inv_naturality q) (Scheme.isoSpec_inv_naturality f)
    (Scheme.isoSpec_inv_naturality g)

/-- A pushout square of the rings of sections over four compatible affine opens is a cartesian
square of the corresponding open subschemes. -/
private theorem isPullback_resLE_of_isPushout_appLE
    {P X Y S : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (UP : P.Opens) (UX : X.Opens) (UY : Y.Opens) (US : S.Opens)
    (hp : UP ≤ p ⁻¹ᵁ UX) (hq : UP ≤ q ⁻¹ᵁ UY)
    (hf : UX ≤ f ⁻¹ᵁ US) (hg : UY ≤ g ⁻¹ᵁ US)
    (hP : IsAffineOpen UP) (hX : IsAffineOpen UX)
    (hY : IsAffineOpen UY) (hS : IsAffineOpen US)
    (H : IsPushout (f.appLE US UX hf) (g.appLE US UY hg)
      (p.appLE UX UP hp) (q.appLE UY UP hq)) :
    IsPullback (p.resLE UX UP hp) (q.resLE UY UP hq)
      (f.resLE US UX hf) (g.resLE US UY hg) := by
  have : IsAffine UP.toScheme := hP
  have : IsAffine UX.toScheme := hX
  have : IsAffine UY.toScheme := hY
  have : IsAffine US.toScheme := hS
  refine isPullback_of_isPushout_appTop
    (H.of_iso US.topIso.symm UX.topIso.symm UY.topIso.symm UP.topIso.symm ?_ ?_ ?_ ?_) <;>
    simp only [Scheme.Hom.resLE_app_top, Iso.symm_hom, Iso.inv_hom_id_assoc]

/-- A square of schemes is cartesian as soon as every point of the lower left corner has an open
neighbourhood over which it becomes cartesian. -/
public theorem isPullback_of_forall_exists_restrict
    {P X Y S : Scheme.{u}} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (H : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      IsPullback (p ∣_ V) ((p ⁻¹ᵁ V).ι ≫ q) (V.ι ≫ f) g) :
    IsPullback p q f g := by
  classical
  choose V hx hV using H
  let cov : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => (V x).toScheme)
    (fun x => (V x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  apply Scheme.isPullback_of_openCover p q f g cov
  intro x
  show IsPullback (Limits.pullback.snd p (V x).ι)
    (Limits.pullback.fst p (V x).ι ≫ q) ((V x).ι ≫ f) g
  let e := (isPullback_morphismRestrict p (V x)).flip.isoPullback
  apply (hV x).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [e]
  · simp [e]
  · simp
  · simp

/-- A square of schemes whose two vertical morphisms are affine is cartesian as soon as the
induced squares of sections over affine opens are pushout squares of rings. -/
private theorem isPullback_of_affine_appLE
    {P X Y S : Scheme.{u}} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom p] [IsAffineHom g]
    (H : ∀ (U : S.Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V →
      ∀ hVU : V ≤ f ⁻¹ᵁ U,
      ∃ hq : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ (g ⁻¹ᵁ U),
        IsPushout (f.appLE U V hVU) (g.app U) (p.app V)
          (q.appLE (g ⁻¹ᵁ U) (p ⁻¹ᵁ V) hq)) :
    IsPullback p q f g := by
  apply isPullback_of_forall_exists_restrict
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU₀⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have hVU : V ≤ f ⁻¹ᵁ U := hVU₀
  obtain ⟨hq, hsq⟩ := H U hU V hV hVU
  have hres := isPullback_resLE_of_isPushout_appLE
    (p ⁻¹ᵁ V) V (g ⁻¹ᵁ U) U le_rfl hq hVU le_rfl
    (hV.preimage p) hV (hU.preimage g) hU (by simpa only [Scheme.Hom.appLE_eq_app] using hsq)
  have hres' : IsPullback (p ∣_ V) (q.resLE (g ⁻¹ᵁ U) (p ⁻¹ᵁ V) hq)
      (f.resLE U V hVU) (g ∣_ U) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hres
  refine ⟨V, hxV, ?_⟩
  simpa only [Scheme.Hom.resLE_comp_ι] using hres'.paste_vert (isPullback_morphismRestrict g U)

/-- In a cartesian square whose right-hand morphism restricts to an isomorphism over an open `U`,
the left-hand morphism restricts over `U` to a morphism that is locally quasi-finite as soon as
the morphism opposite to it is. -/
private theorem locallyQuasiFinite_morphismRestrict_of_isPullback
    {P X Y S : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback p q f g) [LocallyQuasiFinite q]
    (U : S.Opens) [IsIso (g ∣_ U)] : LocallyQuasiFinite (f ∣_ U) := by
  have hres := Scheme.Hom.isPullback_resLE H (US := U)
    (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl
    (UY := p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) rfl
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hres
  have hiso : IsIso (p.resLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) inf_le_left) :=
    hres.isIso_fst_of_isIso
  have hcomp : LocallyQuasiFinite
      (p.resLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) inf_le_left ≫ (f ∣_ U)) := by
    rw [show p.resLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) inf_le_left ≫ (f ∣_ U) = _
      from hres.w]
    infer_instance
  rw [show (f ∣_ U) = CategoryTheory.inv
    (p.resLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) inf_le_left) ≫
      (p.resLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U)) inf_le_left ≫ (f ∣_ U)) by simp]
  infer_instance

/-- If the restriction of `f` over an open `U` is locally quasi-finite, then the fibre of `f`
over a point of `U` is discrete. -/
private theorem isDiscrete_preimage_singleton_of_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [LocallyQuasiFinite (f ∣_ U)]
    (x : U) : _root_.IsDiscrete (f ⁻¹' {x.1}) := by
  have hs := ((f ∣_ U).isDiscrete_preimage_singleton x).image
    (f ⁻¹ᵁ U).ι.isEmbedding.toIsInducing
  have he : (f ⁻¹ᵁ U).ι '' ((f ∣_ U) ⁻¹' {x}) = f ⁻¹' {x.1} := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨z, hz, rfl⟩
      exact (morphismRestrict_base_coe f U z).symm.trans (congrArg Subtype.val hz)
    · intro y hy
      have hyU : f y ∈ U := by
        rw [show f y = x.1 from hy]
        exact x.2
      exact ⟨⟨y, hyU⟩, Subtype.ext ((morphismRestrict_base_coe f U ⟨y, hyU⟩).trans hy), rfl⟩
  exact he ▸ hs

/-- Affine charts of a cartesian square of schemes give a pushout square of the rings of
sections, the open in the fibre product being the intersection of the two inverse images. -/
private theorem isPushout_sections_of_isPullback
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g)
    (US : Z.Opens) (hUS : IsAffineOpen US)
    (UT : Y.Opens) (hUT : IsAffineOpen UT) (hUTle : UT ≤ g ⁻¹ᵁ US)
    (UX : X.Opens) (hUX : IsAffineOpen UX) (hUXle : UX ≤ f ⁻¹ᵁ US)
    (UP : P.Opens) (hUP : UP = fst ⁻¹ᵁ UX ⊓ snd ⁻¹ᵁ UT) :
    IsPushout
      (f.appLE US UX hUXle) (g.appLE US UT hUTle)
      (fst.appLE UX UP (by rw [hUP]; exact inf_le_left))
      (snd.appLE UT UP (by rw [hUP]; exact inf_le_right)) := by
  have hres := Scheme.Hom.isPullback_resLE H hUTle hUXle hUP
  have : IsAffine UX.toScheme := hUX
  have : IsAffine UT.toScheme := hUT
  have : IsAffine US.toScheme := hUS
  refine (isPushout_appTop_of_isPullback hres).of_iso US.topIso UX.topIso UT.topIso UP.topIso
    ?_ ?_ ?_ ?_ <;>
    simp only [Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The map on sections over an open whose inverse image is a given open is the map on sections
over the whole inverse image, transported along that equality of opens. -/
private theorem appLE_eq_app_comp_eqToHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : f ⁻¹ᵁ U = V) :
    f.appLE U V (by rw [← e]) = f.app U ≫ eqToHom (congrArg (fun W => Γ(X, W)) e) := by
  subst V
  simp [Scheme.Hom.appLE]

/-- If a square of schemes commutes, the preimage of an open `V` of the lower right corner, which
lies over `U`, lies over the preimage of `U` in the upper left corner. -/
private theorem preimage_le_preimage_preimage_of_comp_eq
    {X' X Z' Z : Scheme.{u}} {f : X' ⟶ X} {a : X ⟶ Z} {a' : X' ⟶ Z'} {m : Z' ⟶ Z}
    (w : f ≫ a = a' ≫ m) {U : Z.Opens} {V : Z'.Opens} (hVU : V ≤ m ⁻¹ᵁ U) :
    a' ⁻¹ᵁ V ≤ f ⁻¹ᵁ (a ⁻¹ᵁ U) := by
  intro x hx
  have h : m (a' x) ∈ U := hVU hx
  change a (f x) ∈ U
  rwa [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]

/-- **Stacks Project, Tag 0ECK.** The morphism `Y' ⨿_{Z'} X' ⟶ Y ⨿_Z X` induced by a cartesian
diagram over a pushout situation, obtained from the universal property of the upper pushout. -/
noncomputable def pushoutMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    pushoutScheme (inducedSituation s d) ⟶ pushoutScheme s :=
  (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.desc
    (d.f ≫ pushoutInl s) (d.g ≫ pushoutInr s) (by
      rw [← Category.assoc, d.left_isPullback.w, Category.assoc,
        (pushoutAlongClosedImmersionAndIntegral s).isPushout.w,
        ← Category.assoc, ← d.right_isPullback.w, Category.assoc])

/-- The pullback square of sections of a pushout situation over an open `U`, expressed with
`appLE` over the preimages of `U`. -/
private theorem pushoutStructureSheaf_isPullback_appLE
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (U : (pushoutScheme s).Opens)
    (he : s.i ⁻¹ᵁ (pushoutInl s ⁻¹ᵁ U) = s.j ⁻¹ᵁ (pushoutInr s ⁻¹ᵁ U)) :
    IsPullback ((pushoutInr s).appLE U (pushoutInr s ⁻¹ᵁ U) le_rfl)
      ((pushoutInl s).appLE U (pushoutInl s ⁻¹ᵁ U) le_rfl)
      (s.j.appLE (pushoutInr s ⁻¹ᵁ U) (s.j ⁻¹ᵁ (pushoutInr s ⁻¹ᵁ U)) le_rfl)
      (s.i.appLE (pushoutInl s ⁻¹ᵁ U) (s.j ⁻¹ᵁ (pushoutInr s ⁻¹ᵁ U)) (by rw [← he])) := by
  have hi := appLE_eq_app_comp_eqToHom s.i _ _ he
  simpa only [Scheme.Hom.appLE_eq_app, hi] using pushoutStructureSheaf_isPullback s U

/-- The joint content of [Stacks Project, Tag 0ECK] over a pair of affine opens: the map on
sections induced by `AlgebraicGeometry.pushoutMap` over an affine open `V` of the upper pushout
above an affine open `U` of the lower one is of finite type, and each of its two base changes —
to the sections of `X` and to the sections of `Y` — is a pushout square of rings. -/
private theorem pushoutMap_appLE_properties
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s)
    (U : (pushoutScheme s).Opens) (hU : IsAffineOpen U)
    (V : (pushoutScheme (inducedSituation s d)).Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ (pushoutMap s d) ⁻¹ᵁ U) :
    let Ux := pushoutInl s ⁻¹ᵁ U
    let Uy := pushoutInr s ⁻¹ᵁ U
    let Vx := pushoutInl (inducedSituation s d) ⁻¹ᵁ V
    let Vy := pushoutInr (inducedSituation s d) ⁻¹ᵁ V
    ∃ hx : Vx ≤ d.f ⁻¹ᵁ Ux, ∃ hy : Vy ≤ d.g ⁻¹ᵁ Uy,
      ((pushoutMap s d).appLE U V hVU).hom.FiniteType ∧
      IsPushout ((pushoutMap s d).appLE U V hVU) ((pushoutInl s).app U)
        ((pushoutInl (inducedSituation s d)).app V) (d.f.appLE Ux Vx hx) ∧
      IsPushout ((pushoutMap s d).appLE U V hVU) ((pushoutInr s).app U)
        ((pushoutInr (inducedSituation s d)).app V) (d.g.appLE Uy Vy hy) := by
  classical
  let s' := inducedSituation s d
  let a := pushoutInl s
  let b := pushoutInr s
  let a' := pushoutInl s'
  let b' := pushoutInr s'
  let Ux := a ⁻¹ᵁ U
  let Uy := b ⁻¹ᵁ U
  let Uz := s.j ⁻¹ᵁ Uy
  let Vx := a' ⁻¹ᵁ V
  let Vy := b' ⁻¹ᵁ V
  let Vz := s'.j ⁻¹ᵁ Vy
  have hUx : IsAffineOpen Ux := hU.preimage a
  have hUy : IsAffineOpen Uy := hU.preimage b
  have hUz : IsAffineOpen Uz := hUy.preimage s.j
  have hVx : IsAffineOpen Vx := hV.preimage a'
  have hVy : IsAffineOpen Vy := hV.preimage b'
  have he : s.i ⁻¹ᵁ Ux = Uz :=
    congrArg (fun k : s.Z ⟶ pushoutScheme s ↦ k ⁻¹ᵁ U)
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  have he' : s'.i ⁻¹ᵁ Vx = Vz :=
    congrArg (fun k : s'.Z ⟶ pushoutScheme s' ↦ k ⁻¹ᵁ V)
      (pushoutAlongClosedImmersionAndIntegral s').isPushout.w
  have hfa : d.f ≫ a = a' ≫ pushoutMap s d := by simp [a, a', pushoutMap]
  have hgb : d.g ≫ b = b' ≫ pushoutMap s d := by simp [b, b', pushoutMap]
  have hVxle : Vx ≤ d.f ⁻¹ᵁ Ux := preimage_le_preimage_preimage_of_comp_eq hfa hVU
  have hVyle : Vy ≤ d.g ⁻¹ᵁ Uy := preimage_le_preimage_preimage_of_comp_eq hgb hVU
  have hUzle : Uz ≤ s.j ⁻¹ᵁ Uy := le_rfl
  have hVzh : Vz ≤ d.h ⁻¹ᵁ Uz :=
    preimage_le_preimage_preimage_of_comp_eq d.right_isPullback.w.symm hVyle
  have hRightOpen : Vz = d.j' ⁻¹ᵁ Vy ⊓ d.h ⁻¹ᵁ Uz :=
    le_antisymm (le_inf (fun _ hz => hz) hVzh) fun _ hz => hz.1
  have hLeftOpen : Vz = d.i' ⁻¹ᵁ Vx ⊓ d.h ⁻¹ᵁ Uz := by
    refine le_antisymm (le_inf ?_ hVzh) fun z hz => ?_
    · intro z hz
      show z ∈ s'.i ⁻¹ᵁ Vx
      rw [he']
      exact hz
    · show z ∈ Vz
      rw [← he']
      exact hz.1
  have hD : IsPushout (d.g.appLE Uy Vy hVyle) (s.j.appLE Uy Uz hUzle)
      (d.j'.appLE Vy Vz (fun _ hz => hz)) (d.h.appLE Uz Vz hVzh) :=
    isPushout_sections_of_isPullback d.right_isPullback Uy hUy Uz hUz hUzle
      Vy hVy hVyle Vz hRightOpen
  have hC' : IsPushout (d.f.appLE Ux Vx hVxle) (s.i.appLE Ux Uz (by rw [← he]))
      (d.i'.appLE Vx Vz (by rw [← he'])) (d.h.appLE Uz Vz hVzh) :=
    isPushout_sections_of_isPullback d.left_isPullback Ux hUx Uz hUz (by rw [← he])
      Vx hVx hVxle Vz hLeftOpen
  have hSource := pushoutStructureSheaf_isPullback_appLE s U he
  have hTarget := pushoutStructureSheaf_isPullback_appLE s' V he'
  have hsurjection : Function.Surjective (s.i.appLE Ux Uz (by rw [← he])).hom := by
    have hsurj' : Function.Surjective ((s.i.appLE Ux (s.i ⁻¹ᵁ Ux) le_rfl).hom) := by
      simpa only [Scheme.Hom.appLE_eq_app] using s.i.app_surjective Ux hUx
    exact (s.i.appLE_congr le_rfl rfl he (fun k => Function.Surjective k.hom)).mp hsurj'
  have hBcompat : b.appLE U Uy le_rfl ≫ d.g.appLE Uy Vy hVyle =
      (pushoutMap s d).appLE U V hVU ≫ b'.appLE V Vy le_rfl := by
    simp [Scheme.Hom.appLE_comp_appLE, pushoutMap, b, b']
  have hAcompat : a.appLE U Ux le_rfl ≫ d.f.appLE Ux Vx hVxle =
      (pushoutMap s d).appLE U V hVU ≫ a'.appLE V Vx le_rfl := by
    simp [Scheme.Hom.appLE_comp_appLE, pushoutMap, a, a']
  obtain ⟨hft, hleft, hright⟩ :=
    MilnorPatching.finiteType_and_isPushout_of_fibreProduct hSource hTarget hD hC'
    hsurjection hBcompat hAcompat (LocallyOfFiniteType.finiteType_appLE d.g hUy hVy hVyle)
    (LocallyOfFiniteType.finiteType_appLE d.f hUx hVx hVxle)
  refine ⟨hVxle, hVyle, hft, ?_, ?_⟩
  · simpa only [s', a, a', Ux, Vx, Scheme.Hom.appLE_eq_app] using hleft
  · simpa only [s', b, b', Uy, Vy, Scheme.Hom.appLE_eq_app] using hright

/-- **Stacks Project, Tag 0ECK, part (3).** The square relating the two canonical maps from `X`
and `X'` to the two pushouts is cartesian. -/
@[stacks 0ECK "part (3), the X square"]
theorem pushoutMap_left_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    IsPullback (pushoutInl (inducedSituation s d)) d.f (pushoutMap s d) (pushoutInl s) := by
  apply isPullback_of_affine_appLE
  intro U hU V hV hVU
  obtain ⟨hx, -, -, hleft, -⟩ := pushoutMap_appLE_properties s d U hU V hV hVU
  exact ⟨hx, hleft⟩

/-- **Stacks Project, Tag 0ECK, part (3).** The square relating the two canonical maps from `Y`
and `Y'` to the two pushouts is cartesian. -/
@[stacks 0ECK "part (3), the Y square"]
theorem pushoutMap_right_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    IsPullback (pushoutInr (inducedSituation s d)) d.g (pushoutMap s d) (pushoutInr s) := by
  apply isPullback_of_affine_appLE
  intro U hU V hV hVU
  obtain ⟨-, hy, -, -, hright⟩ := pushoutMap_appLE_properties s d U hU V hV hVU
  exact ⟨hy, hright⟩

/-- **Stacks Project, Tag 0ECK, part (2).** The induced morphism of pushouts is separated. -/
@[stacks 0ECK "part (2), separated"]
instance pushoutMap_isSeparated
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    IsSeparated (pushoutMap s d) := by
  have hcm : pushoutCoprodDesc (inducedSituation s d) ≫ pushoutMap s d =
      coprod.map d.g d.f ≫ pushoutCoprodDesc s := by
    apply coprod.hom_ext <;> simp [pushoutCoprodDesc, pushoutMap]
  have hmsep : IsSeparated (coprod.map d.g d.f) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsSeparated) d.g d.f inferInstance inferInstance
  have hcomp : IsSeparated (pushoutCoprodDesc (inducedSituation s d) ≫ pushoutMap s d) := by
    rw [hcm]
    infer_instance
  let source : Over (pushoutScheme s) :=
    Over.mk (pushoutCoprodDesc (inducedSituation s d) ≫ pushoutMap s d)
  let target : Over (pushoutScheme s) := Over.mk (pushoutMap s d)
  let e : source ⟶ target :=
    Over.homMk (pushoutCoprodDesc (inducedSituation s d)) (by simp [source, target])
  have : Surjective e.left := by simpa [e] using pushoutCoprodDesc_surjective (inducedSituation s d)
  have : UniversallyClosed e.left := by
    simpa [e] using pushoutCoprodDesc_universallyClosed (inducedSituation s d)
  have : IsSeparated source.hom := hcomp
  exact isSeparated_of_surjective_universallyClosed e

/-- **Stacks Project, Tag 0ECK, part (2).** The induced morphism of pushouts is locally of finite
type. -/
@[stacks 0ECK "part (2), locally of finite type"]
instance pushoutMap_locallyOfFiniteType
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    LocallyOfFiniteType (pushoutMap s d) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (pushoutScheme s).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pushoutMap s d x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    ((pushoutScheme (inducedSituation s d)).isBasis_affineOpens).exists_subset_of_mem_open
      hxU ((pushoutMap s d) ⁻¹ᵁ U).isOpen
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU,
    (pushoutMap_appLE_properties s d U hU V hV hVU).choose_spec.choose_spec.1⟩

/-- **Stacks Project, Tag 0ECK, part (2).** The induced morphism of pushouts has locally
quasi-finite fibres. -/
@[stacks 0ECK "part (2), locally quasi-finite fibres"]
instance pushoutMap_locallyQuasiFinite
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    LocallyQuasiFinite (pushoutMap s d) := by
  classical
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro p
  by_cases hp : p ∈ Set.range (pushoutInr s)
  · obtain ⟨y, rfl⟩ := hp
    have he : pushoutInr (inducedSituation s d) '' (d.g ⁻¹' {y}) =
        pushoutMap s d ⁻¹' {pushoutInr s y} := by
      simpa only [Set.image_singleton] using Scheme.image_preimage_eq_of_isPullback
        (pushoutMap_right_isPullback s d).flip {y}
    rw [← he]
    exact (d.g.isDiscrete_preimage_singleton y).image
      (pushoutInr (inducedSituation s d)).isEmbedding.toIsInducing
  · have hc : IsClosed (Set.range (pushoutInr s)) := by
      simpa only [Set.image_univ] using (pushoutInr s).isClosedMap Set.univ isClosed_univ
    let U : (pushoutScheme s).Opens := ⟨(Set.range (pushoutInr s))ᶜ, hc.isOpen_compl⟩
    have hU : pushoutInr s ⁻¹ᵁ U = ⊥ := by
      ext y
      simp [U]
    have : IsIso (pushoutInl s ∣_ U) := pushoutInl_isIso_morphismRestrict s U hU
    have : LocallyQuasiFinite (pushoutMap s d ∣_ U) :=
      locallyQuasiFinite_morphismRestrict_of_isPullback (pushoutMap_left_isPullback s d) U
    exact isDiscrete_preimage_singleton_of_morphismRestrict (pushoutMap s d) U ⟨p, hp⟩

end AlgebraicGeometry

end
