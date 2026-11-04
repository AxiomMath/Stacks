module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedFibreCover
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# Base change for pushforward on small étale sites

Let `f : X ⟶ S` be a morphism of schemes. An étale `X`-scheme `U` whose structure morphism to
`S` factors as `U ⟶ V ⟶ S` with `V ⟶ S` étale and `U ⟶ V` flat, quasi-compact and with
geometrically connected fibres computes the inverse image: the sections of `f⁻¹G` over `U` are
the sections of `G` over `V`. When such `U` cover every object of `X_étale` the inverse image
functor is therefore determined objectwise by `G`, and two consequences follow: the inverse
image commutes with arbitrary products, and inverse image after pushforward around a cartesian
square agrees with pushforward after inverse image.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleInverseImageSections` — the canonical comparison
  `G(V) ⟶ (f⁻¹G)(U)` attached to a morphism `U ⟶ V ×_S X` of the small étale site of `X`.
* `Stacks.EtaleCohomology.SmallEtaleSectionsComparisonIsIso` — the assertion that this
  comparison is bijective whenever `U ⟶ V` is flat, quasi-compact and has geometrically
  connected fibres.
* `Stacks.EtaleCohomology.HasFlatConnectedFactorization` — the étale `X`-schemes admitting
  such a factorization.
* `Stacks.EtaleCohomology.smallEtaleSetBaseChange` — the canonical base change map
  `f⁻¹ g_* ⟶ h_* e⁻¹` of a commutative square, on sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.hasEnoughObjects_hasFlatConnectedFactorization` — **Tag 0EY5** read
  on the small étale site: for `f` flat, locally of finite presentation and with geometrically
  reduced fibres, the objects with such a factorization cover every object.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_etaleLocalFactorization` —
  **Tag 0EZX**: in a cartesian square with `f` flat and the covering condition, the base
  change map is an isomorphism on every sheaf of sets.

Tags 0EYR, 0EYS and 0EZZ, which build on these, are proved with no residual hypothesis in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional`.

## Implementation notes

The section comparison being bijective under the stated hypotheses on `U ⟶ V` is Tag 0A3H,
read through the identification of the restriction of `f⁻¹G` to `U_étale` with the pullback of
the restriction of `G` to `V_étale` of Tag 03EF. Neither is available in the form needed here,
so it is carried as a declared hypothesis: as
`Stacks.EtaleCohomology.SmallEtaleSectionsComparisonIsIso`, and, in the form the
cartesian square needs it, as the hypothesis `hlocal` of Tag 0EZX.

The globalization step common to both is that a map of sheaves bijective on sections over a
family of objects covering every object is an isomorphism, which is Tag 0H6Y in the form of
`CategoryTheory.Presheaf.isLocallyInjective_of_hasEnoughObjects_injective` and its surjective
counterpart.

Flatness of `U ⟶ V`, which Tag 0EZX obtains from flatness of `f` by More on Flatness, Tag
05B9, is proved here as `Stacks.EtaleCohomology.flat_of_etale_over_flat`: the induced morphism
`U ⟶ X ×_S V` is étale, and `U ⟶ V` is that morphism followed by a flat projection.

## References

* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0EZZ](https://stacks.math.columbia.edu/tag/0EZZ)
* [Stacks Project, Tag 0EYR](https://stacks.math.columbia.edu/tag/0EYR)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
* [Stacks Project, Tag 0EY5](https://stacks.math.columbia.edu/tag/0EY5)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

-- NO `smallEtaleInverseImageSections` HERE. The copy that used to sit on this line stated and
-- proved exactly `Stacks.EtaleCohomology.smallEtaleInverseImageSections`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SubmersiveSections.lean`:191), which is now
-- public, `@[expose]`, in this same namespace, and imported.

/-- **Stacks Project, Tag 0A3H**, in the localized form in which it is used: for every sheaf
of sets `G` on `S_étale` and every morphism `a : U ⟶ V ×_S X` of the small étale site of `X`
whose induced morphism `U ⟶ V` is flat, quasi-compact and has geometrically connected fibres,
the canonical comparison `G(V) ⟶ (f⁻¹G)(U)` is bijective. -/
def SmallEtaleSectionsComparisonIsIso {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V),
    Flat (a.left ≫ pullback.fst V.hom f) →
      QuasiCompact (a.left ≫ pullback.fst V.hom f) →
        GeometricallyConnected (a.left ≫ pullback.fst V.hom f) →
          IsIso (smallEtaleInverseImageSections.{u, v} f G a)

section Factorization

/-- The morphism `U ⟶ V ×_S X` of the small étale site of `X` determined by a factorization
`U ⟶ V ⟶ S` of the structure morphism of `U`. -/
def smallEtaleFactorizationHom {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Etale} {V : S.Etale}
    (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f) :
    U ⟶ (smallEtaleBaseChange f).obj V :=
  MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤)
    (pullback.lift k U.hom hk) (pullback.lift_snd k U.hom hk)

@[simp]
lemma smallEtaleFactorizationHom_left_fst {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Etale}
    {V : S.Etale} (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f) :
    (smallEtaleFactorizationHom f k hk).left ≫ pullback.fst V.hom f = k :=
  pullback.lift_fst k U.hom hk

/-- A morphism `k : U ⟶ V` over a flat `f : X ⟶ S`, with `U ⟶ X` and `V ⟶ S` étale, is flat:
the induced morphism `U ⟶ X ×_S V` is étale, hence flat, and `k` is that morphism followed by
the flat projection `X ×_S V ⟶ V`. -/
lemma flat_of_etale_over_flat {A B C D : Scheme.{u}} (x : A ⟶ B) (f : B ⟶ D) (y : C ⟶ D)
    (k : A ⟶ C) [Flat f] [Etale x] [Etale y] (hk : k ≫ y = x ≫ f) : Flat k := by
  let q : A ⟶ pullback f y := pullback.lift x k hk.symm
  have hqf : q ≫ pullback.fst f y = x := pullback.lift_fst ..
  have : Etale (q ≫ pullback.fst f y) := by
    rw [hqf]; infer_instance
  have : Etale q := Etale.of_comp q (pullback.fst f y)
  have hqk : k = q ≫ pullback.snd f y := (pullback.lift_snd _ _ _).symm
  rw [hqk]
  infer_instance

end Factorization

section LocalSections

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The sections of a sheaf of sets on the small étale site of `S` over a fixed étale
`S`-scheme. -/
private abbrev sectionsOver (V : S.Etale) :
    Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)) ⥤ Type (max (u + 1) v) :=
  sheafToPresheaf (smallEtaleTopology S) (Type (max (u + 1) v)) ⋙
    (evaluation S.Etaleᵒᵖ (Type (max (u + 1) v))).obj (op V)

/-- Restriction of sections along a morphism of the small étale site, naturally in the
sheaf. -/
private def sectionsRestrict {U V : S.Etale} (a : U ⟶ V) :
    sectionsOver.{u, v} V ⟶ sectionsOver.{u, v} U where
  app G := G.obj.map a.op
  naturality G H φ := by
    ext x
    exact congrArg (fun q => q x) (φ.hom.naturality a.op).symm

/-- Sections of the pushforward over `V` are the sections over the base change of `V`. -/
private def pushforwardSectionsOver (V : S.Etale) :
    (smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology X) ⋙
      sectionsOver.{u, v} V ≅
    sectionsOver.{u, v} ((smallEtaleBaseChange f).obj V) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro F G φ; rfl)

/-- The comparison of `Stacks.EtaleCohomology.smallEtaleInverseImageSections`, assembled as a
natural transformation of functors in the sheaf. -/
private def localSectionsComparison {U : X.Etale} {V : S.Etale}
    (a : U ⟶ (smallEtaleBaseChange f).obj V) :
    sectionsOver.{u, v} V ⟶ smallEtaleInverseImage.{u, v} f ⋙ sectionsOver.{u, v} U :=
  (Functor.leftUnitor (sectionsOver.{u, v} V)).inv ≫
    Functor.whiskerRight (smallEtaleInverseImageAdjunction.{u, v} f).unit
      (sectionsOver.{u, v} V) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (smallEtaleInverseImage.{u, v} f)
      (pushforwardSectionsOver.{u, v} f V).hom ≫
    Functor.whiskerLeft (smallEtaleInverseImage.{u, v} f) (sectionsRestrict.{u, v} a)

private lemma localSectionsComparison_app {U : X.Etale} {V : S.Etale}
    (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) :
    (localSectionsComparison.{u, v} f a).app G = smallEtaleInverseImageSections.{u, v} f G a :=
  rfl

/-- Under the declared form of Tag 0A3H, a factorization `U ⟶ V ⟶ S` with `U ⟶ V` flat,
quasi-compact and with geometrically connected fibres identifies the sections of `f⁻¹G` over
`U` with the sections of `G` over `V`, naturally in `G`. -/
private def localSectionsIso (hA3H : SmallEtaleSectionsComparisonIsIso.{u, v} f)
    {U : X.Etale} {V : S.Etale} (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    [Flat k] [QuasiCompact k] [GeometricallyConnected k] :
    smallEtaleInverseImage.{u, v} f ⋙ sectionsOver.{u, v} U ≅ sectionsOver.{u, v} V := by
  have hA := fun G => hA3H G (smallEtaleFactorizationHom f k hk)
  simp only [smallEtaleFactorizationHom_left_fst] at hA
  have : ∀ G, IsIso ((localSectionsComparison.{u, v} f
      (smallEtaleFactorizationHom f k hk)).app G) := fun G =>
    hA G inferInstance inferInstance inferInstance
  have : IsIso (localSectionsComparison.{u, v} f (smallEtaleFactorizationHom f k hk)) :=
    NatIso.isIso_of_isIso_app _
  exact (asIso (localSectionsComparison.{u, v} f (smallEtaleFactorizationHom f k hk))).symm

end LocalSections

section EnoughObjects

/-- An étale `X`-scheme whose structure morphism to `S` factors through an étale `S`-scheme by
a flat quasi-compact morphism with geometrically connected fibres. -/
def HasFlatConnectedFactorization {X S : Scheme.{u}} (f : X ⟶ S) : ObjectProperty X.Etale :=
  fun U => ∃ (V : S.Etale) (k : U.left ⟶ V.left),
    k ≫ V.hom = U.hom ≫ f ∧ Flat k ∧ QuasiCompact k ∧ GeometricallyConnected k

/-- A scheme smooth over a reduced scheme is reduced: reducedness is a smooth-local property
of schemes, and the source together with the base is a smooth covering of the base. -/
@[sga "3 XV 6.9" "(a)"]
private lemma isReduced_of_smooth {A B : Scheme.{u}} (p : A ⟶ B) [Smooth p] [IsReduced B] :
    IsReduced A := by
  let : ObjectProperty.IsLocal (fun Z : Scheme.{u} => IsReduced Z)
      (Scheme.precoverage @Smooth.{u}) := AlgebraicGeometry.isReduced_isLocal_smooth
  let W : Bool → Scheme.{u} := fun b => match b with | true => A | false => B
  let q : ∀ b, W b ⟶ B := fun b => match b with | true => p | false => 𝟙 B
  have hq : Presieve.ofArrows W q ∈ Scheme.precoverage @Smooth.{u} B := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @Smooth.{u})]
    refine ⟨fun y => ⟨false, y, by simp [q, W]⟩, fun b => ?_⟩
    cases b with
    | true => simpa [q, W]
    | false => infer_instance
  exact ObjectProperty.IsLocal.component (P := fun Z : Scheme.{u} => IsReduced Z)
    (K := Scheme.precoverage @Smooth.{u}) hq p
    (Presieve.ofArrows.mk (Y := W) (f := q) true) ‹IsReduced B›

/-- Precomposing a morphism with geometrically reduced fibres by a smooth morphism again has
geometrically reduced fibres: a geometric fibre of the composite is smooth over the
corresponding geometric fibre of the original morphism, which is reduced. -/
private lemma geometricallyReduced_comp_smooth {A X S : Scheme.{u}} (p : A ⟶ X) (f : X ⟶ S)
    [Smooth p] [GeometricallyReduced f] : GeometricallyReduced (p ≫ f) := by
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  let : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) y
      (pullback.fst f y) (pullback.snd f y) (.of_hasPullback _ _)
  let : Smooth (pullback.snd p (pullback.fst f y)) := inferInstance
  exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
    (pullbackRightPullbackFstIso f y p)
    (isReduced_of_smooth (pullback.snd p (pullback.fst f y)))

/-- **Stacks Project, Tag 0EY5**, read on the small étale site: for `f : X ⟶ S` flat, locally
of finite presentation and with geometrically reduced fibres, every object of `X_étale` has an
étale covering by objects admitting a flat quasi-compact factorization with geometrically
connected fibres through an étale `S`-scheme. -/
theorem hasEnoughObjects_hasFlatConnectedFactorization {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    (smallEtaleTopology X).HasEnoughObjects (HasFlatConnectedFactorization f) := by
  classical
  intro U
  let : LocallyOfFinitePresentation (U.hom ≫ f) := inferInstance
  let : Flat (U.hom ≫ f) := inferInstance
  let : GeometricallyReduced (U.hom ≫ f) := geometricallyReduced_comp_smooth U.hom f
  obtain ⟨C, hC⟩ := exists_etaleCover_factors_geometricallyConnected (U.hom ≫ f)
  choose Sᵢ hᵢ gᵢ hEtale hFlat hFP hConn _hRed hFac using fun i : C.I₀ => hC i
  let U' : C.I₀ → X.Etale := fun i => by
    letI : Etale (C.f i) := C.map_prop i
    exact Scheme.Etale.mk (C.f i ≫ U.hom)
  let a : ∀ i, U' i ⟶ U := fun i => MorphismProperty.Over.homMk (C.f i) rfl
  refine ⟨C.I₀, U', a, ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨j, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp C.mem₀).1 x
    exact Set.mem_iUnion.mpr ⟨j, ⟨y, hy⟩⟩
  · intro i
    refine ⟨Scheme.Etale.mk (hᵢ i), gᵢ i, ?_, hFlat i, (hFP i).quasiCompact, hConn i⟩
    change gᵢ i ≫ hᵢ i = (C.f i ≫ U.hom) ≫ f
    simpa only [Category.assoc] using hFac i

end EnoughObjects

section Products

variable {X S : Scheme.{u}} (f : X ⟶ S)

end Products

section BaseChangeSquare

variable {X Y S T : Scheme.{u}}

/-- The canonical base change map `f⁻¹ g_* ⟶ h_* e⁻¹` on sheaves of sets of the small étale
sites of a commutative square: the mate, under the two inverse-image/direct-image adjunctions,
of the identification of the two composite direct images around the square. -/
def smallEtaleSetBaseChange (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) :
    (smallEtaleBaseChange g).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) ⋙
      smallEtaleInverseImage.{u, v} f ⟶
    smallEtaleInverseImage.{u, v} e ⋙
      (smallEtaleBaseChange h).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y) :=
  (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
      (smallEtaleInverseImageAdjunction.{u, v} f)).symm
    ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
      (eqToIso (congrArg (fun k : Y ⟶ S ↦
        (smallEtaleBaseChange k).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w)).hom ≫
      (smallEtalePushforwardCompIso.{u, v} h f).inv)

/-- Over a flat morphism, a quasi-compact factorization with geometrically connected fibres
through an étale object is automatically flat, so it witnesses
`Stacks.EtaleCohomology.HasFlatConnectedFactorization`. -/
theorem hasFlatConnectedFactorization_of_quasiCompact (f : X ⟶ S) [Flat f] {U : X.Etale}
    (V : S.Etale) (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f) [QuasiCompact k]
    [GeometricallyConnected k] : HasFlatConnectedFactorization f U :=
  ⟨V, k, hk, flat_of_etale_over_flat U.hom f V.hom k hk, ‹_›, ‹_›⟩

/-- The covering condition of Tag 0EZX supplies enough objects with a flat quasi-compact
factorization with geometrically connected fibres: the covering families are reindexed by the
points of the object they cover, which is a type in the morphism universe of the site. -/
theorem hasEnoughObjects_of_etaleLocalFactorization (f : X ⟶ S) [Flat f]
    (hcover : ∀ U : X.Etale,
      ∃ (ι : Type (u + 1)) (U' : ι → X.Etale) (a : ∀ i, U' i ⟶ U)
        (V : ι → S.Etale) (k : ∀ i, (U' i).left ⟶ (V i).left),
        Sieve.ofArrows U' a ∈ smallEtaleTopology X U ∧
          ∀ i, k i ≫ (V i).hom = (U' i).hom ≫ f ∧
            QuasiCompact (k i) ∧ GeometricallyConnected (k i)) :
    (smallEtaleTopology X).HasEnoughObjects (HasFlatConnectedFactorization f) := by
  classical
  intro U
  obtain ⟨ι, U', a, V, k, hcov, hfactor⟩ := hcover U
  have hcoverSet : ⋃ i, Set.range (a i).left = Set.univ :=
    (ofArrows_mem_smallEtaleTopology_iff a).mp hcov
  have hpoint (x : U.left) : ∃ i, ∃ y : (U' i).left, (a i).left y = x := by
    have hx : x ∈ ⋃ i, Set.range (a i).left := by
      rw [hcoverSet]
      exact Set.mem_univ x
    simpa only [Set.mem_iUnion, Set.mem_range] using hx
  let iOf : U.left → ι := fun x => Classical.choose (hpoint x)
  let yOf : ∀ x : U.left, (U' (iOf x)).left := fun x =>
    Classical.choose (Classical.choose_spec (hpoint x))
  have hyOf (x : U.left) : (a (iOf x)).left (yOf x) = x :=
    Classical.choose_spec (Classical.choose_spec (hpoint x))
  refine ⟨U.left, fun x => U' (iOf x), fun x => a (iOf x), ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    exact Set.mem_iUnion.mpr ⟨x, ⟨yOf x, hyOf x⟩⟩
  · intro x
    obtain ⟨hkx, hqc, hgc⟩ := hfactor (iOf x)
    exact hasFlatConnectedFactorization_of_quasiCompact f (V (iOf x)) (k (iOf x)) hkx

/-- The globalization step, stated directly in terms of enough objects: if the étale
`X`-schemes carrying a flat quasi-compact factorization with geometrically connected fibres
cover every object of `X_étale` and the base change map is bijective on sections over them,
then it is an isomorphism. -/
theorem isIso_smallEtaleSetBaseChange_of_hasEnoughObjects (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (hEnough : (smallEtaleTopology X).HasEnoughObjects (HasFlatConnectedFactorization f))
    (hlocal : ∀ ⦃U : X.Etale⦄, HasFlatConnectedFactorization f U →
      Function.Bijective
        (((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F).hom.app (op U))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  let φ := (smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F
  have hInj : Presheaf.IsLocallyInjective (smallEtaleTopology X) φ.hom :=
    Presheaf.isLocallyInjective_of_hasEnoughObjects_injective (smallEtaleTopology X) φ.hom
      hEnough fun {_} hU => (hlocal hU).injective
  have hSurj : Presheaf.IsLocallySurjective (smallEtaleTopology X) φ.hom :=
    Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective (smallEtaleTopology X) φ.hom
      hEnough fun {_} hU => (hlocal hU).surjective
  exact (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨hInj, hSurj⟩

/-- **Stacks Project, Tag 0EZX.** In a cartesian square of schemes with `f : X ⟶ S` flat, if
every object of the small étale site of `X` has an étale covering whose members factor through
an étale `S`-scheme by a quasi-compact morphism with geometrically connected fibres, then the
canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets
`F` on the small étale site of `T`. -/
@[stacks 0EZX "The chain of four identifications of the source's first paragraph -- that the
sections of `f⁻¹ g_* F` and of `h_* e⁻¹ F` over an object with such a factorization are both
the sections of `F` over `V ×_S T`, compatibly with the base change map -- rests on Tag 0A3H
(used twice, once for `f` and once for `e`) read through Tag 03EF, and is carried as the
declared hypothesis `hlocal`. What is supplied here is the source's second paragraph: the
covering condition gives enough objects with a flat such factorization, flatness coming from
`f` by `hasFlatConnectedFactorization_of_quasiCompact`, and a map of sheaves bijective on
sections over a family of objects covering every object is an isomorphism."]
theorem isIso_smallEtaleSetBaseChange_of_etaleLocalFactorization (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g) [Flat f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (hcover : ∀ U : X.Etale,
      ∃ (ι : Type (u + 1)) (U' : ι → X.Etale) (a : ∀ i, U' i ⟶ U)
        (V : ι → S.Etale) (k : ∀ i, (U' i).left ⟶ (V i).left),
        Sieve.ofArrows U' a ∈ smallEtaleTopology X U ∧
          ∀ i, k i ≫ (V i).hom = (U' i).hom ≫ f ∧
            QuasiCompact (k i) ∧ GeometricallyConnected (k i))
    (hlocal : ∀ ⦃U : X.Etale⦄, HasFlatConnectedFactorization f U →
      Function.Bijective
        (((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F).hom.app (op U))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) :=
  isIso_smallEtaleSetBaseChange_of_hasEnoughObjects f h e g sq F
    (hasEnoughObjects_of_etaleLocalFactorization f hcover) hlocal

end BaseChangeSquare

section ConnectedFibreOpens

/-- If every nonempty open of a fibre of `f : X ⟶ S` is connected, then every nonempty fibre
of the composite of an open immersion `j : Z ⟶ X` with `f` is connected: that fibre is the
open subscheme of the fibre of `f` cut out by the image of `j`. -/
private lemma connectedSpace_fiber_comp_of_isOpenImmersion
    {X S Z : Scheme.{u}} (f : X ⟶ S) (j : Z ⟶ X) [IsOpenImmersion j]
    (hconn : ∀ s : S, ∀ W : (f.fiber s).Opens, W ≠ ⊥ → ConnectedSpace W.toScheme)
    {s : S} (hne : Nonempty ((j ≫ f).fiber s)) :
    ConnectedSpace ((j ≫ f).fiber s) := by
  let m : pullback j (f.fiberι s) ⟶ f.fiber s := pullback.snd j (f.fiberι s)
  let W : (f.fiber s).Opens := m.opensRange
  have hW : W ≠ ⊥ := by
    intro hw
    obtain ⟨z⟩ := hne
    have hz : (m ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) j).inv z) :
        f.fiber s) ∈ W := ⟨_, rfl⟩
    rw [hw] at hz
    exact hz
  exact (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) j).hom.homeomorph
    |>.connectedSpace_iff.mp (m.isoOpensRange.hom.homeomorph.connectedSpace_iff.mpr
      (hconn s W hW))

/-- A field isomorphic to a separably closed field is separably closed. -/
private lemma isSepClosed_of_ringEquiv {K L : Type u} [Field K] [Field L]
    (e : K ≃+* L) (hK : IsSepClosed K) : IsSepClosed L := by
  refine ⟨fun p hp => ?_⟩
  have hq : (p.map e.symm.toRingHom).Separable :=
    (Polynomial.separable_map e.symm.toRingHom).mpr hp
  simpa [Polynomial.map_map] using
    (hK.splits_of_separable (p.map e.symm.toRingHom) hq).map e.toRingHom

/-- Let `j : Z ⟶ X` be an open immersion, let `f : X ⟶ S` have separably closed residue
fields and all nonempty opens of its fibres connected, and let `k : Z ⟶ V` present an open
`V` of an open `A ⊆ S` as the image of `Z`. Then `k` has geometrically connected fibres:
each fibre of `k` is a nonempty open of a fibre of `f`, hence connected, and the residue
fields of `V` are separably closed. -/
private lemma geometricallyConnected_of_isOpenImmersion_image
    {X S Z : Scheme.{u}} (f : X ⟶ S) (j : Z ⟶ X) [IsOpenImmersion j]
    (hsep : ∀ s : S, IsSepClosed (S.residueField s))
    (hconn : ∀ s : S, ∀ W : (f.fiber s).Opens, W ≠ ⊥ → ConnectedSpace W.toScheme)
    (A : S.Opens) (q : Z ⟶ A.toScheme) (hq : q ≫ A.ι = j ≫ f)
    (V : A.toScheme.Opens) (hV : (V : Set A.toScheme) = Set.range q)
    (k : Z ⟶ V.toScheme) (hk : k ≫ V.ι = q) : GeometricallyConnected k := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro v
  let a : A.toScheme := V.ι v
  let s : S := A.ι a
  have hsrange : s ∈ Set.range (j ≫ f) := by
    obtain ⟨z, hz⟩ : a ∈ Set.range q := by rw [← hV]; exact v.2
    refine ⟨z, ?_⟩
    change (j ≫ f) z = A.ι (V.ι v)
    rw [← hq]
    simpa only [Scheme.Hom.comp_apply] using congrArg A.ι hz
  obtain ⟨z, hzs⟩ := hsrange
  have hne : Nonempty ((j ≫ f).fiber s) :=
    ⟨((j ≫ f).fiberHomeo s).symm ⟨z, by simpa using hzs⟩⟩
  let eA : S.residueField s ≃+* A.toScheme.residueField a :=
    (asIso (A.ι.residueFieldMap a)).commRingCatIsoToRingEquiv
  let eV : A.toScheme.residueField a ≃+* V.toScheme.residueField v :=
    (asIso (V.ι.residueFieldMap v)).commRingCatIsoToRingEquiv
  let : IsSepClosed (V.toScheme.residueField v) :=
    isSepClosed_of_ringEquiv eV (isSepClosed_of_ringEquiv eA (hsep s))
  refine (AlgebraicGeometry.geometricallyConnected_iff_connectedSpace
    (V.toScheme.residueField v) (k.fiberToSpecResidueField v)).2 ?_
  have hsets : k.base ⁻¹' {v} = (j ≫ f).base ⁻¹' {s} := by
    ext w
    change k w = v ↔ (j ≫ f) w = s
    rw [← hq, ← hk]
    simp only [Scheme.Hom.comp_apply]
    exact (V.ι.isOpenEmbedding.injective.eq_iff).symm.trans
      (A.ι.isOpenEmbedding.injective.eq_iff).symm
  exact ((k.fiberHomeo v).trans ((Homeomorph.setCongr hsets).trans
    ((j ≫ f).fiberHomeo s).symm)).connectedSpace_iff.mpr
    (connectedSpace_fiber_comp_of_isOpenImmersion f j hconn hne)

/-- Under the hypotheses of Tag 0EZZ, every point of an étale `X`-scheme `U` is in the image
of an open subscheme `W ⟶ X` mapping to `U`, whose structure morphism to `S` factors through
an étale `S`-scheme by a quasi-compact morphism with geometrically connected fibres. -/
private theorem exists_isOpenImmersion_connectedFactorization_at
    {X S : Scheme.{u}} (f : X ⟶ S) (hopen : IsOpenMap f)
    (hsep : ∀ s : S, IsSepClosed (S.residueField s))
    (hsplit : ∀ U : X.Etale, IsAffine U.left →
      ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (j : ∀ a, V a ⟶ X)
        (_ : ∀ a, IsOpenImmersion (j a)) (i : U.left ≅ ∐ V),
        i.hom ≫ Sigma.desc j = U.hom)
    (hconn : ∀ s : S, ∀ W : (f.fiber s).Opens, W ≠ ⊥ → ConnectedSpace W.toScheme)
    (U : X.Etale) (x : U.left) :
    ∃ (W : Scheme.{u}) (w : W) (jW : W ⟶ X) (aW : W ⟶ U.left) (V : S.Etale)
      (k : W ⟶ V.left), IsOpenImmersion jW ∧ aW ≫ U.hom = jW ∧ aW w = x ∧
        k ≫ V.hom = jW ≫ f ∧ QuasiCompact k ∧ GeometricallyConnected k := by
  obtain ⟨i₀, y₀, hy₀⟩ := U.left.affineCover.exists_eq x
  let u₀ : U.left.affineCover.X i₀ ⟶ U.left := U.left.affineCover.f i₀
  let U₀ : X.Etale := Scheme.Etale.mk (u₀ ≫ U.hom)
  obtain ⟨n, V₀, j₀, hj₀, iso, hfac⟩ := hsplit U₀ (Scheme.isAffine_affineCover _ _)
  obtain ⟨a₀, zLift, hzLift⟩ := (sigmaOpenCover V₀).exists_eq (iso.hom y₀)
  change V₀ a₀ at zLift
  have hz₀ : Sigma.ι V₀ a₀ zLift = iso.hom y₀ := by
    rw [← sigmaOpenCover_f V₀ a₀]; exact hzLift
  obtain ⟨i₁, y₁, hy₁⟩ := (V₀ a₀).affineCover.exists_eq zLift
  let v₀ : (V₀ a₀).affineCover.X i₁ ⟶ V₀ a₀ := (V₀ a₀).affineCover.f i₁
  let q₀ : (V₀ a₀).affineCover.X i₁ ⟶ S := v₀ ≫ j₀ a₀ ≫ f
  obtain ⟨i₂, y₂, hy₂⟩ := S.affineCover.exists_eq (q₀ y₁)
  let A : S.Opens := (S.affineCover.f i₂).opensRange
  have hyA : q₀ y₁ ∈ A := by
    change q₀ y₁ ∈ (S.affineCover.f i₂).opensRange
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨y₂, hy₂⟩
  let P : ((V₀ a₀).affineCover.X i₁).Opens := q₀ ⁻¹ᵁ A
  obtain ⟨i₃, y₃, hy₃⟩ := P.toScheme.affineCover.exists_eq ⟨y₁, hyA⟩
  let W : Scheme.{u} := P.toScheme.affineCover.X i₃
  let b₃ : W ⟶ P.toScheme := P.toScheme.affineCover.f i₃
  let b₁ : P.toScheme ⟶ (V₀ a₀).affineCover.X i₁ := P.ι
  let jW : W ⟶ X := b₃ ≫ b₁ ≫ v₀ ≫ j₀ a₀
  let : IsOpenImmersion (j₀ a₀) := hj₀ a₀
  let : IsOpenImmersion jW := inferInstance
  let q₁ : P.toScheme ⟶ A.toScheme := q₀ ∣_ A
  let qW : W ⟶ A.toScheme := b₃ ≫ q₁
  have hqW : qW ≫ A.ι = jW ≫ f := by
    calc
      qW ≫ A.ι = b₃ ≫ ((q₀ ∣_ A) ≫ A.ι) := rfl
      _ = b₃ ≫ ((q₀ ⁻¹ᵁ A).ι ≫ q₀) := by rw [morphismRestrict_ι]
      _ = jW ≫ f := by dsimp only [jW, P, q₀, b₃, b₁]; cat_disch
  have hq₀open : IsOpenMap q₀ := hopen.comp (v₀ ≫ j₀ a₀).isOpenEmbedding.isOpenMap
  have hq₁open : IsOpenMap q₁.base := by
    rw [morphismRestrict_base]
    exact hq₀open.mapsToRestrict
      (show IsOpen (q₀.base ⁻¹' (A : Set S)) from A.2.preimage q₀.base.hom.continuous)
      (fun _ hx => hx)
  have hqWopen : IsOpenMap qW :=
    hq₁open.comp (P.toScheme.affineCover.f i₃).isOpenEmbedding.isOpenMap
  let I : A.toScheme.Opens := ⟨Set.range qW, hqWopen.isOpen_range⟩
  have hrange : Set.range qW ⊆ Set.range I.ι := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  let k : W ⟶ I.toScheme := IsOpenImmersion.lift I.ι qW hrange
  have hk : k ≫ I.ι = qW := IsOpenImmersion.lift_fac I.ι qW hrange
  let aW : W ⟶ U.left := b₃ ≫ b₁ ≫ v₀ ≫ Sigma.ι V₀ a₀ ≫ iso.inv ≫ u₀
  have hwX : aW ≫ U.hom = jW := by
    have hfac' : iso.inv ≫ u₀ ≫ U.hom = Sigma.desc j₀ := by
      change iso.inv ≫ U₀.hom = Sigma.desc j₀
      rw [← hfac]; simp
    calc
      aW ≫ U.hom = b₃ ≫ b₁ ≫ v₀ ≫ Sigma.ι V₀ a₀ ≫ (iso.inv ≫ u₀) ≫ U.hom := by
        dsimp only [aW]
        simp only [Category.assoc]
      _ = b₃ ≫ b₁ ≫ v₀ ≫ Sigma.ι V₀ a₀ ≫ iso.inv ≫ u₀ ≫ U.hom :=
        congrArg (fun q => b₃ ≫ b₁ ≫ v₀ ≫ Sigma.ι V₀ a₀ ≫ q)
          (Category.assoc iso.inv u₀ U.hom)
      _ = b₃ ≫ b₁ ≫ v₀ ≫ Sigma.ι V₀ a₀ ≫ Sigma.desc j₀ := by rw [hfac']
      _ = jW := by dsimp only [jW]; simp
  have hw0 : aW y₃ = x := by
    change u₀ (iso.inv (Sigma.ι V₀ a₀ (v₀ (b₁ (b₃ y₃))))) = x
    rw [hy₃]
    change u₀ (iso.inv (Sigma.ι V₀ a₀ (v₀ y₁))) = x
    rw [hy₁, hz₀]
    exact (congrArg u₀ (congrArg (fun m => m y₀) iso.hom_inv_id)).trans hy₀
  let V : S.Etale := Scheme.Etale.mk (I.ι ≫ A.ι)
  have hfactor : k ≫ V.hom = jW ≫ f := by
    calc
      k ≫ V.hom = (k ≫ I.ι) ≫ A.ι := (Category.assoc _ _ _).symm
      _ = qW ≫ A.ι := by rw [hk]
      _ = jW ≫ f := hqW
  have hqcW : QuasiCompact qW := by
    let : IsAffine W := Scheme.isAffine_affineCover _ _
    let : IsAffine A.toScheme := isAffineOpen_opensRange (S.affineCover.f i₂)
    infer_instance
  let : QuasiCompact (k ≫ I.ι) := by rw [hk]; exact hqcW
  exact ⟨W, y₃, jW, aW, V, k, inferInstance, hwX, hw0, hfactor,
    QuasiCompact.of_comp k I.ι,
    geometricallyConnected_of_isOpenImmersion_image f jW hsep hconn A qW hqW I rfl k hk⟩

variable {X Y S T : Scheme.{u}}

end ConnectedFibreOpens

end Stacks.EtaleCohomology

end
