module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# Base change for pushforward on small étale sites, with no residual hypothesis

For a cartesian square of schemes `h ≫ f = e ≫ g` with `f : X ⟶ S` flat, the canonical base
change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` of sheaves of sets on the small étale sites is an isomorphism
under each of three sets of conditions on `f`, and for `f` flat, locally of finite presentation
and with geometrically reduced fibres the inverse image `f⁻¹` commutes with products. The common
input is the localized form of Tag 0A3H, proved here for every morphism of schemes, and the
bijectivity of the base change map on sections over an object of the small étale site of `X`
carrying a flat quasi-compact factorization with geometrically connected fibres.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSectionsComparisonIsIso` — the localized form of Tag 0A3H,
  proved for every `f`.
* `Stacks.EtaleCohomology.local_baseChange_compatible` — over an object carrying a flat
  quasi-compact factorization with geometrically connected fibres, the base change map is
  bijective on sections.
* `Stacks.EtaleCohomology.preservesLimitsOfShape_smallEtaleInverseImage_of_geometricallyReduced`
  — **Tag 0EYR**: for `f` flat, locally of finite presentation and with geometrically reduced
  fibres, the inverse image functor on sheaves of sets of the small étale sites commutes with
  products.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_etaleLocalFactorizationCover` —
  **Tag 0EZX**: in a cartesian square with `f` flat and the covering condition, the base
  change map is an isomorphism on every sheaf of sets.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced` —
  **Tag 0EYS**: the same for `f` flat, locally of finite presentation and with geometrically
  reduced fibres.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isOpenMap_connectedFibreOpens` —
  **Tag 0EZZ**: the same for `f` flat and open over a base with separably closed residue
  fields, when affine étale `X`-schemes split into finitely many open subschemes of `X` and
  nonempty opens of the fibres of `f` are connected.

## References

* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0EZZ](https://stacks.math.columbia.edu/tag/0EZZ)
* [Stacks Project, Tag 0EYR](https://stacks.math.columbia.edu/tag/0EYR)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
* [Stacks Project, Tag 0EY5](https://stacks.math.columbia.edu/tag/0EY5)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-- Tag 0A3H in localized form, for every morphism of schemes `f : X ⟶ S`: for a sheaf of sets
`G` on the small étale site of `S` and a morphism `a : U ⟶ V ×_S X` of the small étale site of
`X` whose composite `U ⟶ V` is flat, quasi-compact and has geometrically connected fibres, the
comparison `G(V) ⟶ (f⁻¹G)(U)` is an isomorphism. -/
theorem smallEtaleSectionsComparisonIsIso {X S : Scheme.{u}} (f : X ⟶ S) :
    SmallEtaleSectionsComparisonIsIso.{u, v} f := by
  intro G U V a hflat hqc hconn
  exact isIso_smallEtaleInverseImageSections.{u, v} f G a
    (universally_isQuotientMap_of_flat_quasiCompact _) hconn

section LocalSections

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- By Tag 0A3H, a factorization `U ⟶ V ⟶ S` with `U ⟶ V` flat, quasi-compact and with
geometrically connected fibres identifies the sections of `f⁻¹G` over `U` with the sections of
`G` over `V`, naturally in `G`. -/
private def smallEtaleInverseImageSectionsIso
    {U : X.Etale} {V : S.Etale} (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    [Flat k] [QuasiCompact k] [GeometricallyConnected k] :
    smallEtaleInverseImage.{u, v} f ⋙ sectionsOver.{u, v} U ≅ sectionsOver.{u, v} V := by
  have : ∀ G, IsIso ((localSectionsComparison.{u, v} f
      (smallEtaleFactorizationHom f k hk)).app G) := fun G => by
    rw [localSectionsComparison_app]
    refine smallEtaleSectionsComparisonIsIso.{u, v} f G _ ?_ ?_ ?_ <;>
      rw [smallEtaleFactorizationHom_left_fst] <;> infer_instance
  have : IsIso (localSectionsComparison.{u, v} f (smallEtaleFactorizationHom f k hk)) :=
    NatIso.isIso_of_isIso_app _
  exact (asIso (localSectionsComparison.{u, v} f (smallEtaleFactorizationHom f k hk))).symm

end LocalSections

section Products

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a morphism of schemes which is flat, locally of finite presentation and has
geometrically reduced fibres, the inverse image functor on sheaves of sets of the small étale
sites commutes with products. -/
@[stacks 0EYR "no residual hypothesis. Both inputs of the source's proof are supplied: the
covering of the small étale site by objects with a flat quasi-compact factorization with
geometrically connected fibres, which is Tag 0EY5 and is
`hasEnoughObjects_hasFlatConnectedFactorization`; and the bijectivity of the canonical
comparison `G(V) ⟶ (f⁻¹G)(U)` over such an object, which is Tag 0A3H in the localized form of
the source's own argument and is `smallEtaleSectionsComparisonIsIso`, proved from Tag 0EZK and
the small-étale instance of Tag 03EF. The globalization from sections to sheaves is Tag 0H6Y."]
theorem preservesLimitsOfShape_smallEtaleInverseImage_of_geometricallyReduced
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (I : Type w) :
    PreservesLimitsOfShape (Discrete I) (smallEtaleInverseImage.{u, max v w} f) := by
  classical
  let H := smallEtaleInverseImage.{u, max v w} f
  let J := smallEtaleTopology X
  have hEnough : J.HasEnoughObjects (HasFlatConnectedFactorization f) :=
    hasEnoughObjects_hasFlatConnectedFactorization f
  have hpi : ∀ F : I → Sheaf (smallEtaleTopology S) (Type (max (u + 1) (max v w))),
      IsIso (piComparison H F) := by
    intro F
    let φ := (sheafToPresheaf J (Type (max (u + 1) (max v w)))).map (piComparison H F)
    have hsection : ∀ ⦃U : X.Etale⦄, HasFlatConnectedFactorization f U →
        Function.Bijective (φ.app (op U)) := by
      intro U hU
      obtain ⟨V, k, hk, hflat, hqc, hconn⟩ := hU
      let eLocal := smallEtaleInverseImageSectionsIso.{u, max v w} f k hk
      let : PreservesLimitsOfShape (Discrete I) (H ⋙ sectionsOver.{u, max v w} U) :=
        preservesLimitsOfShape_of_natIso eLocal.symm
      have hcmp : (sectionsOver.{u, max v w} U).map (piComparison H F) ≫
          piComparison (sectionsOver.{u, max v w} U) (fun i => H.obj (F i)) =
            piComparison (H ⋙ sectionsOver.{u, max v w} U) F := by
        refine Pi.hom_ext _ _ fun i => ?_
        simp only [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
        rfl
      have hcompIso : IsIso ((sectionsOver.{u, max v w} U).map (piComparison H F) ≫
          piComparison (sectionsOver.{u, max v w} U) (fun i => H.obj (F i))) := by
        rw [hcmp]
        infer_instance
      have hfirst : IsIso ((sectionsOver.{u, max v w} U).map (piComparison H F)) :=
        (isIso_comp_right_iff _ _).mp hcompIso
      change Function.Bijective ((sectionsOver.{u, max v w} U).map (piComparison H F))
      rw [← isIso_iff_bijective]
      exact hfirst
    have hInj := Presheaf.isLocallyInjective_of_hasEnoughObjects_injective J φ hEnough
      (fun {_} hU => (hsection hU).injective)
    have hSurj := Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J φ hEnough
      (fun {_} hU => (hsection hU).surjective)
    exact (Sheaf.isLocallyBijective_iff_isIso (piComparison H F)).mp ⟨hInj, hSurj⟩
  let : ∀ F : I → Sheaf (smallEtaleTopology S) (Type (max (u + 1) (max v w))),
      PreservesLimit (Discrete.functor F) H := fun F => by
    let := hpi F
    exact PreservesProduct.of_iso_comparison H F
  exact preservesLimitsOfShape_of_discrete H

end Products

section BaseChangeSquare

variable {X Y S T : Scheme.{u}}

/-! ### The sections of the two sides over an object carrying a factorization

Over an object `U` of the small étale site of `X` admitting a flat quasi-compact factorization
`U ⟶ V ⟶ S` with geometrically connected fibres, the sections of `f⁻¹ g_* F` and of `h_* e⁻¹ F`
are both the sections of `F` over `V ×_S T`, compatibly with the base change map. -/

/-- Étale morphisms admit pullbacks along any morphism of schemes. -/
private lemma hasPullbacksAlong_etale {A B : Scheme.{u}} (p : A ⟶ B) :
    MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) p :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- Étale morphisms are stable under base change along any morphism of schemes. -/
private lemma isStableUnderBaseChangeAlong_etale {A B : Scheme.{u}} (p : A ⟶ B) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) p :=
  ⟨fun pb hq ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hq⟩

/-- Base change along `p` of a morphism of the small étale site, read on the projection to the
base: the projection is the projection of the source followed by the morphism. -/
private lemma smallEtaleBaseChange_map_left_fst {A B : Scheme.{u}} (p : A ⟶ B) {W Z : B.Etale}
    (a : W ⟶ Z) :
    ((smallEtaleBaseChange p).map a).left ≫ pullback.fst Z.hom p =
      pullback.fst W.hom p ≫ a.left :=
  pullback.lift_fst _ _ _

/-- Base change along `p` of a morphism of the small étale site, read on the projection to `A`:
that projection is the structure morphism of the base change, so it is unchanged. -/
private lemma smallEtaleBaseChange_map_left_snd {A B : Scheme.{u}} (p : A ⟶ B) {W Z : B.Etale}
    (a : W ⟶ Z) :
    ((smallEtaleBaseChange p).map a).left ≫ pullback.snd Z.hom p = pullback.snd W.hom p :=
  pullback.lift_snd _ _ _

/-- In a cartesian square `h ≫ f = e ≫ g`, the pullback of `h` along `p : W ⟶ X` is the
pullback of `p ≫ f` along `g`, compatibly with the projections. -/
private lemma exists_pullbackIso_of_isPullback (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S) (sq : IsPullback h e f g) {W : Scheme.{u}} (p : W ⟶ X) :
    ∃ i : pullback h p ≅ pullback (p ≫ f) g,
      i.hom ≫ pullback.fst (p ≫ f) g = pullback.snd h p ∧
        i.hom ≫ pullback.snd (p ≫ f) g = pullback.fst h p ≫ e := by
  let eY : Y ≅ pullback f g := sq.isoPullback
  let m := pullback.map h p (pullback.fst f g) p eY.hom (𝟙 W) (𝟙 X)
    (by rw [Category.comp_id]; exact sq.isoPullback_hom_fst.symm) (by simp)
  have hm_snd : m ≫ pullback.snd (pullback.fst f g) p = pullback.snd h p :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hm_fst : m ≫ pullback.fst (pullback.fst f g) p = pullback.fst h p ≫ eY.hom :=
    pullback.lift_fst _ _ _
  have : IsIso m := by
    dsimp [m]
    infer_instance
  refine ⟨asIso m ≪≫ pullbackSymmetry (pullback.fst f g) p ≪≫
    pullbackRightPullbackFstIso f g p, ?_, ?_⟩
  · change m ≫ (pullbackSymmetry (pullback.fst f g) p).hom ≫
      (pullbackRightPullbackFstIso f g p).hom ≫ pullback.fst (p ≫ f) g = _
    rw [pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst, hm_snd]
  · change m ≫ (pullbackSymmetry (pullback.fst f g) p).hom ≫
      (pullbackRightPullbackFstIso f g p).hom ≫ pullback.snd (p ≫ f) g = _
    rw [pullbackRightPullbackFstIso_hom_snd,
      ← Category.assoc (pullbackSymmetry (pullback.fst f g) p).hom
        (pullback.snd p (pullback.fst f g)) (pullback.snd f g),
      pullbackSymmetry_hom_comp_snd,
      ← Category.assoc m (pullback.fst (pullback.fst f g) p) (pullback.snd f g),
      hm_fst, Category.assoc (pullback.fst h p) eY.hom (pullback.snd f g),
      sq.isoPullback_hom_snd]

/-- A quasi-compact morphism `k : W ⟶ V` over `S` with geometrically connected fibres base
changes along `g : T ⟶ S` to a morphism `W ×_S T ⟶ V ×_S T` with the same two properties. -/
private lemma exists_pullback_map_quasiCompact_geometricallyConnected {W V : Scheme.{u}}
    (a : W ⟶ S) (b : V ⟶ S) (k : W ⟶ V) (hk : k ≫ b = a) (g : T ⟶ S)
    [QuasiCompact k] [GeometricallyConnected k] :
    ∃ kTZ : pullback a g ⟶ pullback b g,
      kTZ ≫ pullback.fst b g = pullback.fst a g ≫ k ∧
        kTZ ≫ pullback.snd b g = pullback.snd a g ∧
          QuasiCompact kTZ ∧ GeometricallyConnected kTZ := by
  let eCommon : pullback a g ≅ pullback (k ≫ b) g := pullback.congrHom hk.symm rfl
  let eWCommon : pullback (pullback.fst b g) k ≅ pullback (k ≫ b) g :=
    pullbackSymmetry (pullback.fst b g) k ≪≫ pullbackRightPullbackFstIso b g k
  let eZ : pullback a g ≅ pullback (pullback.fst b g) k := eCommon ≪≫ eWCommon.symm
  let kTZ : pullback a g ⟶ pullback b g := eZ.hom ≫ pullback.fst (pullback.fst b g) k
  have heZ_U : eZ.hom ≫ pullback.snd (pullback.fst b g) k = pullback.fst a g := by
    simp only [pullback.congrHom, pullback.map, Category.comp_id, Iso.trans_symm, Iso.trans_hom,
      asIso_hom, Iso.symm_hom, Category.assoc, pullbackSymmetry_inv_comp_snd,
      pullbackRightPullbackFstIso_inv_fst, pullback.lift_fst, eZ, eCommon, eWCommon]
  have heCommon_snd : eCommon.hom ≫ pullback.snd (k ≫ b) g = pullback.snd a g := by
    change pullback.map a g (k ≫ b) g (𝟙 W) (𝟙 T) (𝟙 S)
        (by simpa using hk.symm) (by simp) ≫ pullback.snd (k ≫ b) g = pullback.snd a g
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  have heZ_V : kTZ ≫ pullback.fst b g = pullback.fst a g ≫ k := by
    calc
      kTZ ≫ pullback.fst b g = eZ.hom ≫ pullback.fst (pullback.fst b g) k ≫ pullback.fst b g :=
        rfl
      _ = eZ.hom ≫ pullback.snd (pullback.fst b g) k ≫ k := by rw [pullback.condition]
      _ = pullback.fst a g ≫ k := by
        rw [← Category.assoc eZ.hom (pullback.snd (pullback.fst b g) k) k, heZ_U]
  have hassoc : eWCommon.inv ≫ pullback.fst (pullback.fst b g) k ≫ pullback.snd b g =
      pullback.snd (k ≫ b) g := by
    calc
      _ = (pullbackRightPullbackFstIso b g k).inv ≫
          (pullbackSymmetry (pullback.fst b g) k).inv ≫
            pullback.fst (pullback.fst b g) k ≫ pullback.snd b g := rfl
      _ = (pullbackRightPullbackFstIso b g k).inv ≫
          pullback.snd k (pullback.fst b g) ≫ pullback.snd b g := by
        rw [pullbackSymmetry_inv_comp_fst_assoc]
      _ = pullback.snd (k ≫ b) g := pullbackRightPullbackFstIso_inv_snd_snd _ _ _
  have heZ_T : kTZ ≫ pullback.snd b g = pullback.snd a g := by
    calc
      kTZ ≫ pullback.snd b g =
          eZ.hom ≫ pullback.fst (pullback.fst b g) k ≫ pullback.snd b g :=
        Category.assoc _ _ _
      _ = eCommon.hom ≫ eWCommon.inv ≫
            pullback.fst (pullback.fst b g) k ≫ pullback.snd b g := by
        simp only [eZ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      _ = eCommon.hom ≫ pullback.snd (k ≫ b) g := by rw [hassoc]
      _ = pullback.snd a g := heCommon_snd
  have hsqZ : IsPullback kTZ (pullback.fst a g) (pullback.fst b g) k :=
    (IsPullback.of_hasPullback (pullback.fst b g) k).of_iso' eZ (Iso.refl _)
      (Iso.refl _) (Iso.refl _) rfl heZ_U rfl rfl
  exact ⟨kTZ, heZ_V, heZ_T, MorphismProperty.of_isPullback hsqZ.flip inferInstance,
    MorphismProperty.of_isPullback hsqZ.flip inferInstance⟩

/-- Base change of a factorization along the cartesian square: if the structure morphism of
`U : X.Etale` factors through `V : S.Etale` by a quasi-compact `k` with geometrically connected
fibres, then the structure morphism of `U ×_X Y` factors through `V ×_S T` by a morphism with
the same two properties, which is the base change of `k`. -/
private theorem etaleBaseChangeFactor (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) (U : X.Etale) (V : S.Etale) (k : U.left ⟶ V.left)
    (hk : k ≫ V.hom = U.hom ≫ f) [QuasiCompact k] [GeometricallyConnected k] :
    ∃ kT : (Scheme.Etale.mk (pullback.fst h U.hom)).left ⟶
        (Scheme.Etale.mk (pullback.snd V.hom g)).left,
      kT ≫ pullback.snd V.hom g = pullback.fst h U.hom ≫ e ∧
        kT ≫ pullback.fst V.hom g = pullback.snd h U.hom ≫ k ∧
          QuasiCompact kT ∧ GeometricallyConnected kT := by
  obtain ⟨i, hi₁, hi₂⟩ := exists_pullbackIso_of_isPullback f h e g sq U.hom
  obtain ⟨kTZ, hV, hT, hqc, hgc⟩ :=
    exists_pullback_map_quasiCompact_geometricallyConnected (U.hom ≫ f) V.hom k hk g
  have : MorphismProperty.RespectsIso @GeometricallyConnected := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  exact ⟨i.hom ≫ kTZ, (Category.assoc _ _ _).trans ((i.hom ≫= hT).trans hi₂),
    (Category.assoc _ _ _).trans ((i.hom ≫= hV).trans ((Category.assoc _ _ _).symm.trans
      (hi₁ =≫ k))),
    inferInstanceAs (QuasiCompact (i.hom ≫ kTZ)),
    (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected) i.hom kTZ).2 hgc⟩

/-- The component of the composition isomorphism for base change, on underlying schemes: it is
the associativity isomorphism of fibre products. -/
private lemma smallEtaleBaseChangeComp_hom_app_left {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (W : C.Etale) :
    ((smallEtaleBaseChangeComp p q).hom.app W).left =
      (pullbackLeftPullbackSndIso W.hom q p).inv := by
  let := hasPullbacksAlong_etale p
  let := hasPullbacksAlong_etale q
  let := isStableUnderBaseChangeAlong_etale p
  let := isStableUnderBaseChangeAlong_etale q
  simpa [smallEtaleBaseChangeComp, smallEtaleBaseChange] using
    MorphismProperty.Over.pullbackComp_hom_app_left (P := @Etale) (Q := ⊤) p q
      (fg := p ≫ q) (hfg := rfl) W

/-- The inverse component of that composition isomorphism, on underlying schemes. -/
private lemma smallEtaleBaseChangeComp_inv_app_left {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (W : C.Etale) :
    ((smallEtaleBaseChangeComp p q).inv.app W).left =
      (pullbackLeftPullbackSndIso W.hom q p).hom := by
  let := hasPullbacksAlong_etale p
  let := hasPullbacksAlong_etale q
  let := isStableUnderBaseChangeAlong_etale p
  let := isStableUnderBaseChangeAlong_etale q
  simpa [smallEtaleBaseChangeComp, smallEtaleBaseChange] using
    MorphismProperty.Over.pullbackComp_inv_app_left (P := @Etale) (Q := ⊤) p q
      (fg := p ≫ q) (hfg := rfl) W

/-- The projection to `W` of the transport isomorphism of base-change functors along an equality
of morphisms. -/
private lemma smallEtaleBaseChange_eqToIso_inv_app_left_fst {A B : Scheme.{u}} (p q : A ⟶ B)
    (hpq : p = q) (W : B.Etale) :
    ((eqToIso (congrArg (fun m : A ⟶ B ↦ smallEtaleBaseChange m) hpq)).inv.app W).left ≫
      pullback.fst W.hom p = pullback.fst W.hom q := by
  cases hpq
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The projection to `A` of that transport isomorphism. -/
private lemma smallEtaleBaseChange_eqToIso_inv_app_left_snd {A B : Scheme.{u}} (p q : A ⟶ B)
    (hpq : p = q) (W : B.Etale) :
    ((eqToIso (congrArg (fun m : A ⟶ B ↦ smallEtaleBaseChange m) hpq)).inv.app W).left ≫
      pullback.snd W.hom p = pullback.snd W.hom q := by
  cases hpq
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Transport of direct image along an equality of morphisms, computed two ways: pushing the
transport isomorphism of base-change functors through `sheafPushforwardContinuousIso` gives the
transport isomorphism of the direct-image functors. -/
private lemma sheafPushforwardContinuousIso_eqToIso {A B : Scheme.{u}} (p q : A ⟶ B)
    (hpq : p = q) :
    Functor.sheafPushforwardContinuousIso
        (eqToIso (congrArg (fun m : A ⟶ B ↦ smallEtaleBaseChange m) hpq))
        (Type (max (u + 1) v)) (smallEtaleTopology B) (smallEtaleTopology A) =
      eqToIso (congrArg (fun m : A ⟶ B ↦
        (smallEtaleBaseChange m).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology B) (smallEtaleTopology A)) hpq) := by
  cases hpq
  apply Iso.ext
  ext F W x
  simp [Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  rfl

/-- The base change of `U : X.Etale` along `h : Y ⟶ X`, presented with its *first* projection as
the structure morphism: the symmetry of the fibre product. -/
private def etaleBaseChangeSymmIso (h : Y ⟶ X) (U : X.Etale) :
    Scheme.Etale.mk (pullback.fst h U.hom) ≅ (smallEtaleBaseChange h).obj U :=
  MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤) (pullbackSymmetry h U.hom)
    (pullbackSymmetry_hom_comp_snd h U.hom)

/-- Reassociation of a composite of two factors followed by two projections, the middle factors
collapsing by the given identities. -/
private lemma comp_two_proj_two {A B C D E J : Scheme.{u}} (b : A ⟶ B) (a : B ⟶ C) (π : C ⟶ D)
    (γ : D ⟶ E) (κ : B ⟶ D) (σ : B ⟶ J) (ι : J ⟶ E) (φ : A ⟶ J)
    (ha : a ≫ π = κ) (hκ : κ ≫ γ = σ ≫ ι) (hb : b ≫ σ = φ) :
    (b ≫ a) ≫ π ≫ γ = φ ≫ ι := by
  rw [Category.assoc, ← Category.assoc a π γ, ha, hκ, ← Category.assoc, hb]

/-- Reassociation of a composite of two factors followed by one projection. -/
private lemma comp_two_proj_one {A B C D : Scheme.{u}} (b : A ⟶ B) (a : B ⟶ C) (π : C ⟶ D)
    (σ : B ⟶ D) (φ : A ⟶ D) (ha : a ≫ π = σ) (hb : b ≫ σ = φ) :
    (b ≫ a) ≫ π = φ := by
  rw [Category.assoc, ha, hb]

/-- Reassociation of a composite of four factors followed by two projections, each factor
absorbed in turn by the given identities. -/
private lemma comp_four_proj_two {A B C D E J K : Scheme.{u}} (m : A ⟶ B) (q : B ⟶ C)
    (r : C ⟶ D) (s : D ⟶ E) (π : E ⟶ J) (γ : J ⟶ K) (a₁ : D ⟶ K) (a₂ : C ⟶ K) (a₃ : B ⟶ K)
    (ρ : A ⟶ K) (hs : s ≫ π ≫ γ = a₁) (hr : r ≫ a₁ = a₂) (hq : q ≫ a₂ = a₃)
    (hm : m ≫ a₃ = ρ) :
    ((m ≫ q ≫ r ≫ s) ≫ π) ≫ γ = ρ := by
  simp only [Category.assoc]
  rw [hs, hr, hq, hm]

/-- Reassociation of a composite of four factors followed by two projections, when the first
identity produces a composite whose second factor is carried along to the end. -/
private lemma comp_four_proj_two_comp {A B C D E J K L : Scheme.{u}} (m : A ⟶ B) (q : B ⟶ C)
    (r : C ⟶ D) (s : D ⟶ E) (π : E ⟶ J) (γ : J ⟶ K) (a₁ : D ⟶ L) (ε : L ⟶ K) (a₂ : C ⟶ L)
    (a₃ : B ⟶ L) (ρ : A ⟶ L) (hs : s ≫ π ≫ γ = a₁ ≫ ε) (hr : r ≫ a₁ = a₂)
    (hq : q ≫ a₂ = a₃) (hm : m ≫ a₃ = ρ) :
    ((m ≫ q ≫ r ≫ s) ≫ π) ≫ γ = ρ ≫ ε := by
  calc ((m ≫ q ≫ r ≫ s) ≫ π) ≫ γ = m ≫ q ≫ r ≫ s ≫ π ≫ γ := by
        simp only [Category.assoc]
    _ = m ≫ q ≫ r ≫ a₁ ≫ ε := by rw [hs]
    _ = (m ≫ q ≫ r ≫ a₁) ≫ ε := by simp only [Category.assoc]
    _ = ρ ≫ ε := by rw [← hm, ← hq, ← hr]

/-- Reassociation of a composite of four factors followed by one projection. -/
private lemma comp_four_proj_one {A B C D E J : Scheme.{u}} (m : A ⟶ B) (q : B ⟶ C) (r : C ⟶ D)
    (s : D ⟶ E) (π : E ⟶ J) (a₁ : D ⟶ J) (a₂ : C ⟶ J) (a₃ : B ⟶ J) (ρ : A ⟶ J)
    (hs : s ≫ π = a₁) (hr : r ≫ a₁ = a₂) (hq : q ≫ a₂ = a₃) (hm : m ≫ a₃ = ρ) :
    (m ≫ q ≫ r ≫ s) ≫ π = ρ := by
  simp only [Category.assoc]
  rw [hs, hr, hq, hm]

/-- Right-composition with a fixed morphism, as a congruence. -/
private lemma comp_congr_left {A B D : Scheme.{u}} {x y : A ⟶ B} (π : B ⟶ D) (hxy : x = y) :
    x ≫ π = y ≫ π :=
  congrArg (fun z => z ≫ π) hxy

/-- **The two readings of the morphism the base change map is taken along agree.**  Going round
the square one way gives the factorization `U ×_X Y ⟶ (V ×_S T) ×_T Y` produced by
`etaleBaseChangeFactor`; going round it the other way gives the base change along `h` of the
factorization `U ⟶ V ×_S X`, read through the two composition isomorphisms and the transport
along `e ≫ g = h ≫ f`. -/
private lemma etaleBaseChangeFactorizationHom_eq (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (w : e ≫ g = h ≫ f) (U : X.Etale) (V : S.Etale) (k : U.left ⟶ V.left)
    (hk : k ≫ V.hom = U.hom ≫ f)
    (kT : (Scheme.Etale.mk (pullback.fst h U.hom)).left ⟶
      (Scheme.Etale.mk (pullback.snd V.hom g)).left)
    (hkT : kT ≫ (Scheme.Etale.mk (pullback.snd V.hom g)).hom =
      (Scheme.Etale.mk (pullback.fst h U.hom)).hom ≫ e)
    (hkTV : kT ≫ pullback.fst V.hom g = pullback.snd h U.hom ≫ k) :
    (etaleBaseChangeSymmIso h U).inv ≫ smallEtaleFactorizationHom e kT hkT =
      (smallEtaleBaseChange h).map (smallEtaleFactorizationHom f k hk) ≫
        (smallEtaleBaseChangeComp h f).inv.app V ≫
          (eqToIso (congrArg (fun m : Y ⟶ S ↦ smallEtaleBaseChange m) w)).inv.app V ≫
            (smallEtaleBaseChangeComp e g).hom.app V := by
  have hb : (etaleBaseChangeSymmIso h U).inv.hom.left = (pullbackSymmetry h U.hom).inv := rfl
  have haEfst : (smallEtaleFactorizationHom e kT hkT).left ≫
      pullback.fst (Scheme.Etale.mk (pullback.snd V.hom g)).hom e = kT :=
    smallEtaleFactorizationHom_left_fst e kT hkT
  have haEsnd : (smallEtaleFactorizationHom e kT hkT).left ≫
      pullback.snd (Scheme.Etale.mk (pullback.snd V.hom g)).hom e =
        (Scheme.Etale.mk (pullback.fst h U.hom)).hom :=
    MorphismProperty.Over.w _
  have hMapSnd : ((smallEtaleBaseChange h).map (smallEtaleFactorizationHom f k hk)).left ≫
      pullback.snd ((smallEtaleBaseChange f).obj V).hom h = pullback.snd U.hom h :=
    smallEtaleBaseChange_map_left_snd h (smallEtaleFactorizationHom f k hk)
  have hMapFst : ((smallEtaleBaseChange h).map (smallEtaleFactorizationHom f k hk)).left ≫
      pullback.fst ((smallEtaleBaseChange f).obj V).hom h ≫ pullback.fst V.hom f =
        pullback.fst U.hom h ≫ k :=
    (Category.assoc _ _ _).symm.trans
      ((comp_congr_left (pullback.fst V.hom f)
          (smallEtaleBaseChange_map_left_fst h (smallEtaleFactorizationHom f k hk))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => pullback.fst U.hom h ≫ z)
            (smallEtaleFactorizationHom_left_fst f k hk))))
  have hsFst : ((smallEtaleBaseChangeComp e g).hom.app V).left ≫
      pullback.fst (Scheme.Etale.mk (pullback.snd V.hom g)).hom e ≫ pullback.fst V.hom g =
        pullback.fst V.hom (e ≫ g) :=
    (comp_congr_left _ (smallEtaleBaseChangeComp_hom_app_left e g V)).trans
      (pullbackLeftPullbackSndIso_inv_fst V.hom g e)
  have hsSnd : ((smallEtaleBaseChangeComp e g).hom.app V).left ≫
      pullback.fst (Scheme.Etale.mk (pullback.snd V.hom g)).hom e ≫ pullback.snd V.hom g =
        pullback.snd V.hom (e ≫ g) ≫ e :=
    (comp_congr_left _ (smallEtaleBaseChangeComp_hom_app_left e g V)).trans
      (pullbackLeftPullbackSndIso_inv_fst_snd V.hom g e)
  have hsLast : ((smallEtaleBaseChangeComp e g).hom.app V).left ≫
      pullback.snd (Scheme.Etale.mk (pullback.snd V.hom g)).hom e =
        pullback.snd V.hom (e ≫ g) :=
    (comp_congr_left _ (smallEtaleBaseChangeComp_hom_app_left e g V)).trans
      (pullbackLeftPullbackSndIso_inv_snd_snd V.hom g e)
  have hqFst : ((smallEtaleBaseChangeComp h f).inv.app V).left ≫
      pullback.fst V.hom (h ≫ f) =
        pullback.fst ((smallEtaleBaseChange f).obj V).hom h ≫ pullback.fst V.hom f :=
    (comp_congr_left _ (smallEtaleBaseChangeComp_inv_app_left h f V)).trans
      (pullbackLeftPullbackSndIso_hom_fst V.hom f h)
  have hqSnd : ((smallEtaleBaseChangeComp h f).inv.app V).left ≫
      pullback.snd V.hom (h ≫ f) = pullback.snd ((smallEtaleBaseChange f).obj V).hom h :=
    (comp_congr_left _ (smallEtaleBaseChangeComp_inv_app_left h f V)).trans
      (pullbackLeftPullbackSndIso_hom_snd V.hom f h)
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
  · change ((etaleBaseChangeSymmIso h U).inv.hom.left ≫
      (smallEtaleFactorizationHom e kT hkT).left) ≫ _ ≫ _ = _
    rw [hb]
    exact (comp_two_proj_two _ _ _ _ _ _ _ _ haEfst hkTV
        (pullbackSymmetry_inv_comp_snd h U.hom)).trans
      (comp_four_proj_two _ _ _ _ _ _ _ _ _ _ hsFst
        (smallEtaleBaseChange_eqToIso_inv_app_left_fst (e ≫ g) (h ≫ f) w V) hqFst hMapFst).symm
  · change ((etaleBaseChangeSymmIso h U).inv.hom.left ≫
      (smallEtaleFactorizationHom e kT hkT).left) ≫ _ ≫ _ = _
    rw [hb]
    exact (comp_two_proj_two _ _ _ _ _ _ _ _ haEfst hkT
        (pullbackSymmetry_inv_comp_fst h U.hom)).trans
      (comp_four_proj_two_comp _ _ _ _ _ _ _ _ _ _ _ hsSnd
        (smallEtaleBaseChange_eqToIso_inv_app_left_snd (e ≫ g) (h ≫ f) w V) hqSnd hMapSnd).symm
  · change ((etaleBaseChangeSymmIso h U).inv.hom.left ≫
      (smallEtaleFactorizationHom e kT hkT).left) ≫ _ = _
    rw [hb]
    exact (comp_two_proj_one _ _ _ _ _ haEsnd
        (pullbackSymmetry_inv_comp_fst h U.hom)).trans
      (comp_four_proj_one _ _ _ _ _ _ _ _ _ hsLast
        (smallEtaleBaseChange_eqToIso_inv_app_left_snd (e ≫ g) (h ≫ f) w V) hqSnd hMapSnd).symm

/-- A presheaf applied to the opposite of a composite of two morphisms, decomposed. -/
private lemma presheaf_map_op_comp_two {C : Type*} [Category* C] {A B D : C}
    (P : Cᵒᵖ ⥤ Type w) (x : A ⟶ B) (y : B ⟶ D) :
    P.map (x ≫ y).op = P.map y.op ≫ P.map x.op := by
  simp only [op_comp, Functor.map_comp]

/-- A presheaf applied to the opposite of a composite of four morphisms, decomposed. -/
private lemma presheaf_map_op_comp_four {C : Type*} [Category* C] {A B D E J : C}
    (P : Cᵒᵖ ⥤ Type w) (m : A ⟶ B) (q : B ⟶ D) (r : D ⟶ E) (s : E ⟶ J) :
    P.map (m ≫ q ≫ r ≫ s).op =
      P.map s.op ≫ P.map r.op ≫ P.map q.op ≫ P.map m.op := by
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- Transport of the sections functor along an isomorphism of objects of the small étale
site. -/
private def sectionsOverIso {A : Scheme.{u}} {U V : A.Etale} (i : U ≅ V) :
    sectionsOver.{u, v} U ≅ sectionsOver.{u, v} V :=
  Functor.isoWhiskerLeft (sheafToPresheaf (smallEtaleTopology A) (Type (max (u + 1) v)))
    ((evaluation A.Etaleᵒᵖ (Type (max (u + 1) v))).mapIso i.symm.op)

private lemma pushforwardSectionsOver_hom_app {A B : Scheme.{u}} (p : B ⟶ A) (U : A.Etale)
    (F : Sheaf (smallEtaleTopology B) (Type (max (u + 1) v))) :
    (pushforwardSectionsOver.{u, v} p U).hom.app F = 𝟙 _ := rfl

/-- The identification of the sections of `f⁻¹ g_* F` over `U` with the sections of `F` over
`V ×_S T`: the sections of the pushforward are the sections over the base change, and Tag 0A3H
at `f` identifies the sections of the inverse image over `U` with the sections downstairs over
`V`. -/
private def localBaseChangeSourceIso (f : X ⟶ S) (g : T ⟶ S) {U : X.Etale} {V : S.Etale}
    (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    (hflat : Flat k) (hqc : QuasiCompact k) (hconn : GeometricallyConnected k) :
    ((smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) ⋙
        smallEtaleInverseImage.{u, v} f) ⋙ sectionsOver.{u, v} U ≅
      sectionsOver.{u, v} (Scheme.Etale.mk (pullback.snd V.hom g)) :=
  have : Flat k := hflat
  have : QuasiCompact k := hqc
  have : GeometricallyConnected k := hconn
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleInverseImageSectionsIso.{u, v} f k hk) ≪≫
    pushforwardSectionsOver.{u, v} g V

/-- The identification of the sections of `h_* e⁻¹ F` over `U` with the sections of `F` over
`V ×_S T`: the sections of the pushforward are the sections over `U ×_X Y`, and Tag 0A3H at `e`
identifies the sections of the inverse image there with the sections of `F` over `V ×_S T`,
along the factorization produced by `etaleBaseChangeFactor`. -/
private def localBaseChangeTargetIso (e : Y ⟶ T) (h : Y ⟶ X) {U : X.Etale} {V : S.Etale}
    {g : T ⟶ S}
    (kT : (Scheme.Etale.mk (pullback.fst h U.hom)).left ⟶
      (Scheme.Etale.mk (pullback.snd V.hom g)).left)
    (hkT : kT ≫ (Scheme.Etale.mk (pullback.snd V.hom g)).hom =
      (Scheme.Etale.mk (pullback.fst h U.hom)).hom ≫ e)
    (hflat : Flat kT) (hqc : QuasiCompact kT) (hconn : GeometricallyConnected kT) :
    (smallEtaleInverseImage.{u, v} e ⋙
        (smallEtaleBaseChange h).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y)) ⋙
      sectionsOver.{u, v} U ≅
    sectionsOver.{u, v} (Scheme.Etale.mk (pullback.snd V.hom g)) :=
  have : Flat kT := hflat
  have : QuasiCompact kT := hqc
  have : GeometricallyConnected kT := hconn
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushforwardSectionsOver.{u, v} h U) ≪≫
    Functor.isoWhiskerLeft _ (sectionsOverIso.{u, v} (etaleBaseChangeSymmIso h U).symm) ≪≫
    smallEtaleInverseImageSectionsIso.{u, v} e kT hkT

/-- The identification of the two composite direct images around the square, as a two-square for
the two inverse-image/direct-image adjunctions. -/
private def baseChangeTwoSquare (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (w : e ≫ g = h ≫ f) :
    TwoSquare
      ((smallEtaleBaseChange e).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology T) (smallEtaleTopology Y))
      ((smallEtaleBaseChange h).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y))
      ((smallEtaleBaseChange g).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T))
      ((smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology X)) :=
  TwoSquare.mk _ _ _ _
    ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
      (Functor.sheafPushforwardContinuousIso
          (eqToIso (congrArg (fun m : Y ⟶ S ↦ smallEtaleBaseChange m) w))
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)).hom ≫
      (smallEtalePushforwardCompIso.{u, v} h f).inv)

/-- Restriction of sections along the factorization `U ⟶ V ×_S X`, read on a direct image along
`f`: the sections over `V` of `f_* H` are the sections of `H` over `V ×_S X`, and those restrict
to `U`. -/
private def localBaseChangeRestrict (f : X ⟶ S) {U : X.Etale} {V : S.Etale}
    (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    (H : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :
    (sectionsOver.{u, v} V).obj
        (((smallEtaleBaseChange f).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology X)).obj H) ⟶
      (sectionsOver.{u, v} U).obj H :=
  (pushforwardSectionsOver.{u, v} f V).hom.app H ≫
    (sectionsRestrict.{u, v} (smallEtaleFactorizationHom f k hk)).app H

/-- **The target identification, computed.**  Running `localBaseChangeTargetIso` backwards is:
take the unit of the inverse-image adjunction at `e`, push it around the square by
`baseChangeTwoSquare`, and restrict along the factorization. -/
private lemma localBaseChangeTargetIso_inv_app (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (w : e ≫ g = h ≫ f) (U : X.Etale) (V : S.Etale) (k : U.left ⟶ V.left)
    (hk : k ≫ V.hom = U.hom ≫ f)
    (kT : (Scheme.Etale.mk (pullback.fst h U.hom)).left ⟶
      (Scheme.Etale.mk (pullback.snd V.hom g)).left)
    (hkT : kT ≫ (Scheme.Etale.mk (pullback.snd V.hom g)).hom =
      (Scheme.Etale.mk (pullback.fst h U.hom)).hom ≫ e)
    (hkTV : kT ≫ pullback.fst V.hom g = pullback.snd h U.hom ≫ k)
    (hflatT : Flat kT) (hqcT : QuasiCompact kT) (hconnT : GeometricallyConnected kT)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (localBaseChangeTargetIso.{u, v} e h kT hkT hflatT hqcT hconnT).inv.app F =
      (pushforwardSectionsOver.{u, v} g V).inv.app F ≫
        (sectionsOver.{u, v} V).map
            (((smallEtaleBaseChange g).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T)).map
              ((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F) ≫
            (baseChangeTwoSquare.{u, v} f h e g w).app
              ((smallEtaleInverseImage.{u, v} e).obj F)) ≫
          localBaseChangeRestrict.{u, v} f k hk
            (((smallEtaleBaseChange h).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y)).obj
              ((smallEtaleInverseImage.{u, v} e).obj F)) := by
  let UY : Y.Etale := Scheme.Etale.mk (pullback.fst h U.hom)
  let VT : T.Etale := Scheme.Etale.mk (pullback.snd V.hom g)
  let Le := smallEtaleInverseImage.{u, v} e
  let aX : U ⟶ (smallEtaleBaseChange f).obj V := smallEtaleFactorizationHom f k hk
  let aE : UY ⟶ (smallEtaleBaseChange e).obj VT := smallEtaleFactorizationHom e kT hkT
  have hmaps : (Le.obj F).obj.map aE.op ≫
      (Le.obj F).obj.map (etaleBaseChangeSymmIso h U).inv.op =
    (Le.obj F).obj.map ((smallEtaleBaseChangeComp e g).hom.app V).op ≫
      (Le.obj F).obj.map ((eqToIso (congrArg (fun m : Y ⟶ S ↦
          smallEtaleBaseChange m) w)).inv.app V).op ≫
        (Le.obj F).obj.map ((smallEtaleBaseChangeComp h f).inv.app V).op ≫
          (Le.obj F).obj.map ((smallEtaleBaseChange h).map aX).op :=
    (presheaf_map_op_comp_two (Le.obj F).obj _ _).symm.trans
      ((congrArg (fun z : (smallEtaleBaseChange h).obj U ⟶ (smallEtaleBaseChange e).obj VT =>
          (Le.obj F).obj.map z.op)
        (etaleBaseChangeFactorizationHom_eq f h e g w U V k hk kT hkT hkTV)).trans
        (presheaf_map_op_comp_four (Le.obj F).obj _ _ _ _))
  ext s
  dsimp [localBaseChangeTargetIso, smallEtaleInverseImageSectionsIso, localSectionsComparison,
    sectionsOverIso,
    sectionsRestrict, localBaseChangeRestrict, baseChangeTwoSquare,
    smallEtalePushforwardCompIso, smallEtaleBaseChangeComp]
  simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, pushforwardSectionsOver_hom_app]
  convert congrArg (fun q => q
    (((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F).hom.app (op VT) s)) hmaps using 1 <;>
    rfl

/-- The base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is the mate of
`baseChangeTwoSquare`. -/
private lemma smallEtaleSetBaseChange_eq_mate (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (w : e ≫ g = h ≫ f) :
    smallEtaleSetBaseChange.{u, v} e h g f w =
      (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
        (smallEtaleInverseImageAdjunction.{u, v} f)).symm
          (baseChangeTwoSquare.{u, v} f h e g w) := by
  dsimp only [smallEtaleSetBaseChange, baseChangeTwoSquare]
  rw [← congrArg Iso.hom (sheafPushforwardContinuousIso_eqToIso.{u, v} (e ≫ g) (h ≫ f) w)]

/-- The inverse of `localBaseChangeSourceIso` on sections is Tag 0A3H's comparison at `f`: the
unit of the inverse-image adjunction at `V`, followed by restriction along the factorization
`U ⟶ V ×_S X`. -/
private lemma localBaseChangeSourceIso_inv_app (f : X ⟶ S) (g : T ⟶ S) {U : X.Etale}
    {V : S.Etale} (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    (hflat : Flat k) (hqc : QuasiCompact k) (hconn : GeometricallyConnected k)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (localBaseChangeSourceIso.{u, v} f g k hk hflat hqc hconn).inv.app F =
      ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
          (((smallEtaleBaseChange g).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S)
            (smallEtaleTopology T)).obj F)).hom.app (op V) ≫
        ((smallEtaleInverseImage.{u, v} f).obj
          (((smallEtaleBaseChange g).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S)
            (smallEtaleTopology T)).obj F)).obj.map (smallEtaleFactorizationHom f k hk).op :=
  rfl

/-- On sections, pushing the unit of the inverse-image adjunction at `f` forward by a map `δ`
and restricting to `U` is the unit followed by the component of `δ` at `V ×_S X` and the
restriction along the factorization. -/
private lemma localBaseChangeRestrict_unit_comp (f : X ⟶ S) (g : T ⟶ S) {U : X.Etale}
    {V : S.Etale} (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (H : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (δ : (smallEtaleInverseImage.{u, v} f).obj
        (((smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T)).obj F) ⟶ H) :
    (pushforwardSectionsOver.{u, v} g V).inv.app F ≫
        (sectionsOver.{u, v} V).map
            ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
              (((smallEtaleBaseChange g).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T)).obj F) ≫
            ((smallEtaleBaseChange f).sheafPushforwardContinuous
              (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology X)).map δ) ≫
          localBaseChangeRestrict.{u, v} f k hk H =
      ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
          (((smallEtaleBaseChange g).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S)
            (smallEtaleTopology T)).obj F)).hom.app (op V) ≫
        δ.hom.app (op ((smallEtaleBaseChange f).obj V)) ≫
          H.obj.map (smallEtaleFactorizationHom f k hk).op :=
  rfl

/-- **The source identification, composed with the base change map, computed.**  The base change
map is the mate of `baseChangeTwoSquare`, and running `localBaseChangeSourceIso` backwards into
it is: take the unit of the inverse-image adjunction at `f`, apply the mate, and restrict along
the factorization. -/
private lemma localBaseChangeSourceIso_inv_app_comp (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S) (sq : IsPullback h e f g) (U : X.Etale) (V : S.Etale) (k : U.left ⟶ V.left)
    (hk : k ≫ V.hom = U.hom ≫ f) (hflat : Flat k) (hqc : QuasiCompact k)
    (hconn : GeometricallyConnected k)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (localBaseChangeSourceIso.{u, v} f g k hk hflat hqc hconn).inv.app F ≫
        (sectionsOver.{u, v} U).map
          ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) =
      (pushforwardSectionsOver.{u, v} g V).inv.app F ≫
        (sectionsOver.{u, v} V).map
            ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
              (((smallEtaleBaseChange g).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T)).obj F) ≫
            ((smallEtaleBaseChange f).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology X)).map
              (((mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
                (smallEtaleInverseImageAdjunction.{u, v} f)).symm
                  (baseChangeTwoSquare.{u, v} f h e g sq.w.symm)).app F)) ≫
          localBaseChangeRestrict.{u, v} f k hk
            (((smallEtaleBaseChange h).sheafPushforwardContinuous
                (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y)).obj
              ((smallEtaleInverseImage.{u, v} e).obj F)) := by
  let Rg := (smallEtaleBaseChange g).sheafPushforwardContinuous
    (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T)
  let Rh := (smallEtaleBaseChange h).sheafPushforwardContinuous
    (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Y)
  let Le := smallEtaleInverseImage.{u, v} e
  let adjE := smallEtaleInverseImageAdjunction.{u, v} e
  let adjF := smallEtaleInverseImageAdjunction.{u, v} f
  let aX : U ⟶ (smallEtaleBaseChange f).obj V := smallEtaleFactorizationHom f k hk
  let δ := ((mateEquiv adjE adjF).symm (baseChangeTwoSquare.{u, v} f h e g sq.w.symm)).app F
  have hβ : (smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F = δ :=
    congrArg (fun θ => θ.app F)
      (smallEtaleSetBaseChange_eq_mate.{u, v} f h e g sq.w.symm)
  have hL := localBaseChangeSourceIso_inv_app.{u, v} f g k hk hflat hqc hconn F
  have hR := localBaseChangeRestrict_unit_comp.{u, v} f g k hk F (Rh.obj (Le.obj F)) δ
  exact (congrArg (fun z =>
      (localBaseChangeSourceIso.{u, v} f g k hk hflat hqc hconn).inv.app F ≫
        (sectionsOver.{u, v} U).map z) hβ).trans
    ((congrArg (fun z => z ≫ (sectionsOver.{u, v} U).map δ) hL).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (adjF.unit.app (Rg.obj F)).hom.app (op V) ≫ z)
          (δ.hom.naturality aX.op)).trans hR.symm)))

/-- **The two identifications differ by the base change map.**  The source identification
`localBaseChangeSourceIso` is the base change map on sections over `U` followed by the target
identification `localBaseChangeTargetIso`. -/
private lemma local_baseChange_bridge (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) (U : X.Etale) (V : S.Etale) (k : U.left ⟶ V.left)
    (hk : k ≫ V.hom = U.hom ≫ f) (hflat : Flat k) (hqc : QuasiCompact k)
    (hconn : GeometricallyConnected k)
    (kT : (Scheme.Etale.mk (pullback.fst h U.hom)).left ⟶
      (Scheme.Etale.mk (pullback.snd V.hom g)).left)
    (hkT : kT ≫ (Scheme.Etale.mk (pullback.snd V.hom g)).hom =
      (Scheme.Etale.mk (pullback.fst h U.hom)).hom ≫ e)
    (hkTV : kT ≫ pullback.fst V.hom g = pullback.snd h U.hom ≫ k)
    (hflatT : Flat kT) (hqcT : QuasiCompact kT) (hconnT : GeometricallyConnected kT)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (localBaseChangeSourceIso.{u, v} f g k hk hflat hqc hconn).hom.app F =
      (sectionsOver.{u, v} U).map
          ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) ≫
        (localBaseChangeTargetIso.{u, v} e h kT hkT hflatT hqcT hconnT).hom.app F := by
  let eSource := localBaseChangeSourceIso.{u, v} f g k hk hflat hqc hconn
  let eTarget := localBaseChangeTargetIso.{u, v} e h kT hkT hflatT hqcT hconnT
  have hmateCompare : eTarget.inv.app F =
      eSource.inv.app F ≫ (sectionsOver.{u, v} U).map
        ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) :=
    (localBaseChangeTargetIso_inv_app.{u, v} f h e g sq.w.symm U V k hk kT hkT hkTV
        hflatT hqcT hconnT F).trans
      ((congrArg (fun θ => (pushforwardSectionsOver.{u, v} g V).inv.app F ≫
            (sectionsOver.{u, v} V).map θ ≫ localBaseChangeRestrict.{u, v} f k hk _)
          (unit_mateEquiv_symm (smallEtaleInverseImageAdjunction.{u, v} e)
            (smallEtaleInverseImageAdjunction.{u, v} f)
            (baseChangeTwoSquare.{u, v} f h e g sq.w.symm) F)).trans
        (localBaseChangeSourceIso_inv_app_comp.{u, v} f h e g sq U V k hk
          hflat hqc hconn F).symm)
  calc
    eSource.hom.app F = eSource.hom.app F ≫ eTarget.inv.app F ≫ eTarget.hom.app F := by simp
    _ = eSource.hom.app F ≫ (eSource.inv.app F ≫ (sectionsOver.{u, v} U).map
          ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F)) ≫
            eTarget.hom.app F := by rw [hmateCompare]
    _ = (sectionsOver.{u, v} U).map
          ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) ≫
            eTarget.hom.app F := by
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Over an object `U` of the small étale site of `X` carrying a flat quasi-compact
factorization `U ⟶ V` with geometrically connected fibres, the base change map is bijective on
sections over `U`. -/
private theorem local_baseChange_component_bijective (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S) (sq : IsPullback h e f g) [Flat f] (U : X.Etale) (V : S.Etale)
    (k : U.left ⟶ V.left) (hk : k ≫ V.hom = U.hom ≫ f)
    [Flat k] [QuasiCompact k] [GeometricallyConnected k]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    Function.Bijective ((sectionsOver.{u, v} U).map
      ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F)) := by
  obtain ⟨kT, hkT, hkTV, hqcT, hgcT⟩ := etaleBaseChangeFactor f h e g sq U V k hk
  have : Flat e := MorphismProperty.of_isPullback sq inferInstance
  have : Flat kT := flat_of_etale_over_flat (Scheme.Etale.mk (pullback.fst h U.hom)).hom e
    (Scheme.Etale.mk (pullback.snd V.hom g)).hom kT hkT
  rw [← isIso_iff_bijective, ← isIso_comp_right_iff _
      ((localBaseChangeTargetIso.{u, v} e h kT hkT ‹_› ‹_› ‹_›).hom.app F),
    ← local_baseChange_bridge.{u, v} f h e g sq U V k hk ‹_› ‹_› ‹_› kT hkT hkTV ‹_› ‹_› ‹_› F]
  infer_instance

/-- Over an object of the small étale site of `X` carrying a flat quasi-compact factorization
with geometrically connected fibres, the base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is bijective
on sections. -/
theorem local_baseChange_compatible (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Flat f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    ⦃U : X.Etale⦄ (hU : HasFlatConnectedFactorization f U) :
    Function.Bijective
      (((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F).hom.app (op U)) := by
  obtain ⟨V, k, hk, hflat, hqc, hgc⟩ := hU
  exact local_baseChange_component_bijective.{u, v} f h e g sq U V k hk F

/-- In a cartesian square of schemes with `f : X ⟶ S` flat, if every object of the small étale
site of `X` has an étale covering whose members factor through an étale `S`-scheme by a
quasi-compact morphism with geometrically connected fibres, then the canonical base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on the small étale site of
`T`. -/
@[stacks 0EZX "no residual hypothesis. Both paragraphs of the source's proof are supplied. The
first is the chain of four identifications -- that the sections of `f⁻¹ g_* F` and of
`h_* e⁻¹ F` over an object with such a factorization are both the sections of `F` over
`V ×_S T`, compatibly with the base change map -- and it is `local_baseChange_compatible`: Tag
0A3H in the localized form of the source's own argument, used twice, once at `f` and once at
`e`, is `smallEtaleInverseImageSectionsIso` and is unconditional, the factorization upstairs is
`etaleBaseChangeFactor`, and their compatibility with the base change map is the
Beck-Chevalley identity for the mate defining `smallEtaleSetBaseChange`. The second paragraph
is that the covering condition gives enough objects with a flat such factorization, flatness
coming from `f` by `hasFlatConnectedFactorization_of_quasiCompact`, and that a map of sheaves
bijective on sections over a family of objects covering every object is an isomorphism."]
theorem isIso_smallEtaleSetBaseChange_of_etaleLocalFactorizationCover (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g) [Flat f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (hcover : ∀ U : X.Etale,
      ∃ (ι : Type (u + 1)) (U' : ι → X.Etale) (a : ∀ i, U' i ⟶ U)
        (V : ι → S.Etale) (k : ∀ i, (U' i).left ⟶ (V i).left),
        Sieve.ofArrows U' a ∈ smallEtaleTopology X U ∧
          ∀ i, k i ≫ (V i).hom = (U' i).hom ≫ f ∧
            QuasiCompact (k i) ∧ GeometricallyConnected (k i)) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) :=
  isIso_smallEtaleSetBaseChange_of_hasEnoughObjects f h e g sq F
    (hasEnoughObjects_of_etaleLocalFactorization f hcover)
    (local_baseChange_compatible.{u, v} f h e g sq F)

/-- In a cartesian square of schemes whose left vertical morphism `f : X ⟶ S` is flat, locally
of finite presentation and has geometrically reduced fibres, the canonical base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on the small étale site of
`T`. -/
@[stacks 0EYS "no residual hypothesis. The source merges Tag 0EZX with Tag 0EY5, and both are
supplied: the chain of identifications of the sections of `f⁻¹ g_* F` and of `h_* e⁻¹ F` over an
object carrying a flat quasi-compact factorization with geometrically connected fibres is
`local_baseChange_compatible`, exactly as for Tag 0EZX above, and the covering of the small
étale site of `X` by objects with such a factorization is Tag 0EY5 and is
`hasEnoughObjects_hasFlatConnectedFactorization`. The globalization from sections to sheaves is
Tag 0H6Y."]
theorem isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) :=
  isIso_smallEtaleSetBaseChange_of_hasEnoughObjects f h e g sq F
    (hasEnoughObjects_hasFlatConnectedFactorization f)
    (local_baseChange_compatible.{u, v} f h e g sq F)

end BaseChangeSquare

section ConnectedFibreOpens

variable {X Y S T : Scheme.{u}}

/-- Let `f : X ⟶ S` be flat and open, with separably closed residue fields on `S`, with every
affine étale `X`-scheme a finite disjoint union of open subschemes of `X`, and with every
nonempty open of a fibre of `f` connected. Then in a cartesian square over `f` the canonical base
change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on the small
étale site of `T`. -/
@[stacks 0EZZ "no residual hypothesis. The source's proof is omitted with the hint that the
hypotheses imply the covering condition of Tag 0EZX; that implication is what is proved here,
and the chain of identifications of sections which Tag 0EZX then feeds on is
`local_baseChange_compatible`, exactly as for Tag 0EZX above. Hypothesis (3) of the source is
read as the existence of an isomorphism of the étale `X`-scheme with a finite coproduct of open
subschemes of `X` over `X`; the parenthetical examples in (3) and (4), which the source derives
from Tag 09Z9, are not asserted."]
theorem isIso_smallEtaleSetBaseChange_of_isOpenMap_connectedFibreOpens (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g) [Flat f] (hopen : IsOpenMap f)
    (hsep : ∀ s : S, IsSepClosed (S.residueField s))
    (hsplit : ∀ U : X.Etale, IsAffine U.left →
      ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (j : ∀ a, V a ⟶ X)
        (_ : ∀ a, IsOpenImmersion (j a)) (i : U.left ≅ ∐ V),
        i.hom ≫ Sigma.desc j = U.hom)
    (hconn : ∀ s : S, ∀ W : (f.fiber s).Opens, W ≠ ⊥ → ConnectedSpace W.toScheme)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  classical
  refine isIso_smallEtaleSetBaseChange_of_hasEnoughObjects f h e g sq F (fun U => ?_)
    (local_baseChange_compatible.{u, v} f h e g sq F)
  choose W w jW aW V k hjW haW hwx hfac hqc hgc using
    fun x : U.left => exists_isOpenImmersion_connectedFactorization_at f hopen hsep hsplit
      hconn U x
  let U' : U.left → X.Etale := fun x => Scheme.Etale.mk (jW x)
  let a' : ∀ x, U' x ⟶ U := fun x => MorphismProperty.Over.homMk (aW x) (haW x)
  refine ⟨U.left, U', a', ?_, fun x => ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff a']
    exact Set.eq_univ_iff_forall.mpr fun y => Set.mem_iUnion.mpr ⟨y, ⟨w y, hwx y⟩⟩
  · exact ⟨V x, k x, hfac x,
      flat_of_etale_over_flat (jW x) f (V x).hom (k x) (hfac x), hqc x, hgc x⟩

end ConnectedFibreOpens

end Stacks.EtaleCohomology

end
