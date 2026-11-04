module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSectionsClopen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FiniteFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift

import StacksCore.Tactic.StacksAttribute

/-!
# The isomorphism `(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F79

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site with `f` and `f ≫ g` locally
quasi-finite and `g` separated and locally of finite type. The map
`c' : (f ≫ g)_! F ⟶ g_!(f_! F)` of `StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupport`
is an isomorphism. It suffices to check this on the stalks at the geometric points `s` of `Z`.

The stalk of `(f ≫ g)_! F` at `s` is `⊕_{x̄ ↦ s} F_x̄` (Stacks 0F5F). An element of the stalk of
`g_!(f_! F)` at `s` is the germ of a section `τ` of `f_! F` over `W ×_Z Y` whose support `T` is
proper over the étale neighbourhood `W` of `s`, and it has a germ at every point `ȳ` of the
geometric fibre of `g` over `s` (Stacks 0F78). Two facts about these germs give the result:

* `T` is finite over `W`: étale locally on `W ×_Z Y` the section `τ` is a finite sum of
  generators of `f_{p!} F`, so a point of `T` is the image of a point of a support finite over
  an étale neighbourhood, which lies on a scheme locally quasi-finite over `W`; hence the residue
  fields of `T` are finite over those of `W`, and a closed subset proper over `W` with this
  property is finite over `W` (its fibres are Noetherian schemes all of whose points are closed);
* the germ of `τ` at `s` is determined by its germs at the points `ȳ`: if they all vanish, no
  point of `T` lies over the image `v` of `s` in `W`, as such a point would lift to a geometric
  point over `s` at which the germ is nonzero; so the closed image of `T` in `W` misses `v` and
  `τ` vanishes over its complement;
* only finitely many of these germs are nonzero: they are indexed by lifts of `s` into `T`, and
  `T` is finite over `W`.

With the germ formula of `c'` (`AlgebraicGeometry.SmallEtale.isSepCompMap_sepCompShriekMap`) this
shows that `c'` is bijective on stalks: through the regrouping `⊕_{x̄ ↦ s} F_x̄ ≅
⊕_{ȳ ↦ s} (f_! F)_ȳ` of the geometric fibre of `f ≫ g`, the stalk map of `c'` is the inclusion of
the finitely supported families of germs into all families.

## Main results

* `AlgebraicGeometry.finite_setOf_comp_eq_of_isImmersion` — finiteness of the set of lifts of a
  geometric point landing in a subscheme quasi-compact and quasi-finite over the base.
* `AlgebraicGeometry.isFinite_of_isProperOver_of_finite_residueFieldMap` — a closed subset proper
  over the base whose residue field extensions are finite is finite over the base.
* `AlgebraicGeometry.SmallEtale.isFiniteSupport_properSupportSection` — the support of a section of
  `g_!(f_! F)` is finite over the base.
* `AlgebraicGeometry.SmallEtale.properSupportStalkEval_injective` and
  `AlgebraicGeometry.SmallEtale.finite_properSupportStalkEval_ne_zero` — the two facts above.
* `AlgebraicGeometry.SmallEtale.fShriekCompProperIso` — **Stacks 0F79**, the isomorphism.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v

namespace AlgebraicGeometry

section Points

variable {A C : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- **Finiteness of the geometric points of a quasi-finite subscheme.** Let `h : A ⟶ C` be locally
of finite type, `i : Zs ⟶ A` an immersion with `i ≫ h` quasi-compact and locally quasi-finite, and
`c` a geometric point of `C` with algebraically closed field `K`. Only finitely many lifts
`Spec K ⟶ A` of `c` through `h` hit the image of `i`: such a lift is a section of
`A ×_C Spec K ⟶ Spec K`, which is determined by the closed point it hits, and those points lie in
the image of `Zs ×_C Spec K`, which is quasi-compact and quasi-finite over `Spec K`, hence
finite. -/
public theorem finite_setOf_comp_eq_of_isImmersion (h : A ⟶ C) [LocallyOfFiniteType h]
    {Zs : Scheme.{u}} (i : Zs ⟶ A) [IsImmersion i] [LocallyQuasiFinite (i ≫ h)]
    [QuasiCompact (i ≫ h)] (c : Spec (.of K) ⟶ C) :
    {e : Spec (.of K) ⟶ A | e ≫ h = c ∧ e (IsLocalRing.closedPoint K) ∈ Set.range i}.Finite := by
  have hRsq : IsPullback (pullback.fst h c) (pullback.snd h c) h c := IsPullback.of_hasPullback _ _
  have hbig : IsPullback (pullback.fst i (pullback.fst h c))
      (pullback.snd i (pullback.fst h c) ≫ pullback.snd h c) (i ≫ h) c :=
    (IsPullback.of_hasPullback _ _).paste_vert hRsq
  have : LocallyQuasiFinite (pullback.snd i (pullback.fst h c) ≫ pullback.snd h c) :=
    MorphismProperty.of_isPullback hbig inferInstance
  have : QuasiCompact (pullback.snd i (pullback.fst h c) ≫ pullback.snd h c) :=
    MorphismProperty.of_isPullback hbig inferInstance
  have hfinite : Finite ↥(pullback i (pullback.fst h c)) :=
    Set.finite_univ_iff.mp ((Scheme.Hom.finite_preimage_singleton
      (pullback.snd i (pullback.fst h c) ≫ pullback.snd h c) (IsLocalRing.closedPoint K)).subset
        fun _ _ => Subsingleton.elim _ _)
  have hlift : ∀ e : {e : Spec (.of K) ⟶ A //
      e ≫ h = c ∧ e (IsLocalRing.closedPoint K) ∈ Set.range i}, e.1 ≫ h = 𝟙 _ ≫ c := fun e =>
    e.2.1.trans (Category.id_comp c).symm
  let φ : {e : Spec (.of K) ⟶ A // e ≫ h = c ∧ e (IsLocalRing.closedPoint K) ∈ Set.range i} →
      Set.range (pullback.snd i (pullback.fst h c)) := fun e =>
    ⟨(hRsq.lift e.1 (𝟙 _) (hlift e)) (IsLocalRing.closedPoint K), by
      obtain ⟨z, hz⟩ := e.2.2
      have he : (pullback.fst h c) ((hRsq.lift e.1 (𝟙 _) (hlift e))
          (IsLocalRing.closedPoint K)) = e.1 (IsLocalRing.closedPoint K) :=
        congrArg (fun m => m.base (IsLocalRing.closedPoint K))
          (hRsq.lift_fst e.1 (𝟙 _) (hlift e))
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := i)
        (g := pullback.fst h c) z _ (hz.trans he.symm)
      exact ⟨w, hw⟩⟩
  have : Finite (Set.range (pullback.snd i (pullback.fst h c))) :=
    (Set.finite_range _).to_subtype
  have hinj : Function.Injective φ := by
    intro e₁ e₂ h12
    have heq := ext_of_apply_closedPoint_eq (pullback.snd h c)
      (hRsq.lift_snd e₁.1 (𝟙 _) (hlift e₁))
      (hRsq.lift_snd e₂.1 (𝟙 _) (hlift e₂)) (congrArg Subtype.val h12)
    apply Subtype.ext
    rw [← hRsq.lift_fst e₁.1 (𝟙 _) (hlift e₁),
      ← hRsq.lift_fst e₂.1 (𝟙 _) (hlift e₂), heq]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hinj)

/-- A quasi-compact morphism locally of finite type whose residue field extensions are all finite
has finite fibres. -/
public theorem finite_preimage_singleton_of_finite_residueFieldMap (h : A ⟶ C)
    [QuasiCompact h] [LocallyOfFiniteType h] (hres : ∀ x, (h.residueFieldMap x).hom.Finite)
    (c : C) :
    (h ⁻¹' {c}).Finite := by
  have hcl : ∀ (x) (hx : h x = c), IsClosed {(h.fiberHomeo c).symm ⟨x, hx⟩} := by
    rintro x rfl
    exact (isClosed_asFiber_iff_finite_residueField h x).2 (hres x)
  have : T1Space (h.fiber c) := ⟨fun z => by
    have hz : h (h.fiberι c z) = c := (h.fiberHomeo c z).2
    have H := hcl (h.fiberι c z) hz
    have he : (⟨h.fiberι c z, hz⟩ : h ⁻¹' {c}) = h.fiberHomeo c z := Subtype.ext rfl
    rwa [he, Homeomorph.symm_apply_apply] at H⟩
  have : LocallyOfFiniteType (h.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd h (C.fromSpecResidueField c)))
  have : IsLocallyNoetherian (h.fiber c) :=
    LocallyOfFiniteType.isLocallyNoetherian (h.fiberToSpecResidueField c)
  have : IsNoetherian (h.fiber c) := {}
  have : Finite (h.fiber c) := Stacks.SteinFactorization.finite_of_noetherianSpace_of_t1Space _
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (h.fiberHomeo c).toEquiv)

/-- The residue field map of a composite is the composite of the residue field maps. -/
private theorem residueFieldMap_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ((f ≫ g).residueFieldMap x).hom =
      (f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom := by
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- **A closed subset proper over the base with finite residue field extensions is finite over
it.** Let `q : A ⟶ C` be locally of finite type and `T ⊆ A` a closed subset proper over `C`
whose points all have residue fields finite over the residue fields of their images. Then `T`,
with its reduced structure, is finite over `C`: every fibre of `T` is a Noetherian scheme all of
whose points are closed (Stacks 01TF), hence finite, so `T ⟶ C` is locally quasi-finite, and
proper plus locally quasi-finite is finite. -/
public theorem isFinite_of_isProperOver_of_finite_residueFieldMap (q : A ⟶ C)
    [LocallyOfFiniteType q] (T : Closeds A) (hP : IsProperOver q T)
    (hres : ∀ t ∈ (T : Set A), (q.residueFieldMap t).hom.Finite) :
    IsFinite ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ q) := by
  let ι := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  have : IsProper (ι ≫ q) := hP
  have hrange : ∀ x, ι x ∈ (T : Set A) := fun x => by
    have : ι x ∈ Set.range ι.base := ⟨x, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hresh : ∀ x, ((ι ≫ q).residueFieldMap x).hom.Finite := fun x => by
    rw [residueFieldMap_comp_hom]
    exact RingHom.Finite.comp (residueFieldMap_finite_of_surjectiveOnStalks ι x)
      (hres _ (hrange x))
  have := LocallyQuasiFinite.of_finite_preimage_singleton (ι ≫ q)
    (finite_preimage_singleton_of_finite_residueFieldMap (ι ≫ q) hresh)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (ι ≫ q)

end Points

namespace SmallEtale

section Presentation

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The image in `V` of a support of `X_V` finite over `V`. -/
public abbrev finiteSupportImage (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    Set ((SmallEtale.toScheme B Y.obj Y.property).obj V) :=
  (B.inclusion.map (baseChangeObjProjection B f V)).base '' E.1

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The image in `V` of a support finite over `V` is closed. -/
public theorem isClosed_finiteSupportImage (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) : IsClosed (finiteSupportImage f V E) := by
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := E.property
  have : IsFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := hfin
  have h := (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)).isClosedMap.isClosed_range
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange] at h

/-- A finite sum of sheafified generators of `f_{p!} F` is supported in the union of the images
of their supports. -/
public theorem supportSection_sum_generator_subset (V : SmallEtale B Y.obj Y.property) {n : ℕ}
    (E : Fin n → FiniteSupport B f V) (a : ∀ i, (finiteSupportDiagram B f F V).obj (E i)) :
    supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F) V
        (∑ i, (finiteSupportPushforwardGenerator B f F V (E i) ≫
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B f
              (fun _ => inferInstance)).val.obj F)).app (op V)) (a i)) ⊆
      ⋃ i, finiteSupportImage f V (E i) := by
  refine Finset.sum_induction _ (fun z => supportSection B Y.obj Y.property
    ((fShriekFunctor.{u, v} B f).obj F) V z ⊆ ⋃ i, finiteSupportImage f V (E i)) ?_ ?_ ?_
  · exact fun z z' hz hz' => (supportSection_add_subset B Y.obj Y.property _ V z z').trans
      (Set.union_subset hz hz')
  · intro x hx
    exact absurd (show x ∈ (zeroOpen B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F) V 0 :
      Set _) by rw [zeroOpen_zero]; trivial) hx
  · intro i _
    exact supportSection_toSheafify_generator_subset B F V (E i) (a i) _
      (isClosed_iUnion_of_finite fun i => isClosed_finiteSupportImage f V (E i))
      ((Set.subset_preimage_image _ _).trans (Set.preimage_mono (Set.subset_iUnion
        (fun i => finiteSupportImage f V (E i)) i)))

/-- **Local presentation of a section of `f_! F`.** Every point of an object `V` of the small
étale site of `Y` is the image of a point of an affine étale neighbourhood `U ⟶ V` over which a
given section of `f_! F` is a finite sum of sheafified generators `(E, a)`, `E` a support of `X_U`
finite over `U`. -/
public theorem exists_affine_presentation (V : SmallEtale B Y.obj Y.property)
    (t : ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op V))
    (p : (SmallEtale.toScheme B Y.obj Y.property).obj V) :
    ∃ (U : SmallEtale B Y.obj Y.property) (j : U ⟶ V)
      (q : (SmallEtale.toScheme B Y.obj Y.property).obj U),
      AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj U) ∧
      (SmallEtale.toScheme B Y.obj Y.property).map j q = p ∧
      ∃ (n : ℕ) (E : Fin n → FiniteSupport B f U)
        (a : ∀ i, (finiteSupportDiagram B f F U).obj (E i)),
        ((fShriekFunctor.{u, v} B f).obj F).obj.map j.op t =
          ∑ i, (finiteSupportPushforwardGenerator B f F U (E i) ≫
            (toSheafify (SmallEtale.topology B Y.obj Y.property)
              ((finiteSupportPushforward.{u, max (u + 1) v} B f
                (fun _ => inferInstance)).val.obj F)).app (op U)) (a i) := by
  let J := SmallEtale.topology B Y.obj Y.property
  let P := (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).val.obj F
  have := GrothendieckTopology.preservesSheafification_forget_addCommGrpCat.{max (u + 1) v} J
  have := GrothendieckTopology.isLocallySurjective_toSheafify_type_of_univLE.{max (u + 1) v} J
    (P ⋙ forget AddCommGrpCat.{max (u + 1) v})
  have : Presheaf.IsLocallySurjective J (toSheafify J P) := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  obtain ⟨U₁, j₁, hj₁, q₁, hq₁⟩ := geometricPointFiber_jointly_surjective B Y.obj Y.property
    (geometricPointOfEtalePoint B Y.obj Y.property V p) _
    (Presheaf.imageSieve_mem J (toSheafify J P) (U := op V) t)
    (geometricPointOfEtalePointLift B Y.obj Y.property V p)
  let u₁ := q₁.1.base default
  have hu₁ : (SmallEtale.toScheme B Y.obj Y.property).map j₁ u₁ = p := by
    have h : (q₁.1 ≫ (SmallEtale.toScheme B Y.obj Y.property).map j₁).base default =
        (geometricPointOfEtalePointLift B Y.obj Y.property V p).1.base default :=
      congrArg (fun m : (geometricPointOfEtalePoint B Y.obj Y.property V p).source ⟶
        (SmallEtale.toScheme B Y.obj Y.property).obj V => m.base default)
        (congrArg Subtype.val hq₁)
    exact h.trans (geometricPointOfEtalePointLift_base B Y.obj Y.property V p)
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hu₀, -⟩ :=
    ((SmallEtale.toScheme B Y.obj Y.property).obj U₁).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ u₁) isOpen_univ
  let ι := openObjectι B Y.obj Y.property U₁ U₀
  obtain ⟨q, hq⟩ : u₁ ∈ Set.range ((SmallEtale.toScheme B Y.obj Y.property).map ι).base := by
    rwa [openObjectι_range]
  obtain ⟨x, hx⟩ := (Presheaf.imageSieve (toSheafify J P) t).downward_closed hj₁ ι
  obtain ⟨n, E, a, hxa⟩ := exists_finiteSupport_sum B f F (openObject B Y.obj Y.property U₁ U₀) x
  refine ⟨openObject B Y.obj Y.property U₁ U₀, ι ≫ j₁, q, hU₀, ?_, n, E, a, ?_⟩
  · rwa [Functor.map_comp, Scheme.Hom.comp_apply, hq]
  · refine hx.symm.trans ?_
    rw [hxa]
    exact map_sum ((toSheafify J P).app (op (openObject B Y.obj Y.property U₁ U₀))).hom _ _

end Presentation

section Finite

variable {B : BigEtaleSite.{u}} {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- For an étale `U ⟶ W ×_Z Y`, the composite `X_U ⟶ U ⟶ W ×_Z Y ⟶ W` is locally quasi-finite:
it is `X_U ⟶ X_{W ×_Z Y} = X_W ⟶ W`, an étale morphism followed by the base change of the locally
quasi-finite `f ≫ g`. -/
public theorem locallyQuasiFinite_baseChangeObjProjection_comp (W : SmallEtale B Z.obj Z.property)
    {U : SmallEtale B Y.obj Y.property} (j : U ⟶ baseChange B g W) :
    LocallyQuasiFinite ((B.inclusion.map (baseChangeObjProjection B f U) ≫
      (SmallEtale.toScheme B Y.obj Y.property).map j) ≫
        B.inclusion.map (pullback.fst W.obj.hom g)) := by
  have e : (B.inclusion.map (baseChangeObjProjection B f U) ≫
      (SmallEtale.toScheme B Y.obj Y.property).map j) ≫
        B.inclusion.map (pullback.fst W.obj.hom g) =
      (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map j) ≫
        sepCompMap B f g W ≫ B.inclusion.map (pullback.fst W.obj.hom (f ≫ g)) :=
    (congrArg (· ≫ B.inclusion.map (pullback.fst W.obj.hom g))
      (toScheme_baseChange_comp_fst B f (baseChange B g W) U j).symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (sepCompMap_fst B f g W).symm))
  rw [e]
  have : Etale ((SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map j)) :=
    etale_toScheme_map _
  have := (locallyQuasiFinite_of_etale
    ((SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map j))).2
  have : IsIso (sepCompMap B f g W) :=
    ((SmallEtale.toScheme B X.obj X.property).mapIso
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.app W)).isIso_hom
  have : IsOpenImmersion (sepCompMap B f g W) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (MorphismProperty.comp_mem _ _ _ inferInstance
      (locallyQuasiFinite_baseChangeProjection B (f ≫ g) W))

omit [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)] in
/-- **The points of the support of a section of `f_! F` over `W ×_Z Y` have residue fields
finite over `W`.** Étale locally around a point `t` of the support the section is a finite sum
of generators, so a point `u` over `t` is the image of a point `e` of a support finite over the
étale neighbourhood; `e` lies on `X_U`, which is locally quasi-finite over `W`, so `κ(e)` is
finite over `κ(w)`, and `κ(t) ⊆ κ(e)`. -/
public theorem finite_residueFieldMap_of_mem_supportSection (W : SmallEtale B Z.obj Z.property)
    (τ : ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (baseChange B g W)))
    (t : (SmallEtale.toScheme B Y.obj Y.property).obj (baseChange B g W))
    (ht : t ∈ supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F)
      (baseChange B g W) τ) :
    ((B.inclusion.map (pullback.fst W.obj.hom g)).residueFieldMap t).hom.Finite := by
  obtain ⟨U, j, u, -, rfl, n, E, a, hsum⟩ := exists_affine_presentation f F (baseChange B g W) τ t
  have hu : u ∈ supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F) U
      (((fShriekFunctor.{u, v} B f).obj F).obj.map j.op τ) := by
    rwa [supportSection_map]
  rw [hsum] at hu
  obtain ⟨_, ⟨i, rfl⟩, e, -, rfl⟩ := supportSection_sum_generator_subset f F U E a hu
  let ψ := B.inclusion.map (baseChangeObjProjection B f U) ≫
    (SmallEtale.toScheme B Y.obj Y.property).map j
  let q := B.inclusion.map (pullback.fst W.obj.hom g)
  have : LocallyQuasiFinite (ψ ≫ q) := locallyQuasiFinite_baseChangeObjProjection_comp f g W j
  have hφ : ((ψ ≫ q).residueFieldMap e).hom.Finite :=
    residueField_finite_of_locallyQuasiFinite (ψ ≫ q) e
  rw [residueFieldMap_comp_hom ψ q e] at hφ
  exact Stacks.SteinFactorization.ringHom_finite_of_comp _ _ (ψ.residueFieldMap e).hom.injective hφ

omit [IsSeparated (B.inclusion.map g)] in
/-- **The support of a section of `g_!(f_! F)` is finite over the base.** For a section `τ` of
`g_!(f_! F)` over `W`, the support of the corresponding section of `f_! F` over `W ×_Z Y` is
proper over `W`, and its points have residue fields finite over `W`, so it is an eligible
support of Stacks 0F6M for `g`. -/
public theorem isFiniteSupport_properSupportSection (W : SmallEtale B Z.obj Z.property)
    (τ : ((properSupportFunctor.{u, max (u + 1) v} B g).obj
      ((fShriekFunctor.{u, v} B f).obj F)).obj.obj (op W)) :
    IsFiniteSupport B g W (supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F)
      (baseChange B g W) (properSupportSection B g _ W τ)) := by
  have := locallyOfFiniteType_baseChangeProjection B g W
  let T : Closeds ((SmallEtale.toScheme B Y.obj Y.property).obj (baseChange B g W)) :=
    ⟨_, isClosed_supportSection B Y.obj Y.property _ _ (properSupportSection B g _ W τ)⟩
  have hP : IsProperOver (B.inclusion.map (pullback.fst W.obj.hom g)) T := τ.2
  refine ⟨_, (Scheme.IdealSheafData.vanishingIdeal T).subschemeι, inferInstance,
    isFinite_of_isProperOver_of_finite_residueFieldMap (B.inclusion.map
      (pullback.fst W.obj.hom g)) T hP fun t ht =>
      finite_residueFieldMap_of_mem_supportSection f g F W _ t ht, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end Finite

section Stalk

/-- A point of a scheme finite over `S` lying over the image of a geometric point `s` is hit by a
lift of `s`: the fibre product with `Spec κ(s)` is finite over `Spec κ(s)`, so discrete, and its
closed points are `κ(s)`-points. -/
public theorem exists_comp_eq_of_isFinite {T : Scheme.{u}} (s : GeometricPoint T)
    {Q S : Scheme.{u}} (h : Q ⟶ S) [IsFinite h] (c : s.source ⟶ S) (q : Q)
    (hq : h q = c (IsLocalRing.closedPoint s.residueField)) :
    ∃ e : s.source ⟶ Q, e ≫ h = c := by
  obtain ⟨r, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := c) q
    (IsLocalRing.closedPoint s.residueField) hq
  have hd := (pullback.snd h c).isDiscrete_preimage_singleton
    (IsLocalRing.closedPoint s.residueField)
  have huniv : (pullback.snd h c) ⁻¹' {IsLocalRing.closedPoint s.residueField} =
      Set.univ := Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  have hd' : _root_.IsDiscrete (Set.univ : Set ↥(pullback h c)) := huniv ▸ hd
  rw [isDiscrete_univ_iff] at hd'
  refine ⟨pointOfClosedPoint (pullback.snd h c) r (isClosed_discrete _) ≫ pullback.fst h c, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

variable {B : BigEtaleSite.{u}} {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)] in
/-- A lift of a geometric point `s` of `Z` to `W ×_Z Y` through the projection to an étale
neighbourhood `(W, w)` of `s` is the lift of the point of the geometric fibre of `g` it defines. -/
public theorem exists_fiberPointLift_eq (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (q : s.source ⟶ (SmallEtale.toScheme B Y.obj Y.property).obj (baseChange B g W))
    (hq : q ≫ B.inclusion.map (pullback.fst W.obj.hom g) = w.1) :
    ∃ y : GeometricFiberPoint B g s, fiberPointLift B g s W w y = q := by
  have hpb := (IsPullback.of_hasPullback W.obj.hom g).map B.inclusion
  refine ⟨⟨q ≫ B.inclusion.map (pullback.snd W.obj.hom g), ?_⟩, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) hpb.w.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hq).trans w.2)))
  · refine hpb.hom_ext ?_ ?_
    · exact (fiberPointLift_comp_fst B g s W w _).trans hq.symm
    · exact fiberPointLift_comp_snd B g s W w _

omit [IsSeparated (B.inclusion.map g)] in
/-- **Germs at the geometric fibre determine germs of `g_!(f_! F)`.** An element of the stalk of
`g_!(f_! F)` at a geometric point `s` of `Z` whose germs at all the points of the geometric fibre
of `g` over `s` vanish is zero: the support of a representing section is finite over the étale
neighbourhood `W` and has no point over `s`, since such a point would lift to a point of the
geometric fibre at which the germ is nonzero; so it misses the inverse image of an open
neighbourhood of the image of `s` in `W`, on which the section vanishes. -/
public theorem properSupportStalkEval_injective (s : GeometricPoint Z.obj)
    (τ : ↑(etaleStalk B Z.obj Z.property s ((properSupportFunctor.{u, max (u + 1) v} B g).obj
      ((fShriekFunctor.{u, v} B f).obj F)).obj))
    (h : ∀ y : GeometricFiberPoint B g s,
      properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s y τ = 0) : τ = 0 := by
  obtain ⟨W, w, t, rfl⟩ := exists_etaleGerm_eq B Z.obj Z.property s _ τ
  let G := (fShriekFunctor.{u, v} B f).obj F
  let π := B.inclusion.map (pullback.fst W.obj.hom g)
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := isFiniteSupport_properSupportSection f g F W t
  have : IsImmersion i := hi
  have : IsFinite (i ≫ π) := hfin
  have hnot : ∀ z : Zs, (i ≫ π) z ≠ w.1 (IsLocalRing.closedPoint s.residueField) := by
    intro z hz
    obtain ⟨e, he⟩ := exists_comp_eq_of_isFinite s (i ≫ π) w.1 z hz
    obtain ⟨y, hy⟩ := exists_fiberPointLift_eq g s W w (e ≫ i) ((Category.assoc _ _ _).trans he)
    have h0 := h y
    rw [properSupportStalkEval_germ, etaleGerm_eq_zero_iff_mem_zeroOpen] at h0
    have hmem : (fiberPointElement B g s W w y).1 default ∈
        supportSection B Y.obj Y.property G (baseChange B g W)
          (properSupportSection B g G W t) := by
      change (fiberPointLift B g s W w y) default ∈ _
      rw [hy, ← hrange]
      exact ⟨e default, rfl⟩
    exact hmem h0
  let W₀ : ((SmallEtale.toScheme B Z.obj Z.property).obj W).Opens :=
    ⟨_, (i ≫ π).isClosedMap.isClosed_range.isOpen_compl⟩
  have hw : w.1 default ∈ (W₀ : Set _) := by
    rintro ⟨z, hz⟩
    exact hnot z (hz.trans (congrArg w.1 (Subsingleton.elim _ _)))
  let ι₀ := openObjectι B Z.obj Z.property W W₀
  have h0 : ((properSupportFunctor.{u, max (u + 1) v} B g).obj G).obj.map ι₀.op t = 0 := by
    apply Subtype.ext
    change G.obj.map ((smallEtaleBaseChange B g).map ι₀).op (properSupportSection B g G W t) = 0
    refine eq_zero_of_supportSection_eq_empty B Y.obj Y.property G _ _ ?_
    rw [supportSection_map]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    rw [← hrange] at hx
    obtain ⟨z, hz⟩ := hx
    let A := (SmallEtale.toScheme B Y.obj Y.property).map ((smallEtaleBaseChange B g).map ι₀)
    have hc := congrArg (fun m => m.base x) (toScheme_baseChange_comp_fst B g W
      (openObject B Z.obj Z.property W W₀) ι₀)
    have h1 : ((B.inclusion.map (pullback.fst (openObject B Z.obj Z.property W W₀).obj.hom g)
        ≫ (SmallEtale.toScheme B Z.obj Z.property).map ι₀)).base x ∈
        (W₀ : Set ((SmallEtale.toScheme B Z.obj Z.property).obj W)) := by
      rw [← openObjectι_range B Z.obj Z.property W W₀]
      exact ⟨_, rfl⟩
    exact (hc ▸ h1 : (A ≫ π).base x ∈ (W₀ : Set ((SmallEtale.toScheme B Z.obj Z.property).obj W)))
      ⟨z, congrArg π.base hz⟩
  rw [← etaleGerm_openObjectLift B Z.obj Z.property s _ W w W₀ hw t, h0]
  exact etaleGerm_zero B Z.obj Z.property s _ _ _

omit [IsSeparated (B.inclusion.map g)] in
/-- **Only finitely many germs at the geometric fibre are nonzero.** For an element of the stalk
of `g_!(f_! F)` at `s`, the points of the geometric fibre of `g` over `s` at which its germ is
nonzero correspond to lifts of `s` into the support of a representing section, which is finite
over the étale neighbourhood; there are finitely many such lifts. -/
public theorem finite_properSupportStalkEval_ne_zero (s : GeometricPoint Z.obj)
    (τ : ↑(etaleStalk B Z.obj Z.property s ((properSupportFunctor.{u, max (u + 1) v} B g).obj
      ((fShriekFunctor.{u, v} B f).obj F)).obj)) :
    {y : GeometricFiberPoint B g s |
      properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s y τ ≠ 0}.Finite := by
  obtain ⟨W, w, t, rfl⟩ := exists_etaleGerm_eq B Z.obj Z.property s _ τ
  let G := (fShriekFunctor.{u, v} B f).obj F
  let π : (SmallEtale.toScheme B Y.obj Y.property).obj (baseChange B g W) ⟶
      (SmallEtale.toScheme B Z.obj Z.property).obj W :=
    B.inclusion.map (pullback.fst W.obj.hom g)
  have : LocallyOfFiniteType π := locallyOfFiniteType_baseChangeProjection B g W
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := isFiniteSupport_properSupportSection f g F W t
  have : IsImmersion i := hi
  have : IsFinite (i ≫ π) := hfin
  refine Set.Finite.of_finite_image (f := fun y => fiberPointLift B g s W w y)
    ((finite_setOf_comp_eq_of_isImmersion π i w.1).subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨fiberPointLift_comp_fst B g s W w y, ?_⟩
    by_contra hn
    apply hy
    rw [properSupportStalkEval_germ]
    refine etaleGerm_eq_zero_of_notMem_supportSection B Y.obj Y.property _ G _ _ _ ?_
    rw [← hrange]
    change (fiberPointLift B g s W w y) default ∉ _
    rwa [Subsingleton.elim (default : s.source) (IsLocalRing.closedPoint s.residueField)]
  · intro y₁ _ y₂ _ h12
    exact Subtype.ext ((fiberPointLift_comp_snd B g s W w y₁).symm.trans
      ((congrArg (· ≫ B.inclusion.map (pullback.snd W.obj.hom g)) h12).trans
        (fiberPointLift_comp_snd B g s W w y₂)))

end Stalk

section Iso

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The stalk map of `c'` at a geometric point of `Z`. -/
public abbrev sepCompShriekStalkMap (s : GeometricPoint Z.obj) :
    ↑(etaleStalk B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj) →+
      ↑(etaleStalk B Z.obj Z.property s ((properSupportFunctor.{u, max (u + 1) v} B g).obj
        ((fShriekFunctor.{u, v} B f).obj F)).obj) :=
  (colim.map (Functor.whiskerLeft (CategoryOfElements.π
    (geometricPointFiber B Z.obj Z.property s)).op (sepCompShriekMap B f g F).hom)).hom

/-- The stalk map of `c'` is injective: the stalk decomposition of an element is read off from
the germs of its image at the points of the geometric fibre of `g`. -/
public theorem sepCompShriekStalkMap_injective (s : GeometricPoint Z.obj) :
    Function.Injective (sepCompShriekStalkMap B f g F s) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom).1
    inferInstance ?_
  rw [map_zero]
  refine DFinsupp.ext fun x => ?_
  rw [DFinsupp.zero_apply]
  have h := sepCompShriekMap_stalk B f g F s (compFiberPoint B f g s x)
    (compFiberPointLift B f g s x) t
  have h2 : ((fShriekStalkIso.{u, v} B f _ F).hom
      (properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s (compFiberPoint B f g s x)
        (sepCompShriekStalkMap B f g F s t)) : fiberStalks.{u, max (u + 1) v} B f _ F)
        (compFiberPointLift B f g s x) = 0 := by
    rw [ht, map_zero, map_zero]
    rfl
  exact h.symm.trans h2

/-- The stalk map of `c'` is surjective: an element of the stalk of `g_!(f_! F)` has only
finitely many nonzero germs at the points of the geometric fibre of `g`, which assemble through
the regrouping of the geometric fibre of `f ≫ g` into an element of the stalk of `(f ≫ g)_! F`
whose image has the same germs, hence is the given element. -/
public theorem sepCompShriekStalkMap_surjective (s : GeometricPoint Z.obj) :
    Function.Surjective (sepCompShriekStalkMap B f g F s) := by
  intro τ
  let G := (fShriekFunctor.{u, v} B f).obj F
  have hfin := finite_properSupportStalkEval_ne_zero f g F s τ
  classical
  let η : fiberStalks.{u, max (u + 1) v} B g s G :=
    DFinsupp.mk hfin.toFinset fun y => properSupportStalkEval B g G s y.1 τ
  have hη : ∀ y, η y = properSupportStalkEval B g G s y τ := by
    intro y
    by_cases hy : y ∈ hfin.toFinset
    · exact DFinsupp.mk_of_mem hy
    · rw [DFinsupp.mk_of_notMem hy]
      exact not_not.1 fun hne => hy (hfin.mem_toFinset.2 (Ne.symm hne))
  let t := (fShriekStalkIso.{u, v} B (f ≫ g) s F).inv
    ((compFiberStalksEquiv B f g s F).symm η)
  refine ⟨t, sub_eq_zero.1 (properSupportStalkEval_injective f g F s _ fun y => ?_)⟩
  rw [map_sub, sub_eq_zero]
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B f
    (y.toGeometricPoint B g s) F).hom).1 inferInstance (DFinsupp.ext fun x => ?_)
  refine (sepCompShriekMap_stalk B f g F s y x t).trans ?_
  rw [Iso.inv_hom_id_apply, ← compFiberStalksMap_apply B f g s F]
  change ((fShriekStalkIso.{u, v} B f _ F).hom
    ((compFiberStalksEquiv B f g s F ((compFiberStalksEquiv B f g s F).symm η) :
      fiberStalks.{u, max (u + 1) v} B g s G) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x = _
  rw [AddEquiv.apply_symm_apply, hη]

/-- `c'` is an isomorphism: it is bijective on every geometric stalk. -/
public instance isIso_sepCompShriekMap : IsIso (sepCompShriekMap B f g F) := by
  have : ∀ s : GeometricPoint Z.obj, IsIso (((geometricPointSitePoint B Z.obj Z.property
      s).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).map (sepCompShriekMap B f g F)) :=
    fun s => (ConcreteCategory.isIso_iff_bijective _).2
      ⟨sepCompShriekStalkMap_injective B f g F s, sepCompShriekStalkMap_surjective B f g F s⟩
  exact (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Z.obj
    Z.property).jointlyReflectsIsomorphisms.isIso _

/-- **Stacks 0F79.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site with `f`
and `f ≫ g` locally quasi-finite (locally of finite type and locally quasi-finite) and `g`
separated and locally of finite type. Then there is a canonical isomorphism of functors on
abelian étale sheaves `(g ∘ f)_! ≅ g_! ∘ f_!`, where `f_!` and `(g ∘ f)_!` are the direct images
with compact support of locally quasi-finite morphisms (Stacks 0F6R) and `g_!` is the
proper-support direct image of Stacks 0F4X. Its component at `F` is the map `c'` of the source,
`AlgebraicGeometry.SmallEtale.sepCompShriekMap`: the sheafification of the map sending a local
generator `(T, s)` of `(g ∘ f)_{p!} F` over `W` to the generator `(T, s)` of `f_{p!} F` over
`W ×_Z Y`, through `X_{W ×_Z Y} = X_W`. -/
@[stacks 0F79 "the canonical isomorphism g_! ∘ f'_! ≅ f_!"]
public def fShriekCompProperIso :
    fShriekFunctor.{u, v} B (f ≫ g) ≅
      fShriekFunctor.{u, v} B f ⋙ properSupportFunctor.{u, max (u + 1) v} B g :=
  NatIso.ofComponents (fun F => asIso (sepCompShriekMap B f g F))
    (fun φ => (sepCompShriekMap_naturality B f g φ).symm)

/-- The component of the isomorphism of Stacks 0F79 is the map `c'`. -/
@[simp]
public theorem fShriekCompProperIso_hom_app :
    (fShriekCompProperIso B f g).hom.app F = sepCompShriekMap B f g F :=
  rfl

end Iso

end SmallEtale

end AlgebraicGeometry

end
