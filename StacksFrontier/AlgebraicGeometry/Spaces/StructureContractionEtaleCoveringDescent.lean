module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionEtaleLocal

/-!
# Descent of `c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` along an étale covering of a base

Let `c : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and `f : Y ⟶ T` a morphism to a scheme `T` of the site. Let `{τᵢ : Tᵢ ⟶ T}` be an étale
covering family of `T` (étale and jointly surjective) and, for every `i`, let

```
Xᵢ --> X
|cᵢ    |c
Yᵢ --> Y
|      |f
Tᵢ --> T
```

be cartesian squares. If every `cᵢ` has `𝒪_{Yᵢ} = cᵢ,*𝒪_{Xᵢ}` and `R¹cᵢ,*𝒪_{Xᵢ} = 0`
(`AlgebraicGeometry.Space.IsStructureContraction`), then so does `c`. This is the étale locality
on the base of condition (1) of Stacks 0E8A used to glue local stabilizations; it extends the
case of a single surjective étale morphism of
`StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionEtaleLocal` to a covering family.

The family `{Yᵢ ⟶ Y}` need not be indexed so that a single member is surjective, and `Y` need not
be a scheme: for every étale chart `W ⟶ Y`, the fibre products `W ×_T Tᵢ` form an étale covering
family of the scheme `W`, and they are charts of the `Yᵢ`.

## Main results

* `AlgebraicGeometry.Space.exists_mem_forall_smallEtalePostcomp_iso_of_isPullback_of_covering`:
  every étale chart of `Y` has a covering sieve whose members are charts of some `Yᵢ`.
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_smallEtaleRingRestriction_map`: the restrictions
  to the `Yᵢ` jointly reflect isomorphisms of sheaves of rings.
* `AlgebraicGeometry.Space.isZero_of_forall_isZero_etaleModulePullback`: they jointly detect the
  zero module.
* `AlgebraicGeometry.Space.isStructureContraction_of_isPullback_of_covering`: the descent of
  `IsStructureContraction`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] etaleModulePullback_additive

section Covering

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {Y : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} {f : Y ⟶ schemeSpace T}
  {ι : Type u} {Tᵢ : ι → BigFppfOver B S hS} {τ : ∀ i, Tᵢ i ⟶ T}
  (hτet : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (τ i)))
  (hτsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (τ i)))
  {Yᵢ : ι → AlgebraicSpaces B S hS} {p : ∀ i, Yᵢ i ⟶ Y} {q : ∀ i, Yᵢ i ⟶ schemeSpace (Tᵢ i)}
  (hsq : ∀ i, IsPullback (p i) (q i) f (schemeSpaceMap (τ i)))

local notation "𝒯" => BigFppfOver.toScheme B S hS

include hτet hsq in
/-- The base change of an étale morphism of schemes of the site is étale. -/
theorem isEtale_of_isPullback_of_etale (i : ι) : IsEtale B S hS (p i).hom :=
  isEtale_of_isPullback B S hS (q i) (p i) (schemeSpaceMap (τ i)) f (hsq i).flip
    ((isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS (τ i)).2 (hτet i)))

/-- **Base change of a cartesian square along a pullback of representables.** Given a cartesian
square `Y' ⟶ Y`, `Y' ⟶ yoneda T'` over `F : Y ⟶ yoneda T` and `yoneda τ`, and a morphism
`g : yoneda X ⟶ Y` lifting `yoneda w`, the projection `yoneda (X ×_T T') ⟶ yoneda X` is a
pullback of `Y' ⟶ Y` along `g`. -/
private theorem exists_isPullback_yoneda_map_pullback_fst {C : Type*} [Category C] {X T T' : C}
    (w : X ⟶ T) (τ : T' ⟶ T) [HasPullback w τ] {Y Y' : Cᵒᵖ ⥤ Type _} {F : Y ⟶ yoneda.obj T}
    {P : Y' ⟶ Y} {Q : Y' ⟶ yoneda.obj T'} (hsq : IsPullback P Q F (yoneda.map τ))
    (g : yoneda.obj X ⟶ Y) (hw : yoneda.map w = g ≫ F) :
    ∃ v : yoneda.obj (pullback w τ) ⟶ Y', v ≫ P = yoneda.map (pullback.fst w τ) ≫ g ∧
      IsPullback v (yoneda.map (pullback.fst w τ)) P g := by
  refine ⟨hsq.lift (yoneda.map (pullback.fst w τ) ≫ g) (yoneda.map (pullback.snd w τ)) ?_,
    hsq.lift_fst _ _ _, IsPullback.of_right ?_ (hsq.lift_fst _ _ _) hsq.flip⟩
  · have h := congrArg yoneda.map (pullback.condition (f := w) (g := τ))
    simp only [Functor.map_comp] at h
    rw [Category.assoc, ← hw]
    exact h
  · rw [hsq.lift_snd, ← hw]
    exact ((IsPullback.of_hasPullback w τ).map yoneda).flip

include hτet hτsurj hsq in
/-- **The charts of the members of a base-changed étale covering cover.** Let `{τᵢ : Tᵢ ⟶ T}`
be an étale covering family of a scheme `T` of the site and `Yᵢ = Y ×_T Tᵢ` for an algebraic
space `Y` over `T`. Every étale scheme chart `W` of `Y` has a covering sieve whose members are all
isomorphic to charts of `Y` obtained by postcomposing a chart of some `Yᵢ` with `Yᵢ ⟶ Y`. -/
theorem exists_mem_forall_smallEtalePostcomp_iso_of_isPullback_of_covering
    (hp : ∀ i, IsEtale B S hS (p i).hom) (W : SmallEtale B S hS Y.1) :
    ∃ R : Sieve W, R ∈ SmallEtale.topology B S hS Y.1 W ∧
      ∀ ⦃W' : SmallEtale B S hS Y.1⦄ (a : W' ⟶ W), R a →
        ∃ (i : ι) (W'' : SmallEtale B S hS (Yᵢ i).1),
          Nonempty ((smallEtalePostcomp B S hS (p i) (hp i)).obj W'' ≅ W') := by
  have : PreservesLimitsOfShape WalkingCospan (𝒯) := comp_preservesLimitsOfShape _ _
  let w : W.1.left ⟶ T := yoneda.preimage (W.1.hom ≫ f.hom)
  have hw : yoneda.map w = W.1.hom ≫ f.hom := yoneda.map_preimage _
  have hP : ∀ i, IsPullback ((𝒯).map (pullback.fst w (τ i))) ((𝒯).map (pullback.snd w (τ i)))
      ((𝒯).map w) ((𝒯).map (τ i)) := fun i => (IsPullback.of_hasPullback w (τ i)).map (𝒯)
  have hfstEt : ∀ i, Etale ((𝒯).map (pullback.fst w (τ i))) := fun i =>
    MorphismProperty.of_isPullback (hP i).flip (hτet i)
  choose v hv₁ hvsq using fun i => exists_isPullback_yoneda_map_pullback_fst w (τ i)
    (AlgebraicSpaces.isPullback_hom B S hS (hsq i)) W.1.hom hw
  let Vc : ι → SmallEtale B S hS Y.1 := fun i =>
    ⟨CostructuredArrow.mk (yoneda.map (pullback.fst w (τ i)) ≫ W.1.hom),
      etale_comp_of_scheme B S hS (pullback.fst w (τ i)) W.1.hom (hfstEt i) W.property⟩
  let a : ∀ i, Vc i ⟶ W := fun i =>
    ObjectProperty.homMk (CostructuredArrow.homMk (pullback.fst w (τ i)) rfl)
  let E : PreZeroHypercover.{u + 1} ((SmallEtale.toSchemes B S hS Y.1).obj W) :=
    { I₀ := ULift.{u + 1} ι
      X := fun i => (SmallEtale.toSchemes B S hS Y.1).obj (Vc i.down)
      f := fun i => (SmallEtale.toSchemes B S hS Y.1).map (a i.down) }
  have hE : _root_.AlgebraicGeometry.IsEtaleCovering (⟨_, E⟩ : Covering B.Schemes) := by
    change (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map]
    change Presieve.map B.inclusion (Presieve.ofArrows E.X E.f) ∈ Scheme.etalePrecoverage _
    rw [Presieve.map_ofArrows]
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => hfstEt i.down⟩
    obtain ⟨i, y, hy⟩ := hτsurj ((𝒯).map w x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨⟨i⟩, (hP i).isoPullback.inv z, ?_⟩
    change ((𝒯).map (pullback.fst w (τ i))) ((hP i).isoPullback.inv z) = x
    rw [← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst, hz]
  let Rpre : Presieve W :=
    Presieve.ofArrows (fun i : ULift.{u + 1} ι => Vc i.down) (fun i => a i.down)
  have hpre : Rpre ∈ SmallEtale.precoverage B S hS Y.1 W := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact B.presieve₀_mem_etalePrecoverage E hE
  refine ⟨Sieve.generate Rpre, Precoverage.generate_mem_toGrothendieck hpre, ?_⟩
  rintro W' g ⟨Z, h, k, hk, rfl⟩
  obtain ⟨⟨i⟩⟩ := hk
  have hφ : Etale ((𝒯).map h.hom.left) := etale_toScheme_toOver_map B S hS _ h
  let W'' : SmallEtale B S hS (Yᵢ i).1 :=
    ⟨CostructuredArrow.mk (yoneda.map h.hom.left ≫ v i),
      etale_comp_of_scheme B S hS h.hom.left (v i) hφ (presheaf_etale_of_isEtale B S hS
        (isEtale_of_isPullback_yoneda B S hS (hvsq i).flip
          ((isEtale_iff_presheaf_of_yoneda B S hS _).2 W.property)))⟩
  refine ⟨i, W'', ⟨ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  change 𝟙 _ ≫ W'.1.hom = (yoneda.map h.hom.left ≫ v i) ≫ (p i).hom
  rw [Category.id_comp, Category.assoc, hv₁, ← CostructuredArrow.w h.hom]
  rfl

include hτet hτsurj hsq in
/-- **The restrictions to the members of a base-changed étale covering jointly reflect
isomorphisms of sheaves of rings.** -/
theorem isIso_of_forall_isIso_smallEtaleRingRestriction_map
    (hp : ∀ i, IsEtale B S hS (p i).hom)
    {F G : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}} (φ : F ⟶ G)
    (hφ : ∀ i, IsIso ((smallEtaleRingRestriction B S hS (p i) (hp i)).map φ)) : IsIso φ := by
  refine Sheaf.isIso_of_forall_exists_mem_isIso_app φ fun W => ?_
  obtain ⟨R, hR, hRW⟩ :=
    exists_mem_forall_smallEtalePostcomp_iso_of_isPullback_of_covering hτet hτsurj hsq hp W
  refine ⟨R, hR, fun W' a ha => ?_⟩
  obtain ⟨i, W'', ⟨e⟩⟩ := hRW a ha
  have := hφ i
  have h1 : IsIso (φ.hom.app (op ((smallEtalePostcomp B S hS (p i) (hp i)).obj W''))) :=
    inferInstanceAs
      (IsIso (((smallEtaleRingRestriction B S hS (p i) (hp i)).map φ).hom.app (op W'')))
  have : IsIso (φ.hom.app (op W') ≫ G.obj.map e.op.hom) := by
    rw [← φ.hom.naturality e.op.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.obj.map e.op.hom)

include hτet hτsurj hsq in
/-- **The restrictions to the members of a base-changed étale covering jointly detect the zero
module.** -/
theorem isZero_of_forall_isZero_etaleModulePullback (hp : ∀ i, IsEtale B S hS (p i).hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : ∀ i, IsZero ((etaleModulePullback.{u, u} B S hS (p i) (hp i)).obj M)) : IsZero M := by
  rw [SheafOfModules.isZero_iff_forall_isZero_obj]
  intro W
  suffices hAb : IsZero (((SheafOfModules.toSheaf _).obj M).obj.obj (Opposite.op W)) by
    exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 hAb)
  obtain ⟨R, hR, hRW⟩ :=
    exists_mem_forall_smallEtalePostcomp_iso_of_isPullback_of_covering hτet hτsurj hsq hp W
  refine CategoryTheory.Sheaf.isZero_obj_of_mem_of_forall_isZero
    ((SheafOfModules.toSheaf _).obj M) hR fun W' a ha => ?_
  obtain ⟨i, W'', ⟨e⟩⟩ := hRW a ha
  have : Subsingleton
      (M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (p i) (hp i)).obj W''))) :=
    ModuleCat.isZero_iff_subsingleton.1
      ((SheafOfModules.isZero_iff_forall_isZero_obj _ _).1 (hM i) W'')
  exact (AddCommGrpCat.isZero_iff_subsingleton.2 this).of_iso (M.val.presheaf.mapIso e.op)

include hτet hτsurj hsq in
/-- **`c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` descend along an étale covering of a base.** Let
`f : Y ⟶ T` be a morphism from an algebraic space to a scheme of the site, `{τᵢ : Tᵢ ⟶ T}` an
étale covering family, `Yᵢ = Y ×_T Tᵢ` and `cᵢ : Xᵢ ⟶ Yᵢ` the base change of `c : X ⟶ Y`. If
every `cᵢ` has `cᵢ♯ : 𝒪_{Yᵢ} ≅ cᵢ,*𝒪_{Xᵢ}` and `R¹cᵢ,*𝒪_{Xᵢ} = 0`, so does `c`. -/
theorem isStructureContraction_of_isPullback_of_covering {X : AlgebraicSpaces B S hS}
    {c : X ⟶ Y} {Xᵢ : ι → AlgebraicSpaces B S hS} {pX : ∀ i, Xᵢ i ⟶ X} {cᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i}
    (hX : ∀ i, IsPullback (pX i) (cᵢ i) c (p i))
    (h : ∀ i, IsStructureContraction B S hS (cᵢ i)) : IsStructureContraction B S hS c := by
  have hp := isEtale_of_isPullback_of_etale hτet hsq
  refine ⟨isIso_of_forall_isIso_smallEtaleRingRestriction_map hτet hτsurj hsq hp _
      fun i => (isIso_structureSharp_iff_of_isPullback (hX i) (hp i)).1 (h i).1, ?_⟩
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine isZero_of_forall_isZero_etaleModulePullback hτet hτsurj hsq hp _ fun i => ?_
  have := hasInjectiveResolutions_modules B S hS (Xᵢ i).1 (Xᵢ i).2
  exact IsZero.of_iso (h i).2
    (firstHigherDirectImageStructureSheafEtaleBaseChangeIso (hX i) (hp i)).symm

end Covering

end AlgebraicGeometry.Space

end
