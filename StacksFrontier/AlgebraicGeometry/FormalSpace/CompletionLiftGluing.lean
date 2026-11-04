module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionComparison
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Dilatations
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# Lifting a morphism of completions, locally on the source

Let `f : X' ⟶ X` and `g : Y ⟶ X` be morphisms of presheaves on the big fppf site of `S`, let
`T` be a set of points of `X` and let `α : Y_{/T} ⟶ X'_{/T}` be a morphism of the completion
subfunctors (the sections with point-set image in the inverse images of `T`). This file
isolates the gluing part of the proof of the fullness half of **Stacks 0GDR**: a morphism
`a : Y ⟶ X'` over `X` whose completion is `α` may be constructed étale locally on `Y`.

A morphism `c : Z ⟶ X'` *lifts `α` along* `v : Z ⟶ Y`
(`AlgebraicGeometry.Space.IsCompletionLift`) when `c ≫ f = v ≫ g` and `c` agrees with `α ∘ v`
on every section of `Z` whose image in `Y` lies over `T`. A lift along `𝟙 Y` is exactly a
morphism over `X` whose completion is `α`
(`AlgebraicGeometry.Space.completionSubfunctorMap_eq_of_isCompletionLift`).

## Main results

* `AlgebraicGeometry.Space.IsCompletionLift.eq`: two lifts along the same morphism out of a
  locally Noetherian algebraic space agree, when `f` is an isomorphism over the complement `U`
  of `T`. This is the faithfulness half of Stacks 0GDR, read for lifts.
* `AlgebraicGeometry.Space.exists_isCompletionLift_of_range_subset`: over the part of `Y` lying
  over `U` a lift always exists, because `f` is an isomorphism there and the completion along `T`
  of something lying over `U` has sections only over objects covered by the empty sieve
  (`AlgebraicGeometry.Space.isCompletionLift_of_range_subset`). This is the step "the completion
  of `Y ∖ g⁻¹T` is empty" of the source.
* `AlgebraicGeometry.Space.exists_isCompletionLift_of_ofArrows`: lifts on the members of a
  covering family of a representable presheaf which agree on the pairwise fibre products glue.
* `AlgebraicGeometry.Space.exists_isCompletionLift_id_of_atlas`: a lift along a surjective étale
  atlas of `Y` which is invariant under the kernel pair descends to a lift along `𝟙 Y`.
* `AlgebraicGeometry.Space.exists_isCompletionLift_id_of_hasLocalCompletionLifts`: the gluing
  step of the source assembled: if every point over `T` of every Noetherian affine object of the
  site mapping to `Y` has an étale neighbourhood along which `α` lifts
  (`AlgebraicGeometry.Space.HasLocalCompletionLifts`), then `α` lifts along `𝟙 Y`. The étale
  neighbourhoods of the points over `T`, together with the open complement of the inverse image
  of `T`, cover; lifts agree on overlaps by the faithfulness half.
* `AlgebraicGeometry.Space.hasLocalCompletionLifts_of_hasAffineChartCompletionLifts`: the
  reduction of the source to the case where `Y ⟶ X` factors through a Noetherian affine object
  étale over `X`.
* `AlgebraicGeometry.Space.completionOverFunctor_map_injective`: the faithfulness half of Stacks
  0GDR for the completion functor `AlgebraicGeometry.Space.completionOverFunctor` of Stacks 0AR5.
* `AlgebraicGeometry.Space.exists_completionOverFunctor_map_eq_of_hasLocalCompletionLifts`: the
  fullness half of Stacks 0GDR for `completionOverFunctor`, from local lifts.

## What is not here

The local lifts themselves, `AlgebraicGeometry.Space.HasAffineChartCompletionLifts`, are not
proved in this file; their affine case `AlgebraicGeometry.Space.AffineCompletionLiftProperty` is
`AlgebraicGeometry.Space.affineCompletionLiftProperty`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift`, which also states Stacks 0GDR
(`AlgebraicGeometry.Space.completionOverFunctor_map_bijective`). In the source they come from
Stacks 0AR4 applied to the affine pieces of `W = Y_{/T} ×_{X'_{/T}} V_{/T}` for an affine `V`
étale over `X' ×_X X₁`, followed by Stacks 0AR3; the étale neighbourhood of a point `q` over `T`
is the étale `Y'' ⟶ Y'` of Stacks 0AR3, whose completion is an isomorphism, composed with the
algebraization `Y' ⟶ Y₁` of a piece of `W` containing a point over `q`. No attribute for
Stacks 0GDR is placed in this file.

## References

* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X' ⟶ X} {g : Y ⟶ X}
  {T : Set (points B S hS X)}

/-- A morphism `c : Z ⟶ X'` *lifts* the morphism of completions `α : Y_{/T} ⟶ X'_{/T}` along
`v : Z ⟶ Y` when it lies over `X` (`c ≫ f = v ≫ g`) and agrees with `α ∘ v` on every section of
`Z` whose image in `Y` has point-set image over `T`. -/
def IsCompletionLift
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Z ⟶ Y) (c : Z ⟶ X') : Prop :=
  c ≫ f = v ≫ g ∧ ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj W)
    (hz : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop (v.app W z)),
    (α.app W ⟨ULift.up (v.app W z), hz⟩).1.down = c.app W z

/-- The morphism out of a representable presheaf determined by the image of a section. -/
theorem yonedaEquiv_symm_app_eq_comp {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Z ⟶ Z')
    (W : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj W) :
    yonedaEquiv.symm (v.app W z) = (yonedaEquiv (X := W.unop) (F := Z)).symm z ≫ v :=
  (yonedaEquiv_symm_naturality_right _ v z).symm

section

variable {α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor}

/-- The value of `α` on a section depends only on the underlying section of `Y`. -/
theorem completionHom_app_congr (W : (BigFppfOver B S hS)ᵒᵖ) {y₁ y₂ : Y.obj W}
    (h₁ : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y₁)
    (h₂ : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y₂) (h : y₁ = y₂) :
    (α.app W ⟨ULift.up y₁, h₁⟩).1.down = (α.app W ⟨ULift.up y₂, h₂⟩).1.down := by
  subst h
  rfl

/-- The value of `α` on the restriction of a section is the restriction of its value. -/
theorem completionHom_app_map {W W' : (BigFppfOver B S hS)ᵒᵖ} (w : W ⟶ W') (y : Y.obj W)
    (h : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y)
    (h' : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W'.unop (Y.map w y)) :
    (α.app W' ⟨ULift.up (Y.map w y), h'⟩).1.down = X'.map w (α.app W ⟨ULift.up y, h⟩).1.down :=
  congrArg (fun s => s.1.down) (NatTrans.naturality_apply α w ⟨ULift.up y, h⟩)

/-- A lift along `v` restricts to a lift along `w ≫ v`. -/
theorem IsCompletionLift.comp {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {v : Z ⟶ Y}
    {c : Z ⟶ X'} (h : IsCompletionLift α v c) (w : Z' ⟶ Z) :
    IsCompletionLift α (w ≫ v) (w ≫ c) :=
  ⟨by rw [Category.assoc, h.1, Category.assoc], fun W z hz => h.2 W (w.app W z) hz⟩

/-- A lift along `𝟙 Y` is a morphism over `X` whose completion along `T` is `α`. -/
theorem completionSubfunctorMap_eq_of_isCompletionLift {a : Y ⟶ X'} (hag : a ≫ f = g)
    (h : IsCompletionLift α (𝟙 Y) a) :
    completionSubfunctorMap B S hS a (pointsMap B S hS Y g ⁻¹' T) (pointsMap B S hS X' f ⁻¹' T)
      (image_preimage_subset_preimage_of_comp_eq B S hS hag T) = α := by
  ext W x
  apply Subtype.ext
  apply ULift.ext
  exact (h.2 W x.1.down x.2).symm

/-- A morphism over `X` lifts its own completion along `𝟙 Y`. -/
theorem isCompletionLift_of_completionSubfunctorMap_eq {a : Y ⟶ X'} (hag : a ≫ f = g)
    (h : completionSubfunctorMap B S hS a (pointsMap B S hS Y g ⁻¹' T)
      (pointsMap B S hS X' f ⁻¹' T) (image_preimage_subset_preimage_of_comp_eq B S hS hag T) = α) :
    IsCompletionLift α (𝟙 Y) a := by
  refine ⟨by rw [hag, Category.id_comp], fun W y hy => ?_⟩
  subst h
  rfl

/-- **Lifts are unique**, along a morphism out of a locally Noetherian algebraic space, when
`f` is an isomorphism over the complement of `T`: this is the faithfulness half of Stacks 0GDR,
`AlgebraicGeometry.Space.eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd`, since two
lifts along `v` have the same completion `α ∘ v_{/T}`. -/
theorem IsCompletionLift.eq {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX' : IsAlgebraicSpace B S hS X')
    (hZnoeth : HasEtaleLocalProperty B S hS Z
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    {v : Z ⟶ Y} {c₁ c₂ : Z ⟶ X'} (h₁ : IsCompletionLift α v c₁)
    (h₂ : IsCompletionLift α v c₂) : c₁ = c₂ := by
  refine eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd B S hS hZ hX' hZnoeth hX'noeth
    hT hfU h₁.1 h₂.1 ?_
  ext W x
  apply Subtype.ext
  apply ULift.ext
  have hx : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop (v.app W x.1.down) :=
    ((completionSubfunctorMap B S hS v (pointsMap B S hS Z (v ≫ g) ⁻¹' T)
      (pointsMap B S hS Y g ⁻¹' T)
      (image_preimage_subset_preimage_of_comp_eq B S hS (rfl : v ≫ g = v ≫ g) T)).app W x).2
  exact (h₁.2 W x.1.down hx).symm.trans (h₂.2 W x.1.down hx)

/-- A morphism over `X` out of something lying over the complement of `T` is a lift: the
sections of the completion along `T` live over objects covered by the empty sieve, over which
the sheaf `X'` has at most one section. -/
theorem isCompletionLift_of_range_subset
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {v : Z ⟶ Y} {c : Z ⟶ X'} (hc : c ≫ f = v ≫ g)
    (hv : Set.range (pointsMap B S hS Z (v ≫ g)) ⊆ Tᶜ) : IsCompletionLift α v c := by
  refine ⟨hc, fun W z hz => ?_⟩
  have hbot : (⊥ : Sieve W.unop) ∈ BigFppfOver.topology B S hS W.unop := by
    refine bot_mem_of_mem_openSubspaceOfPoints B S hS (F := Y) (W := ∅) rfl
      (s := v.app W z) ?_
    rw [mem_openSubspaceOfPoints_iff]
    rintro _ ⟨p, rfl⟩
    have h1 := (hasImageIn_iff_range_subset B S hS _ W.unop (v.app W z)).mp hz ⟨p, rfl⟩
    have h2 : pointsMap B S hS Y g (pointsMap B S hS (yoneda.obj W.unop)
        (yonedaEquiv.symm (v.app W z)) p) ∈ Tᶜ := by
      rw [← pointsMap_comp_apply, yonedaEquiv_symm_app_eq_comp, Category.assoc,
        pointsMap_comp_apply]
      exact hv ⟨_, rfl⟩
    exact (h2 h1).elim
  exact (subsingleton_of_bot_mem B S hS hX' hbot).elim _ _

/-- **Over the complement of `T` a lift exists**: a morphism `v : Z ⟶ Y` whose composite with
`g` has point-set image off `T` factors through the open subspace `U` of `X` with points `Tᶜ`,
over which `f` is an isomorphism. -/
theorem exists_isCompletionLift_of_range_subset
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Z ⟶ Y)
    (hv : Set.range (pointsMap B S hS Z (v ≫ g)) ⊆ Tᶜ) : ∃ c, IsCompletionLift α v c := by
  have hle : Subfunctor.range (v ≫ g) ≤ openSubspaceOfPoints B S hS X Tᶜ := by
    rintro W _ ⟨z, rfl⟩
    rw [mem_openSubspaceOfPoints_iff]
    rintro _ ⟨p, rfl⟩
    rw [yonedaEquiv_symm_app_eq_comp, pointsMap_comp_apply]
    exact hv ⟨_, rfl⟩
  refine ⟨Subfunctor.lift (v ≫ g) hle ≫
      inv (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι) ≫
      pullback.fst f (openSubspaceOfPoints B S hS X Tᶜ).ι,
    isCompletionLift_of_range_subset hX' ?_ hv⟩
  rw [Category.assoc, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc,
    Subfunctor.lift_ι]

/-- Restricting a section of `Y` lying over `T` gives a section lying over `T`. -/
private theorem hasImageIn_map {W W' : (BigFppfOver B S hS)ᵒᵖ} (w : W ⟶ W') {y : Y.obj W}
    (h : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y) :
    HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W'.unop (Y.map w y) :=
  (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).map w
    (show ULift.up y ∈ (completionSubfunctor B S hS Y _).obj W from h)

/-- **Lifting is local on a representable source.** If `c` lies over `X` and becomes a lift
after restriction along every member of a covering sieve, it is a lift. -/
theorem isCompletionLift_of_sieve (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {Y₀ : BigFppfOver B S hS} {v : yoneda.obj Y₀ ⟶ Y} {c : yoneda.obj Y₀ ⟶ X'}
    (hc : c ≫ f = v ≫ g) (R : Sieve Y₀) (hR : R ∈ BigFppfOver.topology B S hS Y₀)
    (hloc : ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ Y₀), R k →
      IsCompletionLift α (yoneda.map k ≫ v) (yoneda.map k ≫ c)) :
    IsCompletionLift α v c := by
  refine ⟨hc, fun W z hz => ?_⟩
  have hsep := (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) X').mp hX') _
    ((BigFppfOver.topology B S hS).pullback_stable z hR)).isSeparatedFor
  refine hsep.ext fun W' w hw => ?_
  have hz' : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W' (Y.map w.op (v.app W z)) :=
    hasImageIn_map w.op hz
  have nat : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : yoneda.obj Y₀ ⟶ F),
      t.app (op W') (𝟙 W' ≫ w ≫ z) = F.map w.op (t.app W z) := fun t => by
    rw [Category.id_comp]
    exact NatTrans.naturality_apply t w.op z
  have hid : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W'
      ((yoneda.map (w ≫ z) ≫ v).app (op W') (𝟙 W')) :=
    (congrArg (HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W') (nat v)).mpr hz'
  have key := (hloc (w ≫ z) hw).2 (op W') (𝟙 W') hid
  rw [← completionHom_app_map w.op (v.app W z) hz hz']
  exact (completionHom_app_congr (op W') hz' hid (nat v).symm).trans (key.trans (nat c))

/-- A lift along `𝟙 Y` is the same as a lift along every morphism out of a representable
presheaf. -/
theorem isCompletionLift_id_of_forall {a : Y ⟶ X'} (hag : a ≫ f = g)
    (h : ∀ (W : BigFppfOver B S hS) (y : yoneda.obj W ⟶ Y), IsCompletionLift α y (y ≫ a)) :
    IsCompletionLift α (𝟙 Y) a := by
  refine ⟨by rw [hag, Category.id_comp], fun W y hy => ?_⟩
  have e : ((yonedaEquiv (X := W.unop) (F := Y)).symm y).app W (𝟙 W.unop) = y := by
    show Y.map (𝟙 W.unop).op y = y
    rw [op_id, FunctorToTypes.map_id_apply]
  have hy' : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop
      (((yonedaEquiv (X := W.unop) (F := Y)).symm y).app W (𝟙 W.unop)) := by
    rw [e]
    exact hy
  have key := (h W.unop (yonedaEquiv.symm y)).2 W (𝟙 W.unop) hy'
  refine (completionHom_app_congr W hy hy' e.symm).trans (key.trans ?_)
  show a.app W (((yonedaEquiv (X := W.unop) (F := Y)).symm y).app W (𝟙 W.unop)) = a.app W y
  rw [e]

/-- **Gluing lifts over a covering family of a representable presheaf.** Lifts along the members
of a covering family `{V_i ⟶ Y₀}` which agree on the pairwise fibre products glue to a lift
along `v : h_{Y₀} ⟶ Y`. -/
theorem exists_isCompletionLift_of_ofArrows
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {Y₀ : BigFppfOver B S hS} (v : yoneda.obj Y₀ ⟶ Y) {I : Type u}
    {V : I → BigFppfOver B S hS} (π : ∀ i, V i ⟶ Y₀)
    (hπ : Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS Y₀)
    (c : ∀ i, yoneda.obj (V i) ⟶ X') (hc : ∀ i, IsCompletionLift α (yoneda.map (π i) ≫ v) (c i))
    (hcompat : ∀ i j, yoneda.map (pullback.fst (π i) (π j)) ≫ c i =
      yoneda.map (pullback.snd (π i) (π j)) ≫ c j) :
    ∃ c₀, IsCompletionLift α v c₀ := by
  have hsheaf : (Presieve.ofArrows V π).IsSheafFor X' :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) X').mp hX') _ hπ)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks X' π).mp hsheaf
    (fun i => yonedaEquiv (c i)) fun i j => by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality, hcompat i j]
  have hct : ∀ i, yoneda.map (π i) ≫ yonedaEquiv.symm t = c i := fun i => by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, ht i]
  have hc₀ : yonedaEquiv.symm t ≫ f = v ≫ g :=
    hom_ext_of_cover B S hS hX Y₀ V π hπ fun i => by
      rw [← Category.assoc, hct i, (hc i).1, Category.assoc]
  refine ⟨yonedaEquiv.symm t, isCompletionLift_of_sieve hX' hc₀ _ hπ fun W k hk => ?_⟩
  obtain ⟨_, u, _, ⟨i⟩, rfl⟩ := hk
  have := (hc i).comp (yoneda.map u)
  rw [Functor.map_comp, Category.assoc, Category.assoc, hct i]
  exact this

/-- **Descending a lift along a surjective étale atlas.** A lift along a surjective étale atlas
`p : h_{U₀} ⟶ Y` of an fppf sheaf `Y` whose two pullbacks to every represented kernel pair agree
descends to a morphism `a : Y ⟶ X'` over `X` lifting `α` along `𝟙 Y`. -/
theorem exists_isCompletionLift_id_of_atlas
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {U₀ : BigFppfOver B S hS} (p : yoneda.obj U₀ ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    {c₀ : yoneda.obj U₀ ⟶ X'} (hc₀ : IsCompletionLift α p c₀)
    (hcompat : ∀ (R : BigFppfOver B S hS) (s t : R ⟶ U₀),
      IsPullback (yoneda.map s) (yoneda.map t) p p → yoneda.map s ≫ c₀ = yoneda.map t ≫ c₀) :
    ∃ a : Y ⟶ X', a ≫ f = g ∧ IsCompletionLift α (𝟙 Y) a := by
  obtain ⟨a, ha, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hY hX' p hsurj hetale c₀ hcompat
  have hag : a ≫ f = g := hom_ext_of_etale_atlas B S hS hY hX p hsurj hetale (by
    rw [← Category.assoc, ha, hc₀.1])
  refine ⟨a, hag, isCompletionLift_id_of_forall hag fun W y => ?_⟩
  have hq := hsurj.rep
  refine isCompletionLift_of_sieve hX' (by rw [Category.assoc, hag])
    (Sieve.generate (Presieve.singleton (hq.snd y)))
    (sieve_generate_singleton_mem_topology_over B S hS _ (hsurj.property_snd y)
      (hetale.property _ _ _ (hq.isPullback y))) fun W' k hk => ?_
  obtain ⟨_, k', _, ⟨⟩, rfl⟩ := hk
  have hw : yoneda.map (hq.snd y) ≫ y = hq.fst y ≫ p := (hq.w y).symm
  have := (hc₀.comp (hq.fst y)).comp (yoneda.map k')
  have e1 : yoneda.map (k' ≫ hq.snd y) ≫ y = yoneda.map k' ≫ hq.fst y ≫ p := by
    rw [Functor.map_comp, Category.assoc, hw]
  have e2 : yoneda.map (k' ≫ hq.snd y) ≫ y ≫ a = yoneda.map k' ≫ hq.fst y ≫ c₀ := by
    rw [← Category.assoc, e1, Category.assoc, Category.assoc, ha]
  rw [e1, e2]
  exact this

/-! ### From completion subfunctors to completions

For fppf sheaves `Y` and `X'` the completion `Y_{/T}` of Stacks 0AMC is the completion
subfunctor itself (`AlgebraicGeometry.Space.completionSheafIsoSubfunctor`), so a morphism of
completions is the same as a morphism of completion subfunctors, and the completion of a morphism
over `X`, `AlgebraicGeometry.Space.completionOverFunctor`, is `completionSubfunctorMap`. -/

section Sheafified

/-- The morphism of completion subfunctors underlying a morphism of completions of fppf sheaves.
-/
noncomputable def completionSubfunctorHom (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : completionSheaf B S hS Y (pointsMap B S hS Y g ⁻¹' T) ⟶
      completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T)) :
    (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor :=
  (completionSheafIsoSubfunctor B S hS hY _).inv ≫ α.hom ≫
    (completionSheafIsoSubfunctor B S hS hX' _).hom

/-- The morphism of completion subfunctors underlying `α`, followed by the identification of the
completion subfunctor of `X'` with its sheafification, is `α`. -/
theorem completionSubfunctorHom_comp_inv (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : completionSheaf B S hS Y (pointsMap B S hS Y g ⁻¹' T) ⟶
      completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T)) :
    completionSubfunctorHom hY hX' α ≫
        (completionSheafIsoSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T)).inv =
      (completionSheafIsoSubfunctor B S hS hY (pointsMap B S hS Y g ⁻¹' T)).inv ≫ α.hom := by
  simp [completionSubfunctorHom]

/-- The completion of a morphism, transported along an equality of the source sets, is the
sheafification of `completionSubfunctorMap`. -/
private theorem toSheafify_comp_eqToHom_completionSheafMap {M N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : M ⟶ N) (T' : Set (points B S hS N)) {T₁ : Set (points B S hS M)}
    (h : T₁ = pointsMap B S hS M a ⁻¹' T') (ha : pointsMap B S hS M a '' T₁ ⊆ T') :
    (BigFppfOver.topology B S hS).toSheafify _ ≫
        (eqToHom (congrArg (completionSheaf B S hS M) h) ≫ completionSheafMap B S hS a T').hom =
      completionSubfunctorMap B S hS a T₁ T' ha ≫ (BigFppfOver.topology B S hS).toSheafify _ := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  show (BigFppfOver.topology B S hS).toSheafify _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS a T') = _
  rw [GrothendieckTopology.toSheafify_naturality]
  rfl

/-- The completion of a morphism over `X` is the sheafification of `completionSubfunctorMap`. -/
theorem toSheafify_comp_completionOverMap {M N : Over X} (a : M ⟶ N) :
    (BigFppfOver.topology B S hS).toSheafify _ ≫ (completionOverMap B S hS T a).hom =
      completionSubfunctorMap B S hS a.left (pointsMap B S hS M.left M.hom ⁻¹' T)
          (pointsMap B S hS N.left N.hom ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w a) T) ≫
        (BigFppfOver.topology B S hS).toSheafify _ :=
  toSheafify_comp_eqToHom_completionSheafMap a.left _ (preimage_pointsMap_over B S hS T a) _

/-- **A lift along `𝟙 Y` has completion `α`**: a morphism `a` over `X` lifting the morphism of
completion subfunctors underlying `α` is carried by completion along `T` to `α`. -/
theorem completionOverFunctor_map_eq_of_isCompletionLift
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f))
    (a : Over.mk g ⟶ Over.mk f)
    (ha : IsCompletionLift (completionSubfunctorHom hY hX' α.left) (𝟙 Y) a.left) :
    (completionOverFunctor B S hS T).map a = α := by
  have hsub := completionSubfunctorMap_eq_of_isCompletionLift (Over.w a) ha
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine (BigFppfOver.topology B S hS).sheafify_hom_ext _ _
    ((BigFppfOver.topology B S hS).sheafify_isSheaf _) ?_
  show (BigFppfOver.topology B S hS).toSheafify _ ≫ (completionOverMap B S hS T a).hom = _
  rw [toSheafify_comp_completionOverMap]
  show _ ≫ (completionSheafIsoSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T)).inv =
    (completionSheafIsoSubfunctor B S hS hY (pointsMap B S hS Y g ⁻¹' T)).inv ≫ α.left.hom
  rw [hsub]
  exact completionSubfunctorHom_comp_inv hY hX' α.left

/-- Completion along `T` determines the morphism of completion subfunctors. -/
theorem completionSubfunctorMap_eq_of_completionOverFunctor_map_eq
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X') {a b : Over.mk g ⟶ Over.mk f}
    (h : (completionOverFunctor B S hS T).map a = (completionOverFunctor B S hS T).map b) :
    completionSubfunctorMap B S hS a.left (pointsMap B S hS Y g ⁻¹' T)
        (pointsMap B S hS X' f ⁻¹' T)
        (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w a) T) =
      completionSubfunctorMap B S hS b.left (pointsMap B S hS Y g ⁻¹' T)
        (pointsMap B S hS X' f ⁻¹' T)
        (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w b) T) := by
  rw [← cancel_mono (completionSheafIsoSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T)).inv]
  have ha := toSheafify_comp_completionOverMap (T := T) a
  have hb := toSheafify_comp_completionOverMap (T := T) b
  have hl : (completionOverMap B S hS T a).hom = (completionOverMap B S hS T b).hom :=
    congrArg (fun φ : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f) => φ.left.hom) h
  exact ha.symm.trans ((congrArg _ hl).trans hb)

end Sheafified

end

/-! ### Assembling the lifts -/

section Assembly

/-- An object of the site with locally Noetherian underlying scheme is a locally Noetherian
algebraic space: the identity is a surjective étale atlas. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_yoneda {U : BigFppfOver B S hS}
    (hU : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)) :
    HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) := by
  refine ⟨U, 𝟙 _, presheaf_id_of_iso B S hS _ (fun _ _ φ hφ => ?_) U,
    presheaf_id_of_iso B S hS _ (fun _ _ φ hφ => ?_) U, hU⟩
  · have : IsIso ((BigFppfOver.toScheme B S hS).map φ) := Functor.map_isIso _ φ
    exact (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map φ))
  · have : IsIso ((BigFppfOver.toScheme B S hS).map φ) := Functor.map_isIso _ φ
    exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map φ))

/-- The first projection of a fibre product of the site along an étale morphism is étale. -/
theorem etale_toScheme_map_pullback_fst {A A' Z : BigFppfOver B S hS} (p : A ⟶ Z) (q : A' ⟶ Z)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst p q)) :=
  (presheaf_yoneda_map_of_inverseImage B S hS (P := @Etale) inferInstance q hq).property
    (yoneda.map p) (yoneda.map (pullback.snd p q)) (pullback.fst p q)
    ((IsPullback.of_hasPullback p q).flip.map yoneda)

/-- The inclusion of an open of the underlying scheme of an object of the site is étale. -/
private theorem etale_toScheme_map_openIncl {Z : BigFppfOver B S hS}
    (O : ((BigFppfOver.toScheme B S hS).obj Z).Opens) :
    Etale ((BigFppfOver.toScheme B S hS).map (openIncl B S hS Z O)) := by
  rw [toScheme_map_openIncl]
  exact inferInstanceAs (Etale O.ι)

/-- An affine open of a locally Noetherian object of the site is a Noetherian affine object. -/
private theorem isNoetherian_toScheme_openObj {Z : BigFppfOver B S hS}
    (hZ : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z))
    {O : ((BigFppfOver.toScheme B S hS).obj Z).Opens} (hO : IsAffineOpen O) :
    _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (openObj B S hS Z O)) :=
  have : IsAffine (Scheme.Opens.toScheme O) := hO
  { toIsLocallyNoetherian := inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
      (Scheme.Opens.toScheme O))
    toCompactSpace := inferInstanceAs (CompactSpace (Scheme.Opens.toScheme O)) }

variable {α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor}

/-- The local existence statement the fullness half of Stacks 0GDR reduces to: over every
Noetherian affine object `Y₁` of the site mapping to `Y`, every point lying over `T` has an
étale neighbourhood along which `α` lifts. -/
def HasLocalCompletionLifts
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor) : Prop :=
  ∀ (Y₁ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) →
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y₁) →
    ∀ (v₁ : yoneda.obj Y₁ ⟶ Y) (q : points B S hS (yoneda.obj Y₁)),
      pointsMap B S hS _ (v₁ ≫ g) q ∈ T →
      ∃ (V : BigFppfOver B S hS) (π : V ⟶ Y₁), Etale ((BigFppfOver.toScheme B S hS).map π) ∧
        q ∈ Set.range (pointsMap B S hS _ (yoneda.map π)) ∧
        ∃ c, IsCompletionLift α (yoneda.map π ≫ v₁) c

/-- Every point of a locally Noetherian object of the site mapping to `Y` has an étale
neighbourhood along which `α` lifts, given local lifts over Noetherian affine objects at the
points lying over `T`. Off `T` the lift is provided by
`AlgebraicGeometry.Space.exists_isCompletionLift_of_range_subset`. -/
theorem exists_etale_isCompletionLift_of_hasLocalCompletionLifts
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hloc : HasLocalCompletionLifts α) {Y₀ : BigFppfOver B S hS}
    (hY₀ : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y₀))
    (v : yoneda.obj Y₀ ⟶ Y) (y : (BigFppfOver.toScheme B S hS).obj Y₀) :
    ∃ (V : BigFppfOver B S hS) (π : V ⟶ Y₀), Etale ((BigFppfOver.toScheme B S hS).map π) ∧
      y ∈ Set.range ((BigFppfOver.toScheme B S hS).map π) ∧
      ∃ c, IsCompletionLift α (yoneda.map π ≫ v) c := by
  classical
  obtain ⟨q, hq⟩ := surjective_pointsToScheme B S hS Y₀ y
  by_cases hqT : pointsMap B S hS _ (v ≫ g) q ∈ T
  · obtain ⟨O', hO', hyO, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj Y₀) (x := y) (U := ⊤)
      (show y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj Y₀).Opens) from trivial)
    let j := openIncl B S hS Y₀ O'
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS Y₀ O')) := hO'
    have := isNoetherian_toScheme_openObj hY₀ hO'
    obtain ⟨q₁, hq₁⟩ := surjective_pointsToScheme B S hS (openObj B S hS Y₀ O') ⟨y, hyO⟩
    have hq₁q : pointsMap B S hS _ (yoneda.map j) q₁ = q := by
      apply (bijective_pointsToScheme B S hS Y₀).1
      rw [pointsToScheme_pointsMap_yoneda, hq₁, hq]
      rfl
    obtain ⟨V, π, hπ, ⟨r, hr⟩, c, hc⟩ := hloc _ inferInstance inferInstance (yoneda.map j ≫ v) q₁
      (by rwa [Category.assoc, pointsMap_comp_apply, hq₁q])
    refine ⟨V, π ≫ j, ?_, ⟨pointsToScheme B S hS V r, ?_⟩, c, ?_⟩
    · rw [Functor.map_comp]
      exact MorphismProperty.comp_mem _ _ _ hπ (etale_toScheme_map_openIncl O')
    · rw [← pointsToScheme_pointsMap_yoneda, Functor.map_comp, pointsMap_comp_apply, hr, hq₁q, hq]
    · rw [Functor.map_comp, Category.assoc]
      exact hc
  · have hZ : IsClosed (pointsToScheme B S hS Y₀ '' (pointsMap B S hS _ (v ≫ g) ⁻¹' T)) :=
      isClosed_image_pointsToScheme B S hS Y₀ (hT.preimage (continuous_pointsMap B S hS _))
    let O : ((BigFppfOver.toScheme B S hS).obj Y₀).Opens := ⟨_, hZ.isOpen_compl⟩
    have hyO : y ∈ O := by
      rintro ⟨q', hq', hq'y⟩
      rw [← hq] at hq'y
      exact hqT ((bijective_pointsToScheme B S hS Y₀).1 hq'y ▸ hq')
    let j := openIncl B S hS Y₀ O
    refine ⟨_, j, etale_toScheme_map_openIncl O, ⟨⟨y, hyO⟩, rfl⟩, ?_⟩
    refine exists_isCompletionLift_of_range_subset hX' hfU _ ?_
    rintro _ ⟨r, rfl⟩ hr
    have hmem : pointsToScheme B S hS Y₀ (pointsMap B S hS _ (yoneda.map j) r) ∈ O := by
      rw [pointsToScheme_pointsMap_yoneda, toScheme_map_openIncl]
      exact (pointsToScheme B S hS _ r).2
    refine hmem ⟨_, ?_, rfl⟩
    rw [Set.mem_preimage, ← pointsMap_comp_apply]
    simpa only [Category.assoc] using hr

/-- **Lifts along a locally Noetherian representable source.** Given local lifts over
Noetherian affine objects at the points over `T`, `α` lifts along every morphism
`v : h_{Y₀} ⟶ Y` out of a locally Noetherian object of the site: the étale neighbourhoods of
`AlgebraicGeometry.Space.exists_etale_isCompletionLift_of_hasLocalCompletionLifts` cover `Y₀`,
and the lifts on them agree on overlaps by uniqueness of lifts. -/
theorem exists_isCompletionLift_of_hasLocalCompletionLifts
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : IsAlgebraicSpace B S hS X')
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hloc : HasLocalCompletionLifts α) {Y₀ : BigFppfOver B S hS}
    (hY₀ : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y₀))
    (v : yoneda.obj Y₀ ⟶ Y) : ∃ c, IsCompletionLift α v c := by
  choose V π hπ hπr c hc using
    exists_etale_isCompletionLift_of_hasLocalCompletionLifts hX'.isSheaf hT hfU hloc hY₀ v
  have hV : ∀ y, _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (V y)) := fun y => by
    have := hπ y
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map (π y))
  refine exists_isCompletionLift_of_ofArrows hX hX'.isSheaf v π
    (Space.sieve_ofArrows_mem_topology_of_etale B hS V π (fun y => ?_) hπ) c hc fun i j => ?_
  · obtain ⟨x, hx⟩ := hπr y
    exact ⟨y, x, hx⟩
  · have hP : _root_.AlgebraicGeometry.IsLocallyNoetherian
        ((BigFppfOver.toScheme B S hS).obj (pullback (π i) (π j))) := by
      have := etale_toScheme_map_pullback_fst (π i) (π j) (hπ j)
      have := hV i
      exact LocallyOfFiniteType.isLocallyNoetherian
        ((BigFppfOver.toScheme B S hS).map (pullback.fst (π i) (π j)))
    have e : yoneda.map (pullback.snd (π i) (π j)) ≫ yoneda.map (π j) ≫ v =
        yoneda.map (pullback.fst (π i) (π j)) ≫ yoneda.map (π i) ≫ v := by
      rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
        Category.assoc]
    have h₂ := (hc j).comp (yoneda.map (pullback.snd (π i) (π j)))
    rw [e] at h₂
    exact IsCompletionLift.eq (isAlgebraicSpace_yoneda B S hS _) hX'
      (hasEtaleLocalProperty_isLocallyNoetherian_yoneda hP) hX'noeth hT hfU
      ((hc i).comp (yoneda.map (pullback.fst (π i) (π j)))) h₂

/-- **The reduction of the fullness half of Stacks 0GDR to local lifts.** For a locally
Noetherian algebraic space `Y`, local lifts of `α` over Noetherian affine objects of the site at
the points over `T` produce a morphism `a : Y ⟶ X'` over `X` lifting `α`. -/
theorem exists_isCompletionLift_id_of_hasLocalCompletionLifts
    (hY : IsAlgebraicSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : IsAlgebraicSpace B S hS X')
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hloc : HasLocalCompletionLifts α) :
    ∃ a : Y ⟶ X', a ≫ f = g ∧ IsCompletionLift α (𝟙 Y) a := by
  obtain ⟨U₀, p, hsurj, hetale, hU₀⟩ := hYnoeth
  obtain ⟨c₀, hc₀⟩ :=
    exists_isCompletionLift_of_hasLocalCompletionLifts hX hX' hX'noeth hT hfU hloc hU₀ p
  refine exists_isCompletionLift_id_of_atlas hY.isSheaf hX hX'.isSheaf p hsurj hetale hc₀
    fun R s t hR => ?_
  have hRet : Etale ((BigFppfOver.toScheme B S hS).map t) :=
    hetale.property p (yoneda.map s) t hR
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) :=
    hU₀
  have hRnoeth : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj R) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map t)
  have h₂ := hc₀.comp (yoneda.map t)
  rw [← hR.w] at h₂
  exact IsCompletionLift.eq (isAlgebraicSpace_yoneda B S hS R) hX'
    (hasEtaleLocalProperty_isLocallyNoetherian_yoneda hRnoeth) hX'noeth hT hfU
    (hc₀.comp (yoneda.map s)) h₂

end Assembly

/-! ### Stacks 0GDR in the vocabulary of `completionOverFunctor` -/

section CompletionOverFunctor

/-- **The faithfulness half of Stacks 0GDR, for `completionOverFunctor`.** Two morphisms
`Y ⟶ X'` over `X` with the same completion along `T`, the completion being
`AlgebraicGeometry.Space.completionOverFunctor` as in Stacks 0AR5, are equal, when `Y` and `X'`
are locally Noetherian algebraic spaces, `T` is closed and `X' ⟶ X` is an isomorphism over the
complement of `T`. -/
theorem completionOverFunctor_map_injective
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    Function.Injective
      (fun a : Over.mk g ⟶ Over.mk f => (completionOverFunctor B S hS T).map a) := by
  intro a b h
  exact Over.OverMorphism.ext (eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd B S hS hY
    hX' hYnoeth hX'noeth hT hfU (Over.w a) (Over.w b)
    (completionSubfunctorMap_eq_of_completionOverFunctor_map_eq hX'.isSheaf h))

/-- **The fullness half of Stacks 0GDR, reduced to local lifts.** A morphism
`α : Y_{/T} ⟶ X'_{/T}` over `X_{/T}` is the completion of a morphism `Y ⟶ X'` over `X` as soon
as the morphism of completion subfunctors underlying it lifts étale locally around the points
over `T` of the Noetherian affine objects of the site mapping to `Y`
(`AlgebraicGeometry.Space.HasLocalCompletionLifts`). -/
theorem exists_completionOverFunctor_map_eq_of_hasLocalCompletionLifts
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f))
    (hloc : HasLocalCompletionLifts (completionSubfunctorHom hY.isSheaf hX'.isSheaf α.left)) :
    ∃ a : Over.mk g ⟶ Over.mk f, (completionOverFunctor B S hS T).map a = α := by
  obtain ⟨a, hag, ha⟩ :=
    exists_isCompletionLift_id_of_hasLocalCompletionLifts hY hYnoeth hX hX' hX'noeth hT hfU hloc
  exact ⟨Over.homMk a hag,
    completionOverFunctor_map_eq_of_isCompletionLift hY.isSheaf hX'.isSheaf α _ ha⟩

end CompletionOverFunctor

/-! ### Reduction to an affine étale chart of `X` -/

section AffineChart

variable {α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor}

/-- The local existence statement of `AlgebraicGeometry.Space.HasLocalCompletionLifts`, asked
only of Noetherian affine objects `Y₁` whose morphism to `X` factors through a Noetherian affine
object `X₁` étale over `X`. This is the situation the source reduces to before applying Stacks
0AR4 and Stacks 0AR3: "we may assume that `Y` is affine and that `g` factors as `Y ⟶ X₁` and an
étale morphism `X₁ ⟶ X` with `X₁` affine". -/
def HasAffineChartCompletionLifts
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor) : Prop :=
  ∀ (X₁ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj X₁) →
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj X₁) →
    ∀ (e : yoneda.obj X₁ ⟶ X), (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e →
    ∀ (Y₁ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) →
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y₁) →
    ∀ (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y), v₁ ≫ g = yoneda.map h ≫ e →
    ∀ q : points B S hS (yoneda.obj Y₁), pointsMap B S hS _ (v₁ ≫ g) q ∈ T →
      ∃ (V : BigFppfOver B S hS) (π : V ⟶ Y₁), Etale ((BigFppfOver.toScheme B S hS).map π) ∧
        q ∈ Set.range (pointsMap B S hS _ (yoneda.map π)) ∧
        ∃ c, IsCompletionLift α (yoneda.map π ≫ v₁) c

/-- **Reduction to an affine étale chart of `X`** (the second reduction step of the source's
proof of Stacks 0GDR). When `X` has a surjective étale atlas by a locally Noetherian scheme,
local lifts over Noetherian affine objects whose morphism to `X` factors through a Noetherian
affine étale chart give local lifts over all Noetherian affine objects.

The fibre product of the atlas with `Y₁ ⟶ X` is a scheme surjective and étale over `Y₁`; around
a point over `q` it contains an affine open whose image in the atlas lies in an affine open
`X₁`. -/
theorem hasLocalCompletionLifts_of_hasAffineChartCompletionLifts
    (hX : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (h : HasAffineChartCompletionLifts α) : HasLocalCompletionLifts α := by
  intro Y₁ hY₁a hY₁n v₁ q hq
  obtain ⟨U, p, hps, hpe, hU⟩ := hX
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hU
  let Pe := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let k := v₁ ≫ g
  let hrep := hpe.rep
  let P := hrep.pullback k
  let fst : P ⟶ U := hrep.fst' k
  let snd : P ⟶ Y₁ := hrep.snd k
  have hsq : yoneda.map fst ≫ p = yoneda.map snd ≫ k := by
    rw [Functor.relativelyRepresentable.map_fst']
    exact hrep.w k
  have hsnde : Etale ((BigFppfOver.toScheme B S hS).map snd) := hpe.property_snd k
  have hsnds : Surjective ((BigFppfOver.toScheme B S hS).map snd) := hps.property_snd k
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj P) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map snd)
  obtain ⟨z, hz⟩ := hsnds.surj (pointsToScheme B S hS Y₁ q)
  -- an affine open of the atlas around the image of `z`
  obtain ⟨O₁, hO₁, hxO₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme B S hS).obj U) (x := (BigFppfOver.toScheme B S hS).map fst z)
    (U := ⊤) (show _ ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) from trivial)
  -- an affine open of the fibre product around `z` mapping into it
  obtain ⟨O₀, hO₀, hzO₀, hO₀sub⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme B S hS).obj P) (x := z)
    (U := (BigFppfOver.toScheme B S hS).map fst ⁻¹ᵁ O₁) hxO₁
  let X₁ := openObj B S hS U O₁
  let Y₀ := openObj B S hS P O₀
  let jU := openIncl B S hS U O₁
  let jP := openIncl B S hS P O₀
  have hX₁a : IsAffine ((BigFppfOver.toScheme B S hS).obj X₁) := hO₁
  have hY₀a : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀) := hO₀
  have hjUo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU) := by
    rw [toScheme_map_openIncl]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O₁.ι)
  obtain ⟨h₀, hh₀⟩ := exists_factorization_of_isOpenImmersion jU hjUo (jP ≫ fst) (by
    rintro _ ⟨w, rfl⟩
    have hw : (BigFppfOver.toScheme B S hS).map fst w.1 ∈ O₁ := hO₀sub w.2
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [Functor.map_comp]
    show O₁.ι ⟨_, hw⟩ = (BigFppfOver.toScheme B S hS).map fst (O₀.ι w)
    rfl)
  let e : yoneda.obj X₁ ⟶ X := yoneda.map jU ≫ p
  have he : Pe.presheaf e := MorphismProperty.comp_mem Pe.presheaf _ _
    (MorphismProperty.relative_map (etale_toScheme_map_openIncl O₁)) hpe
  let v₀ : yoneda.obj Y₀ ⟶ Y := yoneda.map (jP ≫ snd) ≫ v₁
  have hv₀ : v₀ ≫ g = yoneda.map h₀ ≫ e := by
    show yoneda.map (jP ≫ snd) ≫ v₁ ≫ g = yoneda.map h₀ ≫ yoneda.map jU ≫ p
    rw [← Category.assoc (yoneda.map h₀), ← Functor.map_comp, hh₀, Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc, hsq]
  obtain ⟨q₀, hq₀⟩ := surjective_pointsToScheme B S hS Y₀ ⟨z, hzO₀⟩
  have hq₀q : pointsMap B S hS _ (yoneda.map (jP ≫ snd)) q₀ = q := by
    apply (bijective_pointsToScheme B S hS Y₁).1
    rw [pointsToScheme_pointsMap_yoneda, hq₀, Functor.map_comp, toScheme_map_openIncl]
    exact hz
  obtain ⟨V, π, hπ, ⟨r, hr⟩, c, hc⟩ := h X₁ hX₁a (isNoetherian_toScheme_openObj ‹_› hO₁) e he Y₀
    hY₀a (isNoetherian_toScheme_openObj ‹_› hO₀) h₀ v₀ hv₀ q₀ (by
    show pointsMap B S hS _ (yoneda.map (jP ≫ snd) ≫ v₁ ≫ g) q₀ ∈ T
    rw [pointsMap_comp_apply, hq₀q]
    exact hq)
  refine ⟨V, π ≫ jP ≫ snd, ?_, ⟨r, ?_⟩, c, ?_⟩
  · rw [Functor.map_comp, Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hπ
      (MorphismProperty.comp_mem _ _ _ (etale_toScheme_map_openIncl O₀) hsnde)
  · rw [Functor.map_comp, pointsMap_comp_apply, hr, hq₀q]
  · rw [Functor.map_comp, Category.assoc]
    exact hc

end AffineChart

/-! ### Base change of `X'` to an affine étale chart -/

section BaseChange

/-- Two morphisms into `X` agreeing after `g` and `g'` carry the same sections over `T`. -/
theorem hasImageIn_of_comp_eq {Y' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g' : Y' ⟶ X}
    {a : Z ⟶ Y} {b : Z ⟶ Y'} (hab : a ≫ g = b ≫ g') (W : (BigFppfOver B S hS)ᵒᵖ)
    (z : Z.obj W) (hz : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop (a.app W z)) :
    HasImageIn B S hS Y' (pointsMap B S hS Y' g' ⁻¹' T) W.unop (b.app W z) := by
  rw [hasImageIn_iff_range_subset] at hz ⊢
  rintro _ ⟨w, rfl⟩
  have := hz ⟨w, rfl⟩
  simp only [Set.mem_preimage, yonedaEquiv_symm_app_eq_comp, ← pointsMap_comp_apply,
    Category.assoc] at this ⊢
  rwa [← hab]

/-- The local existence statement over a Noetherian affine base, the case the source's proof
reduces to: `X₁` and `Y₁` Noetherian affine objects of the site, `X'₁` an algebraic space locally
of finite type over `X₁` which is an isomorphism over the complement of a closed `T₁`, and
`α₁ : Y_{1,/T₁} ⟶ X'_{1,/T₁}` a morphism of completion subfunctors over `X₁`. Every point of `Y₁`
over `T₁` then has an étale neighbourhood along which `α₁` lifts. -/
def AffineCompletionLiftProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ (X₁ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj X₁) →
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj X₁) →
  ∀ (T₁ : Set (points B S hS (yoneda.obj X₁))), IsClosed T₁ →
  ∀ (X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X'₁ →
  ∀ (f₁ : X'₁ ⟶ yoneda.obj X₁), IsLocallyOfFiniteType B S hS f₁ →
    IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS _ T₁ᶜ).ι) →
  ∀ (Y₁ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) →
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y₁) →
  ∀ (h : Y₁ ⟶ X₁)
    (α₁ : (completionSubfunctor B S hS (yoneda.obj Y₁)
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)).toFunctor ⟶
      (completionSubfunctor B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)).toFunctor),
    (∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : (yoneda.obj Y₁).obj W)
      (hy : HasImageIn B S hS (yoneda.obj Y₁) (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)
        W.unop y), f₁.app W (α₁.app W ⟨ULift.up y, hy⟩).1.down = (yoneda.map h).app W y) →
  ∀ q : points B S hS (yoneda.obj Y₁), pointsMap B S hS _ (yoneda.map h) q ∈ T₁ →
    ∃ (V : BigFppfOver B S hS) (π : V ⟶ Y₁), Etale ((BigFppfOver.toScheme B S hS).map π) ∧
      q ∈ Set.range (pointsMap B S hS _ (yoneda.map π)) ∧
      ∃ c, IsCompletionLift α₁ (yoneda.map π) c

variable {α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor}

/-- The section of `X' ×_X X₁` over `W` attached by `(α, h)` to a section `s` of `Y₁` over
`W` lying over `T`. -/
noncomputable def baseChangeCompletionLift
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) (W : (BigFppfOver B S hS)ᵒᵖ) (s : W.unop ⟶ Y₁)
    (hs : HasImageIn B S hS (yoneda.obj Y₁)
      (pointsMap B S hS _ (yoneda.map h) ⁻¹' (pointsMap B S hS _ e ⁻¹' T)) W.unop s) :
    yoneda.obj W.unop ⟶ pullback f e :=
  pullback.lift
    ((yonedaEquiv (X := W.unop) (F := X')).symm (α.app W ⟨ULift.up (v₁.app W s),
      hasImageIn_of_comp_eq (a := yoneda.map h) (g := e) hv.symm W s hs⟩).1.down)
    (yoneda.map (s ≫ h)) (by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
      refine (hα W _ _).trans ?_
      exact congrFun (congrArg (fun φ => (φ.app W : _ → _)) hv) s)

/-- The first projection of `baseChangeCompletionLift` to `X'` is the section that `α` attaches
to `v₁.app W s`. -/
theorem baseChangeCompletionLift_fst
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) (W : (BigFppfOver B S hS)ᵒᵖ) (s : W.unop ⟶ Y₁) (hs) :
    baseChangeCompletionLift hα e h v₁ hv W s hs ≫ pullback.fst f e =
      (yonedaEquiv (X := W.unop) (F := X')).symm (α.app W ⟨ULift.up (v₁.app W s),
        hasImageIn_of_comp_eq (a := yoneda.map h) (g := e) hv.symm W s hs⟩).1.down :=
  pullback.lift_fst _ _ _

/-- The second projection of `baseChangeCompletionLift` to `X₁` is `s ≫ h`. -/
theorem baseChangeCompletionLift_snd
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) (W : (BigFppfOver B S hS)ᵒᵖ) (s : W.unop ⟶ Y₁) (hs) :
    baseChangeCompletionLift hα e h v₁ hv W s hs ≫ pullback.snd f e = yoneda.map (s ≫ h) :=
  pullback.lift_snd _ _ _

/-- `baseChangeCompletionLift` is natural in `W`. -/
theorem baseChangeCompletionLift_naturality
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) {W W' : (BigFppfOver B S hS)ᵒᵖ} (k : W ⟶ W')
    (s : W.unop ⟶ Y₁) (hs) (hs') :
    yoneda.map k.unop ≫ baseChangeCompletionLift hα e h v₁ hv W s hs =
      baseChangeCompletionLift hα e h v₁ hv W' (k.unop ≫ s) hs' := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeCompletionLift_fst, baseChangeCompletionLift_fst,
      yonedaEquiv_symm_naturality_left]
    congr 1
    have h₁ : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop (v₁.app W s) :=
      hasImageIn_of_comp_eq (a := yoneda.map h) (g := e) hv.symm W s hs
    have h₂ := hasImageIn_map k h₁
    exact ((completionHom_app_map k _ h₁ h₂).symm.trans
      (completionHom_app_congr W' h₂ _ (NatTrans.naturality_apply v₁ k s).symm))
  · rw [Category.assoc, baseChangeCompletionLift_snd, baseChangeCompletionLift_snd,
      ← Functor.map_comp, Category.assoc]

/-- The section `baseChangeCompletionLift` of `X' ×_X X₁` lies over the inverse image of `T`
in `X₁`. -/
theorem hasImageIn_baseChangeCompletionLift
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) (W : (BigFppfOver B S hS)ᵒᵖ) (s : W.unop ⟶ Y₁) (hs) :
    HasImageIn B S hS (pullback f e)
      (pointsMap B S hS _ (pullback.snd f e) ⁻¹' (pointsMap B S hS _ e ⁻¹' T)) W.unop
      (yonedaEquiv (baseChangeCompletionLift hα e h v₁ hv W s hs)) := by
  rw [hasImageIn_iff_range_subset, Equiv.symm_apply_apply]
  rintro _ ⟨w, rfl⟩
  have hs' := (hasImageIn_iff_range_subset B S hS (X := yoneda.obj Y₁) _ W.unop s).mp hs ⟨w, rfl⟩
  rw [yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map s).symm] at hs'
  rw [Set.mem_preimage, Set.mem_preimage, ← pointsMap_comp_apply, ← pointsMap_comp_apply,
    ← Category.assoc, baseChangeCompletionLift_snd, Functor.map_comp, Category.assoc,
    pointsMap_comp_apply, pointsMap_comp_apply]
  exact hs'

/-- The morphism of completions `Y_{1,/T₁} ⟶ (X' ×_X X₁)_{/T₁}` induced by `α` and by
`h : Y₁ ⟶ X₁`, for a chart `e : X₁ ⟶ X` with `v₁ ≫ g = h ≫ e`: the morphism `α₁ = (α, h_{/T})` of
the source. -/
noncomputable def baseChangeCompletionHom
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y)
    {X₁ Y₁ : BigFppfOver B S hS} (e : yoneda.obj X₁ ⟶ X) (h : Y₁ ⟶ X₁) (v₁ : yoneda.obj Y₁ ⟶ Y)
    (hv : v₁ ≫ g = yoneda.map h ≫ e) :
    (completionSubfunctor B S hS (yoneda.obj Y₁)
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' (pointsMap B S hS _ e ⁻¹' T))).toFunctor ⟶
      (completionSubfunctor B S hS (pullback f e)
        (pointsMap B S hS _ (pullback.snd f e) ⁻¹' (pointsMap B S hS _ e ⁻¹' T))).toFunctor where
  app W := ↾fun s => ⟨ULift.up (yonedaEquiv (baseChangeCompletionLift hα e h v₁ hv W s.1.down s.2)),
    hasImageIn_baseChangeCompletionLift hα e h v₁ hv W s.1.down s.2⟩
  naturality W W' k := by
    ext s
    apply Subtype.ext
    apply ULift.ext
    exact (congrArg yonedaEquiv (baseChangeCompletionLift_naturality hα e h v₁ hv k s.1.down s.2
      _)).symm.trans (yonedaEquiv_naturality' _ k).symm

/-- **Base change to an affine étale chart** (the source's replacement of `X, T, X', α` by
`X₁, T₁, X'₁ = X' ×_X X₁, α₁ = (α, (g₁)_{/T₁})`). The local existence statement over a
Noetherian affine base, `AlgebraicGeometry.Space.AffineCompletionLiftProperty`, gives local
lifts over Noetherian affine charts of `X`: the base change `X' ×_X X₁ ⟶ X₁` is again an
algebraic space locally of finite type which is an isomorphism over the complement of
`T₁ = e⁻¹T`, and a lift of `α₁` composed with the projection to `X'` is a lift of `α`. -/
theorem hasAffineChartCompletionLifts_of_affineCompletionLiftProperty
    (hcore : AffineCompletionLiftProperty B S hS)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hf : IsLocallyOfFiniteType B S hS f) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y) :
    HasAffineChartCompletionLifts α := by
  intro X₁ hX₁a hX₁n e he Y₁ hY₁a hY₁n h v₁ hv q hq
  have hX'₁ : IsAlgebraicSpace B S hS (pullback f e) :=
    isAlgebraicSpace_pullback B S hS f e hX' (isAlgebraicSpace_yoneda B S hS X₁) hX
  have hf₁ : IsLocallyOfFiniteType B S hS (pullback.snd f e) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (pullback.fst f e) :
          (⟨pullback f e, hX'₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X', hX'⟩)
        (ObjectProperty.homMk (pullback.snd f e) : (⟨pullback f e, hX'₁⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj X₁, isAlgebraicSpace_yoneda B S hS X₁⟩)
        (ObjectProperty.homMk f : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
        (ObjectProperty.homMk e : (⟨yoneda.obj X₁, isAlgebraicSpace_yoneda B S hS X₁⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F))
        (IsPullback.of_hasPullback f e)
    exact (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hsq hf
  have hfU₁ : IsIso (pullback.snd (pullback.snd f e)
      (openSubspaceOfPoints B S hS _ (pointsMap B S hS _ e ⁻¹' T)ᶜ).ι) := by
    have := isIso_pullback_snd_preimage B S hS f e (openSubspaceOfPoints B S hS X Tᶜ) hfU
    rwa [preimage_openSubspaceOfPoints, Set.preimage_compl] at this
  obtain ⟨V, π, hπ, hqπ, c₁, hc₁⟩ := hcore X₁ hX₁a hX₁n _
    (hT.preimage (continuous_pointsMap B S hS e)) _ hX'₁ _ hf₁ hfU₁ Y₁ hY₁a hY₁n h
    (baseChangeCompletionHom hα e h v₁ hv) (fun W y hy => by
      show (pullback.snd f e).app W (yonedaEquiv
        (baseChangeCompletionLift hα e h v₁ hv W y hy)) = y ≫ h
      rw [← yonedaEquiv_comp, baseChangeCompletionLift_snd, yonedaEquiv_yoneda_map]) q (by
      show pointsMap B S hS _ e (pointsMap B S hS _ (yoneda.map h) q) ∈ T
      rw [← pointsMap_comp_apply, ← hv]
      exact hq)
  refine ⟨V, π, hπ, hqπ, c₁ ≫ pullback.fst f e, ?_, fun W z hz => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hc₁.1, Category.assoc, ← hv,
      Category.assoc]
  · have hset : pointsMap B S hS _ (yoneda.map h) ⁻¹' (pointsMap B S hS _ e ⁻¹' T) =
        pointsMap B S hS _ (yoneda.map h ≫ e) ⁻¹' T := by
      rw [pointsMap_comp]
      rfl
    have hz₁ : HasImageIn B S hS (yoneda.obj Y₁)
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' (pointsMap B S hS _ e ⁻¹' T)) W.unop
        ((yoneda.map π).app W z) := by
      rw [hset]
      exact hasImageIn_of_comp_eq (a := yoneda.map π ≫ v₁) (b := yoneda.map π)
        (by rw [Category.assoc, hv]) W z hz
    have key := hc₁.2 W z hz₁
    show _ = (pullback.fst f e).app W (c₁.app W z)
    rw [← key]
    show _ = (pullback.fst f e).app W
      (yonedaEquiv (baseChangeCompletionLift hα e h v₁ hv W _ hz₁))
    rw [← yonedaEquiv_comp, baseChangeCompletionLift_fst, Equiv.apply_symm_apply]
    rfl

end BaseChange

/-! ### Stacks 0GDR from the affine case -/

section FromAffine

/-- The morphism of completion subfunctors underlying a morphism over `X_{/T}` lies over the
completion subfunctor of `X`. -/
theorem completionSubfunctorHom_comp_completionMap
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : completionSheaf B S hS Y (pointsMap B S hS Y g ⁻¹' T) ⟶
      completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T))
    (hα : α ≫ completionSheafMap B S hS f T = completionSheafMap B S hS g T) :
    completionSubfunctorHom hY hX' α ≫ completionMap B S hS f T = completionMap B S hS g T := by
  have hiso := GrothendieckTopology.isIso_toSheafify (BigFppfOver.topology B S hS)
    (isSheaf_completionSubfunctor B S hS hX T)
  rw [← cancel_mono ((BigFppfOver.topology B S hS).toSheafify _), Category.assoc,
    GrothendieckTopology.toSheafify_naturality, GrothendieckTopology.toSheafify_naturality]
  show completionSubfunctorHom hY hX' α ≫
      (completionSheafIsoSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T)).inv ≫
      (completionSheafMap B S hS f T).hom =
    (completionSheafIsoSubfunctor B S hS hY (pointsMap B S hS Y g ⁻¹' T)).inv ≫
      (completionSheafMap B S hS g T).hom
  rw [← Category.assoc, completionSubfunctorHom_comp_inv, Category.assoc, ← hα]
  rfl

/-- The morphism of completion subfunctors underlying a morphism over `X_{/T}` lies over `X`,
section by section. -/
theorem completionSubfunctorHom_over (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f))
    (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
    (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y) :
    f.app W ((completionSubfunctorHom hY hX' α.left).app W ⟨ULift.up y, hy⟩).1.down =
      g.app W y := by
  have key := completionSubfunctorHom_comp_completionMap hX hY hX' α.left (Over.w α)
  exact congrArg (fun s => s.1.down) (congrFun (congrArg (fun φ => (φ.app W : _ → _)) key)
    ⟨ULift.up y, hy⟩)

/-- **Stacks 0GDR, fullness, from its affine case.** Let `X` be a locally Noetherian algebraic
space, `T ⊆ |X|` closed, `f : X' ⟶ X` a morphism of algebraic spaces locally of finite type
which is an isomorphism over the complement of `T`, and `g : Y ⟶ X` with `Y` a locally
Noetherian algebraic space. Granted the local existence statement over a Noetherian affine base,
`AlgebraicGeometry.Space.AffineCompletionLiftProperty`, every morphism `Y_{/T} ⟶ X'_{/T}` over
`X_{/T}` is the completion of a morphism `Y ⟶ X'` over `X`.

This assembles the reductions of the source's proof: gluing over étale coverings
(`AlgebraicGeometry.Space.exists_isCompletionLift_id_of_hasLocalCompletionLifts`), the
reduction to an affine étale chart of `X`
(`AlgebraicGeometry.Space.hasLocalCompletionLifts_of_hasAffineChartCompletionLifts`) and the
base change to that chart
(`AlgebraicGeometry.Space.hasAffineChartCompletionLifts_of_affineCompletionLiftProperty`). -/
theorem exists_completionOverFunctor_map_eq_of_affineCompletionLiftProperty
    (hcore : AffineCompletionLiftProperty B S hS)
    (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hY : IsAlgebraicSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX' : IsAlgebraicSpace B S hS X') (hf : IsLocallyOfFiniteType B S hS f)
    (hT : IsClosed T) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f)) :
    ∃ a : Over.mk g ⟶ Over.mk f, (completionOverFunctor B S hS T).map a = α :=
  exists_completionOverFunctor_map_eq_of_hasLocalCompletionLifts hX.isSheaf hY hX' hYnoeth
    (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX' hX f hf hXnoeth) hT hfU α
    (hasLocalCompletionLifts_of_hasAffineChartCompletionLifts hXnoeth
      (hasAffineChartCompletionLifts_of_affineCompletionLiftProperty hcore hX hX' hf hT hfU
        (completionSubfunctorHom_over hX.isSheaf hY.isSheaf hX'.isSheaf α)))

end FromAffine

/-! ### Morphisms of completions from morphisms of completion subfunctors -/

section OfSubfunctor

/-- The morphism of completions of fppf sheaves given by a morphism of completion subfunctors. -/
noncomputable def completionSheafHomOfSubfunctor
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor) :
    completionSheaf B S hS Y (pointsMap B S hS Y g ⁻¹' T) ⟶
      completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T) :=
  ObjectProperty.homMk ((completionSheafIsoSubfunctor B S hS hY _).hom ≫ α ≫
    (completionSheafIsoSubfunctor B S hS hX' _).inv)

/-- `completionSubfunctorHom` is a left inverse of `completionSheafHomOfSubfunctor`. -/
theorem completionSubfunctorHom_completionSheafHomOfSubfunctor
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor) :
    completionSubfunctorHom hY hX' (completionSheafHomOfSubfunctor hY hX' α) = α := by
  simp [completionSubfunctorHom, completionSheafHomOfSubfunctor]

/-- A morphism of completion subfunctors lying over `X` gives a morphism of completions over the
completion of `X`. -/
theorem completionSheafHomOfSubfunctor_comp
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor)
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y) :
    completionSheafHomOfSubfunctor hY hX' α ≫ completionSheafMap B S hS f T =
      completionSheafMap B S hS g T := by
  have _ := hX
  have hαf : α ≫ completionMap B S hS f T = completionMap B S hS g T := by
    ext W x
    apply Subtype.ext
    apply ULift.ext
    exact hα W x.1.down x.2
  apply ObjectProperty.hom_ext
  refine (BigFppfOver.topology B S hS).sheafify_hom_ext _ _
    ((BigFppfOver.topology B S hS).sheafify_isSheaf _) ?_
  have hYs := isSheaf_completionSubfunctor B S hS hY (pointsMap B S hS Y g ⁻¹' T)
  have hX's := isSheaf_completionSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T)
  show (BigFppfOver.topology B S hS).toSheafify _ ≫
      (((BigFppfOver.topology B S hS).isoSheafify hYs).inv ≫ α ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX's).hom) ≫
      (BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS f T) =
    (BigFppfOver.topology B S hS).toSheafify _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS g T)
  have e1 : (BigFppfOver.topology B S hS).toSheafify _ ≫
      ((BigFppfOver.topology B S hS).isoSheafify hYs).inv = 𝟙 _ := by
    rw [← GrothendieckTopology.isoSheafify_hom (BigFppfOver.topology B S hS) hYs]
    exact Iso.hom_inv_id _
  calc _ = ((BigFppfOver.topology B S hS).toSheafify _ ≫
          ((BigFppfOver.topology B S hS).isoSheafify hYs).inv) ≫ α ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX's).hom ≫
        (BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS f T) := by
        simp only [Category.assoc]
    _ = α ≫ completionMap B S hS f T ≫ (BigFppfOver.topology B S hS).toSheafify _ := by
        rw [e1, Category.id_comp, GrothendieckTopology.isoSheafify_hom,
          GrothendieckTopology.toSheafify_naturality]
    _ = completionMap B S hS g T ≫ (BigFppfOver.topology B S hS).toSheafify _ := by
        rw [← Category.assoc, hαf]
    _ = _ := GrothendieckTopology.toSheafify_naturality _ _

/-- The morphism over `X_{/T}` given by a morphism of completion subfunctors over `X`. -/
noncomputable def completionOverHomOfSubfunctor
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor)
    (hα : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj W)
      (hy : HasImageIn B S hS Y (pointsMap B S hS Y g ⁻¹' T) W.unop y),
      f.app W (α.app W ⟨ULift.up y, hy⟩).1.down = g.app W y) :
    (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f) :=
  Over.homMk (completionSheafHomOfSubfunctor hY hX' α)
    (completionSheafHomOfSubfunctor_comp hX hY hX' α hα)

/-- **Lifts from an equation of completions.** If the completion of `c : Z ⟶ X'` over `X` is the
completion of `v : Z ⟶ Y` followed by `α`, then `c` lifts the morphism of completion subfunctors
underlying `α` along `v`. -/
theorem isCompletionLift_of_completionOverFunctor_map_eq
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Z ⟶ Y) (c : Z ⟶ X') (hc : c ≫ f = v ≫ g)
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f))
    (h : (completionOverFunctor B S hS T).map
        (Over.homMk c hc : Over.mk (v ≫ g) ⟶ Over.mk f) =
      (completionOverFunctor B S hS T).map
        (Over.homMk v rfl : Over.mk (v ≫ g) ⟶ Over.mk g) ≫ α) :
    IsCompletionLift (completionSubfunctorHom hY hX' α.left) v c := by
  have hiso := GrothendieckTopology.isIso_toSheafify (BigFppfOver.topology B S hS)
    (isSheaf_completionSubfunctor B S hS hX' (pointsMap B S hS X' f ⁻¹' T))
  have h1 := toSheafify_comp_completionOverMap (T := T)
    (Over.homMk c hc : Over.mk (v ≫ g) ⟶ Over.mk f)
  have h2 := toSheafify_comp_completionOverMap (T := T)
    (Over.homMk v rfl : Over.mk (v ≫ g) ⟶ Over.mk g)
  have hl : (completionOverMap B S hS T (Over.homMk c hc : Over.mk (v ≫ g) ⟶ Over.mk f)).hom =
      (completionOverMap B S hS T (Over.homMk v rfl : Over.mk (v ≫ g) ⟶ Over.mk g)).hom ≫
        α.left.hom :=
    congrArg (fun φ : (completionOverFunctor B S hS T).obj (Over.mk (v ≫ g)) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f) => φ.left.hom) h
  have key : completionSubfunctorMap B S hS c (pointsMap B S hS Z (v ≫ g) ⁻¹' T)
        (pointsMap B S hS X' f ⁻¹' T)
        (image_preimage_subset_preimage_of_comp_eq B S hS hc T) =
      completionSubfunctorMap B S hS v (pointsMap B S hS Z (v ≫ g) ⁻¹' T)
          (pointsMap B S hS Y g ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS (rfl : v ≫ g = v ≫ g) T) ≫
        completionSubfunctorHom hY hX' α.left := by
    rw [← cancel_mono ((BigFppfOver.topology B S hS).toSheafify _)]
    exact h1.symm.trans
      ((congrArg (fun φ => (BigFppfOver.topology B S hS).toSheafify _ ≫ φ) hl).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun φ => φ ≫ α.left.hom) h2).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun φ =>
          completionSubfunctorMap B S hS v (pointsMap B S hS Z (v ≫ g) ⁻¹' T)
            (pointsMap B S hS Y g ⁻¹' T)
            (image_preimage_subset_preimage_of_comp_eq B S hS (rfl : v ≫ g = v ≫ g) T) ≫ φ)
          (completionSubfunctorHom_comp_inv hY hX' α.left).symm).trans
          (Category.assoc _ _ _).symm)))))
  refine ⟨hc, fun W z hz => ?_⟩
  have hz' : HasImageIn B S hS Z (pointsMap B S hS Z (v ≫ g) ⁻¹' T) W.unop z :=
    hasImageIn_of_comp_eq (a := v) (b := 𝟙 Z) (g' := v ≫ g) (by simp) W z hz
  have := congrArg (fun s => s.1.down)
    (congrFun (congrArg (fun φ => (φ.app W : _ → _)) key) ⟨ULift.up z, hz'⟩)
  exact this.symm

/-- The morphism of completions given by a morphism of completion subfunctors, on sections. -/
theorem completionSheafHomOfSubfunctor_app
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (α : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor)
    (W : (BigFppfOver B S hS)ᵒᵖ)
    (x : (completionSubfunctor B S hS Y (pointsMap B S hS Y g ⁻¹' T)).toFunctor.obj W) :
    (completionSheafHomOfSubfunctor hY hX' α).hom.app W
        ((completionSheafIsoSubfunctor B S hS hY _).inv.app W x) =
      (completionSheafIsoSubfunctor B S hS hX' _).inv.app W (α.app W x) := by
  have hid : (completionSheafIsoSubfunctor B S hS hY _).hom.app W
      ((completionSheafIsoSubfunctor B S hS hY _).inv.app W x) = x :=
    congrFun (congrArg (fun φ => (φ.app W : _ → _))
      (completionSheafIsoSubfunctor B S hS hY (pointsMap B S hS Y g ⁻¹' T)).inv_hom_id) x
  show (completionSheafIsoSubfunctor B S hS hX' _).inv.app W (α.app W
    ((completionSheafIsoSubfunctor B S hS hY _).hom.app W
      ((completionSheafIsoSubfunctor B S hS hY _).inv.app W x))) = _
  rw [hid]

end OfSubfunctor

end AlgebraicGeometry.Space

end
