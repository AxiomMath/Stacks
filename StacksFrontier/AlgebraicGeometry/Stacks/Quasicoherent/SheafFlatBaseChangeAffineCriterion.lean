module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty

/-!
# The flat base change property from cartesianness along flat maps of affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of modules over
its structure sheaf `𝒪`, with sections in the universe of the schemes. This file proves that if
`F(y) ⊗_{𝒪(y)} 𝒪(x) ⟶ F(x)` is an isomorphism for every arrow `x ⟶ y` of `𝒳` lying over a flat
morphism of affine schemes, then `F` has the flat base change property of **Stacks 0762** in the
sheaf-level reading `AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`: along every arrow
`φ : x ⟶ y` over a flat morphism `a : U ⟶ V`, the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC** is locally injective and locally
surjective for the étale topology of `U`.

This is the implication used to place quasi-coherent modules in `LQCoh^fbc` (the flat base change
half of **Stacks 06WK**): a quasi-coherent module on `𝒳` is cartesian along all arrows between
affine objects.

## The argument

Nothing computes the sections of the presheaf pullback `a_{small}^*`, which is a left adjoint;
they are spanned by the restrictions of the images of the unit
(`PresheafOfModules.mem_pullbackUnitSubmodule`). Base change `a^* : V_ét ⥤ U_ét` preserves finite
limits, so its categories of arrows `X ⟶ a^*W` are cofiltered and a single index `W` suffices for
every section (`PresheafOfModules.exists_mem_pullbackUnitSpan`). Étale locally on `U`, an arrow
`X ⟶ a^*W` is refined by an arrow `X' ⟶ a^*W'` with `X'` and `W'` affine
(`AlgebraicGeometry.generate_affineBaseChangeRefinements_mem`). For such an arrow the composite of
`c_φ` with `r ⊗ m ↦ r · m` is, up to the identifications of structure sheaves of Stacks 06W9, the
base-change map of `F` along an arrow of `𝒳` lying over the flat morphism `X' ⟶ a^*W' ⟶ W'`
(`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE_app_unit`,
`AlgebraicGeometry.Stack.localStructurePresheafIso_hom_app_map_smallEtaleStructureComparison`),
hence bijective; so `c_φ` is injective on the span of those generators and maps it onto the
sections over `X'`
(`AlgebraicGeometry.Stack.isGoodPullbackIndex_restrictModulePullbackComparisonUnivLE`).
The abstract local criterion is
`PresheafOfModules.isLocallyInjective_and_isLocallySurjective_of_goodPullbackRefinements`.

## Main results

* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange`: the
  criterion.
* `PresheafOfModules.exists_mem_pullbackUnitSpan`: over a cofiltered category of arrows, every
  section of a pullback of presheaves of modules is spanned by generators with one index.
* `PresheafOfModules.isLocallyInjective_and_isLocallySurjective_of_goodPullbackRefinements`: a map
  out of a pullback of presheaves of modules is a local isomorphism when its indices are refined,
  locally, by indices on whose spans it is bijective.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w v₁ v₂ u₁ u₂

namespace Stacks.TensorProduct

variable {A B K M Q P : Type*} [CommRing A] [CommRing B] [Ring K]
  [AddCommGroup M] [AddCommGroup Q] [AddCommGroup P]
  {_ : Module A M} {_ : Module B Q} [Module K P] {_ : Module A B}

/-- **An additive map which is bijective after base change is injective on the span of its
generators.** Let `β : B ⊗[A] M → Q` be a bijection sending `b ⊗ m` to `b • μ m`, let
`e : K ≃+* B` be an isomorphism of rings and `c : P → Q` an additive map which is semilinear along
`e`, and let `gen : M → P` be additive, semilinear along `e⁻¹ ∘ f`, with `c ∘ gen = μ`. Then `c`
is injective on the `K`-span of the image of `gen` and maps that span onto `Q`. -/
theorem injOn_and_surjOn_span_of_bijective (f : A →+* B) (hAB : ∀ (a : A) (b : B), a • b = f a * b)
    (μ : M → Q) (β : TensorProduct A B M →+ Q) (hβ : ∀ (b : B) (m : M), β (b ⊗ₜ m) = b • μ m)
    (hβbij : Function.Bijective β) (e : K ≃+* B) (c : P →+ Q)
    (hc : ∀ (k : K) (x : P), c (k • x) = e k • c x) (gen : M →+ P)
    (hgen₁ : ∀ m, c (gen m) = μ m) (hgen₂ : ∀ (a : A) (m : M), gen (a • m) = e.symm (f a) • gen m) :
    (∀ s ∈ Submodule.span K (Set.range gen), c s = 0 → s = 0) ∧
      ∀ q : Q, ∃ s ∈ Submodule.span K (Set.range gen), c s = q := by
  let Θ : TensorProduct A B M →+ P :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => e.symm b • gen m)
          (fun m m' => by rw [map_add, smul_add]))
        (fun b b' => AddMonoidHom.ext fun m => by
          change e.symm (b + b') • gen m = e.symm b • gen m + e.symm b' • gen m
          rw [map_add, add_smul]))
      (fun a b m => by
        change e.symm (a • b) • gen m = e.symm b • gen (a • m)
        rw [hgen₂, hAB, mul_comm, map_mul, mul_smul])
  have hΘ : ∀ (b : B) (m : M), Θ (b ⊗ₜ m) = e.symm b • gen m := fun _ _ => rfl
  have hcΘ : ∀ z, c (Θ z) = β z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b m => rw [hΘ, hc, hgen₁, RingEquiv.apply_symm_apply, hβ]
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
  have hsmul : ∀ (k : K) (z : TensorProduct A B M), ∃ w, k • Θ z = Θ w := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
    | tmul b m => exact ⟨(e k * b) ⊗ₜ m, by rw [hΘ, hΘ, map_mul, e.symm_apply_apply, mul_smul]⟩
    | add z z' hz hz' =>
      obtain ⟨w, hw⟩ := hz
      obtain ⟨w', hw'⟩ := hz'
      exact ⟨w + w', by rw [map_add, smul_add, hw, hw', map_add]⟩
  have hrange : ∀ s ∈ Submodule.span K (Set.range gen), ∃ z, Θ z = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact ⟨1 ⊗ₜ m, by rw [hΘ, map_one, one_smul]⟩
    | zero => exact ⟨0, map_zero Θ⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨z', rfl⟩ := hy
      exact ⟨z + z', map_add Θ z z'⟩
    | smul k x _ hx =>
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hsmul k z
      exact ⟨w, hw.symm⟩
  have hmem : ∀ z, Θ z ∈ Submodule.span K (Set.range gen) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul b m => rw [hΘ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'
  refine ⟨fun s hs hcs => ?_, fun q => ?_⟩
  · obtain ⟨z, rfl⟩ := hrange s hs
    have hz : z = 0 := hβbij.1 (by rw [← hcΘ, hcs, map_zero])
    rw [hz, map_zero]
  · obtain ⟨z, rfl⟩ := hβbij.2 q
    exact ⟨Θ z, hmem z, hcΘ z⟩

end Stacks.TensorProduct

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint] (M : PresheafOfModules.{v} S)

/-- The sections of the pullback of `M` over `X` spanned by the generators indexed by one arrow
`g : X ⟶ F.obj Y`: the restrictions along `g` of the images of the sections of `M` over `Y` under
the unit of the pullback--pushforward adjunction. -/
noncomputable def pullbackUnitSpan (X : Dᵒᵖ) (Y : C) (g : X.unop ⟶ F.obj Y) :
    _root_.Submodule (R.obj X) (((pullback.{v} φ).obj M).obj X) :=
  _root_.Submodule.span (R.obj X) (Set.range fun m : M.obj (op Y) =>
    ((pullback.{v} φ).obj M).map g.op
      (((pullbackPushforwardAdjunction.{v} φ).unit.app M).app (op Y) m))

/-- A generator indexed by `g ≫ F.map k` is a generator indexed by `g`. -/
theorem pullback_map_unit_app_comp (X : Dᵒᵖ) {Y Y' : C} (g : X.unop ⟶ F.obj Y) (k : Y ⟶ Y')
    (m : M.obj (op Y')) :
    ((pullback.{v} φ).obj M).map (g ≫ F.map k).op
        (((pullbackPushforwardAdjunction.{v} φ).unit.app M).app (op Y') m) =
      ((pullback.{v} φ).obj M).map g.op
        (((pullbackPushforwardAdjunction.{v} φ).unit.app M).app (op Y) (M.map k.op m)) := by
  refine Eq.trans ?_ (congrArg (((pullback.{v} φ).obj M).map g.op)
    (naturality_apply ((pullbackPushforwardAdjunction.{v} φ).unit.app M) k.op m)).symm
  exact ((pullback.{v} φ).obj M).map_comp_apply (F.map k).op g.op _

/-- The span indexed by `g ≫ F.map k` is contained in the span indexed by `g`. -/
theorem pullbackUnitSpan_le (X : Dᵒᵖ) {Y Y' : C} (g : X.unop ⟶ F.obj Y) (k : Y ⟶ Y') :
    pullbackUnitSpan φ M X Y' (g ≫ F.map k) ≤ pullbackUnitSpan φ M X Y g := by
  refine _root_.Submodule.span_le.2 ?_
  rintro _ ⟨m, rfl⟩
  exact _root_.Submodule.subset_span ⟨M.map k.op m, (pullback_map_unit_app_comp φ M X g k m).symm⟩

/-- **Over a cofiltered category of arrows, one index suffices.** If the arrows from `X` to the
image of `F` form a cofiltered category, every section of the pullback of `M` over `X` lies in
the span of the generators indexed by a single arrow `X ⟶ F.obj Y`. -/
theorem exists_mem_pullbackUnitSpan (X : Dᵒᵖ) [IsCofiltered (StructuredArrow X.unop F)]
    (s : ((pullback.{v} φ).obj M).obj X) :
    ∃ (Y : C) (g : X.unop ⟶ F.obj Y), s ∈ pullbackUnitSpan φ M X Y g := by
  have hle : ∀ {a c : StructuredArrow X.unop F} (f : c ⟶ a),
      pullbackUnitSpan φ M X a.right a.hom ≤ pullbackUnitSpan φ M X c.right c.hom := fun f => by
    rw [← StructuredArrow.w f]
    exact pullbackUnitSpan_le φ M X _ _
  have hs := mem_pullbackUnitSubmodule φ M X s
  change s ∈ _root_.Submodule.span (R.obj X) (pullbackUnitGenerators φ M X) at hs
  induction hs using _root_.Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Y, g, m, rfl⟩ := hx
    exact ⟨Y, g, Submodule.subset_span ⟨m, rfl⟩⟩
  | zero =>
    obtain ⟨a⟩ := IsCofiltered.nonempty (C := StructuredArrow X.unop F)
    exact ⟨a.right, a.hom, _root_.Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y₁, g₁, h₁⟩ := hx
    obtain ⟨Y₂, g₂, h₂⟩ := hy
    let a := StructuredArrow.mk g₁
    let b := StructuredArrow.mk g₂
    exact ⟨_, _, _root_.Submodule.add_mem _ (hle (IsCofiltered.minToLeft a b) h₁)
      (hle (IsCofiltered.minToRight a b) h₂)⟩
  | smul r x _ hx =>
    obtain ⟨Y, g, h⟩ := hx
    exact ⟨Y, g, _root_.Submodule.smul_mem _ r h⟩

/-- Restricting a generator indexed by `g` along `f` gives the generator indexed by `f ≫ g`. -/
theorem pullbackUnitSpan_map {X X' : Dᵒᵖ} (f : X ⟶ X') (Y : C) (g : X.unop ⟶ F.obj Y)
    (s : ((pullback.{v} φ).obj M).obj X) (hs : s ∈ pullbackUnitSpan φ M X Y g) :
    ((pullback.{v} φ).obj M).map f s ∈ pullbackUnitSpan φ M X' Y (f.unop ≫ g) := by
  induction hs using _root_.Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine _root_.Submodule.subset_span ⟨m, ?_⟩
    exact (((pullback.{v} φ).obj M).map_comp_apply g.op f _)
  | zero => rw [map_zero]; exact _root_.Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact _root_.Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact _root_.Submodule.smul_mem _ _ hx

variable {M} {N : PresheafOfModules.{v} R} (c : (pullback.{v} φ).obj M ⟶ N)

/-- An arrow `g : X ⟶ F.obj Y` is a *good index* for `c` when `c` is injective on the span of the
generators indexed by `g` and carries that span onto the sections of `N` over `X`. -/
def IsGoodPullbackIndex (X : D) (Y : C) (g : X ⟶ F.obj Y) : Prop :=
  (∀ s ∈ pullbackUnitSpan φ M (op X) Y g, c.app (op X) s = 0 → s = 0) ∧
    ∀ n : N.obj (op X), ∃ s ∈ pullbackUnitSpan φ M (op X) Y g, c.app (op X) s = n

/-- The arrows `f : X' ⟶ X` along which an index `g : X ⟶ F.obj Y` is refined by a good index:
`f ≫ g = g' ≫ F.map k` for a good index `g' : X' ⟶ F.obj Y'`. -/
def goodPullbackRefinements (X : D) (Y : C) (g : X ⟶ F.obj Y) : Presieve X :=
  fun X' f => ∃ (Y' : C) (k : Y' ⟶ Y) (g' : X' ⟶ F.obj Y'),
    g' ≫ F.map k = f ≫ g ∧ IsGoodPullbackIndex φ c X' Y' g'

/-- **A local criterion for a map out of a pullback of presheaves of modules to be a local
isomorphism.** If the arrows from objects of `D` to the image of `F` form cofiltered categories
(e.g. `F` is representably flat) and every index `g : X ⟶ F.obj Y` is refined, locally for `J`,
by good indices, then `c` is locally injective and locally surjective. -/
theorem isLocallyInjective_and_isLocallySurjective_of_goodPullbackRefinements
    (J : GrothendieckTopology D) [∀ X : D, IsCofiltered (StructuredArrow X F)]
    (hJ : ∀ (X : D) (Y : C) (g : X ⟶ F.obj Y),
      Sieve.generate (goodPullbackRefinements φ c X Y g) ∈ J X) :
    Presheaf.IsLocallyInjective J ((toPresheaf R).map c) ∧
      Presheaf.IsLocallySurjective J ((toPresheaf R).map c) := by
  refine ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {X} n => ?_⟩⟩
  · let x' : ((pullback.{v} φ).obj M).obj X := x
    let y' : ((pullback.{v} φ).obj M).obj X := y
    let d : ((pullback.{v} φ).obj M).obj X := x' - y'
    have hd : c.app X d = 0 :=
      (map_sub (c.app X).hom x' y').trans (sub_eq_zero.2 hxy)
    obtain ⟨Y, g, hmem⟩ := exists_mem_pullbackUnitSpan φ M X d
    refine J.superset_covering ?_ (hJ X.unop Y g)
    rw [Sieve.generate_le_iff]
    rintro X' f ⟨Y', k, g', hfac, hgood, -⟩
    have h1 := pullbackUnitSpan_map φ M f.op Y g d hmem
    rw [Quiver.Hom.unop_op, ← hfac] at h1
    have h2 := pullbackUnitSpan_le φ M (op X') g' k h1
    have h3 : c.app (op X') (((pullback.{v} φ).obj M).map f.op d) = 0 :=
      (naturality_apply c f.op d).trans ((congrArg (N.map f.op) hd).trans (map_zero _))
    have h4 := hgood _ h2 h3
    change ((pullback.{v} φ).obj M).map f.op x = ((pullback.{v} φ).obj M).map f.op y
    exact sub_eq_zero.1 ((map_sub (((pullback.{v} φ).obj M).map f.op).hom x' y').symm.trans h4)
  · obtain ⟨a⟩ := IsCofiltered.nonempty (C := StructuredArrow X F)
    refine J.superset_covering ?_ (hJ X a.right a.hom)
    rw [Sieve.generate_le_iff]
    rintro X' f ⟨Y', k, g', -, -, hgood⟩
    obtain ⟨s, -, hs⟩ := hgood (N.map f.op n)
    exact ⟨s, hs⟩

end PresheafOfModules

namespace AlgebraicGeometry

variable (E : BigEtaleSite.{u}) {Sb Tb : E.Scheme} (f : Tb ⟶ Sb)

/-- The arrows `ι : T' ⟶ T` of the small étale site of `Tb` with affine source along which an
arrow `g : T ⟶ f^*W` into a base change is refined by an arrow `g' : T' ⟶ f^*W'` into the base
change of an affine `W'` mapping to `W`. -/
def affineBaseChangeRefinements (T : SmallEtale E Tb.obj Tb.property)
    (W : SmallEtale E Sb.obj Sb.property) (g : T ⟶ (smallEtaleBaseChange E f).obj W) :
    Presieve T :=
  fun T' ι => IsAffine ((SmallEtale.toScheme E _ _).obj T') ∧
    ∃ (W' : SmallEtale E Sb.obj Sb.property) (k : W' ⟶ W)
      (g' : T' ⟶ (smallEtaleBaseChange E f).obj W'),
      IsAffine ((SmallEtale.toScheme E _ _).obj W') ∧ g' ≫ (smallEtaleBaseChange E f).map k = ι ≫ g

/-- **Arrows into a base change are refined, étale locally, by arrows between affines.** The
affine opens of `W` cover `W`, their base changes cover `f^*W`, the pullbacks along `g` cover `T`,
and the affine opens of those cover them in turn. -/
theorem generate_affineBaseChangeRefinements_mem (T : SmallEtale E Tb.obj Tb.property)
    (W : SmallEtale E Sb.obj Sb.property) (g : T ⟶ (smallEtaleBaseChange E f).obj W) :
    Sieve.generate (affineBaseChangeRefinements E f T W g) ∈
      SmallEtale.topology E Tb.obj Tb.property T := by
  have hW := SmallEtale.mem_topology_sieve₀_affineSubordinateCover E Sb.obj Sb.property W
  have hcp : CoverPreserving (SmallEtale.topology E Sb.obj Sb.property)
      (SmallEtale.topology E Tb.obj Tb.property) (smallEtaleBaseChange E f) :=
    Functor.isContinuous_iff_coverPreserving.1 inferInstance
  have h2 := (SmallEtale.topology E Tb.obj Tb.property).pullback_stable g (hcp.cover_preserve hW)
  refine (SmallEtale.topology E Tb.obj Tb.property).transitive h2 _ ?_
  rintro T₁ l ⟨Z, e, l₁, he, hfac⟩
  obtain ⟨Z', e₁, e₂, ⟨i⟩, rfl⟩ := he
  refine (SmallEtale.topology E Tb.obj Tb.property).superset_covering ?_
    (SmallEtale.mem_topology_sieve₀_affineSubordinateCover E Tb.obj Tb.property T₁)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨j⟩
  apply Sieve.le_generate
  unfold affineBaseChangeRefinements
  refine ⟨j.down.1.2, (SmallEtale.affineSubordinateCover E Sb.obj Sb.property W).X i,
    (SmallEtale.affineSubordinateCover E Sb.obj Sb.property W).f i,
    (SmallEtale.affineSubordinateCover E Tb.obj Tb.property T₁).f j ≫ l₁ ≫
      (smallEtaleBaseChange E f).map e₁, i.down.1.2, ?_⟩
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← hfac]
  rfl

end AlgebraicGeometry


namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Generators

variable {x y : 𝒳} (φ : x ⟶ y)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-- **The comparison map on a generator of the pullback.** Let `W'` be étale over the scheme
below `x`, `W` étale over the scheme below `y`, and `g : W' ⟶ a^*W`. For an arrow `φ'` of `𝒳`
lifting the projection `a^*W ⟶ W` as in `AlgebraicGeometry.Stack.exists_restrictionComparisonLift`,
the comparison map `c_φ` carries the restriction along `g` of the unit's image of a section `m` of
`F` over the lift of `W` to `F` restricted along the composite arrow of `𝒳`. -/
theorem restrictModulePullbackComparisonUnivLE_app_unit
    {W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    {W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (g : W' ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W) ⟶
      (etaleIndex B E h S hS p hp y).obj W)
    (hφ' : (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op W) =
      F.presheaf.map φ'.op)
    (m : F.obj (op ((etaleIndex B E h S hS p hp y).obj W))) :
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F).app (op W')
      (((PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).obj
          (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B) F)).map g.op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).unit.app
          (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B) F)).app (op W) m)) =
      F.map ((etaleIndex B E h S hS p hp x).map g ≫ φ').op m := by
  have hadj := restrictModulePullbackComparisonUnivLE_adjunct B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B) F
  rw [Adjunction.homEquiv_unit] at hadj
  have h2 := (ConcreteCategory.congr_hom
    (congrArg (fun k => PresheafOfModules.Hom.app k (op W)) hadj) m).trans
    (ConcreteCategory.congr_hom hφ' m)
  refine (PresheafOfModules.naturality_apply _ g.op _).trans ?_
  refine (congrArg (ConcreteCategory.hom ((restrictModuleToSmallEtale B E h S hS p hp x
    (etaleTopology B) (etaleTopology_le_topology B) F).map g.op)) h2).trans ?_
  exact (F.map_comp_apply φ'.op ((etaleIndex B E h S hS p hp x).map g).op m).symm

/-- **The map of structure sheaves on a generator.** Under the identifications of Stacks 06W9, the
map `a_{small}^♯` followed by restriction along `g : W' ⟶ a^*W` is the restriction of the structure
sheaf of `𝒳` along the composite arrow of `𝒳`, for an arrow `φ'` lifting the projection
`a^*W ⟶ W` as in `AlgebraicGeometry.Stack.exists_restrictionComparisonLift`. -/
theorem localStructurePresheafIso_hom_app_map_smallEtaleStructureComparison
    {W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    {W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (g : W' ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W) ⟶
      (etaleIndex B E h S hS p hp y).obj W)
    (hφ' : (restrictionPushforwardComparison B E h S hS p hp φ
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj).app (op W) =
      (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj.map φ'.op)
    (s : (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj.obj
      (op W)) :
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app (op W')
      ((SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.map g.op
        ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B)).app (op W) s)) =
      (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj.map ((etaleIndex B E h S hS p hp x).map g ≫ φ').op
        ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B)).hom.app (op W) s) := by
  let isoX := localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let R := (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  refine (ConcreteCategory.congr_hom (isoX.hom.naturality g.op)
    ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B)).app (op W) s)).trans ?_
  have h2 := ConcreteCategory.congr_hom (isoX.inv_hom_id_app
      (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)))
    ((restrictionPushforwardComparison B E h S hS p hp φ R).app (op W)
      ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app (op W) s))
  refine (congrArg (ConcreteCategory.hom (R.map ((etaleIndex B E h S hS p hp x).map g).op))
    (h2.trans (ConcreteCategory.congr_hom hφ' _))).trans ?_
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (R.map_comp φ'.op ((etaleIndex B E h S hS p hp x).map g).op).symm _)

/-- A morphism of schemes isomorphic, as an arrow, to a flat morphism is flat. -/
private theorem flat_of_arrow_iso {X Y X' Y' : Scheme.{u}} (a : X ⟶ Y) (b : X' ⟶ Y')
    (i : X ≅ X') (j : Y ≅ Y') (hsq : a ≫ j.hom = i.hom ≫ b) (hb : Flat b) : Flat a := by
  rw [show a = (i.hom ≫ b) ≫ j.inv by
    rw [← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- A lift `φ'` of the projection `a^*W ⟶ W` along a flat `φ` is flat: up to the isomorphisms
`εx` and `εy`, it is the base change of `p.map φ` along `W ⟶ p.obj y`. -/
private theorem flat_map_left_of_isPullback_square (hflat : Flat (B.inclusion.map (p.map φ).left))
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {x' : Over x} {y' : Over y} (φ' : x'.left ⟶ y'.left)
    (εx : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).obj x' ≅
      (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W))
    (εy : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).obj y' ≅
      (smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj W)
    (hbase : B.inclusion.map (p.map φ').left ≫ B.inclusion.map εy.hom.left =
      B.inclusion.map εx.hom.left ≫
        E.inclusion.map (Limits.pullback.fst W.obj.hom (smallEtaleBaseMorphism B E h S hS p φ))) :
    Flat (B.inclusion.map (p.map φ').left) :=
  flat_of_arrow_iso _ _
    (B.inclusion.mapIso ((Over.forget ((p ⋙ Over.forget (B.obj hS)).obj x)).mapIso εx))
    (B.inclusion.mapIso ((Over.forget ((p ⋙ Over.forget (B.obj hS)).obj y)).mapIso εy)) hbase
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback W.obj.hom _).flip.map E.inclusion) hflat)

/-- Precomposing an arrow of `𝒳` lying over a flat morphism with the image under `etaleIndex` of a
morphism of the small étale site again gives an arrow lying over a flat morphism. -/
private theorem flat_map_etaleIndex_map_comp
    {V' V : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (g : V' ⟶ V)
    {z : 𝒳} (ψ : (etaleIndex B E h S hS p hp x).obj V ⟶ z)
    (hψ : Flat (B.inclusion.map (p.map ψ).left)) :
    Flat (B.inclusion.map (p.map ((etaleIndex B E h S hS p hp x).map g ≫ ψ)).left) := by
  have : Flat (B.inclusion.map (p.map ((etaleIndex B E h S hS p hp x).map g)).left) :=
    (Etale.iff_flat_and_formallyUnramified.mp (etale_etaleIndex_map B E h S hS p hp x g)).1
  rw [Functor.map_comp, Over.comp_left, Functor.map_comp]
  infer_instance

/-- **Arrows between affines are good indices for the comparison map.** If `F` is cartesian along
every arrow of `𝒳` over a flat morphism of affine schemes and `φ` lies over a flat morphism, then
for affine `W'` and `W` and `g : W' ⟶ a^*W` the comparison map `c_φ` is injective on the span of
the generators indexed by `g` and maps it onto the sections over `W'`. -/
theorem isGoodPullbackIndex_restrictModulePullbackComparisonUnivLE
    (hcart : ∀ {x y : 𝒳} (φ : x ⟶ y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      Flat (B.inclusion.map (p.map φ).left) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F φ.op))
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    {W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    {W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (hW' : IsAffine ((SmallEtale.toScheme E _ _).obj W'))
    (hW : IsAffine ((SmallEtale.toScheme E _ _).obj W))
    (g : W' ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W) :
    PresheafOfModules.IsGoodPullbackIndex
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F) W' W g := by
  obtain ⟨φ', hfac, hbase⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W
  have hφ'flat : Flat (B.inclusion.map (p.map φ').left) := by
    have := isEquivalence_overPost B S hS p hp x
    have := isEquivalence_overPost B S hS p hp y
    exact flat_map_left_of_isPullback_square B E h S hS p φ hflat W φ'
      ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app _)
      ((Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app _) hbase
  have hiso := hcart _ (isAffine_etaleIndex_obj B E h S hS p hp x W' hW')
    (isAffine_etaleIndex_obj B E h S hS p hp y W hW)
    (flat_map_etaleIndex_map_comp B E h S hS p hp g φ' hφ'flat)
  let ψ := (etaleIndex B E h S hS p hp x).map g ≫ φ'
  let R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  let sEsc := smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B)
  let Fy := restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
    (etaleTopology_le_topology B) F
  let P := (PresheafOfModules.pullback.{u} sEsc).obj Fy
  let η := (PresheafOfModules.pullbackPushforwardAdjunction.{u} sEsc).unit.app Fy
  let c := restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B) F
  let e : (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj.obj (op W') ≃+*
      R.obj (op ((etaleIndex B E h S hS p hp x).obj W')) :=
    ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).app (op W')).ringCatIsoToRingEquiv
  let gen : F.obj (op ((etaleIndex B E h S hS p hp y).obj W)) →+ P.obj (op W') :=
    (P.map g.op).hom.toAddMonoidHom.comp (η.app (op W)).hom.toAddMonoidHom
  exact Stacks.TensorProduct.injOn_and_surjOn_span_of_bijective (R.map ψ.op).hom
    (fun _ _ => rfl) (fun m => F.map ψ.op m)
    (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u} (R := R) F ψ.op).hom.toAddMonoidHom
    (fun b m => Stacks.PresheafOfModules.restrictionBaseChange_tmul (R := R) F ψ.op b m)
    ((ConcreteCategory.isIso_iff_bijective _).1 hiso) e (c.app (op W')).hom.toAddMonoidHom
    (fun k n => (c.app (op W')).hom.map_smul k n) gen
    (fun m => restrictModulePullbackComparisonUnivLE_app_unit B E h S hS p hp φ F g φ'
      (restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf W φ' hfac hbase) m)
    (fun a m => by
      let eY : (SmallEtale.structureSheaf E (p.obj y).left.1
          (contains_base B E h S hS p y)).obj.obj (op W) ≃+*
          R.obj (op ((etaleIndex B E h S hS p hp y).obj W)) :=
        ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B)).app (op W)).ringCatIsoToRingEquiv
      obtain ⟨r, rfl⟩ := eY.surjective a
      have h3 : (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj.map g.op (sEsc.app (op W) r) =
          e.symm ((R.map ψ.op).hom (eY r)) :=
        (e.symm_apply_apply _).symm.trans (congrArg e.symm
          (localStructurePresheafIso_hom_app_map_smallEtaleStructureComparison B E h S hS p hp φ g
            φ' (restrictionPushforwardComparison_app B E h S hS p hp φ
              (ringStructureSheafCore B S hS p hp (etaleTopology B)
                (etaleTopology_le_topology B)).obj W φ' hfac hbase) r))
      exact ((congrArg (P.map g.op) ((η.app (op W)).hom.map_smul r m)).trans
        (P.map_smul g.op _ _)).trans (congrArg (· • gen m) h3))

/-- **Stacks 0762 from cartesianness along flat morphisms of affines.** A locally quasi-coherent
module `F` such that `F(y) ⊗_{𝒪(y)} 𝒪(x) ⟶ F(x)` is an isomorphism for every arrow `x ⟶ y` of `𝒳`
lying over a flat morphism of affine schemes has the flat base change property of Stacks 0762:
along every arrow over a flat morphism the comparison map `c_φ` is a local isomorphism of the
small étale site.

The hypothesis `hF` of local quasi-coherence is not used by the proof; it is kept so that the
statement is the one the consumers of the criterion are written against. -/
theorem hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherent B E h S hS p hp F)
    (hcart : ∀ {x y : 𝒳} (φ : x ⟶ y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      Flat (B.inclusion.map (p.map φ).left) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F φ.op)) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F := by
  intro x y φ hflat
  refine PresheafOfModules.isLocallyInjective_and_isLocallySurjective_of_goodPullbackRefinements
    (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B))
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F) _ (fun T W g => ?_)
  refine (SmallEtale.topology E _ _).superset_covering ?_
    (generate_affineBaseChangeRefinements_mem E (smallEtaleBaseMorphism B E h S hS p φ) T W g)
  rw [Sieve.generate_le_iff]
  rintro T' ι ⟨hT', W', k, g', hW', hfac⟩
  apply Sieve.le_generate
  exact ⟨W', k, g', hfac,
    isGoodPullbackIndex_restrictModulePullbackComparisonUnivLE B E h S hS p hp φ F hcart hflat
      hT' hW' g'⟩

end Generators

end AlgebraicGeometry.Stack

end
