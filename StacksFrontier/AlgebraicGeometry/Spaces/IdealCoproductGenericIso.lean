module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSupportSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# A generically invertible map out of a direct sum of copies of a sheaf of ideals

Let `X` be an algebraic space over a scheme `S` which is étale-locally reduced and whose space
of points is irreducible, let `T ⊆ |X|` be a closed subset which is not everything, let
`ℐ ⊆ 𝒪_X` be the quasi-coherent sheaf of ideals cutting out `T` and let `φ : ℐ^{⊕ r} ⟶ F` be a
map of `𝒪_X`-modules which is bijective on the sections over every étale chart carrying the
unit ideal of `ℐ` — the chartwise reading of "`φ` is an isomorphism over the open complement
`U = X \ T`".  This file proves the two conclusions of [Stacks, Tag 07UQ] about such a `φ`: it
is **injective**, and the **support of its cokernel is contained in `T`**, a proper closed
subset of `|X|`.  Together with the fact that `ℐ` is a nonzero quasi-coherent sheaf of ideals,
also proved here, that is the conclusion of the tag in the case `Z = X`, `i = id`, to which the
source reduces it.

The sheaf of ideals is `AlgebraicGeometry.Space.reducedIdealSheaf`, the defining ideal sheaf of
the reduced closed subspace on `T`.  That is the appeal to Properties of Spaces, Section
[Stacks, Tag 03IP] in the source's proof: "let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals
whose associated closed subspace is the complement of `U` in `X`".

The direct sum `ℐ^{⊕ r}` is spelled as the categorical product `∏ᶜ` of `r` copies of `ℐ`; for a
finite index set the product and the coproduct of a family in an additive category agree, so
this is the object the source writes `ℐ^{⊕ r}`.  Only the projections, and the fact that a
morphism into a product is determined by its components, are used below.

## Where this file sits in the proof of Tag 07UQ

The map `φ` is an argument here: these are the two conclusions of the tag drawn from a map
which is bijective over the charts carrying the unit ideal.  The tag itself is
`AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentIrreducibleIdealInjection.lean`, which constructs
the map from the surjectivity of [Stacks, Tag 07UM],
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective`, applied to a generic
trivialization, and uses the key lemma
`AlgebraicGeometry.Space.eq_zero_of_val_app_eq_zero_on_idealUnitCharts` of this file.

## The general case `i : Z ⟶ X`

The source reduces its statement to the case `Z = X` by Lemma [Stacks, Tag 07UG], and the last
section of this file performs that reduction in the opposite direction: from the case `Z = X`,
applied on `Z`, it produces the statement for a closed immersion `i : Z ⟶ X` and an `𝒪_X`-module
`F` which is the direct image of an `𝒪_Z`-module.  Three transports are needed, and all three
are available:

* injectivity is preserved by the direct image, `mono_modulePushforward_map`;
* the cokernel is preserved, `modulePushforwardCokernelIso` — the direct image along a closed
  immersion is exact, which is
  `exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`;
* the support of a direct image lies in a closed set over which the module is supported,
  `supportOfSheaf_modulePushforward_subset_of_isClosed`, the image of the closed set `T` being
  closed because a closed immersion is closed on points.

Coherence of the source `i_*(ℐ^{⊕ r})` is not asserted there; the tag's statement in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentIrreducibleIdealInjection.lean` proves it.

## The proof of injectivity

This is the argument of the last sentence of the source's proof, and it is where reducedness and
irreducibility are used.  Let `ψ : L ⟶ ℐ^{⊕ r}` satisfy `ψ ≫ φ = 0`.  Over a chart carrying the
unit ideal `φ` is injective on sections, so `ψ` is zero on sections there; hence each of the `r`
coordinates of `ψ`, read as a morphism `L ⟶ 𝒪_X`, vanishes on the sections over every such
chart.  The key lemma
`AlgebraicGeometry.Space.eq_zero_of_val_app_eq_zero_on_idealUnitCharts` then says that such a
morphism is zero: a nonzero one has a section `t` over some chart `V` whose image `s` is a
nonzero regular function on `V`, and `V` is a *reduced* scheme, so the non-vanishing locus of
`s` is a nonempty open of `V`, itself an étale chart `W` on which `s` becomes a unit.  The image
of `W` in `|X|` is a nonempty open, the unit locus of `ℐ` is a nonempty open, and `|X|` is
irreducible, so the two meet; over a point of the intersection sits a chart `W' ⟶ W` carrying
the unit ideal and having a point, on which `s` is still a unit and therefore nonzero — while
the morphism was assumed to vanish on the sections over `W'`.  With all `r` coordinates zero
`ψ` is zero, and injectivity of `φ` follows from the cancellation criterion for monomorphisms in
a preadditive category.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_val_app_eq_zero_on_idealUnitCharts`: **on a reduced
  algebraic space with irreducible space of points, a morphism to the structure sheaf which
  vanishes on the sections over every chart carrying the unit ideal of a sheaf of ideals with
  nonempty unit locus is zero.**
* `AlgebraicGeometry.Space.ne_bot_of_idealUnitLocus_nonempty`: a sheaf of ideals with nonempty
  unit locus is nonzero.
* `AlgebraicGeometry.Space.mono_of_injective_on_idealUnitCharts`: **a map out of a direct sum of
  copies of a sheaf of ideals which is injective on the sections over the charts carrying the
  unit ideal is a monomorphism.**
* `AlgebraicGeometry.Space.subsingleton_cokernel_val_obj_of_forall_surjective` and
  `AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective`: a map
  surjective on the sections over a chart and over everything below it has a cokernel with no
  sections there, so **the cokernel of a map surjective on the sections over the charts carrying
  the unit ideal is supported in the zero locus of the ideal.**
* `AlgebraicGeometry.Space.exists_mono_supportOfSheaf_cokernel_subset_of_bijective_on_unitCharts`:
  the conclusions of [Stacks, Tag 07UQ] in the case `Z = X`, for a given generically bijective
  map.
* `AlgebraicGeometry.Space.modulePushforwardBiproductConstIso`: the direct image of a finite
  direct sum of copies of a module is the direct sum of the copies of its direct image, so that
  the source of the injection may be written `i_*(ℐ^{⊕ r})` or `(i_*ℐ)^{⊕ r}` at will.
* `AlgebraicGeometry.Space.exists_mono_modulePushforward_cokernelCofork_support_subset_image`:
  the same for a general closed subspace `i : Z ⟶ X`.

## References

* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 03IP](https://stacks.math.columbia.edu/tag/03IP)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The structure sheaf of an algebraic space, read as a module over itself. -/
noncomputable abbrev spaceStructureSheafModule : Modules.{u, u} B S hS X.1 X.2 :=
  SheafOfModules.unit (structureRingSheaf B S hS X)

/-- Composition of morphisms of sheaves of modules, read on a section. -/
private theorem comp_val_app_section {C : Type*} [Category* C] {JJ : GrothendieckTopology C}
    {R : Sheaf JJ RingCat.{u}} {P P' Q : SheafOfModules.{u} R}
    (f : P ⟶ P') (g : P' ⟶ Q) (V : Cᵒᵖ)
    (t : P.val.obj V) : (f ≫ g).val.app V t = g.val.app V (f.val.app V t) := rfl

/-- A composite morphism of sheaves of modules which is zero sends every section to zero. -/
private theorem comp_val_app_section_eq_zero {C : Type*} [Category* C] {JJ : GrothendieckTopology C}
    {R : Sheaf JJ RingCat.{u}} {P P' Q : SheafOfModules.{u} R}
    (f : P ⟶ P') (g : P' ⟶ Q) (h : f ≫ g = 0) (V : Cᵒᵖ)
    (t : P.val.obj V) : g.val.app V (f.val.app V t) = 0 := by
  rw [← comp_val_app_section, h]
  rfl

/-- A morphism of modules vanishing on every section over every chart is zero. -/
private theorem eq_zero_of_forall_val_app_section {P Q : Modules.{u, u} B S hS X.1 X.2}
    (ψ : P ⟶ Q) (h : ∀ V t, ψ.val.app V t = 0) : ψ = 0 := by
  ext V t
  exact h V t

/-- Restriction of a section of the structure sheaf, read as a module over itself, along a
morphism of charts is restriction of regular functions. -/
private theorem unit_val_map_apply {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (x : (structureRingSheaf B S hS X).obj.obj (op U)) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).val.map f.op x =
      chartRestrict (hF := X.2) f x := rfl

/-- **The key lemma.** On an étale-locally reduced algebraic space whose space of points is
irreducible, let `J` be a sheaf of ideals whose unit locus is nonempty. A morphism
`θ : K ⟶ 𝒪_X` of modules which vanishes on the sections over every chart carrying the unit ideal
of `J` is zero. -/
theorem eq_zero_of_val_app_eq_zero_on_idealUnitCharts
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hJ : (idealUnitLocus B S hS X J).Nonempty)
    {K : Modules.{u, u} B S hS X.1 X.2}
    (θ : K ⟶ spaceStructureSheafModule B S hS X)
    (hθ : ∀ W : SmallEtale B S hS X.1, J.obj (op W) = ⊤ →
      ∀ x : K.val.obj (op W), θ.val.app (op W) x = 0) :
    θ = 0 := by
  by_contra hne
  obtain ⟨V, t, hst⟩ : ∃ (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (t : K.val.obj V),
      θ.val.app V t ≠ 0 := by
    by_contra hc
    exact hne (eq_zero_of_forall_val_app_section B S hS X θ
      fun V t => not_not.1 fun h => hc ⟨V, t, h⟩)
  obtain ⟨V⟩ := V
  have _ : IsReduced (chartScheme V) :=
    isReduced_chartScheme B S hS X hred V
  set s : (structureRingSheaf B S hS X).obj.obj (op V) := θ.val.app (op V) t
  have hs0 : (s : Γ(chartScheme V, ⊤)) ≠ 0 := hst
  obtain ⟨c, hc⟩ := nonempty_basicOpen_of_ne_zero (chartScheme V) hs0
  set O : (chartScheme V).Opens := (chartScheme V).basicOpen s
  set W : SmallEtale B S hS X.1 := openChart B S hS X.1 V O
  set g : W ⟶ V := openChartInclusion B S hS X.1 V O
  have hunit : IsUnit (chartRestrict (hF := X.2) g s) :=
    isUnit_chartRestrict_basicOpenChart B S hS X V s
  obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X.1).obj W) (⟨c, hc⟩ : (O : Type u))
  have hWopen : IsOpen (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom)) :=
    (isOpenMap_pointsMap_of_presheafEtale B S hS W.1.hom W.property).isOpen_range
  have _ : IrreducibleSpace (points B S hS X.1) := hirr
  have hdense : Dense (idealUnitLocus B S hS X J) :=
    (isOpen_idealUnitLocus B S hS X J).dense hJ
  obtain ⟨x, hxW, hxU⟩ := hdense.inter_open_nonempty _ hWopen ⟨_, ⟨p, rfl⟩⟩
  obtain ⟨q, hq⟩ := hxW
  rw [← hq] at hxU
  obtain ⟨W', g', hW'top, z, -⟩ :=
    (mem_idealUnitLocus_iff_exists_over B S hS X J W q).mp hxU
  refine one_ne_zero_structureRingSheaf_obj B S hS W' (pointsToScheme B S hS _ z) ?_
  have hu2 : IsUnit (chartRestrict (hF := X.2) g' (chartRestrict (hF := X.2) g s)) :=
    IsUnit.map (chartRestrict (hF := X.2) g') hunit
  obtain ⟨v, hv⟩ := hu2.exists_left_inv
  have hzero : chartRestrict (hF := X.2) g' (chartRestrict (hF := X.2) g s) = 0 := by
    have hnat := PresheafOfModules.naturality_apply θ.val (g' ≫ g).op t
    have h0 := hθ W' hW'top (K.val.map (g' ≫ g).op t)
    have hval : (spaceStructureSheafModule B S hS X).val.map (g' ≫ g).op s = 0 :=
      hnat.symm.trans h0
    have h3 : chartRestrict (hF := X.2) (g' ≫ g) s =
        chartRestrict (hF := X.2) g' (chartRestrict (hF := X.2) g s) :=
      congrArg (fun r : (structureRingSheaf B S hS X).obj.obj (op V) →+*
        (structureRingSheaf B S hS X).obj.obj (op W') => r s) (chartRestrict_comp g g')
    exact h3.symm.trans ((unit_val_map_apply B S hS X (g' ≫ g) s).symm.trans hval)
  have hprod : v * chartRestrict (hF := X.2) g' (chartRestrict (hF := X.2) g s) = 0 := by
    rw [hzero, mul_zero]
  exact hv.symm.trans hprod


/-- A sheaf of ideals whose unit locus is nonempty is not the zero ideal. -/
theorem ne_bot_of_idealUnitLocus_nonempty
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hJ : (idealUnitLocus B S hS X J).Nonempty) : J ≠ ⊥ := by
  obtain ⟨-, W, hWtop, y, -⟩ := hJ
  intro hbot
  refine one_ne_zero_structureRingSheaf_obj B S hS W (pointsToScheme B S hS _ y) ?_
  have h1 : SheafOfModules.unitOf (1 : (structureRingSheaf B S hS X).obj.obj (op W)) ∈
      J.obj (op W) := by
    rw [hWtop]
    exact Submodule.mem_top
  rw [hbot, SheafOfModules.Submodule.obj_eq_bot] at h1
  exact (Submodule.mem_bot _).1 h1

/-- **Injectivity.** On an étale-locally reduced algebraic space whose space of points is
irreducible, let `J` be a sheaf of ideals whose unit locus is nonempty. A map
`φ : J^{⊕ r} ⟶ F` which is injective on the sections over every chart carrying the unit ideal of
`J` is a monomorphism. -/
theorem mono_of_injective_on_idealUnitCharts
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hJ : (idealUnitLocus B S hS X J).Nonempty) {r : ℕ}
    {F : Modules.{u, u} B S hS X.1 X.2}
    (φ : (∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS X.1 X.2)) ⟶ F)
    (hφ : ∀ W : SmallEtale B S hS X.1, J.obj (op W) = ⊤ →
      ∀ y : (∏ᶜ fun _ : Fin r =>
          (J.toSheafOfModules : Modules.{u, u} B S hS X.1 X.2)).val.obj (op W),
        φ.val.app (op W) y = 0 → y = 0) :
    Mono φ := by
  have _ : Mono J.ι := SheafOfModules.Submodule.mono_ι_via_forget J
  refine Preadditive.mono_of_cancel_zero φ ?_
  intro L ψ hψ
  have hker : ∀ W : SmallEtale B S hS X.1, J.obj (op W) = ⊤ →
      ∀ y : L.val.obj (op W), ψ.val.app (op W) y = 0 := by
    intro W hW y
    exact hφ W hW _ (comp_val_app_section_eq_zero ψ φ hψ (op W) y)
  have hcoord : ∀ i : Fin r, ψ ≫ Pi.π (fun _ : Fin r =>
      (J.toSheafOfModules : Modules.{u, u} B S hS X.1 X.2)) i ≫ J.ι = 0 := by
    intro i
    refine eq_zero_of_val_app_eq_zero_on_idealUnitCharts B S hS X hred hirr J hJ _ ?_
    intro W hW y
    refine (comp_val_app_section ψ _ (op W) y).trans ?_
    rw [hker W hW y]
    exact map_zero _
  refine Pi.hom_ext _ _ fun i => ?_
  rw [zero_comp]
  refine (cancel_mono J.ι).1 ?_
  rw [zero_comp, Category.assoc]
  exact hcoord i

/-- If `φ : P ⟶ F` is surjective on the sections over every chart mapping to `W`, then the
cokernel of `φ` has no nonzero section over `W`. -/
theorem subsingleton_cokernel_val_obj_of_forall_surjective
    {P F : Modules.{u, u} B S hS X.1 X.2} (φ : P ⟶ F) (W : SmallEtale B S hS X.1)
    (h : ∀ W' : SmallEtale B S hS X.1, (W' ⟶ W) →
      ∀ s : F.val.obj (op W'), ∃ y : P.val.obj (op W'), φ.val.app (op W') y = s) :
    Subsingleton ((cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.obj (op W)) := by
  have hzero : ∀ t : (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.obj (op W), t = 0 := by
    intro t
    obtain ⟨Sv, hSv, hcov⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ) t
    refine (Presheaf.IsSheaf.isSeparated
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).isSheaf) W Sv hSv t 0 ?_
    intro Y f hf
    obtain ⟨b, hb⟩ := hcov f hf
    obtain ⟨y, hy⟩ := h Y f b
    have hz : (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val.app (op Y) b = 0 := by
      rw [← hy]
      exact comp_val_app_section_eq_zero φ _ (cokernel.condition _) (op Y) y
    rw [map_zero]
    exact hb.symm.trans hz
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- The unit locus of the reduced ideal sheaf of a proper closed subset is nonempty. -/
private theorem nonempty_idealUnitLocus_reducedIdealSheaf (Z : AlgebraicSpaces B S hS)
    (T : Set (points B S hS Z.1)) (hT : IsClosed T) (hTne : T ≠ Set.univ) :
    (idealUnitLocus B S hS Z (reducedIdealSheaf B S hS Z T hT)).Nonempty := by
  have h1 : (idealZeroLocus B S hS Z (reducedIdealSheaf B S hS Z T hT))ᶜ =
      idealUnitLocus B S hS Z (reducedIdealSheaf B S hS Z T hT) := compl_compl _
  rw [idealZeroLocus_reducedIdealSheaf] at h1
  rw [← h1]
  exact Set.nonempty_compl.2 hTne

/-- **The cokernel is supported in the zero locus.** If `φ : P ⟶ F` is surjective on the
sections over every chart carrying the unit ideal of `J`, then the support of the cokernel of
`φ` is contained in the zero locus of `J`. -/
theorem supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {P F : Modules.{u, u} B S hS X.1 X.2} (φ : P ⟶ F)
    (hsurj : ∀ W : SmallEtale B S hS X.1, J.obj (op W) = ⊤ →
      ∀ s : F.val.obj (op W), ∃ y : P.val.obj (op W), φ.val.app (op W) y = s) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ)) ⊆
      idealZeroLocus B S hS X J := by
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X _ J ?_
  intro V hV W g
  refine subsingleton_cokernel_val_obj_of_forall_surjective B S hS X φ W ?_
  intro W' g' s
  exact hsurj W' (SheafOfModules.Submodule.unit_obj_eq_top_of_map J (g' ≫ g).op hV) s

/-- A map out of copies of the reduced ideal sheaf of a proper closed `T`, bijective over the
charts carrying the unit ideal, is a monomorphism whose cokernel is supported in `T`. -/
private theorem mono_and_support_cokernel_subset_of_bijective_reducedIdealSheaf
    (Z : AlgebraicSpaces B S hS)
    (hred : HasEtaleLocalProperty B S hS Z.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS Z.1))
    (T : Set (points B S hS Z.1)) (hT : IsClosed T) (hTne : T ≠ Set.univ)
    {G : Modules.{u, u} B S hS Z.1 Z.2} {r : ℕ}
    (ψ : (∏ᶜ fun _ : Fin r => ((reducedIdealSheaf B S hS Z T hT).toSheafOfModules :
        Modules.{u, u} B S hS Z.1 Z.2)) ⟶ G)
    (hψ : ∀ W : SmallEtale B S hS Z.1, (reducedIdealSheaf B S hS Z T hT).obj (op W) = ⊤ →
      Function.Bijective (ψ.val.app (op W))) :
    Mono ψ ∧ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj
      (cokernel (C := Modules.{u, u} B S hS Z.1 Z.2) ψ)) ⊆ T :=
  ⟨mono_of_injective_on_idealUnitCharts B S hS Z hred hirr _
    (nonempty_idealUnitLocus_reducedIdealSheaf B S hS Z T hT hTne) ψ
    (fun W hW _ hy => (hψ W hW).1 (hy.trans (map_zero _).symm)),
    (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS Z _ ψ
      (fun W hW b => (hψ W hW).2 b)).trans
      (idealZeroLocus_reducedIdealSheaf B S hS Z T hT).le⟩

/-- **A generically bijective map out of a direct sum of copies of a reduced ideal sheaf is
injective, with cokernel supported in the closed set the ideal cuts out.**  This is the last
paragraph of the proof of [Stacks, Tag 07UQ] in the case `Z = X`. -/
theorem exists_mono_supportOfSheaf_cokernel_subset_of_bijective_on_unitCharts
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTne : T ≠ Set.univ)
    (F : Modules.{u, u} B S hS X.1 X.2) (r : ℕ) (hr : 0 < r)
    (φ : (∏ᶜ fun _ : Fin r => ((reducedIdealSheaf B S hS X T hT).toSheafOfModules :
        Modules.{u, u} B S hS X.1 X.2)) ⟶ F)
    (hφ : ∀ W : SmallEtale B S hS X.1, (reducedIdealSheaf B S hS X T hT).obj (op W) = ⊤ →
      Function.Bijective (φ.val.app (op W))) :
    ∃ (n : ℕ) (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule),
      0 < n ∧ J.toSheafOfModules.IsQuasicoherentOnSite ∧ J ≠ ⊥ ∧
        idealZeroLocus B S hS X J = T ∧
        ∃ ϕ : (∏ᶜ fun _ : Fin n => (J.toSheafOfModules : Modules.{u, u} B S hS X.1 X.2)) ⟶ F,
          Mono ϕ ∧ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
            (cokernel (C := Modules.{u, u} B S hS X.1 X.2) ϕ)) ⊆ T := by
  have hzl : idealZeroLocus B S hS X (reducedIdealSheaf B S hS X T hT) = T :=
    idealZeroLocus_reducedIdealSheaf B S hS X T hT
  have hJ := nonempty_idealUnitLocus_reducedIdealSheaf B S hS X T hT hTne
  refine ⟨r, reducedIdealSheaf B S hS X T hT, hr,
    isQuasicoherentOnSite_reducedIdealSheaf B S hS X T hT,
    ne_bot_of_idealUnitLocus_nonempty B S hS X _ hJ, hzl, φ,
    (mono_and_support_cokernel_subset_of_bijective_reducedIdealSheaf B S hS X hred hirr T hT
      hTne φ hφ).1, ?_⟩
  exact (mono_and_support_cokernel_subset_of_bijective_reducedIdealSheaf B S hS X hred hirr T hT
    hTne φ hφ).2

/-! ### The general case: a closed subspace `i : Z ⟶ X` -/

/-- **The direct image of a finite direct sum of copies of a module.**  The direct image is a
right adjoint, hence preserves the product of `n` copies of `M`, and a finite product in an
additive category is the direct sum; so the direct sum of `n` copies of `i_*M` is `i_*(M^{⊕ n})`.

This is the identification under which the source of the injection of [Stacks, Tag 07UQ] may be
written either way: the source writes `i_*(I^{⊕ r})`, while a consumer which wants the direct
sum outside the direct image — as
`AlgebraicGeometry.Space.exists_mono_biproduct_idealPushforward_of_schemeTheoreticSupport_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissageHigherRank.lean` does — composes the
morphism produced below with this isomorphism. -/
noncomputable def modulePushforwardBiproductConstIso {Y : AlgebraicSpaces B S hS} (i : Y ⟶ X)
    (n : ℕ) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (⨁ fun _ : Fin n => (modulePushforward B S hS i).obj M) ≅
      (modulePushforward B S hS i).obj (∏ᶜ fun _ : Fin n => M) :=
  have _ : PreservesLimits (modulePushforward B S hS i) :=
    (modulePullbackAdjunction B S hS i).rightAdjoint_preservesLimits
  biproduct.isoProduct _ ≪≫ (PreservesProduct.iso (modulePushforward B S hS i)
    (fun _ : Fin n => M)).symm

/-- **The general case of a closed subspace `i : Z ⟶ X`, for a given map.**  For a closed
immersion `i : Z ⟶ X` with `Z` étale-locally reduced and `|Z|` irreducible, an `𝒪_X`-module
`F ≅ i_*G` and a map `ψ` out of a direct sum of copies of the reduced ideal sheaf of a closed
`T ⊊ |Z|` which is bijective over the charts carrying the unit ideal, the direct image of `ψ` is
an injection into `F` whose cokernel is supported in the image of `T`.  Injectivity and the
support of the cokernel on `Z` come from the case `Z = X` above, and the direct image along a
closed immersion is exact. -/
theorem exists_mono_modulePushforward_cokernelCofork_support_subset_image
    {Y : AlgebraicSpaces B S hS} (i : Y ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : IrreducibleSpace (points B S hS Y.1))
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (eG : (modulePushforward B S hS i).obj G ≅ F)
    (T : Set (points B S hS Y.1)) (hT : IsClosed T) (hTne : T ≠ Set.univ)
    (r : ℕ) (hr : 0 < r)
    (ψ : (∏ᶜ fun _ : Fin r => ((reducedIdealSheaf B S hS Y T hT).toSheafOfModules :
        Modules.{u, u} B S hS Y.1 Y.2)) ⟶ G)
    (hψ : ∀ W : SmallEtale B S hS Y.1, (reducedIdealSheaf B S hS Y T hT).obj (op W) = ⊤ →
      Function.Bijective (ψ.val.app (op W))) :
    ∃ (n : ℕ) (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule),
      0 < n ∧ I.toSheafOfModules.IsQuasicoherentOnSite ∧ I ≠ ⊥ ∧
      ∃ φ : (modulePushforward B S hS i).obj
          (∏ᶜ fun _ : Fin n => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ⟶ F,
        Mono φ ∧ ∃ (Q : Modules.{u, u} B S hS X.1 X.2) (q : F ⟶ Q) (hq : φ ≫ q = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ q hq)) ∧
            ∃ T' : Set (points B S hS Y.1), IsClosed T' ∧ T' ≠ Set.univ ∧
              supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) ⊆
                pointsMap B S hS Y.1 i.hom '' T' := by
  have hJ := nonempty_idealUnitLocus_reducedIdealSheaf B S hS Y T hT hTne
  obtain ⟨hmψ, hsupp⟩ := mono_and_support_cokernel_subset_of_bijective_reducedIdealSheaf B S hS Y
    hred hirr T hT hTne ψ hψ
  have hTimg : IsClosed (pointsMap B S hS Y.1 i.hom '' T) :=
    isClosedMorphism_of_isClosedImmersion B S hS Y.2 X.2 i.hom hi T hT
  have hmono : Mono ((modulePushforward B S hS i).map ψ ≫ eG.hom) := by
    have h1 : Mono ((modulePushforward B S hS i).map ψ) :=
      mono_modulePushforward_map B S hS i ψ hmψ
    have h2 : Mono eG.hom := mono_of_mono_fac eG.hom_inv_id
    exact mono_comp _ _
  refine ⟨r, reducedIdealSheaf B S hS Y T hT, hr,
    isQuasicoherentOnSite_reducedIdealSheaf B S hS Y T hT,
    ne_bot_of_idealUnitLocus_nonempty B S hS Y _ hJ,
    (modulePushforward B S hS i).map ψ ≫ eG.hom, hmono,
    cokernel (C := Modules.{u, u} B S hS X.1 X.2)
      ((modulePushforward B S hS i).map ψ ≫ eG.hom),
    cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
      ((modulePushforward B S hS i).map ψ ≫ eG.hom), cokernel.condition _,
    ⟨cokernelIsCokernel (C := Modules.{u, u} B S hS X.1 X.2) _⟩, T, hT, hTne, ?_⟩
  have e1 : cokernel (C := Modules.{u, u} B S hS X.1 X.2)
      ((modulePushforward B S hS i).map ψ ≫ eG.hom) ≅
      cokernel (C := Modules.{u, u} B S hS X.1 X.2)
        ((modulePushforward B S hS i).map ψ) :=
    cokernelCompIsIso _ _
  rw [supportOfSheaf_eq_of_iso B S hS X (e1.trans (modulePushforwardCokernelIso B S hS i hi ψ))]
  refine supportOfSheaf_modulePushforward_subset_of_isClosed B S hS i _ _ hTimg ?_
  exact le_trans hsupp (Set.subset_preimage_image _ _)

end AlgebraicGeometry.Space

end
