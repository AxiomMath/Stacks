module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimit

/-!
# Finite members of the `Sym(F_k)/(E)` system that agree with the algebra over a chart

Let `𝒜` be an integral quasi-coherent algebra on a quasi-compact algebraic space, presented as in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimit` by the system
`(k, E) ↦ Sym(F_k)/(E)`. Let `U` be an affine étale chart over which `𝒜(U)` is a finite and
finitely presented algebra over the chart ring. Then the members of the system which are finite and
whose comparison map to `𝒜` is bijective over `U` are cofinal, so that `𝒜` is a directed colimit of
quasi-coherent algebras that are finite, of finite presentation, and agree with `𝒜` over `U`.

## Main results

* `Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered_of_legs`: a filtered colimit with
  an essentially `w`-small index is a directed colimit over a preorder in `Type w` whose legs are
  legs of the original cocone.
* `AlgebraicGeometry.Space.FPAlgColim.surjective_ψ_app_of_span`: `Sym(F_k)(U) ⟶ 𝒜(U)` is surjective
  when the image of `F_k(U)` contains generators of the module `𝒜(U)`.
* `AlgebraicGeometry.Space.FPAlgColim.exists_hom_forall_bijective`: every member of the system maps
  to one over which every larger `E` gives a comparison bijective over `U`.
* `AlgebraicGeometry.Space.FPAlgColim.exists_hom_isFinite_bijective`: every member maps to a finite
  one whose comparison is bijective over `U`.
* `AlgebraicGeometry.Space.exists_directed_isColimit_isFinite_bijective_of_presentation`: `𝒜` is a
  directed colimit of quasi-coherent algebras that are finite and of finite presentation, with legs
  bijective over `U`.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₂ u₂ v₁ u₁ u

namespace Stacks.FilteredCardIndex

variable {C : Type u₁} [Category.{v₁} C]

/-- A filtered colimit with an essentially `w`-small index is a directed colimit over a preorder in
`Type w` whose legs are legs of the original cocone: a property `Q` of morphisms into `A` holding
for every leg of `t` holds for every leg of the new cocone. -/
theorem exists_directed_index_of_isFiltered_of_legs {D : Type u₂} [Category.{v₂} D]
    [IsFiltered D] [EssentiallySmall.{w} D] {G : D ⥤ C} {A : C}
    (t : G ⟶ (Functor.const D).obj A) (ht : IsColimit (Cocone.mk A t))
    (Q : ∀ X : C, (X ⟶ A) → Prop) (hQ : ∀ d, Q _ (t.app d)) :
    ∃ (I : Type w) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ C) (s : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A s)),
      ∀ i, Q _ (s.app i) := by
  have : IsFiltered (SmallModel.{w} D) := IsFiltered.of_equivalence (equivSmallModel.{w} D)
  obtain ⟨α, _, _, _, F₀, _⟩ := IsFiltered.exists_directed (SmallModel.{w} D)
  let e : SmallModel.{w} D ≌ D := (equivSmallModel.{w} D).symm
  exact ⟨α, inferInstance, inferInstance, inferInstance, F₀ ⋙ e.functor ⋙ G,
    (((Cocone.mk A t).whisker e.functor).whisker F₀).ι,
    (Functor.Final.isColimitWhiskerEquiv F₀ _).symm (ht.whiskerEquivalence e), fun i => hQ _⟩

end Stacks.FilteredCardIndex

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- A family of modules of finite presentation consists of quasi-coherent modules of finite
presentation on the site. -/
private theorem forall_isQuasicoherentOnSite_and_isFinitePresentationOnSite {K : Type u}
    [SmallCategory K] {D : K ⥤ Modules.{u, u} B S hS F hF}
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) :
    (∀ k, (D.obj k).IsQuasicoherentOnSite) ∧
      ∀ k, SheafOfModules.IsFinitePresentationOnSite (D.obj k) :=
  ⟨fun k =>
      have := hfp k
      Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation (D.obj k),
    fun k => SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation (D.obj k)
      (h := hfp k)⟩

namespace FPAlgColim

variable {𝒜 : AlgebraSheaf.{u, u} B S hS F hF} {K : Type u} [SmallCategory K]
  {D : K ⥤ Modules.{u, u} B S hS F hF}
  {φ : D ⟶ (Functor.const K).obj (AlgebraSheaf.underlyingModule 𝒜)}

/-- `Sym(F_k)(U) ⟶ 𝒜(U)` is surjective as soon as the image of `F_k(U)` contains a set of
generators of the module `𝒜(U)`. -/
theorem surjective_ψ_app_of_span {k : K} {U : SmallEtale B S hS F}
    (s : Set ((AlgebraSheaf.underlyingModule 𝒜).val.obj (op U)))
    (hs : Submodule.span (chartRing B S hS F hF U) s = ⊤)
    (hsk : ∀ x ∈ s, ∃ m : (D.obj k).val.obj (op U), (φ.app k).val.app (op U) m = x) :
    Function.Surjective ((ψ φ k).right.hom.app (op U)).hom := by
  suffices h : ∀ a : (AlgebraSheaf.underlyingModule 𝒜).val.obj (op U),
      ∃ b, ((ψ φ k).right.hom.app (op U)).hom b = a from h
  intro a
  have ha : a ∈ Submodule.span (chartRing B S hS F hF U) s := hs ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hsk x hx
    exact ⟨SymSections.genApp (D.obj k) (op U) m, SymSections.gen_lift_apply (φ.app k) (op U) m⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨b + c, (map_add _ b c).trans (congrArg₂ (· + ·) hb hc)⟩
  | smul r x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨(SymSections.algebra (D.obj k)).algebraMap (op U) r * b, (map_mul _ _ b).trans ?_⟩
    rw [hb]
    exact congrArg (· * (show 𝒜.right.obj.obj (op U) from x)) ((ψ φ k).comm (op U) r)

variable (hfp : ∀ k, (D.obj k).IsFinitePresentation) (h𝒜 : 𝒜.IsQuasicoherent)
  (h0829 : ∀ G : Modules.{u, u} B S hS F hF, G.IsQuasicoherentOnSite →
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF G)))

include hfp h𝒜 h0829 in
/-- Every member of the system `(k, E) ↦ Sym(F_k)/(E)` maps to a member `(k₁, E₁)` such that, for
every finite type quasi-coherent `E ⊇ E₁` in `J_{k₁}`, the comparison `Sym(F_{k₁})/(E) ⟶ 𝒜` is
bijective over `U`, provided `𝒜(U)` is a finite and finitely presented algebra over the chart ring
of the affine chart `U`. -/
theorem exists_hom_forall_bijective [IsFiltered K] (hc : IsColimit (Cocone.mk _ φ))
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hfinU : RingHom.Finite (𝒜.algebraMap (op U)))
    (hfpU : RingHom.FinitePresentation (𝒜.algebraMap (op U))) (i : Idx φ) :
    ∃ (j : Idx φ) (_ : i ⟶ j), ∀ E : FiniteTypeQuasicoherentSubobject B S hS F hF (J φ j.k),
      (j.E ⟶ E) →
        Function.Bijective (((coconeι φ).app (⟨j.k, E⟩ : Idx φ)).right.hom.app (op U)).hom := by
  classical
  obtain ⟨hD, hD'⟩ := forall_isQuasicoherentOnSite_and_isFinitePresentationOnSite hfp
  have hfinM : Module.Finite (chartRing B S hS F hF U)
      ((AlgebraSheaf.underlyingModule 𝒜).val.obj (op U)) := hfinU
  obtain ⟨s, hs⟩ := hfinM.fg_top
  choose kx mx hmx using fun x => exists_eq_of_isColimit_of_isQuasicoherentOnSite φ hc hD h𝒜 hU x
  let O : Finset K := insert i.k (s.image kx)
  let k₁ := IsFiltered.sup O ∅
  have hik : i.k ∈ O := Finset.mem_insert_self _ _
  have hxk : ∀ x ∈ s, kx x ∈ O := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
  have hsurj : Function.Surjective ((ψ φ k₁).right.hom.app (op U)).hom := by
    refine surjective_ψ_app_of_span (s : Set _) hs fun x hx =>
      ⟨(D.map (IsFiltered.toSup O ∅ (hxk x hx))).val.app (op U) (mx x), ?_⟩
    have hnat : D.map (IsFiltered.toSup O ∅ (hxk x hx)) ≫ φ.app k₁ = φ.app (kx x) :=
      (φ.naturality _).trans (Category.comp_id _)
    exact (congrArg (fun g => g.val.app (op U) (mx x)) hnat).trans (hmx x)
  let ℬ := SymSections.algebra (D.obj k₁)
  let _ : Algebra ((structureSheaf B S hS F hF).obj.obj (op U)) (ℬ.right.obj.obj (op U)) :=
    (ℬ.algebraMap (op U)).toAlgebra
  let _ : Algebra ((structureSheaf B S hS F hF).obj.obj (op U)) (𝒜.right.obj.obj (op U)) :=
    (𝒜.algebraMap (op U)).toAlgebra
  have hfpB : RingHom.FinitePresentation (ℬ.algebraMap (op U)) :=
    SymSections.isFinitePresentation_algebra _ (hD k₁) (hD' k₁) U hU
  let ψA : ℬ.right.obj.obj (op U) →ₐ[(structureSheaf B S hS F hF).obj.obj (op U)]
      𝒜.right.obj.obj (op U) :=
    { ((ψ φ k₁).right.hom.app (op U)).hom with commutes' := fun r => (ψ φ k₁).comm (op U) r }
  have hker : (RingHom.ker ψA.toRingHom).FG :=
    @Algebra.FinitePresentation.ker_fG_of_surjective _ _ _ _ _ _ _ _ ψA hsurj hfpB hfpU
  obtain ⟨t, ht⟩ := hker
  have hJq := isQuasicoherentOnSite_J φ hD h𝒜 k₁
  have hJ : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS F hF (J φ k₁)) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS F hF (J φ k₁)
  obtain ⟨hcol⟩ := h0829 (J φ k₁) hJq
  have hw : ∀ w : t, ∃ (E : FiniteTypeQuasicoherentSubobject B S hS F hF (J φ k₁))
      (z : (Subobject.underlying.obj E.obj).val.obj (op U)),
      (ι φ k₁).val.app (op U) (E.obj.arrow.val.app (op U) z) = w.1 := by
    intro w
    have h0 : (ψ φ k₁).right.hom.app (op U) w.1 = 0 :=
      (ht ▸ Ideal.subset_span w.2 : w.1 ∈ RingHom.ker ψA.toRingHom)
    obtain ⟨E, z, hz⟩ := exists_eq_of_isColimit_of_mono
      (finiteTypeQuasicoherentSubobjectCocone B S hS F hF (J φ k₁)).ι hcol
      (fun E => (inferInstance : Mono E.obj.arrow)) hU
      (⟨w.1, (SheafOfModules.mem_kerSubmodule _ _ _).2 h0⟩ : (J φ k₁).val.obj (op U))
    exact ⟨E, z, congrArg Subtype.val hz⟩
  choose Ew zw hzw using hw
  let O' : Finset (FiniteTypeQuasicoherentSubobject B S hS F hF (J φ k₁)) :=
    insert (imageFT φ hD h𝒜 i.E (IsFiltered.toSup O ∅ hik)) (Finset.univ.image Ew)
  let E₁ := IsFiltered.sup O' ∅
  have hEw : ∀ w : t, Ew w ∈ O' := fun w =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  refine ⟨⟨k₁, E₁⟩, homOfImageLE (j := ⟨k₁, E₁⟩) (IsFiltered.toSup O ∅ hik)
    (leOfHom (IsFiltered.toSup O' ∅ (Finset.mem_insert_self _ _)).hom), fun E hE => ?_⟩
  let j' : Idx φ := ⟨k₁, E⟩
  have hℬq : ℬ.IsQuasicoherent := SymSections.isQuasicoherent_algebra _ (hD k₁)
  have hb := GenQuot.bijective_unit_app (n j') hℬq E.property.1 U hU
  have hfac : ∀ a, ((coconeι φ).app j').right.hom.app (op U)
      ((GenQuot.unit (n j')).app (op U) (GenQuot.mk (n j') (op U) a)) =
        (ψ φ k₁).right.hom.app (op U) a :=
    fun a => GenQuot.lift_app_unit (n j') (ψ φ k₁) (kills j') (op U) a
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨q, rfl⟩ := hb.2 y
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hw0 : w ∈ RingHom.ker ψA.toRingHom := (hfac w).symm.trans hy
    rw [← ht] at hw0
    have hle : Ideal.span (t : Set (ℬ.right.obj.obj (op U))) ≤
        GenQuot.sectionIdeal (n j') (op U) := by
      refine Ideal.span_le.2 fun w' hw' => ?_
      let w'' : t := ⟨w', hw'⟩
      have hle' : (Ew w'').obj ≤ E.obj :=
        (leOfHom (IsFiltered.toSup O' ∅ (hEw w'')).hom).trans (leOfHom hE.hom)
      refine Ideal.subset_span ⟨(Subobject.ofLE _ _ hle').val.app (op U) (zw w''), ?_⟩
      have h3 : Subobject.ofLE _ _ hle' ≫ E.obj.arrow ≫ ι φ k₁ = (Ew w'').obj.arrow ≫ ι φ k₁ := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      exact (ConcreteCategory.congr_hom (congrArg (fun g => g.val.app (op U)) h3)
        (zw w'')).trans (hzw w'')
    have hmk : GenQuot.mk (n j') (op U) w = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hle hw0)
    show (GenQuot.unit (n j')).app (op U) (GenQuot.mk (n j') (op U) w) = 0
    rw [hmk, map_zero]
  · obtain ⟨a, ha⟩ := hsurj y
    exact ⟨_, (hfac a).trans ha⟩

include hfp h𝒜 h0829 in
/-- Every member of the system `(k, E) ↦ Sym(F_k)/(E)` maps to a finite member whose comparison
with `𝒜` is bijective over `U`, provided `𝒜(U)` is a finite and finitely presented algebra over the
chart ring of the affine chart `U`. -/
theorem exists_hom_isFinite_bijective [IsFiltered K] (hc : IsColimit (Cocone.mk _ φ))
    (hint : 𝒜.IsIntegral) {U₀ : SmallEtale B S hS F}
    (hU₀ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U₀))
    (hcov : (SmallEtale.topology B S hS F).CoversTop fun _ : PUnit.{u + 2} => U₀)
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hfinU : RingHom.Finite (𝒜.algebraMap (op U)))
    (hfpU : RingHom.FinitePresentation (𝒜.algebraMap (op U))) (i : Idx φ) :
    ∃ (j : Idx φ) (_ : i ⟶ j), ((diagram φ).obj j).IsFinite ∧
      Function.Bijective (((coconeι φ).app j).right.hom.app (op U)).hom := by
  obtain ⟨j, f, hj⟩ := exists_hom_forall_bijective hfp h𝒜 h0829 hc hU hfinU hfpU i
  obtain ⟨E, g, hE⟩ := exists_le_isFinite hfp h𝒜 hint h0829 hU₀ hcov j.k j.E
  refine ⟨⟨j.k, E⟩, f ≫ homOfImageLE (j := ⟨j.k, E⟩) (𝟙 j.k) ?_, hE, hj E g⟩
  rw [jmap_id, Category.comp_id, imageSubobject_mono, Subobject.mk_arrow]
  exact leOfHom g.hom

end FPAlgColim

variable (B S hS F hF) in
/-- An integral quasi-coherent algebra `𝒜` on a quasi-compact algebraic space, finite and finitely
presented over an affine chart `U`, is a directed colimit of quasi-coherent algebras that are
finite and of finite presentation, whose legs are bijective over `U`, given a filtered presentation
`φ` of its underlying module by modules of finite presentation and the colimit assertion of Stacks
0829 (`h0829`). The index is a nonempty directed preorder in the universe of the schemes, and the
colimit is taken in the category of all algebra sheaves. -/
theorem exists_directed_isColimit_isFinite_bijective_of_presentation
    (hqc : IsQuasiCompactSpace B S hS F) (𝒜 : AlgebraSheaf.{u, u} B S hS F hF)
    (h𝒜 : 𝒜.IsQuasicoherent) (hint : 𝒜.IsIntegral) {K : Type u} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS F hF}
    (φ : D ⟶ (Functor.const K).obj (AlgebraSheaf.underlyingModule 𝒜))
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) (hc : IsColimit (Cocone.mk _ φ))
    (h0829 : ∀ G : Modules.{u, u} B S hS F hF, G.IsQuasicoherentOnSite →
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF G)))
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hfinU : RingHom.Finite (𝒜.algebraMap (op U)))
    (hfpU : RingHom.FinitePresentation (𝒜.algebraMap (op U))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (E : I ⥤ AlgebraSheaf.{u, u} B S hS F hF) (t : E ⟶ (Functor.const I).obj 𝒜)
      (_ : IsColimit (Cocone.mk 𝒜 t)),
      ∀ i, (E.obj i).IsQuasicoherent ∧ (E.obj i).IsFinite ∧ (E.obj i).IsFinitePresentation ∧
        Function.Bijective ((t.app i).right.hom.app (op U)).hom := by
  obtain ⟨hD, hD'⟩ := forall_isQuasicoherentOnSite_and_isFinitePresentationOnSite hfp
  obtain ⟨U₀, hU₀, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS F hF hqc
  have := FPAlgColim.isFiltered hD h𝒜 (φ := φ)
  have := FPAlgColim.essentiallySmall (φ := φ)
  obtain ⟨hcol⟩ := FPAlgColim.nonempty_isColimit hc hD h𝒜 h0829
  let P : ObjectProperty (FPAlgColim.Idx φ) := fun j =>
    ((FPAlgColim.diagram φ).obj j).IsFinite ∧
      Function.Bijective (((FPAlgColim.coconeι φ).app j).right.hom.app (op U)).hom
  have hP : ∀ i, ∃ j : P.FullSubcategory, Nonempty (i ⟶ P.ι.obj j) := fun i => by
    obtain ⟨j, f, hj⟩ :=
      FPAlgColim.exists_hom_isFinite_bijective hfp h𝒜 h0829 hc hint hU₀ hcov hU hfinU hfpU i
    exact ⟨⟨j, hj⟩, ⟨f⟩⟩
  have : IsFiltered P.FullSubcategory := IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι hP
  have : P.ι.Final := Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι hP
  have : EssentiallySmall.{u} P.FullSubcategory := essentiallySmall_of_fully_faithful P.ι
  have hcolP : IsColimit (Cocone.mk 𝒜 (Functor.whiskerLeft P.ι (FPAlgColim.coconeι φ))) :=
    (Functor.Final.isColimitWhiskerEquiv P.ι (Cocone.mk 𝒜 (FPAlgColim.coconeι φ))).symm hcol
  exact Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered_of_legs.{u}
    (Functor.whiskerLeft P.ι (FPAlgColim.coconeι φ)) hcolP
    (fun (A : AlgebraSheaf.{u, u} B S hS F hF) (a : A ⟶ 𝒜) =>
      A.IsQuasicoherent ∧ A.IsFinite ∧ A.IsFinitePresentation ∧
        Function.Bijective ((a.right.hom.app (op U))).hom)
    (fun j => ⟨FPAlgColim.isQuasicoherent_diagram_obj hD j.obj, j.property.1,
      FPAlgColim.isFinitePresentation_diagram_obj hD hD' j.obj, j.property.2⟩)

end AlgebraicGeometry.Space

end
