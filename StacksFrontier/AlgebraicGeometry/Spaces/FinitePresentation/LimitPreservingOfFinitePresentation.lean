module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QuotientPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SheafifyRelative

/-!
# Local finite presentation implies relative limit preservation

A morphism of algebraic spaces over a scheme which is locally of finite presentation is
relatively limit preserving. This is the implication (1) ⇒ (2) of Stacks 04AK, for a morphism
which is not assumed representable.

## Main definitions

* `AlgebraicGeometry.sectionFiberMap` is the map on presheaves of lifts of a section of the
  target induced by a transformation over that target.

## Main results

* `AlgebraicGeometry.isLocallySurjective_sectionFiberMap`: a locally surjective transformation
  over the target induces locally surjective maps on the presheaves of lifts.
* `AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`: a morphism of
  algebraic spaces which is locally of finite presentation is relatively limit preserving.

## Implementation notes

Let `a : F ⟶ G` be locally of finite presentation, let `p : yoneda.obj U ⟶ F` be a surjective
étale atlas of the source and let `R` represent the kernel pair of `p`, with projections
`r₁, r₂ : R ⟶ U`. Both `p` and `yoneda.map r₁ ≫ p` are étale charts of `F`, so both `p ≫ a`
and `(yoneda.map r₁ ≫ p) ≫ a` are relatively limit preserving by
`AlgebraicGeometry.relativelyLimitPreserving_comp_of_etale_chart`. Over a fixed section `y` of
`G`, the two projections give two maps of presheaves of lifts on the slice over the base of
`y`, and their coequalizer is limit preserving because a coequalizer of presheaves of sets is
computed objectwise.

The canonical map from that coequalizer to the presheaf of lifts of `y` through `a` is locally
surjective, because `p` is locally surjective and local surjectivity passes to presheaves of
lifts; and it is objectwise injective, because two lifts of `y` through `p ≫ a` with the same
image in `F` are the two projections of a point of the kernel pair and so are identified in
the coequalizer. Tag 049O on the slice, in the form
`AlgebraicGeometry.limitPreserving_sectionFiber_of_isLocallyBijective`, then transports limit
preservation across it.

## References

* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 049O](https://stacks.math.columbia.edu/tag/049O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction in a presheaf of lifts is restriction of the underlying section. -/
@[simp]
theorem sectionFiber_map_coe {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (X : BigFppfOver B S hS) (y : G.obj (op X)) {W W' : (Over X)ᵒᵖ} (f : W ⟶ W')
    (x : (sectionFiber B S hS a X y).obj W) :
    (((sectionFiber B S hS a X y).map f) x).1 = F.map f.unop.left.op x.1 := by
  simp [sectionFiber]

section SectionFiberMap

variable {F₁ F₂ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a₁ : F₁ ⟶ G} {a₂ : F₂ ⟶ G}

/-- Applying `a₂` after `g` is applying `a₁` when `g ≫ a₂ = a₁`. -/
private theorem app_comp_eq_of_comp_eq (g : F₁ ⟶ F₂) (hg : g ≫ a₂ = a₁) (X : (BigFppfOver B S hS)ᵒᵖ)
    (x : F₁.obj X) : a₂.app X (g.app X x) = a₁.app X x := by
  rw [← NatTrans.comp_app_apply, hg]

/-- The image of a lift of `y` through `a₁` under a transformation over the target is a lift of
`y` through `a₂`. -/
theorem app_mem_sectionFiber (g : F₁ ⟶ F₂) (hg : g ≫ a₂ = a₁) (X : BigFppfOver B S hS)
    (y : G.obj (op X)) (W : (Over X)ᵒᵖ) (x : (sectionFiber B S hS a₁ X y).obj W) :
    a₂.app (op W.unop.left) (g.app (op W.unop.left) x.1) = G.map W.unop.hom.op y :=
  (app_comp_eq_of_comp_eq B S hS g hg _ _).trans x.2

/-- The map on presheaves of lifts of a section of the target induced by a transformation over
that target. -/
def sectionFiberMap (g : F₁ ⟶ F₂) (hg : g ≫ a₂ = a₁) (X : BigFppfOver B S hS)
    (y : G.obj (op X)) :
    sectionFiber B S hS a₁ X y ⟶ sectionFiber B S hS a₂ X y where
  app W := ↾fun x => ⟨g.app (op W.unop.left) x.1, app_mem_sectionFiber B S hS g hg X y W x⟩
  naturality W W' f := by
    ext x
    refine Subtype.ext ?_
    simp [sectionFiber]

/-- The underlying section of the image of a lift under `sectionFiberMap` is the image of the
underlying section under the transformation. -/
@[simp]
theorem sectionFiberMap_app_coe (g : F₁ ⟶ F₂) (hg : g ≫ a₂ = a₁) (X : BigFppfOver B S hS)
    (y : G.obj (op X)) (W : (Over X)ᵒᵖ) (x : (sectionFiber B S hS a₁ X y).obj W) :
    ((sectionFiberMap B S hS g hg X y).app W x).1 = g.app (op W.unop.left) x.1 := by
  simp [sectionFiberMap]

/-- A locally surjective transformation over the target induces locally surjective maps on the
presheaves of lifts of a section, for the topology of the slice over the base of that section. -/
theorem isLocallySurjective_sectionFiberMap (g : F₁ ⟶ F₂) (hg : g ≫ a₂ = a₁)
    (X : BigFppfOver B S hS) (y : G.obj (op X))
    (hgsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g) :
    Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over X)
      (sectionFiberMap B S hS g hg X y) := by
  refine ⟨fun {W} x => ?_⟩
  refine ((BigFppfOver.topology B S hS).over X).superset_covering ?_
    ((BigFppfOver.topology B S hS).overEquiv_symm_mem_over W _
      (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) g (U := op W.left) x.1))
  intro Z f hf
  rw [Sieve.overEquiv_symm_iff] at hf
  obtain ⟨t, ht⟩ := hf
  have hx : a₂.app (op W.left) x.1 = G.map W.hom.op y := x.2
  have h₂ : a₂.app (op Z.left) (F₂.map f.left.op x.1) = G.map Z.hom.op y := by
    rw [NatTrans.naturality_apply a₂ f.left.op x.1, hx, ← Functor.map_comp_apply, ← op_comp,
      Over.w f]
  have hcond : a₁.app (op Z.left) t = G.map Z.hom.op y := by
    rw [← app_comp_eq_of_comp_eq B S hS g hg, ht, h₂]
  refine ⟨⟨t, hcond⟩, Subtype.ext ?_⟩
  simpa only [sectionFiberMap_app_coe, sectionFiber_map_coe, unop_op,
    Quiver.Hom.unop_op] using ht

end SectionFiberMap

/-- Limit preservation of the presheaf of lifts of a section through a morphism of algebraic
spaces, given a locally surjective atlas of the source with a represented kernel pair whose
two composites with the morphism are relatively limit preserving. -/
private theorem limitPreserving_sectionFiber_of_atlas
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {a : F ⟶ G}
    {U R : BigFppfOver B S hS} {p : yoneda.obj U ⟶ F} (r₁ r₂ : R ⟶ U)
    (hpb : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p)
    (hpsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p)
    (hLPR : RelativelyLimitPreserving.{u, u, u, u} B S hS ((yoneda.map r₁ ≫ p) ≫ a))
    (hLPU : RelativelyLimitPreserving.{u, u, u, u} B S hS (p ≫ a))
    (X : BigFppfOver B S hS) (y : G.obj (op X)) :
    LimitPreserving.{u, u, u, u, u + 1} (Over.forget X ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a X y) := by
  let s : sectionFiber B S hS ((yoneda.map r₁ ≫ p) ≫ a) X y ⟶
      sectionFiber B S hS (p ≫ a) X y :=
    sectionFiberMap B S hS (yoneda.map r₁) (Category.assoc _ _ _).symm X y
  let t : sectionFiber B S hS ((yoneda.map r₁ ≫ p) ≫ a) X y ⟶
      sectionFiber B S hS (p ≫ a) X y :=
    sectionFiberMap B S hS (yoneda.map r₂) (by rw [← Category.assoc, hpb.w]) X y
  let κ : sectionFiber B S hS (p ≫ a) X y ⟶ sectionFiber B S hS a X y :=
    sectionFiberMap B S hS (a₁ := p ≫ a) (a₂ := a) p rfl X y
  have hκ : s ≫ κ = t ≫ κ := by
    ext W x
    refine Subtype.ext ?_
    have h := congrArg (fun φ : yoneda.obj R ⟶ F => φ.app (op W.unop.left) x.1) hpb.w
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, TypeCat.Fun.toFun_apply,
      sectionFiberMap_app_coe, s, t, κ] using h
  let η : (coequalizer s t : (Over X)ᵒᵖ ⥤ Type u) ⟶ sectionFiber B S hS a X y :=
    coequalizer.desc κ hκ
  have hfac : coequalizer.π s t ≫ η = κ := coequalizer.π_desc κ hκ
  have hηfac : ∀ (W : (Over X)ᵒᵖ) (x : (sectionFiber B S hS (p ≫ a) X y).obj W),
      η.app W ((coequalizer.π s t).app W x) = κ.app W x := by
    intro W x
    have h : ((coequalizer.π s t ≫ η).app W) x = (κ.app W) x := by rw [hfac]
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  -- the comparison map is locally surjective
  have hκsurj : Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over X) κ :=
    isLocallySurjective_sectionFiberMap B S hS p rfl X y hpsurj
  have hηsurj : Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over X) η :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  -- the comparison map is objectwise injective
  have hπsurj : ∀ W : (Over X)ᵒᵖ, Function.Surjective ((coequalizer.π s t).app W) :=
    fun W => surjective_of_epi _
  have hηinj : ∀ W : (Over X)ᵒᵖ, Function.Injective (η.app W) := by
    intro W z₁ z₂ hz
    obtain ⟨x₁, rfl⟩ := hπsurj W z₁
    obtain ⟨x₂, rfl⟩ := hπsurj W z₂
    rw [hηfac, hηfac] at hz
    have hval : p.app (op W.unop.left) x₁.1 = p.app (op W.unop.left) x₂.1 := by
      simpa only [sectionFiberMap_app_coe, κ] using congrArg Subtype.val hz
    have hlift : yoneda.map x₁.1 ≫ p = yoneda.map x₂.1 ≫ p := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
      exact hval
    let w : W.unop.left ⟶ R :=
      yoneda.preimage (hpb.lift (yoneda.map x₁.1) (yoneda.map x₂.1) hlift)
    have hmap : yoneda.map w = hpb.lift (yoneda.map x₁.1) (yoneda.map x₂.1) hlift :=
      yoneda.map_preimage _
    have hw₁ : w ≫ r₁ = x₁.1 :=
      yoneda.map_injective (by rw [Functor.map_comp, hmap]; exact hpb.lift_fst _ _ _)
    have hw₂ : w ≫ r₂ = x₂.1 :=
      yoneda.map_injective (by rw [Functor.map_comp, hmap]; exact hpb.lift_snd _ _ _)
    have happ₁ : (yoneda.map r₁).app (op W.unop.left) w = w ≫ r₁ := by simp
    have happ₂ : (yoneda.map r₂).app (op W.unop.left) w = w ≫ r₂ := by simp
    have hcond : ((yoneda.map r₁ ≫ p) ≫ a).app (op W.unop.left) w =
        G.map W.unop.hom.op y := by
      rw [← app_comp_eq_of_comp_eq B S hS (yoneda.map r₁) (a₁ := (yoneda.map r₁ ≫ p) ≫ a)
        (a₂ := p ≫ a) (Category.assoc _ _ _).symm, happ₁, hw₁]
      exact x₁.2
    have hs : s.app W ⟨w, hcond⟩ = x₁ := Subtype.ext (by
      simpa only [sectionFiberMap_app_coe, s, happ₁] using hw₁)
    have ht : t.app W ⟨w, hcond⟩ = x₂ := Subtype.ext (by
      simpa only [sectionFiberMap_app_coe, t, happ₂] using hw₂)
    have hcoeq : ((s ≫ coequalizer.π s t).app W) (⟨w, hcond⟩ : _) =
        ((t ≫ coequalizer.π s t).app W) (⟨w, hcond⟩ : _) := by rw [coequalizer.condition]
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hs, ht] using hcoeq
  have hηinj' : Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over X) η :=
    Presheaf.isLocallyInjective_of_injective _ _ hηinj
  -- limit preservation of the coequalizer
  have hP : LimitPreserving.{u, u, u, u, u + 1}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS) (coequalizer s t) :=
    Stacks.Groupoids.limitPreserving_of_isColimit_cofork _ s t (coequalizer.π s t)
      (fun W => NatTrans.congr_app (coequalizer.condition s t) W)
      (fun W => ⟨isColimitOfHasCoequalizerOfPreservesColimit
        ((evaluation ((Over X)ᵒᵖ) (Type u)).obj W) s t⟩)
      (hLPR X y) (hLPU X y)
  exact limitPreserving_sectionFiber_of_isLocallyBijective B S hS a hF.isSheaf hG.isSheaf X y
    η hP

/-- A morphism of algebraic spaces over `S` which is locally of finite presentation is relatively
limit preserving, for index categories in the universe of the schemes. -/
@[stacks 04AK "locally of finite presentation implies relatively limit preserving"]
theorem relativelyLimitPreserving_of_isLocallyOfFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {a : F ⟶ G} (ha : Space.IsLocallyOfFinitePresentation B S hS a) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS a := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := hF.exists_atlas
  obtain ⟨R, r₁, r₂, hpb⟩ := Space.exists_kernelPair_of_etale_atlas B S hS p hpEtale
  have hr₁ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r₁) :=
    hpEtale.property p (yoneda.map r₂) r₁ hpb.flip
  exact limitPreserving_sectionFiber_of_atlas B S hS hF hG r₁ r₂ hpb
    (isLocallySurjective_of_surjective_etale B S hS p hpSurj hpEtale)
    (relativelyLimitPreserving_comp_of_etale_chart B S hS hF hG ha (yoneda.map r₁ ≫ p)
      (Space.etale_comp_of_scheme B S hS r₁ p hr₁ hpEtale))
    (relativelyLimitPreserving_comp_of_etale_chart B S hS hF hG ha p hpEtale)

end AlgebraicGeometry

end
