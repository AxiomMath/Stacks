module

public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness as essential surjectivity of the induced functor to the 2-fibre product

A morphism `φ : 𝓕 ⟶ 𝓖` of categories cofibered in groupoids over `𝒞_Λ` is smooth exactly when,
for every surjection `B → A` of the base, the functor `𝓕(B) ⟶ 𝓕(A) ×_{𝓖(A)} 𝓖(B)` determined
by a choice of pushforwards along it is essentially surjective; the choice may be fixed once and
for all, or quantified over.  By Tag 06HH it suffices to test this on small extensions.

## Main results

* `Deformation.exists_fiberIso_of_isHomLift_id`: a vertical arrow is an isomorphism of its
  fibre, and `Deformation.fiber_hom_ext_of_cocartesian` is the extensionality principle for
  arrows out of the codomain of a strongly cocartesian arrow.
* `Deformation.essSurj_inducedFunctorToPullback_of_isSmooth`: smoothness gives essential
  surjectivity of the induced functor.
* `Deformation.exists_lift_of_inducedFunctorToPullback_essSurj_of_choice`: essential
  surjectivity of the induced functor for one choice of pushforwards over one arrow of the base
  solves every lifting problem over that arrow.
* `Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj_of_choices`: Tag 06HI for a fixed
  choice of pushforwards, tested on surjections.
* `Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj_smallExtension_of_choices`: Tag 06HI
  for a fixed choice of pushforwards, tested on small extensions.
* `Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj` and
  `Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj_smallExtension`: the same
  equivalences with the choices quantified over.

## Implementation notes

The functors between fibres and the 2-cell relating them are the ones *determined* by the
choices of pushforwards, namely `Deformation.pushforwardSquareOfChoices`, whose 2-cell is
characterized by `Deformation.pushforwardComparison_hom_fac`: the image of a chosen cocartesian
arrow composed with the 2-cell is again the chosen cocartesian arrow.  That identity is what
translates between the two formulations, in both directions.

Unwinding essential surjectivity at an object `(a, b, i)` of the categorical pullback gives an
object of `𝓕(B)` together with an isomorphism to `a` after pushforward and an isomorphism of
its image with `b`; unwinding smoothness at the lifting problem attached to `i` gives the same
data.  The isomorphisms of fibres are produced by `Deformation.cocartesianComparison`, since in
a category cofibered in groupoids every arrow is strongly cocartesian over its image.

## References

* [Stacks Project, Tag 06HI](https://stacks.math.columbia.edu/tag/06HI)
* [Stacks Project, Tag 06HH](https://stacks.math.columbia.edu/tag/06HH)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits InfinitesimalLifting
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
variable {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}

/-- A vertical arrow of a category cofibered in groupoids is realized by an isomorphism of the
fibre it lies in. -/
public lemma exists_fiberIso_of_isHomLift_id
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p) {S : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (b c : 𝓖.p.Fiber S) (v : b.1 ⟶ c.1) (hv : 𝓖.p.IsHomLift (𝟙 S) v) :
    ∃ e : b ≅ c, e.hom.1 = v := by
  have hiso : IsIso v := isIso_of_isHomLift_id h𝓖 v hv
  have hinv : 𝓖.p.IsHomLift (𝟙 S) (inv v) := IsHomLift.lift_id_inv_isIso 𝓖.p S v
  refine ⟨⟨⟨v, hv⟩, ⟨inv v, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Functor.Fiber.hom_ext (IsIso.hom_inv_id v)
  · exact Functor.Fiber.hom_ext (IsIso.inv_hom_id v)

/-- Two arrows of a fibre out of the codomain of a strongly cocartesian arrow agree as soon as
their composites with that arrow agree. -/
public lemma fiber_hom_ext_of_cocartesian
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (a : p.Fiber B) (b c : p.Fiber A) (u : a.1 ⟶ b.1)
    (hu : p.IsStronglyCocartesian f u) (s t : b ⟶ c)
    (h : u ≫ s.1 = u ≫ t.1) : s = t := by
  have := s.2
  have := t.2
  exact Functor.Fiber.hom_ext (Functor.IsCocartesian.ext p f u s.1 t.1 h)

/-- **Stacks Project, Tag 06HI.** For a smooth morphism of categories cofibered in groupoids,
the functor to the 2-fibre product determined by any choice of pushforwards along a surjection
of the base is essentially surjective. -/
@[stacks 06HI "smooth_iff_essSurj"]
public lemma essSurj_inducedFunctorToPullback_of_isSmooth
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (hsm : IsSmooth φ)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom)
    (PF : PushforwardChoice 𝓕.p f) (PG : PushforwardChoice 𝓖.p f) :
    (inducedFunctorToPullback
      (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG)).EssSurj := by
  classical
  set S := pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG
  refine ⟨fun z => ?_⟩
  -- the lifting problem attached to the structural isomorphism of `z`
  have hg : 𝓖.p.IsHomLift f (PG.inclusion z.snd ≫ z.iso.inv.1) :=
    homLift_inclusion_comp PG z.snd z.iso.inv
  obtain ⟨x', l, α, hl, hα, hfac⟩ :=
    hsm f hf z.snd.1 z.fst.1 (PG.inclusion z.snd ≫ z.iso.inv.1) hg
  have hx' : 𝓕.p.obj x' = B := IsHomLift.domain_eq 𝓕.p f l
  let xx : 𝓕.p.Fiber B := ⟨x', hx'⟩
  -- the isomorphism of the first components, from the universal property of the pushforward
  have hlc : 𝓕.p.IsStronglyCocartesian f l :=
    isStronglyCocartesian_of_isCofiberedInGroupoids h𝓕 f l hl
  let eₗ : PF.obj xx ≅ z.fst :=
    cocartesianComparison 𝓕.p f xx (PF.obj xx) z.fst (PF.inclusion xx) l
      (PF.cocartesian xx) hlc
  have heₗ : PF.inclusion xx ≫ eₗ.hom.1 = l :=
    cocartesianComparison_hom_fac 𝓕.p f xx (PF.obj xx) z.fst (PF.inclusion xx) l
      (PF.cocartesian xx) hlc
  -- the isomorphism of the second components, from the vertical arrow produced by smoothness
  obtain ⟨eᵣ, heᵣ⟩ := exists_fiberIso_of_isHomLift_id h𝓖
    ((fiberFunctorOver φ.toFunctor φ.w B).obj xx) z.snd α hα
  -- the 2-cell of the determined square is compatible with the chosen arrows
  have hcomm : φ.map (PF.inclusion xx) ≫ (S.comm.app xx).hom.1 =
      PG.inclusion ((fiberFunctorOver φ.toFunctor φ.w B).obj xx) :=
    pushforwardComparison_hom_fac 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG xx
  have hκ : 𝓖.p.IsStronglyCocartesian f (φ.map (PF.inclusion xx)) := by
    have := (PF.cocartesian xx).toIsHomLift
    exact mapped_cocartesian 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w (PF.inclusion xx)
  have hinvhom : z.iso.inv.1 ≫ z.iso.hom.1 = 𝟙 _ :=
    (Functor.Fiber.fiberInclusion.mapIso z.iso).inv_hom_id
  have hmc : φ.map (PF.inclusion xx) ≫ φ.map eₗ.hom.1 =
      α ≫ (PG.inclusion z.snd ≫ z.iso.inv.1) := by
    have h1 : φ.map (PF.inclusion xx) ≫ φ.map eₗ.hom.1 =
        φ.map (PF.inclusion xx ≫ eₗ.hom.1) := (φ.toFunctor.map_comp _ _).symm
    rw [h1, heₗ]
    exact hfac
  have hnat : PG.inclusion ((fiberFunctorOver φ.toFunctor φ.w B).obj xx) ≫
      (S.target.map eᵣ.hom).1 = eᵣ.hom.1 ≫ PG.inclusion z.snd :=
    S.target.inclusion_naturality eᵣ.hom
  have hL : φ.map (PF.inclusion xx) ≫ (φ.map eₗ.hom.1 ≫ z.iso.hom.1) =
      α ≫ PG.inclusion z.snd := by
    erw [← Category.assoc, hmc]
    erw [Category.assoc, Category.assoc, hinvhom, Category.comp_id]
    rfl
  have hR : φ.map (PF.inclusion xx) ≫
        ((S.comm.app xx).hom.1 ≫ (S.target.map eᵣ.hom).1) =
      α ≫ PG.inclusion z.snd := by
    erw [← Category.assoc, hcomm, hnat]
    exact congrArg (· ≫ PG.inclusion z.snd) heᵣ
  refine ⟨xx, ⟨CategoricalPullback.mkIso eₗ eᵣ ?_⟩⟩
  exact fiber_hom_ext_of_cocartesian f ((fiberFunctorOver φ.toFunctor φ.w B).obj xx)
    ((fiberFunctorOver φ.toFunctor φ.w A).obj (PF.obj xx))
    (S.target.toFunctor.obj z.snd) (φ.map (PF.inclusion xx)) hκ _ _ (hL.trans hR.symm)

/-- **Stacks Project, Tag 06HI.** If the functor to the 2-fibre product determined by one
fixed choice `PF`, `PG` of pushforwards along an arrow `f` of the base is essentially
surjective, then every lifting problem over `f` has a compatible solution. -/
@[stacks 06HI "smooth_iff_essSurj: the 'if' direction, fixed choice of pushforwards",
  sga "7 VI 2.6(b)" "The 'if' direction"]
public lemma exists_lift_of_inducedFunctorToPullback_essSurj_of_choice
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (PF : PushforwardChoice 𝓕.p f) (PG : PushforwardChoice 𝓖.p f)
    (hes : (inducedFunctorToPullback
        (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG)).EssSurj)
    (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x) (hg : 𝓖.p.IsHomLift f g) :
    ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
      𝓕.p.IsHomLift f lift ∧ 𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map lift = a ≫ g := by
  classical
  set S := pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG
  have hx : 𝓕.p.obj x = A :=
    (BasedFunctor.w_obj φ x).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)
  have hy : 𝓖.p.obj y = B := IsHomLift.domain_eq 𝓖.p f g
  let a : 𝓕.p.Fiber A := ⟨x, hx⟩
  let b : 𝓖.p.Fiber B := ⟨y, hy⟩
  have hgc : 𝓖.p.IsStronglyCocartesian f g :=
    isStronglyCocartesian_of_isCofiberedInGroupoids h𝓖 f g hg
  let i : (fiberFunctorOver φ.toFunctor φ.w A).obj a ≅ PG.obj b :=
    cocartesianComparison 𝓖.p f b ((fiberFunctorOver φ.toFunctor φ.w A).obj a) (PG.obj b)
      g (PG.inclusion b) hgc (PG.cocartesian b)
  have hi : g ≫ i.hom.1 = PG.inclusion b :=
    cocartesianComparison_hom_fac 𝓖.p f b
      ((fiberFunctorOver φ.toFunctor φ.w A).obj a) (PG.obj b)
      g (PG.inclusion b) hgc (PG.cocartesian b)
  obtain ⟨xx, ⟨e⟩⟩ := hes.mem_essImage ⟨a, b, i⟩
  have hcomm : φ.map (PF.inclusion xx) ≫ (S.comm.app xx).hom.1 =
      PG.inclusion ((fiberFunctorOver φ.toFunctor φ.w B).obj xx) :=
    pushforwardComparison_hom_fac 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG xx
  have hwL : φ.map e.hom.fst.1 ≫ i.hom.1 =
      (S.comm.app xx).hom.1 ≫ (S.target.map e.hom.snd).1 :=
    congrArg (fun t => Functor.Fiber.fiberInclusion.map t) e.hom.w
  have hnat : PG.inclusion ((fiberFunctorOver φ.toFunctor φ.w B).obj xx) ≫
      (S.target.map e.hom.snd).1 = e.hom.snd.1 ≫ PG.inclusion b :=
    S.target.inclusion_naturality e.hom.snd
  refine ⟨xx.1, PF.inclusion xx ≫ e.hom.fst.1, e.hom.snd.1, ?_, e.hom.snd.2, ?_⟩
  · exact homLift_inclusion_comp PF xx e.hom.fst
  · have hLHS : φ.map (PF.inclusion xx ≫ e.hom.fst.1) ≫ i.hom.1 =
        e.hom.snd.1 ≫ PG.inclusion b := by
      erw [Functor.map_comp, Category.assoc, hwL, ← Category.assoc, hcomm, hnat]
    have hRHS : (e.hom.snd.1 ≫ g) ≫ i.hom.1 = e.hom.snd.1 ≫ PG.inclusion b := by
      erw [Category.assoc, hi]
    have : IsIso i.hom.1 := (Functor.Fiber.fiberInclusion.mapIso i).isIso_hom
    exact (cancel_mono i.hom.1).mp (hLHS.trans hRHS.symm)

/-- If the functor to the 2-fibre product determined by every choice of pushforwards along an
arrow `f` of the base is essentially surjective, then every lifting problem over `f` has a
compatible solution.  This is the special case of
`Deformation.exists_lift_of_inducedFunctorToPullback_essSurj_of_choice` for the choices given by
`Deformation.pushforwardChoiceOfIsCofibered`. -/
public lemma exists_lift_of_inducedFunctorToPullback_essSurj
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hes : ∀ (PF : PushforwardChoice 𝓕.p f) (PG : PushforwardChoice 𝓖.p f),
      (inducedFunctorToPullback
        (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG)).EssSurj)
    (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x) (hg : 𝓖.p.IsHomLift f g) :
    ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
      𝓕.p.IsHomLift f lift ∧ 𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map lift = a ≫ g :=
  exists_lift_of_inducedFunctorToPullback_essSurj_of_choice h𝓖 φ f
    (pushforwardChoiceOfIsCofibered h𝓕 f) (pushforwardChoiceOfIsCofibered h𝓖 f) (hes _ _)
    y x g hg

/-- **Stacks Project, Tag 06HI.** Fix, for every arrow `f : B ⟶ A` of the base, choices
`PF f`, `PG f` of pushforwards along `f` in `𝓕` and in `𝓖`.  A morphism `φ` of categories
cofibered in groupoids over `𝒞_Λ` is smooth if and only if, for every surjection `B → A`, the
functor `𝓕(B) ⟶ 𝓕(A) ×_{𝓖(A)} 𝓖(B)` determined by the fixed choices is essentially
surjective. -/
@[stacks 06HI "smooth_iff_essSurj: fixed choice of pushforwards, on surjections"]
public theorem isSmooth_iff_inducedFunctorToPullback_essSurj_of_choices
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (PF : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), PushforwardChoice 𝓕.p f)
    (PG : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), PushforwardChoice 𝓖.p f) :
    IsSmooth φ ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        Function.Surjective f.hom →
          (inducedFunctorToPullback
            (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w (PF f) (PG f))).EssSurj where
  mp hsm _ _ f hf :=
    essSurj_inducedFunctorToPullback_of_isSmooth h𝓕 h𝓖 φ hsm f hf (PF f) (PG f)
  mpr hes _ _ f hf y x g hg :=
    exists_lift_of_inducedFunctorToPullback_essSurj_of_choice h𝓖 φ f (PF f) (PG f)
      (hes f hf) y x g hg

/-- **Stacks Project, Tag 06HI.** Fix, for every arrow `f : B ⟶ A` of the base, choices
`PF f`, `PG f` of pushforwards along `f` in `𝓕` and in `𝓖`.  A morphism `φ` of categories
cofibered in groupoids over `𝒞_Λ` is smooth if and only if, for every small extension
`B → A`, the functor `𝓕(B) ⟶ 𝓕(A) ×_{𝓖(A)} 𝓖(B)` determined by the fixed choices is
essentially surjective.  The reverse direction goes through Tag 06HH. -/
@[stacks 06HI "smooth_iff_essSurj: fixed choice of pushforwards, on small extensions"]
public theorem isSmooth_iff_inducedFunctorToPullback_essSurj_smallExtension_of_choices
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (PF : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), PushforwardChoice 𝓕.p f)
    (PG : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), PushforwardChoice 𝓖.p f) :
    IsSmooth φ ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
          (inducedFunctorToPullback
            (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w (PF f) (PG f))).EssSurj where
  mp hsm _ _ f hf :=
    essSurj_inducedFunctorToPullback_of_isSmooth h𝓕 h𝓖 φ hsm f hf.2.2.2.2.1 (PF f) (PG f)
  mpr hes :=
    isSmooth_of_lifts_smallExtensions h𝓕 h𝓖 φ fun _ _ f hf y x g hg =>
      exists_lift_of_inducedFunctorToPullback_essSurj_of_choice h𝓖 φ f (PF f) (PG f)
        (hes f hf) y x g hg

/-- A morphism of categories cofibered in groupoids over `𝒞_Λ` is smooth if and only if, for
every surjection `B → A` of the base and every choice of pushforwards along it, the functor
`𝓕(B) ⟶ 𝓕(A) ×_{𝓖(A)} 𝓖(B)` determined by those choices is essentially surjective.  Tag 06HI
for a fixed choice is `Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj_of_choices`. -/
public theorem isSmooth_iff_inducedFunctorToPullback_essSurj
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) :
    IsSmooth φ ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        Function.Surjective f.hom →
        ∀ (PF : PushforwardChoice 𝓕.p f) (PG : PushforwardChoice 𝓖.p f),
          (inducedFunctorToPullback
            (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG)).EssSurj where
  mp hsm _ _ f hf PF PG :=
    essSurj_inducedFunctorToPullback_of_isSmooth h𝓕 h𝓖 φ hsm f hf PF PG
  mpr hes _ _ f hf y x g hg :=
    exists_lift_of_inducedFunctorToPullback_essSurj h𝓕 h𝓖 φ f (hes f hf) y x g hg

/-- The same equivalence, tested only on small extensions and on every choice of pushforwards:
by Tag 06HH the lifting property for small extensions already implies smoothness.  Tag 06HI for
a fixed choice is
`Deformation.isSmooth_iff_inducedFunctorToPullback_essSurj_smallExtension_of_choices`. -/
public theorem isSmooth_iff_inducedFunctorToPullback_essSurj_smallExtension
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) :
    IsSmooth φ ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ (PF : PushforwardChoice 𝓕.p f) (PG : PushforwardChoice 𝓖.p f),
          (inducedFunctorToPullback
            (pushforwardSquareOfChoices 𝓕.p 𝓖.p h𝓖 φ.toFunctor φ.w PF PG)).EssSurj where
  mp hsm _ _ f hf PF PG :=
    essSurj_inducedFunctorToPullback_of_isSmooth h𝓕 h𝓖 φ hsm f hf.2.2.2.2.1 PF PG
  mpr hes :=
    isSmooth_of_lifts_smallExtensions h𝓕 h𝓖 φ fun _ _ f hf y x g hg =>
      exists_lift_of_inducedFunctorToPullback_essSurj h𝓕 h𝓖 φ f (hes f hf) y x g hg

end

end Deformation
