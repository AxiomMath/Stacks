module

public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Deformation.Applications.InfinitesimalAutomorphismTransfer
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Functoriality
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.Deformation.Cofibered.Over

/-!
# Smoothness of the base change of a 2-fibre product along a morphism

Let `p₁ : ℋ₁ → 𝒢`, `p₂ : ℋ₂ → 𝒢` and `q : 𝒢 → ℱ` be morphisms of categories cofibered in
groupoids over `𝒞_Λ`. If `ℱ` and `𝒢` are deformation categories, `T𝒢 → Tℱ` is injective and
the infinitesimal automorphisms of `𝒢` surject onto those of `ℱ`, then the canonical functor
`ℋ₁ ×_𝒢 ℋ₂ → ℋ₁ ×_ℱ ℋ₂` is smooth.

## Main definitions

* `mapTwoFibreProductBaseChange`: the canonical functor over `𝒞_Λ` from the `2`-fibre product
  over `𝒢` to the `2`-fibre product over `ℱ`.

## Main results

* `isCofiberedInGroupoids_twoFibreProductBasedCategory`: a `2`-fibre product of categories
  cofibered in groupoids is cofibered in groupoids.
* `surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_inducedInfinitesimal`: if
  `Inf(𝒢) → Inf(ℱ)` is surjective, then `q` is surjective on the infinitesimal automorphisms of
  the source of an arrow of `𝒢` relative to its target, along every surjection whose kernel is
  annihilated by the maximal ideal.
* `isSmooth_mapTwoFibreProductBaseChange`: the canonical functor is smooth when `q` is
  surjective on relative infinitesimal automorphisms.
* `isSmooth_mapTwoFibreProductBaseChange'`: the canonical functor is smooth when
  `Inf(𝒢) → Inf(ℱ)` is surjective.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
* [Stacks Project, Tag 0DYN](https://stacks.math.columbia.edu/tag/0DYN)
-/

@[expose] public section

namespace Deformation

open CategoryTheory IsLocalRing

universe u w u₁ v₁ u₂ v₂ uG vG uF vF

/-! ### Cofiberedness of a 2-fibre product -/

section Cofibered
universe uC vC uX vX uX' vX'

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]

/-- In a category cofibered in groupoids, an arrow lying over a composite factors uniquely
through an arrow lying over the first factor, by an arrow lying over the second. -/
private lemma existsUnique_factor_isHomLift (p : X ⥤ C) (hp : IsCofiberedInGroupoids p)
    {R S T : C} {x y z : X} (u : R ⟶ S) (v : S ⟶ T) (fa : x ⟶ y) (fb : x ⟶ z)
    (hfa : p.IsHomLift u fa) (hfb : p.IsHomLift (u ≫ v) fb) :
    ∃! c : y ⟶ z, p.IsHomLift v c ∧ fa ≫ c = fb := by
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp u fa hfa
  exact Functor.IsStronglyCocartesian.universal_property p u fa v (u ≫ v) rfl fb

/-- In a category cofibered in groupoids an arrow out of the source of a lifting arrow is
cancellable among arrows lying over one arrow of the base. -/
private lemma cofibered_cancel (p : X ⥤ C) (hp : IsCofiberedInGroupoids p)
    {s m t : X} (f : s ⟶ m) (c d : m ⟶ t)
    (hbase : p.map c = p.map d) (hcomm : f ≫ c = f ≫ d) : c = d := by
  obtain ⟨_, _, huniq⟩ :=
    exists_unique_cofibered_factor hp f (f ≫ c) (p.map c) (p.map_comp _ _).symm
  exact (huniq c ⟨rfl, rfl⟩).trans (huniq d ⟨hbase.symm, hcomm.symm⟩).symm

end Cofibered

section TwoFibreProduct

attribute [local implicit_reducible] BasedCategory.ofFunctor twoFibreProductBasedCategory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓗₁ : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓗₂ : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- A `2`-fibre product of categories cofibered in groupoids over `𝒞_Λ` is cofibered in
groupoids: the construction of the `2`-fibre product as categories over `𝒞_Λ` serves as the
`2`-fibre product in the `(2, 1)`-category of categories cofibered in groupoids over `𝒞_Λ`. -/
@[stacks 06GK "(13) the 2-fibre product of categories cofibered in groupoids over 𝒞_Λ is given \
by the construction of their 2-fibre product as categories over 𝒞_Λ"]
public lemma isCofiberedInGroupoids_twoFibreProductBasedCategory
    (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖)
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p) :
    IsCofiberedInGroupoids (twoFibreProductBasedCategory p₁ p₂).p := by
  constructor
  · intro target source baseMap object hobject
    let original := object.unop
    subst source
    obtain ⟨first, firstMap, hfirst⟩ :=
      exists_pushforward h𝓗₁ baseMap.unop original.x original.hx
    obtain ⟨second, secondMap, hsecond⟩ :=
      exists_pushforward h𝓗₂ baseMap.unop original.y original.hy
    have hfx : 𝓗₁.p.obj first = target.unop := IsHomLift.codomain_eq 𝓗₁.p baseMap.unop firstMap
    have hsy : 𝓗₂.p.obj second = target.unop := IsHomLift.codomain_eq 𝓗₂.p baseMap.unop secondMap
    have := original.vertical
    have := p₁.preserves_isHomLift baseMap.unop firstMap
    have := p₂.preserves_isHomLift baseMap.unop secondMap
    have : 𝓖.p.IsHomLift baseMap.unop (original.iso.hom ≫ p₂.map secondMap) :=
      IsHomLift.comp_lift_id_left' 𝓖.p original.base original.iso.hom
        baseMap.unop (p₂.map secondMap)
    have := isStronglyCocartesian_of_isCofiberedInGroupoids h𝓖
      baseMap.unop (p₁.map firstMap) inferInstance
    let comparison := Functor.IsCocartesian.map 𝓖.p baseMap.unop
      (p₁.map firstMap) (original.iso.hom ≫ p₂.map secondMap)
    have hcomparison : 𝓖.p.IsHomLift (𝟙 target.unop) comparison := inferInstance
    have := isIso_of_isHomLift_id h𝓖 comparison hcomparison
    let image : (twoFibreProductBasedCategory p₁ p₂).obj :=
      { base := target.unop, x := first, y := second, hx := hfx, hy := hsy,
        iso := asIso comparison, vertical := hcomparison }
    let lift : original ⟶ image :=
      { hbase := baseMap.unop, a := firstMap, b := secondMap, ha := hfirst, hb := hsecond,
        w := Functor.IsCocartesian.fac 𝓖.p baseMap.unop (p₁.map firstMap)
          (original.iso.hom ≫ p₂.map secondMap) }
    refine ⟨Opposite.op image, lift.op, ?_⟩
    change (twoFibreProductBasedCategory p₁ p₂).p.op.IsHomLift baseMap lift.op
    have hmap : (twoFibreProductBasedCategory p₁ p₂).p.op.map lift.op = baseMap :=
      Quiver.Hom.unop_inj rfl
    exact hmap ▸ IsHomLift.map _ _
  · intro object first second firstMap secondMap baseMap hcomm
    have := firstMap.unop.ha
    have := firstMap.unop.hb
    have hcomm' : firstMap.unop.hbase ≫ baseMap.unop = secondMap.unop.hbase :=
      congrArg Quiver.Hom.unop hcomm
    have hfbFst : 𝓗₁.p.IsHomLift (firstMap.unop.hbase ≫ baseMap.unop) secondMap.unop.a :=
      hcomm' ▸ secondMap.unop.ha
    have hfbSnd : 𝓗₂.p.IsHomLift (firstMap.unop.hbase ≫ baseMap.unop) secondMap.unop.b :=
      hcomm' ▸ secondMap.unop.hb
    obtain ⟨firstComparison, ⟨hfirstLift, hfirstFac⟩, hfirstUnique⟩ :=
      existsUnique_factor_isHomLift 𝓗₁.p h𝓗₁ firstMap.unop.hbase baseMap.unop
        firstMap.unop.a secondMap.unop.a firstMap.unop.ha hfbFst
    obtain ⟨secondComparison, ⟨hsecondLift, hsecondFac⟩, hsecondUnique⟩ :=
      existsUnique_factor_isHomLift 𝓗₂.p h𝓗₂ firstMap.unop.hbase baseMap.unop
        firstMap.unop.b secondMap.unop.b firstMap.unop.hb hfbSnd
    have hw : p₁.map firstComparison ≫ second.unop.iso.hom =
        first.unop.iso.hom ≫ p₂.map secondComparison := by
      apply cofibered_cancel 𝓖.p h𝓖 (p₁.map firstMap.unop.a)
      · have := second.unop.vertical
        have := first.unop.vertical
        have : 𝓖.p.IsHomLift baseMap.unop (p₁.map firstComparison) :=
          isHomLift_basedFunctor_map p₁ baseMap.unop firstComparison hfirstLift
        have : 𝓖.p.IsHomLift baseMap.unop (p₂.map secondComparison) :=
          isHomLift_basedFunctor_map p₂ baseMap.unop secondComparison hsecondLift
        have : 𝓖.p.IsHomLift baseMap.unop (p₁.map firstComparison ≫ second.unop.iso.hom) :=
          IsHomLift.comp_lift_id_right' 𝓖.p baseMap.unop
            (p₁.map firstComparison) second.unop.base second.unop.iso.hom
        have : 𝓖.p.IsHomLift baseMap.unop (first.unop.iso.hom ≫ p₂.map secondComparison) :=
          IsHomLift.comp_lift_id_left' 𝓖.p first.unop.base first.unop.iso.hom
            baseMap.unop (p₂.map secondComparison)
        rw [IsHomLift.fac' 𝓖.p baseMap.unop (p₁.map firstComparison ≫ second.unop.iso.hom),
          IsHomLift.fac' 𝓖.p baseMap.unop (first.unop.iso.hom ≫ p₂.map secondComparison)]
      · calc
          p₁.map firstMap.unop.a ≫ (p₁.map firstComparison ≫ second.unop.iso.hom) =
              p₁.map secondMap.unop.a ≫ second.unop.iso.hom := by
            rw [← Category.assoc, ← p₁.map_comp, hfirstFac]
          _ = object.unop.iso.hom ≫ p₂.map secondMap.unop.b := secondMap.unop.w
          _ = (p₁.map firstMap.unop.a ≫ first.unop.iso.hom) ≫ p₂.map secondComparison := by
            rw [firstMap.unop.w, Category.assoc, ← p₂.map_comp, hsecondFac]
          _ = _ := Category.assoc _ _ _
    let comparison : first.unop ⟶ second.unop :=
      { hbase := baseMap.unop, a := firstComparison, b := secondComparison,
        ha := hfirstLift, hb := hsecondLift, w := hw }
    refine ⟨comparison.op, ⟨rfl, ?_⟩, ?_⟩
    · exact Quiver.Hom.unop_inj (TwoFibreProductOver.Hom.ext' hfirstFac hsecondFac)
    · intro other hother
      have hmap : other.unop.hbase = baseMap.unop := congrArg Quiver.Hom.unop hother.1
      have hfac : firstMap.unop ≫ other.unop = secondMap.unop :=
        congrArg Quiver.Hom.unop hother.2
      exact Quiver.Hom.unop_inj (TwoFibreProductOver.Hom.ext'
        (hfirstUnique _ ⟨hmap ▸ other.unop.ha, congrArg TwoFibreProductOver.Hom.a hfac⟩)
        (hsecondUnique _ ⟨hmap ▸ other.unop.hb, congrArg TwoFibreProductOver.Hom.b hfac⟩))

/-! ### The canonical functor between the two 2-fibre products -/

/-- The canonical functor over `𝒞_Λ` from the `2`-fibre product of `ℋ₁` and `ℋ₂` over `𝒢` to
their `2`-fibre product over `ℱ`, for a morphism `q : 𝒢 → ℱ`: it keeps both components and
applies `q` to the comparison isomorphism. -/
@[stacks 0DYN "the canonical functor between the two 2-fibre products"]
public def mapTwoFibreProductBaseChange
    (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖) (q : BasedFunctor 𝓖 𝓕) :
    BasedFunctor (twoFibreProductBasedCategory p₁ p₂)
      (twoFibreProductBasedCategory (BasedFunctor.comp p₁ q) (BasedFunctor.comp p₂ q)) where
  toFunctor :=
    { obj := fun P ↦
        { base := P.base
          x := P.x
          y := P.y
          hx := P.hx
          hy := P.hy
          iso := q.toFunctor.mapIso P.iso
          vertical := by
            have : 𝓖.p.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
            exact q.preserves_isHomLift (𝟙 P.base) P.iso.hom }
      map := fun f ↦
        { hbase := f.hbase
          a := f.a
          b := f.b
          ha := f.ha
          hb := f.hb
          w := by
            simpa [BasedFunctor.comp, Functor.map_comp] using congrArg q.toFunctor.map f.w }
      map_id _ := TwoFibreProductOver.Hom.ext' rfl rfl
      map_comp _ _ := TwoFibreProductOver.Hom.ext' rfl rfl }
  w := rfl

end TwoFibreProduct

/-! ### Lifting arrows of `𝒢` along a small extension -/

section Lifts

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- A morphism of deformation categories injective on tangent spaces is injective on classes
of lifts along a surjection whose kernel is annihilated by the maximal ideal. -/
private lemma mapLiftClasses_injective (q : BasedFunctor 𝓖 𝓕)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : B, a ∈ maximalIdeal B →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : B) = 0)
    (x : 𝓖.p.Fiber A) :
    Function.Injective (mapLiftClasses q f x) := by
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let hS2G := schlessingerConditionS2_of_isIsomorphismClasses 𝓖 h𝓖.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓖.satisfiesRS) (.inl h𝓖.predeformation)
  let hS2F := schlessingerConditionS2_of_isIsomorphismClasses 𝓕 h𝓕.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS) (.inl h𝓕.predeformation)
  have : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  have : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  have : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨hS2G⟩
  have : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2F⟩
  let := liftAction 𝓖 h𝓖 f hf hann x
  let := liftAction 𝓕 h𝓕 f hf hann ((fiberFunctor q A).obj x)
  let dq := IsLinearMap.mk' _
    (differential_isLinearMap 𝓖 𝓕 h𝓖.predeformation h𝓕.predeformation hS2G hS2F q)
  have hinjective := Module.Flat.rTensor_preserves_injective_linearMap
    (M := RingHom.ker f.hom.toRingHom) dq htangent
  intro first second heq
  obtain ⟨difference, hdifference⟩ :=
    (liftAction_bijective 𝓖 h𝓖 f hf hann x first).2 second
  change difference +ᵥ first = second at hdifference
  have hzero : TensorProduct.map dq LinearMap.id difference = 0 := by
    apply (liftAction_bijective 𝓕 h𝓕 f hf hann ((fiberFunctor q A).obj x)
      (mapLiftClasses q f x first)).1
    dsimp only
    rw [zero_vadd, ← mapLiftClasses_vadd 𝓖 𝓕 h𝓖 h𝓕 q f hf hann x, hdifference]
    exact heq.symm
  rwa [hinjective (hzero.trans (map_zero (LinearMap.rTensor _ dq)).symm), zero_vadd]
    at hdifference

/-- Two lifts of an object of `𝒢` whose images in `ℱ` are isomorphic are isomorphic, when the
differential of the morphism is injective. -/
private lemma exists_iso_of_mapLiftClasses_eq (q : BasedFunctor 𝓖 𝓕)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : B, a ∈ maximalIdeal B →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : B) = 0)
    (x : 𝓖.p.Fiber A) (first second : Lift 𝓖.p f x)
    (himage : Nonempty ((liftFunctor q f x).obj first ≅ (liftFunctor q f x).obj second)) :
    ∃ comparison : first.obj ≅ second.obj,
      𝓖.p.IsHomLift (𝟙 B) comparison.hom ∧ comparison.hom ≫ second.hom = first.hom := by
  have hclasses : ThinSkeleton.mk first = ThinSkeleton.mk second :=
    mapLiftClasses_injective q h𝓖 h𝓕 htangent f hf hann x (Quotient.sound himage)
  obtain ⟨comparison⟩ := Quotient.exact hclasses
  have := isIso_of_isHomLift_id h𝓖.predeformation.cofibered
    comparison.hom.hom comparison.hom.isHomLift
  exact ⟨asIso comparison.hom.hom, comparison.hom.isHomLift, comparison.hom.fac⟩

/-- Injectivity of the differential produces a vertical comparison isomorphism between the
sources of two lifting arrows whose images in `ℱ` are identified. -/
private lemma exists_iso_lift_of_differential_injective (q : BasedFunctor 𝓖 𝓕)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : B, a ∈ maximalIdeal B →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : B) = 0)
    {z₁ z₂ t₁ t₂ : 𝓖.obj} (r₁ : z₁ ⟶ t₁) (r₂ : z₂ ⟶ t₂)
    (b : t₁ ≅ t₂) (a : q.obj z₁ ≅ q.obj z₂)
    (hr₁ : 𝓖.p.IsHomLift f r₁) (hr₂ : 𝓖.p.IsHomLift f r₂)
    (hb : 𝓖.p.IsHomLift (𝟙 A) b.hom) (ha : 𝓕.p.IsHomLift (𝟙 B) a.hom)
    (hw : q.map r₁ ≫ q.map b.hom = a.hom ≫ q.map r₂) :
    ∃ comparison : z₁ ≅ z₂,
      𝓖.p.IsHomLift (𝟙 B) comparison.hom ∧ comparison.hom ≫ r₂ = r₁ ≫ b.hom := by
  let target : 𝓖.p.Fiber A := ⟨t₂, IsHomLift.codomain_eq 𝓖.p f r₂⟩
  let first : Lift 𝓖.p f target :=
    { obj := z₁, hom := r₁ ≫ b.hom, isHomLift := inferInstance }
  let second : Lift 𝓖.p f target := { obj := z₂, hom := r₂, isHomLift := hr₂ }
  let imageIso : (liftFunctor q f target).obj first ≅ (liftFunctor q f target).obj second :=
    { hom :=
        { hom := a.hom
          isHomLift := ha
          fac := ((q.map_comp r₁ b.hom).trans hw).symm }
      inv :=
        { hom := a.inv
          isHomLift := IsHomLift.lift_id_inv 𝓕.p B a
          fac := by
            change a.inv ≫ q.map (r₁ ≫ b.hom) = q.map r₂
            rw [q.map_comp, hw, ← Category.assoc, a.inv_hom_id, Category.id_comp] }
      hom_inv_id := Lift.Hom.ext a.hom_inv_id
      inv_hom_id := Lift.Hom.ext a.inv_hom_id }
  exact exists_iso_of_mapLiftClasses_eq q h𝓖 h𝓕 htangent f hf hann target first second ⟨imageIso⟩

/-- A vertical comparison isomorphism is corrected to have a prescribed image under `q` by a
relative infinitesimal automorphism. -/
private lemma exists_iso_lift_of_mapRelativeInfinitesimalAutomorphisms_surjective
    (q : BasedFunctor 𝓖 𝓕) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A)
    {z₁ t₁ : 𝓖.obj} {z₂ : 𝓖.p.Fiber B} {t₂ : 𝓖.p.Fiber A}
    (r₁ : z₁ ⟶ t₁) (r₂ : z₂.1 ⟶ t₂.1)
    (b : t₁ ≅ t₂.1) (a : q.obj z₁ ≅ q.obj z₂.1)
    (hr₁ : 𝓖.p.IsHomLift f r₁) (hr₂ : 𝓖.p.IsHomLift f r₂)
    (ha : 𝓕.p.IsHomLift (𝟙 B) a.hom)
    (hw : q.map r₁ ≫ q.map b.hom = a.hom ≫ q.map r₂)
    (c : z₁ ≅ z₂.1) (hc : 𝓖.p.IsHomLift (𝟙 B) c.hom) (hcomm : r₁ ≫ b.hom = c.hom ≫ r₂)
    (hsurj : Function.Surjective
      (mapRelativeInfinitesimalAutomorphisms q h𝓖 h𝓕 f r₂ hr₂)) :
    ∃ d : z₁ ≅ z₂.1, 𝓖.p.IsHomLift (𝟙 B) d.hom ∧
      r₁ ≫ b.hom = d.hom ≫ r₂ ∧ q.toFunctor.mapIso d = a := by
  have := hr₁
  have hainv : 𝓕.p.IsHomLift (𝟙 B) a.inv := IsHomLift.lift_id_inv 𝓕.p B a
  have hqcinv : 𝓕.p.IsHomLift (𝟙 B) (q.map c.inv) :=
    isHomLift_basedFunctor_map q (𝟙 B) c.inv (IsHomLift.lift_id_inv 𝓖.p B c)
  have hqchom : 𝓕.p.IsHomLift (𝟙 B) (q.map c.hom) :=
    isHomLift_basedFunctor_map q (𝟙 B) c.hom hc
  let difference : Aut ((fiberFunctor q B).obj z₂) := Aut.of
    { hom := ⟨q.map c.inv ≫ a.hom, IsHomLift.comp_of_lift_id 𝓕.p B (q.map c.inv) a.hom⟩
      inv := ⟨a.inv ≫ q.map c.hom, IsHomLift.comp_of_lift_id 𝓕.p B a.inv (q.map c.hom)⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        change (q.map c.inv ≫ a.hom) ≫ (a.inv ≫ q.map c.hom) = 𝟙 (q.obj z₂.1)
        rw [Category.assoc, ← Category.assoc a.hom, a.hom_inv_id, Category.id_comp,
          ← q.map_comp, c.inv_hom_id, q.map_id]
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        change (a.inv ≫ q.map c.hom) ≫ (q.map c.inv ≫ a.hom) = 𝟙 (q.obj z₂.1)
        rw [Category.assoc, ← Category.assoc (q.map c.hom), ← q.map_comp, c.hom_inv_id,
          q.map_id, Category.id_comp, a.inv_hom_id] }
  have hdifference : difference ∈ relativeInfinitesimalAutomorphisms
      (x' := (fiberFunctor q B).obj z₂) (x := (fiberFunctor q A).obj t₂)
      h𝓕 f (q.map r₂) (isHomLift_basedFunctor_map q f r₂ hr₂) := by
    refine (mem_relativeInfinitesimalAutomorphisms_iff
      (x' := (fiberFunctor q B).obj z₂) (x := (fiberFunctor q A).obj t₂)
      h𝓕 f (q.map r₂) (isHomLift_basedFunctor_map q f r₂ hr₂) difference).mpr ?_
    change (q.map c.inv ≫ a.hom) ≫ q.map r₂ = q.map r₂
    rw [Category.assoc, ← hw, ← q.map_comp, hcomm, q.map_comp, ← Category.assoc,
      ← q.map_comp, c.inv_hom_id, q.map_id, Category.id_comp]
  obtain ⟨correction, hcorrection⟩ := hsurj ⟨difference, hdifference⟩
  have hfix : correction.1.asIso.hom.val ≫ r₂ = r₂ :=
    (mem_relativeInfinitesimalAutomorphisms_iff h𝓖 f r₂ hr₂ correction.1).mp correction.2
  have hmap : q.map correction.1.asIso.hom.val = q.map c.inv ≫ a.hom := by
    have h := mapRelativeInfinitesimalAutomorphisms_hom q h𝓖 h𝓕 f r₂ hr₂ correction
    rw [hcorrection] at h
    exact h.symm
  have hvert : 𝓖.p.IsHomLift (𝟙 B) correction.1.asIso.hom.val :=
    correction.1.asIso.hom.property
  let correctionIso : z₂.1 ≅ z₂.1 := isoOfIsHomLiftId h𝓖 correction.1.asIso.hom.val hvert
  refine ⟨c ≪≫ correctionIso, ?_, ?_, ?_⟩
  · change 𝓖.p.IsHomLift (𝟙 B) (c.hom ≫ correction.1.asIso.hom.val)
    exact IsHomLift.comp_of_lift_id 𝓖.p B c.hom correction.1.asIso.hom.val
  · change r₁ ≫ b.hom = (c.hom ≫ correction.1.asIso.hom.val) ≫ r₂
    rwa [Category.assoc, hfix]
  · apply Iso.ext
    change q.map (c.hom ≫ correction.1.asIso.hom.val) = a.hom
    rw [q.map_comp, hmap, ← Category.assoc, ← q.map_comp, c.hom_inv_id, q.map_id,
      Category.id_comp]

end Lifts

/-! ### Smoothness of the base change -/

section Smooth

attribute [local implicit_reducible] BasedCategory.ofFunctor twoFibreProductBasedCategory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓗₁ : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓗₂ : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- The canonical functor between the two `2`-fibre products is smooth as soon as every
lifting problem in `𝒢` over a small extension that is solved after applying `q` is solved
in `𝒢` compatibly. -/
private lemma isSmooth_mapTwoFibreProductBaseChange_of_lifts
    (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖) (q : BasedFunctor 𝓖 𝓕)
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p) (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (hlift : ∀ {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (z₁ z₂ t₁ t₂ : 𝓖.obj) (r₁ : z₁ ⟶ t₁) (r₂ : z₂ ⟶ t₂)
        (b : t₁ ≅ t₂) (a : q.obj z₁ ≅ q.obj z₂),
        𝓖.p.IsHomLift f r₁ → 𝓖.p.IsHomLift f r₂ → 𝓖.p.IsHomLift (𝟙 A) b.hom →
        𝓕.p.IsHomLift (𝟙 B) a.hom → q.map r₁ ≫ q.map b.hom = a.hom ≫ q.map r₂ →
        ∃ c : z₁ ≅ z₂, 𝓖.p.IsHomLift (𝟙 B) c.hom ∧
          r₁ ≫ b.hom = c.hom ≫ r₂ ∧ q.toFunctor.mapIso c = a) :
    IsSmooth (mapTwoFibreProductBaseChange p₁ p₂ q) := by
  apply isSmooth_of_lifts_smallExtensions
    (isCofiberedInGroupoids_twoFibreProductBasedCategory p₁ p₂ h𝓗₁ h𝓗₂ h𝓖)
    (isCofiberedInGroupoids_twoFibreProductBasedCategory
      (BasedFunctor.comp p₁ q) (BasedFunctor.comp p₂ q) h𝓗₁ h𝓗₂ h𝓕)
  intro B A f hsmall Y X g hg
  cases hg
  have ha : 𝓗₁.p.IsHomLift g.hbase g.a := g.ha
  have hb : 𝓗₂.p.IsHomLift g.hbase g.b := g.hb
  obtain ⟨comparison, hcomparison, hcomm, hmap⟩ :=
    hlift g.hbase hsmall (p₁.obj Y.x) (p₂.obj Y.y) (p₁.obj X.x) (p₂.obj X.y)
      (p₁.map g.a) (p₂.map g.b) X.iso Y.iso (p₁.preserves_isHomLift g.hbase g.a)
      (p₂.preserves_isHomLift g.hbase g.b) X.vertical Y.vertical g.w
  let Z : (twoFibreProductBasedCategory p₁ p₂).obj :=
    { base := Y.base, x := Y.x, y := Y.y, hx := Y.hx, hy := Y.hy,
      iso := comparison, vertical := hcomparison }
  let lift : Z ⟶ X :=
    { hbase := g.hbase, a := g.a, b := g.b, ha := g.ha, hb := g.hb, w := hcomm }
  let adjustment : (mapTwoFibreProductBaseChange p₁ p₂ q).obj Z ⟶ Y :=
    { hbase := 𝟙 Y.base, a := 𝟙 Y.x, b := 𝟙 Y.y,
      ha := IsHomLift.id Y.hx, hb := IsHomLift.id Y.hy,
      w := by
        change q.map (p₁.map (𝟙 Y.x)) ≫ Y.iso.hom =
          q.map comparison.hom ≫ q.map (p₂.map (𝟙 Y.y))
        rw [p₁.map_id, p₂.map_id, q.map_id, q.map_id]
        exact (Category.id_comp _).trans
          ((congrArg Iso.hom hmap.symm).trans (Category.comp_id _).symm) }
  exact ⟨Z, lift, adjustment, IsHomLift.map _ lift, IsHomLift.map _ adjustment,
    TwoFibreProductOver.Hom.ext' (Category.id_comp _).symm (Category.id_comp _).symm⟩

/-- Let `p₁ : ℋ₁ → 𝒢`, `p₂ : ℋ₂ → 𝒢` and `q : 𝒢 → ℱ` be morphisms of categories cofibered in
groupoids over `𝒞_Λ` with `ℱ` and `𝒢` deformation categories, `T𝒢 → Tℱ` injective, and `q`
surjective on the infinitesimal automorphisms along every arrow over a surjection whose kernel is
annihilated by the maximal ideal. Then `ℋ₁ ×_𝒢 ℋ₂ → ℋ₁ ×_ℱ ℋ₂` is smooth. -/
public theorem isSmooth_mapTwoFibreProductBaseChange
    (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖) (q : BasedFunctor 𝓖 𝓕)
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    (hinf : ∀ {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A),
      Function.Surjective f.hom →
      (∀ c : B, c ∈ maximalIdeal B →
        ∀ i : RingHom.ker f.hom.toRingHom, c * (i : B) = 0) →
      ∀ (z : 𝓖.p.Fiber B) (t : 𝓖.p.Fiber A) (r : z.1 ⟶ t.1) (hr : 𝓖.p.IsHomLift f r),
        Function.Surjective (mapRelativeInfinitesimalAutomorphisms q
          h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered f r hr)) :
    IsSmooth (mapTwoFibreProductBaseChange p₁ p₂ q) := by
  apply isSmooth_mapTwoFibreProductBaseChange_of_lifts p₁ p₂ q h𝓗₁ h𝓗₂
    h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered
  intro B A f hsmall z₁ z₂ t₁ t₂ r₁ r₂ b a hr₁ hr₂ hb ha hw
  have hf : Function.Surjective f.hom := hsmall.2.2.2.2.1
  have hann : ∀ c : B, c ∈ maximalIdeal B →
      ∀ i : RingHom.ker f.hom.toRingHom, c * (i : B) = 0 := by
    let kernel := RingHom.ker f.hom.toRingHom
    have : IsSimpleModule B kernel := Module.length_eq_one_iff.mp hsmall.2.2.2.2.2
    have hAnnEq : Module.annihilator B kernel = maximalIdeal B :=
      eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
    intro c hc i
    exact congrArg Subtype.val ((Module.mem_annihilator.mp (hAnnEq.symm ▸ hc)) i)
  obtain ⟨comparison, hcomparison, hcomm⟩ := exists_iso_lift_of_differential_injective q
    h𝓖 h𝓕 htangent f hf hann r₁ r₂ b a hr₁ hr₂ hb ha hw
  exact exists_iso_lift_of_mapRelativeInfinitesimalAutomorphisms_surjective q
    h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered f
    (z₂ := ⟨z₂, IsHomLift.domain_eq 𝓖.p f r₂⟩)
    (t₂ := ⟨t₂, IsHomLift.codomain_eq 𝓖.p f r₂⟩) r₁ r₂ b a hr₁ hr₂ ha hw
    comparison hcomparison hcomm.symm
    (hinf f hf hann ⟨z₂, IsHomLift.domain_eq 𝓖.p f r₂⟩
      ⟨t₂, IsHomLift.codomain_eq 𝓖.p f r₂⟩ r₂ hr₂)

/-! ### Smoothness when `Inf(𝒢) → Inf(ℱ)` is surjective -/

/-- The special fibre of a predeformation category is thin: it is equivalent to the category
with one object and one morphism. -/
private theorem isThin_fiber_residueFieldObject {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k} (hp : IsPredeformationCategory p) :
    Quiver.IsThin (p.Fiber (residueFieldObject.{u, w, w} Λ k)) := by
  obtain ⟨-, hu⟩ := (CategoryTheory.equiv_punit_iff_unique _).mp hp.specialFiber
  intro X Y
  obtain ⟨uu⟩ := hu X Y
  exact uu.instSubsingleton

/-- If `Inf(𝒢) → Inf(ℱ)` is surjective, then for every arrow of `𝒢` over a surjection whose
kernel is annihilated by the maximal ideal, `q` is surjective on the infinitesimal automorphisms
of the source relative to the target. -/
public theorem
    surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_inducedInfinitesimal
    (q : BasedFunctor 𝓖 𝓕) (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    {z₀ : 𝓖.p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (PG : ChosenPushforwardsAt 𝓖.p z₀.1) (PF : ChosenPushforwardsAt 𝓕.p (q.obj z₀.1))
    (hinf :
      letI := naturalLocalizedTangentAddCommGroup PG h𝓖.satisfiesRS
      letI := naturalLocalizedTangentModule PG h𝓖.satisfiesRS
      letI := naturalLocalizedTangentAddCommGroup PF h𝓕.satisfiesRS
      letI := naturalLocalizedTangentModule PF h𝓕.satisfiesRS
      Function.Surjective (inducedInfinitesimalLinearMapOfEq q.toFunctor q.w
        h𝓖.satisfiesRS h𝓕.satisfiesRS PG PF)) :
    ∀ {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A), Function.Surjective f.hom →
      (∀ c : B, c ∈ maximalIdeal B →
        ∀ i : RingHom.ker f.hom.toRingHom, c * (i : B) = 0) →
      ∀ (z : 𝓖.p.Fiber B) (t : 𝓖.p.Fiber A) (r : z.1 ⟶ t.1) (hr : 𝓖.p.IsHomLift f r),
        Function.Surjective (mapRelativeInfinitesimalAutomorphisms q
          h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered f r hr) := by
  have hthinG := isThin_fiber_residueFieldObject h𝓖.predeformation
  have hthinF := isThin_fiber_residueFieldObject h𝓕.predeformation
  have hline := surjective_mapFiberAut_dualNumbersUnder q h𝓖.satisfiesRS h𝓕.satisfiesRS
    hthinF PG PF hinf
  intro B A f hf hann z t r hr
  obtain ⟨X₀, φ₀, hφ₀⟩ := exists_pushforward h𝓖.predeformation.cofibered
    (residueMorphism B) z.1 z.2
  obtain ⟨-, hu⟩ :=
    (CategoryTheory.equiv_punit_iff_unique _).mp h𝓖.predeformation.specialFiber
  obtain ⟨uu⟩ := hu ⟨X₀, IsHomLift.codomain_eq 𝓖.p (residueMorphism B) φ₀⟩ z₀
  exact surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_dualNumbers q
    h𝓖.satisfiesRS h𝓕.satisfiesRS hthinG hthinF f hf hann r hr PG
    (φ₀ ≫ (uu.default : _ ⟶ _).val) hline

/-- Let `p₁ : ℋ₁ → 𝒢`, `p₂ : ℋ₂ → 𝒢` and `q : 𝒢 → ℱ` be morphisms of categories cofibered in
groupoids over `𝒞_Λ`. Assume that `ℱ` and `𝒢` are deformation categories, that `T𝒢 → Tℱ` is
injective, and that `Inf(𝒢) → Inf(ℱ)` is surjective. Then `ℋ₁ ×_𝒢 ℋ₂ → ℋ₁ ×_ℱ ℋ₂` is smooth. -/
@[stacks 0DYN "smoothness"]
public theorem isSmooth_mapTwoFibreProductBaseChange'
    (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖) (q : BasedFunctor 𝓖 𝓕)
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    {z₀ : 𝓖.p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (PG : ChosenPushforwardsAt 𝓖.p z₀.1) (PF : ChosenPushforwardsAt 𝓕.p (q.obj z₀.1))
    (hinf :
      letI := naturalLocalizedTangentAddCommGroup PG h𝓖.satisfiesRS
      letI := naturalLocalizedTangentModule PG h𝓖.satisfiesRS
      letI := naturalLocalizedTangentAddCommGroup PF h𝓕.satisfiesRS
      letI := naturalLocalizedTangentModule PF h𝓕.satisfiesRS
      Function.Surjective (inducedInfinitesimalLinearMapOfEq q.toFunctor q.w
        h𝓖.satisfiesRS h𝓕.satisfiesRS PG PF)) :
    IsSmooth (mapTwoFibreProductBaseChange p₁ p₂ q) :=
  isSmooth_mapTwoFibreProductBaseChange p₁ p₂ q h𝓗₁ h𝓗₂ h𝓖 h𝓕 htangent
    (surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_inducedInfinitesimal q
      h𝓖 h𝓕 PG PF hinf)

/-- Under the hypotheses of `isSmooth_mapTwoFibreProductBaseChange`, every lifting problem for
the canonical functor between the two `2`-fibre products over a surjection of `𝒞_Λ` has a
compatible solution. -/
example (p₁ : BasedFunctor 𝓗₁ 𝓖) (p₂ : BasedFunctor 𝓗₂ 𝓖) (q : BasedFunctor 𝓖 𝓕)
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (h𝓖 : IsDeformationCategory 𝓖.p) (h𝓕 : IsDeformationCategory 𝓕.p)
    (htangent : Function.Injective
      (differential h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered q))
    (hinf : ∀ {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A),
      Function.Surjective f.hom →
      (∀ c : B, c ∈ maximalIdeal B →
        ∀ i : RingHom.ker f.hom.toRingHom, c * (i : B) = 0) →
      ∀ (z : 𝓖.p.Fiber B) (t : 𝓖.p.Fiber A) (r : z.1 ⟶ t.1) (hr : 𝓖.p.IsHomLift f r),
        Function.Surjective (mapRelativeInfinitesimalAutomorphisms q
          h𝓖.predeformation.cofibered h𝓕.predeformation.cofibered f r hr)) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A), Function.Surjective f.hom →
      ∀ (Y : TwoFibreProductOver 𝓗₁.p 𝓗₂.p 𝓕.p (BasedFunctor.comp p₁ q).toFunctor
          (BasedFunctor.comp p₂ q).toFunctor)
        (X : TwoFibreProductOver 𝓗₁.p 𝓗₂.p 𝓖.p p₁.toFunctor p₂.toFunctor)
        (g : Y ⟶ (mapTwoFibreProductBaseChange p₁ p₂ q).obj X),
        (TwoFibreProductOver.structureFunctor 𝓗₁.p 𝓗₂.p 𝓕.p
            (BasedFunctor.comp p₁ q).toFunctor
            (BasedFunctor.comp p₂ q).toFunctor).IsHomLift f g →
        ∃ (X' : TwoFibreProductOver 𝓗₁.p 𝓗₂.p 𝓖.p p₁.toFunctor p₂.toFunctor) (h : X' ⟶ X)
          (a : (mapTwoFibreProductBaseChange p₁ p₂ q).obj X' ⟶ Y),
          (TwoFibreProductOver.structureFunctor 𝓗₁.p 𝓗₂.p 𝓖.p p₁.toFunctor
              p₂.toFunctor).IsHomLift f h ∧
          (TwoFibreProductOver.structureFunctor 𝓗₁.p 𝓗₂.p 𝓕.p
              (BasedFunctor.comp p₁ q).toFunctor
              (BasedFunctor.comp p₂ q).toFunctor).IsHomLift (𝟙 B) a ∧
          (mapTwoFibreProductBaseChange p₁ p₂ q).map h = a ≫ g :=
  isSmooth_mapTwoFibreProductBaseChange p₁ p₂ q h𝓗₁ h𝓗₂ h𝓖 h𝓕 htangent hinf

end Smooth

end Deformation

end
