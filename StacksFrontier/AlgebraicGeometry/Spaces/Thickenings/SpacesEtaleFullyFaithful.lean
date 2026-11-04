module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleHomLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale

/-!
# Base change on the spaces-étale sites of a thickening

Let `f : X ⟶ Y` be the inclusion of a thickening of algebraic spaces over a scheme `S`, that is
a monomorphism whose range is a closed subspace with the same points. Base change
`V ↦ X ×_Y V` is then fully faithful from the spaces-étale site of `Y` to that of `X`.

This is proved for a first-order thickening and, with no order hypothesis, for an arbitrary
thickening.

## Main results

* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isFirstOrderThickening` and
  `AlgebraicGeometry.Space.full_spacesBaseChange_of_isFirstOrderThickening`: base change is
  faithful, and full, at a first-order thickening.
* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening`: base change
  is fully faithful at a first-order thickening (Stacks 05ZH).
* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_mono_of_isThickening`,
  `AlgebraicGeometry.Space.full_spacesBaseChange_of_mono_of_isThickening` and
  `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfMonoOfIsThickening`: base change is
  faithful, full and fully faithful at a thickening of arbitrary order (Stacks 05ZH).

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Matching a cartesian square with an inverse-image subfunctor -/

/-- A base change of a morphism which factors isomorphically through a subfunctor `G` factors
isomorphically through the inverse image of `G`. -/
private theorem exists_iso_preimage_of_isPullback
    {X Y V P : AlgebraicSpaces B S hS} {f : X ⟶ Y} {v : V ⟶ Y} {π : P ⟶ V} {q : P ⟶ X}
    (hpb : IsPullback π q v f) (G : Subfunctor Y.obj)
    (e : X.obj ⟶ G.toFunctor) (he : IsIso e) (hei : e ≫ G.ι = f.hom) :
    ∃ d : P.obj ⟶ (G.preimage v.hom).toFunctor,
      IsIso d ∧ d ≫ (G.preimage v.hom).ι = π.hom := by
  have h1 : IsPullback π.hom q.hom v.hom f.hom := AlgebraicSpaces.isPullback_hom B S hS hpb
  have hiso : IsPullback (inv e) G.ι f.hom (𝟙 Y.obj) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← hei, IsIso.inv_hom_id_assoc]⟩
  have hpaste := (Subfunctor.isPullback_preimage v.hom G).paste_horiz hiso
  rw [Category.comp_id] at hpaste
  exact ⟨(h1.isoIsPullback _ _ hpaste.flip).hom, inferInstance,
    IsPullback.isoIsPullback_hom_fst _ _ h1 hpaste.flip⟩

/-! ### Unique extension of morphisms across the projection of a base change -/

/-- Let `f : X ⟶ Y`
factor isomorphically through a first-order thickening `G ⊂ Y`, let `π : P ⟶ V` be a base
change of `f`, and let `w : W ⟶ Y` be formally étale. Every `Y`-morphism `P ⟶ W` extends
uniquely to a `Y`-morphism `V ⟶ W`. -/
private theorem existsUnique_hom_of_isPullback_of_formallyEtale
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (G : Subfunctor Y.obj)
    (hG : IsFirstOrderThickening B S hS Y G)
    (e : X.obj ⟶ G.toFunctor) (he : IsIso e) (hei : e ≫ G.ι = f.hom)
    {V W P : AlgebraicSpaces B S hS} {v : V ⟶ Y} {π : P ⟶ V} {q : P ⟶ X}
    (hpb : IsPullback π q v f) (w : W ⟶ Y) (hw : FormallyEtale w.hom)
    (d : P.obj ⟶ W.obj) (hd : d ≫ w.hom = π.hom ≫ v.hom) :
    ∃! a : V.obj ⟶ W.obj, π.hom ≫ a = d ∧ a ≫ w.hom = v.hom := by
  obtain ⟨θ, hθiso, hθ⟩ := exists_iso_preimage_of_isPullback B S hS hpb G e he hei
  have hsq : (inv θ ≫ d) ≫ w.hom = (G.preimage v.hom).ι ≫ v.hom := by
    rw [Category.assoc, hd, ← hθ]
    simp
  obtain ⟨a, ⟨ha1, ha2⟩, hauniq⟩ :=
    FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS w hw
      (G.preimage v.hom) (isFirstOrderThickening_preimage B S hS G v hG) (inv θ ≫ d) v.hom hsq
  refine ⟨a, ⟨?_, ha2⟩, fun b ⟨hb1, hb2⟩ ↦ hauniq b ⟨?_, hb2⟩⟩
  · rw [← hθ, Category.assoc, ha1, IsIso.hom_inv_id_assoc]
  · rw [← hb1, ← hθ]
    simp

/-! ### Full faithfulness of base change at a first-order thickening -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- An object of the spaces-étale site of `Y` is formally étale over `Y`. -/
private theorem formallyEtale_hom_of_spacesEtale (V : SpacesEtale B S hS Y) :
    FormallyEtale V.1.hom.hom :=
  ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
    V.1.left.property Y.property V.1.hom.hom).mp V.property).2

/-- The unique-extension property of the projection of a base-change datum `D`: for objects `V'`
and `V` of the spaces-étale site of `Y`, every morphism over `Y` from the base change of `V'` to
`V` extends uniquely across the projection to a morphism `V' ⟶ V` over `Y`. -/
private def UniqueExtensionAlongSpacesBaseChange (D : SpacesBaseChange B S hS f) : Prop :=
  ∀ (V' V : SpacesEtale B S hS Y) (d : (D.functor.obj V').1.left.obj ⟶ V.1.left.obj),
    d ≫ V.1.hom.hom = (D.projection.app V').hom ≫ V'.1.hom.hom →
    ∃! a : V'.1.left.obj ⟶ V.1.left.obj,
      (D.projection.app V').hom ≫ a = d ∧ a ≫ V.1.hom.hom = V'.1.hom.hom

/-- At a first-order thickening, every morphism over `Y` from the base change of an object `V'`
of the spaces-étale site of `Y` to an object `V` extends uniquely across the projection to a
morphism `V' ⟶ V` over `Y`. -/
private theorem existsUnique_hom_of_spacesBaseChange [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    (D : SpacesBaseChange B S hS f) (V' V : SpacesEtale B S hS Y)
    (d : (D.functor.obj V').1.left.obj ⟶ V.1.left.obj)
    (hd : d ≫ V.1.hom.hom = (D.projection.app V').hom ≫ V'.1.hom.hom) :
    ∃! a : V'.1.left.obj ⟶ V.1.left.obj,
      (D.projection.app V').hom ≫ a = d ∧ a ≫ V.1.hom.hom = V'.1.hom.hom :=
  existsUnique_hom_of_isPullback_of_formallyEtale B S hS (Subfunctor.range f.hom) hT
    (Subfunctor.toRange f.hom) inferInstance (Subfunctor.toRange_ι f.hom) (D.isPullback V')
    V.1.hom (formallyEtale_hom_of_spacesEtale B S hS V) d hd

/-- Two morphisms of the spaces-étale site of `Y` with the same base change are equal. -/
private theorem map_injective_spacesBaseChange'
    (D : SpacesBaseChange B S hS f)
    (hext : UniqueExtensionAlongSpacesBaseChange B S hS f D)
    (V' V : SpacesEtale B S hS Y) (a b : V' ⟶ V)
    (hab : D.functor.map a = D.functor.map b) :
    a = b := by
  have key : ∀ c : V' ⟶ V,
      (D.projection.app V').hom ≫ c.hom.left.hom =
        (D.functor.map c).hom.left.hom ≫ (D.projection.app V).hom :=
    fun c ↦ (congrArg (fun k ↦ k.hom) (D.projection.naturality c)).symm
  have hw : ∀ c : V' ⟶ V, c.hom.left.hom ≫ V.1.hom.hom = V'.1.hom.hom :=
    fun c ↦ congrArg (fun k ↦ k.hom) (Over.w c.hom)
  have hd : ((D.projection.app V').hom ≫ a.hom.left.hom) ≫ V.1.hom.hom =
      (D.projection.app V').hom ≫ V'.1.hom.hom := by
    rw [Category.assoc, hw a]
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    ((hext V' V _ hd).unique ⟨rfl, hw a⟩ ⟨by rw [key a, key b, hab], hw b⟩)))

/-- Every morphism of base changes is the base change of a morphism of the spaces-étale site of
`Y`. -/
private theorem exists_map_eq_spacesBaseChange'
    (D : SpacesBaseChange B S hS f)
    (hext : UniqueExtensionAlongSpacesBaseChange B S hS f D)
    (V' V : SpacesEtale B S hS Y)
    (c : D.functor.obj V' ⟶ D.functor.obj V) :
    ∃ a : V' ⟶ V, D.functor.map a = c := by
  have hcX : c.hom.left ≫ (D.functor.obj V).1.hom = (D.functor.obj V').1.hom := Over.w c.hom
  have hAS : (c.hom.left ≫ D.projection.app V) ≫ V.1.hom
      = D.projection.app V' ≫ V'.1.hom := by
    rw [Category.assoc, (D.isPullback V).w, ← Category.assoc, hcX, (D.isPullback V').w]
  obtain ⟨a, ⟨ha1, ha2⟩, -⟩ :=
    hext V' V (c.hom.left ≫ D.projection.app V).hom (congrArg (fun k ↦ k.hom) hAS)
  have hα : (ObjectProperty.homMk a : V'.1.left ⟶ V.1.left) ≫ V.1.hom = V'.1.hom :=
    ObjectProperty.hom_ext _ ha2
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα), ?_⟩
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((D.isPullback V).hom_ext ?_ ?_))
  · exact (D.projection.naturality
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα) : V' ⟶ V)).trans
      (ObjectProperty.hom_ext _ ha1)
  · exact (Over.w (D.functor.map
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα))).hom).trans hcX.symm

/-- Base change along the inclusion
of a first-order thickening is faithful on spaces-étale sites. -/
theorem faithful_spacesBaseChange_of_isFirstOrderThickening [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Faithful where
  map_injective {V' V} {a b} hab :=
    map_injective_spacesBaseChange' B S hS f (spacesBaseChange B S hS f)
      (existsUnique_hom_of_spacesBaseChange B S hS f hT _) V' V a b hab

/-- Base change along the inclusion of a
first-order thickening is full on spaces-étale sites. -/
theorem full_spacesBaseChange_of_isFirstOrderThickening [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Full where
  map_surjective {V' V} c :=
    exists_map_eq_spacesBaseChange' B S hS f (spacesBaseChange B S hS f)
      (existsUnique_hom_of_spacesBaseChange B S hS f hT _) V' V c

/-- Base change `V ↦ X ×_Y V` along the inclusion `f` of a first-order thickening is fully
faithful from the spaces-étale site of `Y` to that of `X`. -/
@[stacks 05ZH "full faithfulness at a first-order thickening"]
noncomputable def fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  letI := full_spacesBaseChange_of_isFirstOrderThickening B S hS f hT
  letI := faithful_spacesBaseChange_of_isFirstOrderThickening B S hS f hT
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### Full faithfulness of base change at an arbitrary thickening -/

/-- The projection of a base-change datum along the inclusion of a thickening of arbitrary order
has the unique-extension property. -/
private theorem existsUnique_hom_of_spacesBaseChange_of_isThickening [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) (D : SpacesBaseChange B S hS f) :
    UniqueExtensionAlongSpacesBaseChange B S hS f D := fun V' V d hd ↦
  existsUnique_hom_presheaf_of_isThickening B S hS f hT V'.1.left.property V.1.left.property
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V')) V.1.hom.hom V.property d hd

/-- Base change along the inclusion
of a thickening — of no prescribed order — is faithful on spaces-étale sites. -/
@[stacks 05ZH "faithfulness at an arbitrary thickening"]
theorem faithful_spacesBaseChange_of_mono_of_isThickening [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Faithful where
  map_injective {V' V} {a b} hab :=
    map_injective_spacesBaseChange' B S hS f (spacesBaseChange B S hS f)
      (existsUnique_hom_of_spacesBaseChange_of_isThickening B S hS f hT _) V' V a b hab

/-- Base change along the inclusion of a
thickening — of no prescribed order — is full on spaces-étale sites. -/
@[stacks 05ZH "fullness at an arbitrary thickening"]
theorem full_spacesBaseChange_of_mono_of_isThickening [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Full where
  map_surjective {V' V} c :=
    exists_map_eq_spacesBaseChange' B S hS f (spacesBaseChange B S hS f)
      (existsUnique_hom_of_spacesBaseChange_of_isThickening B S hS f hT _) V' V c

/-- Base change `V ↦ X ×_Y V` is fully faithful from the spaces-étale site of `Y` to that of `X`,
for `f` a monomorphism whose range is a thickening of `Y` of arbitrary order. -/
@[stacks 05ZH "full faithfulness at an arbitrary thickening"]
noncomputable def fullyFaithfulSpacesBaseChangeOfMonoOfIsThickening [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  letI := full_spacesBaseChange_of_mono_of_isThickening B S hS f hT
  letI := faithful_spacesBaseChange_of_mono_of_isThickening B S hS f hT
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.Space

end
