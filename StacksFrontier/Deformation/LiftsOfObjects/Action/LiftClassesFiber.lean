module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.LiftsOfObjects.IdentityLifts

/-!
# Classes of lifts over the residue field, and classes in a fibre

For a predeformation category `p : F ⥤ 𝒞_Λ` the special fibre over the residue-field object
is equivalent to the one-object one-morphism category. Consequently, for a fixed object `x₀`
of that special fibre and the canonical morphism `r : A ⟶ k` of `𝒞_Λ`, the category of lifts
of `x₀` along `r` has the same isomorphism classes as the whole fibre of `p` over `A`: a lift
of `x₀` is just an object of the fibre over `A` together with the (essentially unique) arrow
to `x₀`.

This file assembles that identification together with the comparison of `ThinSkeleton` of a
fibre with the value of the associated functor of isomorphism classes, which is what turns a
pair of lifts into an element of the associated functor.

## Main definitions

* `Deformation.liftForgetFunctor`: a lift of `x` along `r : A ⟶ B`, read as an object of the
  fibre over `A`.
* `Deformation.fiberClassEquiv`: the thin skeleton of a fibre is the value of the associated
  functor of isomorphism classes there.
* `Deformation.liftSourceClass`: the associated class of the source of a lift.
* `Deformation.liftClassesEquivFiber`: the isomorphism classes of lifts of an object of the
  special fibre are the isomorphism classes of the fibre over the source.
* `Deformation.residuePushforwardLift`: an object of a fibre, read as a lift of its own
  pushforward to the special fibre.

## Main results

* `Deformation.residueFieldMorphism_surjective`: the canonical morphism to the residue-field
  object is surjective.
* `Deformation.homLift_unique_to_specialFiber`: two morphisms into an object of the special
  fibre lying over one morphism of the base agree.
* `Deformation.isHomLift_of_pullback_projections`: a morphism whose two composites with the
  projections of a fibre square lie over the corresponding composites itself lies over the
  base morphism.

## Implementation notes

`liftClassesEquivFiber` is built from the two halves of bijectivity rather than from an
inverse construction: surjectivity needs a pushforward of a fibre object to the special
fibre, and injectivity needs the uniqueness of arrows into the special fibre, and neither is
canonical enough to give a clean inverse map.

`isHomLift_of_pullback_projections` is the converse direction of `IsHomLift.comp` for a fibre
square: `IsHomLift.of_fac` reduces it to an equality of base morphisms out of the pullback,
which `IsPullback.hom_ext` then settles from the two projections.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

namespace Deformation

/-! ### Surjectivity of the canonical morphism to the residue-field object -/

section
open CategoryTheory IsLocalRing
universe u v w

/-- The canonical morphism of `𝒞_Λ` into the residue-field object is surjective: the residue
map is surjective and the remaining identifications are isomorphisms. -/
public theorem residueFieldMorphism_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} :
    Function.Surjective
      (residueFieldMorphism (B := B) : B ⟶ residueFieldObject.{u, v, w} Λ k).hom := by
  intro y
  obtain ⟨a, ha⟩ := residue_surjective
    (B.residueEquiv.symm (ULift.algEquiv (R := Λ) (A := k) y))
  refine ⟨a, ?_⟩
  change ULift.up (B.residueEquiv (residue B a)) = y
  apply ULift.ext
  change B.residueEquiv (residue B a) = y.down
  rw [ha]
  exact B.residueEquiv.apply_symm_apply y.down

end

/-! ### Morphisms into the special fibre -/

section
open CategoryTheory
universe u v w uF vF

/-- In a predeformation category, the special fibre over the residue-field object is thin. -/
public theorem specialFiber_hom_subsingleton
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {x y : p.Fiber (residueFieldObject.{u, v, w} Λ k)} :
    Subsingleton (x ⟶ y) := by
  have h := (CategoryTheory.equiv_punit_iff_unique
    (C := p.Fiber (residueFieldObject.{u, v, w} Λ k))).mp hp.specialFiber
  let : Unique (x ⟶ y) := Classical.choice (h.2 x y)
  exact inferInstance

/-- Two morphisms into an object of the special fibre which lie over one and the same
morphism of the base are equal. -/
public theorem homLift_unique_to_specialFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (r : A ⟶ residueFieldObject.{u, v, w} Λ k)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    {y : F} (a b : y ⟶ x₀.1)
    (ha : p.IsHomLift r a) (hb : p.IsHomLift r b) : a = b := by
  classical
  let := ha
  let := hb
  let : Subsingleton (x₀ ⟶ x₀) := specialFiber_hom_subsingleton p hp
  have hbase : 𝟙 (Opposite.op (p.obj x₀.1)) ≫ p.op.map a.op = p.op.map b.op := by
    change (𝟙 (Opposite.op (p.obj x₀.1))) ≫ Opposite.op (p.map a) =
      Opposite.op (p.map b)
    have hab : p.map a = p.map b := by
      rw [CategoryTheory.IsHomLift.fac' p r a, CategoryTheory.IsHomLift.fac' p r b]
    rw [hab]
    simp
  obtain ⟨j, hj, _⟩ := hp.cofibered.unique_lift a.op b.op
    (𝟙 (Opposite.op (p.obj x₀.1))) hbase
  have hj' : j = 𝟙 (Opposite.op x₀.1) := by
    apply Opposite.unop_injective
    have hmap : p.map j.unop = 𝟙 (p.obj x₀.1) := by
      have h := congrArg Quiver.Hom.unop hj.1
      simpa using h
    have hjLift : p.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) j.unop :=
      CategoryTheory.IsHomLift.of_fac p (𝟙 (residueFieldObject.{u, v, w} Λ k))
        j.unop x₀.2 x₀.2 (by simp [hmap])
    let := hjLift
    let jF : x₀ ⟶ x₀ := CategoryTheory.Functor.Fiber.homMk p
      (residueFieldObject.{u, v, w} Λ k) j.unop
    have hid : jF = 𝟙 x₀ := Subsingleton.elim _ _
    exact congrArg (CategoryTheory.Functor.Fiber.fiberInclusion (p := p)
      (S := residueFieldObject.{u, v, w} Λ k)).map hid
  have h := congrArg Quiver.Hom.unop hj.2
  simpa [hj'] using h

end

/-! ### Lifts and the fibre over the source -/

section
open CategoryTheory
universe u v uF vF

/-- A lift of `x` along `r : A ⟶ B`, read as an object of the fibre of `p` over `A`. -/
@[implicit_reducible]
public def liftForgetFunctor
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {A B : C} (p : F ⥤ C) (r : A ⟶ B) (x₀ : p.Fiber B) :
    Lift p r x₀ ⥤ p.Fiber A where
  obj z := ⟨z.obj, CategoryTheory.IsHomLift.domain_eq p r z.hom⟩
  map {_ _} f := ⟨f.hom, f.isHomLift⟩
  map_id := by intros; apply CategoryTheory.Functor.Fiber.hom_ext; rfl
  map_comp := by intros; apply CategoryTheory.Functor.Fiber.hom_ext; rfl

end

/-! ### Classes in a fibre and the associated functor -/

section
open CategoryTheory
universe u v uF vF

/-- The thin skeleton of a fibre is the value of the associated functor of isomorphism
classes at the same object. -/
public noncomputable def fiberClassEquiv
    {C : Type u} [Category.{v} C] (𝓕 : BasedCategory.{vF, uF} C)
    (hp : IsCofiberedInGroupoids 𝓕.p) (A : C) :
    ThinSkeleton (𝓕.p.Fiber A) ≃ (isomorphismClasses 𝓕 hp).obj A :=
  (Equiv.cast (isomorphismClasses_obj 𝓕 hp A)).symm

/-- The comparison of thin skeleton and associated functor sends the class of an object of
the fibre to its associated class. -/
public lemma fiberClassEquiv_mk
    {C : Type u} [Category.{v} C] (𝓕 : BasedCategory.{vF, uF} C)
    (hp : IsCofiberedInGroupoids 𝓕.p) {A : C} (x : 𝓕.p.Fiber A) :
    fiberClassEquiv 𝓕 hp A (ThinSkeleton.mk x) = classOf 𝓕 hp x :=
  (fiberClassEquiv 𝓕 hp A).eq_symm_apply.1 (classOf_eq 𝓕 hp x).symm

/-- The associated isomorphism class of the source of a lift. -/
public noncomputable def liftSourceClass
    {C : Type u} [Category.{v} C] (𝓕 : BasedCategory.{vF, uF} C)
    (hp : IsCofiberedInGroupoids 𝓕.p)
    {A B : C} (f : A ⟶ B) (x : 𝓕.p.Fiber B) :
    LiftClasses 𝓕.p f x → (isomorphismClasses 𝓕 hp).obj A :=
  fun z => fiberClassEquiv 𝓕 hp A ((ThinSkeleton.map (liftForgetFunctor 𝓕.p f x)).obj z)

/-- On a representative, the associated class of the source of a lift is the associated class
of its source object. -/
public lemma liftSourceClass_mk
    {C : Type u} [Category.{v} C] (𝓕 : BasedCategory.{vF, uF} C)
    (hp : IsCofiberedInGroupoids 𝓕.p)
    {A B : C} (f : A ⟶ B) (x : 𝓕.p.Fiber B) (z : Lift 𝓕.p f x) :
    liftSourceClass 𝓕 hp f x (ThinSkeleton.mk z) =
      classOf 𝓕 hp ((liftForgetFunctor 𝓕.p f x).obj z) :=
  fiberClassEquiv_mk 𝓕 hp _

end

/-! ### Lifts of an object of the special fibre -/

section
open CategoryTheory
universe u v w uF vF

/-- For an object `x₀` of the special fibre of a predeformation category and any morphism
`r : A ⟶ k` of `𝒞_Λ`, the isomorphism classes of lifts of `x₀` along `r` are the isomorphism
classes of the fibre over `A`. -/
public noncomputable def liftClassesEquivFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (r : A ⟶ residueFieldObject.{u, v, w} Λ k)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    LiftClasses p r x₀ ≃ ThinSkeleton (p.Fiber A) := by
  classical
  let Fforget := liftForgetFunctor p r x₀
  let e : LiftClasses p r x₀ → ThinSkeleton (p.Fiber A) :=
    (ThinSkeleton.map Fforget).obj
  have hinj : Function.Injective e := by
    intro q q' h
    refine Quotient.inductionOn₂ q q' ?_ h
    intro a b hab
    change Quotient.mk _ (Fforget.obj a) = Quotient.mk _ (Fforget.obj b) at hab
    obtain ⟨i⟩ := Quotient.exact hab
    let j := i.hom.val
    change a.obj ⟶ b.obj at j
    have hj : p.IsHomLift (𝟙 A) j := i.hom.property
    have hfac : j ≫ b.hom = a.hom := by
      let : p.IsHomLift (𝟙 A) j := hj
      let : p.IsHomLift r b.hom := b.isHomLift
      have hc : p.IsHomLift r (j ≫ b.hom) := by
        have hc' : p.IsHomLift ((𝟙 A) ≫ r) (j ≫ b.hom) :=
          CategoryTheory.IsHomLift.comp (p := p) (f := 𝟙 A) (g := r) (φ := j) (ψ := b.hom)
        simpa using hc'
      exact (homLift_unique_to_specialFiber p hp r x₀ a.hom (j ≫ b.hom)
        a.isHomLift hc).symm
    have hiInv : i.inv.val ≫ i.hom.val = 𝟙 b.obj :=
      congrArg ((CategoryTheory.Functor.Fiber.fiberInclusion (p := p) (S := A)).map)
        i.inv_hom_id
    have hiHom : i.hom.val ≫ i.inv.val = 𝟙 a.obj :=
      congrArg ((CategoryTheory.Functor.Fiber.fiberInclusion (p := p) (S := A)).map)
        i.hom_inv_id
    have hfac' : i.hom.val ≫ b.hom = a.hom := hfac
    have hfacInv : i.inv.val ≫ a.hom = b.hom := by
      rw [← hfac']
      exact (Category.assoc i.inv.val i.hom.val b.hom).symm.trans
        ((congrArg (· ≫ b.hom) hiInv).trans (Category.id_comp b.hom))
    let iso : a ≅ b :=
      { hom := ⟨i.hom.val, i.hom.property, hfac'⟩
        inv := ⟨i.inv.val, i.inv.property, hfacInv⟩
        hom_inv_id := Lift.Hom.ext hiHom
        inv_hom_id := Lift.Hom.ext hiInv }
    exact Quotient.sound ⟨iso⟩
  have hsurj : Function.Surjective e := by
    intro q
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨y₀, φ, hy₀, hφ⟩ := exists_pushforward_codomain hp.cofibered y.2 r
    let y₀' : p.Fiber (residueFieldObject.{u, v, w} Λ k) := ⟨y₀, hy₀⟩
    obtain ⟨E⟩ := hp.specialFiber
    let i : y₀' ≅ x₀ :=
      (E.unitIso.app y₀') ≪≫
        E.inverse.mapIso (eqToIso (Subsingleton.elim _ _)) ≪≫ (E.unitIso.app x₀).symm
    let : p.IsHomLift r φ := hφ
    let : p.IsHomLift
      (𝟙 (residueFieldObject.{u, v, w} Λ k)) i.hom.val := i.hom.property
    let z : Lift p r x₀ := ⟨y.1, φ ≫ i.hom.val, inferInstance⟩
    refine ⟨ThinSkeleton.mk z, ?_⟩
    change Quotient.mk _ (Fforget.obj z) = Quotient.mk _ y
    exact Quotient.sound ⟨Iso.refl y⟩
  exact Equiv.ofBijective e ⟨hinj, hsurj⟩

/-- An object of a fibre of a category cofibered in groupoids, read as a lift of a chosen
pushforward of itself to the special fibre along the canonical morphism to the residue-field
object. -/
public noncomputable def residuePushforwardLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : p.Fiber A) :
    Σ x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k),
      Lift p (residueFieldMorphism (B := A) :
        A ⟶ residueFieldObject.{u, v, w} Λ k) x₀ := by
  classical
  let h := exists_pushforward_codomain hp x.2
    (residueFieldMorphism (B := A) : A ⟶ residueFieldObject.{u, v, w} Λ k)
  let y := Classical.choose h
  let hyφ := Classical.choose_spec h
  let φ := Classical.choose hyφ
  let hspec := Classical.choose_spec hyφ
  exact ⟨⟨y, hspec.1⟩, ⟨x.1, φ, hspec.2⟩⟩

end

/-! ### Recognizing a lift from the projections of a fibre square -/

section
open CategoryTheory CategoryTheory.Limits
universe u v uF vF

/-- A morphism whose composites with the two projection arrows of a fibre square lie over the
corresponding composites in the base lies over the base morphism itself. -/
public lemma isHomLift_of_pullback_projections
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F] (p : F ⥤ C)
    {P A B D R : C} {p₁ : P ⟶ A} {p₂ : P ⟶ B} {f : A ⟶ D} {g : B ⟶ D}
    (hP : IsPullback p₁ p₂ f g)
    {z y a b : F} (r₁ : y ⟶ a) (r₂ : y ⟶ b)
    (hr₁ : p.IsHomLift p₁ r₁) (hr₂ : p.IsHomLift p₂ r₂)
    (t : R ⟶ P) (q : z ⟶ y)
    (hq₁ : p.IsHomLift (t ≫ p₁) (q ≫ r₁))
    (hq₂ : p.IsHomLift (t ≫ p₂) (q ≫ r₂)) :
    p.IsHomLift t q := by
  let := hr₁
  let := hr₂
  let := hq₁
  let := hq₂
  apply CategoryTheory.IsHomLift.of_fac p t q
    (CategoryTheory.IsHomLift.domain_eq p (t ≫ p₁) (q ≫ r₁))
    (CategoryTheory.IsHomLift.domain_eq p p₁ r₁)
  exact hP.hom_ext
    (by simpa [CategoryTheory.IsHomLift.fac' p p₁ r₁] using
      CategoryTheory.IsHomLift.fac p (t ≫ p₁) (q ≫ r₁))
    (by simpa [CategoryTheory.IsHomLift.fac' p p₂ r₂] using
      CategoryTheory.IsHomLift.fac p (t ≫ p₂) (q ≫ r₂))

end

end Deformation
