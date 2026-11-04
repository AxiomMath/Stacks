module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Representable.SolutionSet

/-!
# Divided power rings (Stacks, Divided Power Algebra)

A divided power ring is a commutative ring `A` together with an ideal `I ⊆ A` and a divided
power structure `γ` on `I`.  A morphism of divided power rings is a ring homomorphism carrying
the distinguished ideal into the distinguished ideal and commuting with every divided power
operation; Mathlib's `DividedPowers.DPMorphism` is exactly this notion, so the category
structure below uses it directly instead of introducing a second bundled morphism.

This file sets up the category `DividedPowerRing` and shows that limits exist and are computed
on the underlying commutative rings: the limit of a diagram is the subring of sections of the
underlying diagram of rings, with the ideal of sections landing in each distinguished ideal and
the pointwise divided powers.  It also shows that a set-valued functor on divided power rings
that preserves limits and has a cardinally bounded solution set is corepresentable.

## Main definitions

* `DividedPowerRing` — a commutative ring with an ideal and divided powers on that ideal,
  bundled as the object of a category whose morphisms are `DividedPowers.DPMorphism`.
* `DividedPowerRing.forget` — the forgetful functor to commutative rings.

## Main results

* `DividedPowerRing.hasLimits` — the category of divided power rings has all small limits.
* `DividedPowerRing.forgetPreservesLimits` — those limits agree with limits of rings.
* `DividedPowerRing.isCorepresentable_of_cardinal_solutionSet` — a limit-preserving functor to
  `Type u` with a cardinally bounded solution set is corepresentable.

## References

* [Stacks Project, Tag 07GU](https://stacks.math.columbia.edu/tag/07GU)
* [Stacks Project, Tag 07GV](https://stacks.math.columbia.edu/tag/07GV)
* [Stacks Project, Tag 07GW](https://stacks.math.columbia.edu/tag/07GW)
-/

@[expose] public section

universe u

/-- A divided power ring is a commutative ring equipped with an ideal and a divided power
structure on that ideal. -/
@[stacks_fixed 07GU "divided power rings"]
public structure DividedPowerRing where
  /-- Bundle a commutative ring, an ideal, and its divided power structure. -/
  of ::
  /-- The underlying type of the divided power ring. -/
  carrier : Type u
  /-- The commutative ring structure on the underlying type. -/
  [commRing : CommRing carrier]
  /-- The ideal carrying the divided power structure. -/
  ideal : Ideal carrier
  /-- The divided power structure on the distinguished ideal. -/
  dividedPowers : DividedPowers ideal

attribute [instance] DividedPowerRing.commRing

add_to_stacks 07GU "homomorphisms of divided power rings" DividedPowers.DPMorphism

namespace DividedPowerRing

section CategoryStructure

open CategoryTheory

/-- A divided power ring coerces to its underlying type. -/
public instance : CoeSort DividedPowerRing (Type u) := ⟨carrier⟩

attribute [coe] carrier

/-- Divided power rings and divided power morphisms form a category. -/
public instance : Category.{u} DividedPowerRing where
  Hom A B := DividedPowers.DPMorphism A.dividedPowers B.dividedPowers
  id A := DividedPowers.DPMorphism.id A.dividedPowers; comp f g := g.comp f
  id_comp f := (by ext; rfl); comp_id f := (by ext; rfl); assoc f g h := by ext; rfl

/-- The concrete category structure remembers the underlying function of a divided power
morphism. -/
public instance : ConcreteCategory DividedPowerRing
    (fun A B ↦ DividedPowers.DPMorphism A.dividedPowers B.dividedPowers) where
  hom f := f; ofHom f := f

/-- The forgetful functor from divided power rings to commutative rings. -/
@[implicit_reducible]
public def forget : DividedPowerRing ⥤ CommRingCat where
  obj A := CommRingCat.of A; map f := CommRingCat.ofHom f.toRingHom
  map_id _ := rfl; map_comp _ _ := rfl

end CategoryStructure

section SmallLimits

open CategoryTheory Limits

/-- The commutative ring structure on the value at `j` of the underlying diagram of types. -/
public instance sectionsObjCommRing {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (j : J) :
    CommRing ((F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).obj j) :=
  inferInstanceAs (CommRing (F.obj j))

/-- The sections of the underlying diagram of commutative rings form a commutative ring. -/
public instance sectionsCommRing {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) :
    CommRing (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections :=
  let R := F ⋙ DividedPowerRing.forget
  @Subring.toCommRing (∀ j, R.obj j) _
    (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat))

/-- Evaluation at an object `j` of a section of the underlying diagram of commutative rings. -/
public def sectionsEval {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (j : J) :
    (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections →+* F.obj j where
  toFun x := x.1 j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ideal of those sections whose value at every object lies in the distinguished ideal. -/
public def sectionsIdeal {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) :
    Ideal (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections where
  carrier := {x | ∀ j, x.1 j ∈ (F.obj j).ideal}
  zero_mem' := by
    intro j
    exact (F.obj j).ideal.zero_mem
  add_mem' := by
    intro x y hx hy j
    exact (F.obj j).ideal.add_mem (hx j) (hy j)
  smul_mem' := by
    intro a x hx j
    exact (F.obj j).ideal.mul_mem_left _ (hx j)

/-- The pointwise divided power operation on sections, extended by zero outside
`sectionsIdeal`. -/
public noncomputable def sectionsDpow {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (n : ℕ)
    (x : (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections) :
    (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections := by
  classical
  by_cases hx : x ∈ sectionsIdeal F
  · refine ⟨fun j => (F.obj j).dividedPowers.dpow n (x.1 j), ?_⟩
    intro a b f
    have h := (F.map f).dpow_comp (n := n) (x.1 a) (hx a)
    change (F.map f) ((F.obj a).dividedPowers.dpow n (x.1 a)) =
      (F.obj b).dividedPowers.dpow n (x.1 b)
    rw [← show (F.map f) (x.1 a) = x.1 b from x.property f]
    exact h.symm
  · exact 0

/-- On a section lying in `sectionsIdeal`, `sectionsDpow` is computed objectwise. -/
public lemma sectionsDpow_apply {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (n : ℕ)
    (x : (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections)
    (hx : x ∈ sectionsIdeal F) (j : J) :
    (sectionsDpow F n x).1 j = (F.obj j).dividedPowers.dpow n (x.1 j) := by
  simp [sectionsDpow, hx]

/-- The divided power structure on `sectionsIdeal F`, computed objectwise. -/
public noncomputable def sectionsDividedPowers {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) : DividedPowers (sectionsIdeal F) where
  dpow := sectionsDpow F
  dpow_null := by
    intro n x hx
    simp [sectionsDpow, hx]
  dpow_zero := by
    intro x hx
    apply Subtype.ext
    funext j
    rw [sectionsDpow_apply F 0 x hx j]
    exact (F.obj j).dividedPowers.dpow_zero (hx j)
  dpow_one := by
    intro x hx
    apply Subtype.ext
    funext j
    rw [sectionsDpow_apply F 1 x hx j]
    exact (F.obj j).dividedPowers.dpow_one (hx j)
  dpow_mem := by
    intro n x hn hx j
    rw [sectionsDpow_apply F n x hx j]
    exact (F.obj j).dividedPowers.dpow_mem hn (hx j)
  dpow_add := by
    intro n x y hx hy
    apply Subtype.ext
    funext j
    rw [sectionsDpow_apply F n (x + y) ((sectionsIdeal F).add_mem hx hy) j]
    change (F.obj j).dividedPowers.dpow n (x.1 j + y.1 j) = _
    rw [(F.obj j).dividedPowers.dpow_add (hx j) (hy j)]
    change _ = (sectionsEval F j)
      (∑ k ∈ Finset.antidiagonal n, sectionsDpow F k.1 x * sectionsDpow F k.2 y)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul]
    exact congrArg₂ (· * ·) (sectionsDpow_apply F k.1 x hx j).symm
      (sectionsDpow_apply F k.2 y hy j).symm
  dpow_mul := by
    intro n a x hx
    apply Subtype.ext
    funext j
    rw [sectionsDpow_apply F n (a * x) ((sectionsIdeal F).mul_mem_left a hx) j]
    change (F.obj j).dividedPowers.dpow n (a.1 j * x.1 j) = _
    rw [(F.obj j).dividedPowers.dpow_mul (hx j)]
    change ((sectionsEval F j) a) ^ n * (F.obj j).dividedPowers.dpow n (x.1 j) =
      (sectionsEval F j) (a ^ n * sectionsDpow F n x)
    rw [map_mul, map_pow]
    change _ = _ * (sectionsDpow F n x).1 j
    rw [sectionsDpow_apply F n x hx j]
  mul_dpow := by
    intro m n x hx
    apply Subtype.ext
    funext j
    change (sectionsDpow F m x).1 j * (sectionsDpow F n x).1 j =
      (↑(Nat.choose (m + n) m) * sectionsDpow F (m + n) x).1 j
    rw [sectionsDpow_apply F m x hx j, sectionsDpow_apply F n x hx j]
    change _ = (sectionsEval F j) ((Nat.choose (m + n) m : _) * sectionsDpow F (m + n) x)
    rw [map_mul, map_natCast]
    have h := sectionsDpow_apply F (m + n) x hx j
    change _ = (Nat.choose (m + n) m : F.obj j) * (sectionsEval F j) (sectionsDpow F (m + n) x)
    rw [show (sectionsEval F j) (sectionsDpow F (m + n) x) = _ from h]
    exact (F.obj j).dividedPowers.mul_dpow (hx j)
  dpow_comp := by
    intro m n x hn hx
    have hnx : sectionsDpow F n x ∈ sectionsIdeal F := by
      intro j
      rw [sectionsDpow_apply F n x hx j]
      exact (F.obj j).dividedPowers.dpow_mem hn (hx j)
    apply Subtype.ext
    funext j
    change (sectionsDpow F m (sectionsDpow F n x)).1 j =
      (↑(Nat.uniformBell m n) * sectionsDpow F (m * n) x).1 j
    rw [sectionsDpow_apply F m (sectionsDpow F n x) hnx j,
      sectionsDpow_apply F n x hx j]
    change _ = (sectionsEval F j) ((Nat.uniformBell m n : _) * sectionsDpow F (m * n) x)
    rw [map_mul, map_natCast]
    have h := sectionsDpow_apply F (m * n) x hx j
    change _ = (Nat.uniformBell m n : F.obj j) * (sectionsEval F j) (sectionsDpow F (m * n) x)
    rw [show (sectionsEval F j) (sectionsDpow F (m * n) x) = _ from h]
    exact (F.obj j).dividedPowers.dpow_comp hn (hx j)

/-- The limit of a diagram of divided power rings: the sections of the underlying diagram of
commutative rings, with the ideal and the divided powers of sections. -/
public noncomputable def limitObject {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) : DividedPowerRing.{u} :=
  { carrier := (F ⋙ DividedPowerRing.forget ⋙ CategoryTheory.forget CommRingCat).sections
    commRing := sectionsCommRing F
    ideal := sectionsIdeal F
    dividedPowers := sectionsDividedPowers F }

/-- The projection from `limitObject F` to the value of `F` at an object `j`. -/
public noncomputable def limitProjection {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (j : J) : limitObject F ⟶ F.obj j := by
  let f : (limitObject F) →+* F.obj j := sectionsEval F j
  refine DividedPowers.DPMorphism.mk' (f := f) ⟨?_, ?_⟩
  · exact Ideal.map_le_iff_le_comap.mpr fun x hx ↦ hx j
  · intro n a ha
    exact (sectionsDpow_apply F n a ha j).symm

/-- The cone on `F` with vertex `limitObject F`, whose legs are the projections. -/
public noncomputable def limitCone {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) : Cone F where
  pt := limitObject F
  π :=
    { app := limitProjection F
      naturality := by
        intro a b f
        ext x
        exact (x.property f).symm }

/-- The ring homomorphism from the vertex of a cone on `F` to `limitObject F`. -/
public noncomputable def limitLiftRingHom {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (c : Cone F) :
    c.pt →+* limitObject F where
  toFun x :=
    ⟨fun j => c.π.app j x, by
      intro a b f
      exact congrArg (fun (g : c.pt ⟶ F.obj b) => g x) (c.w f)⟩
  map_one' := Subtype.ext (funext fun j => (c.π.app j).toRingHom.map_one)
  map_mul' x y := Subtype.ext (funext fun j => (c.π.app j).toRingHom.map_mul x y)
  map_zero' := Subtype.ext (funext fun j => (c.π.app j).toRingHom.map_zero)
  map_add' x y := Subtype.ext (funext fun j => (c.π.app j).toRingHom.map_add x y)

/-- The morphism of divided power rings from the vertex of a cone on `F` to `limitObject F`. -/
public noncomputable def limitLift {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) (c : Cone F) : c.pt ⟶ limitObject F := by
  let f := limitLiftRingHom F c
  refine DividedPowers.DPMorphism.mk' (f := f) ⟨?_, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx j
    exact (c.π.app j).ideal_comp (Ideal.mem_map_of_mem _ hx)
  · intro n a ha
    apply Subtype.ext
    funext j
    change (sectionsDpow F n (f a)).1 j = (f (c.pt.dividedPowers.dpow n a)).1 j
    rw [sectionsDpow_apply F n (f a)
      (fun k ↦ (c.π.app k).ideal_comp (Ideal.mem_map_of_mem _ ha)) j]
    exact (c.π.app j).dpow_comp a ha

/-- `limitCone F` is a limit cone. -/
public noncomputable def limitConeIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) : IsLimit (limitCone F) where
  lift c := limitLift F c
  fac c j := by
    ext x
    rfl
  uniq c m hm := by
    ext x
    apply Subtype.ext
    funext j
    exact congrArg (fun (g : c.pt ⟶ F.obj j) => g x) (hm j)

private noncomputable def ringLimitLift {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u})
    (c : Cone (F ⋙ DividedPowerRing.forget)) :
    c.pt ⟶ (DividedPowerRing.forget.mapCone (limitCone F)).pt := by
  apply CommRingCat.ofHom
  refine
    { toFun := fun x =>
        ⟨fun j => c.π.app j x, by
          intro a b f
          exact congrArg (fun (g : c.pt ⟶ (F ⋙ DividedPowerRing.forget).obj b) =>
            g x) (c.w f)⟩
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
  · exact Subtype.ext (funext fun j => (c.π.app j).hom.map_one)
  · intro x y; exact Subtype.ext (funext fun j => (c.π.app j).hom.map_mul x y)
  · exact Subtype.ext (funext fun j => (c.π.app j).hom.map_zero)
  · intro x y; exact Subtype.ext (funext fun j => (c.π.app j).hom.map_add x y)

private noncomputable def ringConeIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ DividedPowerRing.{u}) :
    IsLimit (DividedPowerRing.forget.mapCone (limitCone F)) where
  lift c := ringLimitLift F c
  fac c j := by
    ext x
    rfl
  uniq c m hm := by
    ext x
    apply Subtype.ext
    funext j
    exact congrArg (fun (g : c.pt ⟶ (F ⋙ DividedPowerRing.forget).obj j) =>
      g x) (hm j)

/-- The category of divided power rings has all small limits. -/
@[stacks 07GV "existence of limits"]
public instance hasLimits : HasLimits DividedPowerRing.{u} where
  has_limits_of_shape _ _ :=
    { has_limit := fun F => ⟨limitCone F, limitConeIsLimit F⟩ }

/-- Limits of divided power rings are computed on their underlying commutative rings. -/
@[stacks 07GV "agreement with limits of rings"]
public noncomputable instance forgetPreservesLimits :
    PreservesLimits DividedPowerRing.forget.{u} where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F) (ringConeIsLimit F) }

end SmallLimits

section Representability

open CategoryTheory CategoryTheory.Limits

private structure BoundedModel (α : Type u) where
  support : Set α
  [ring : CommRing support]
  ideal : Ideal support
  dividedPowers : DividedPowers ideal

private def BoundedModel.toObj {α : Type u} (i : BoundedModel α) :
    DividedPowerRing.{u} :=
  { carrier := i.support, commRing := i.ring, ideal := i.ideal,
    dividedPowers := i.dividedPowers }

private lemma exists_bounded_model (α : Type u)
    (A : DividedPowerRing.{u}) (h : Cardinal.mk A ≤ Cardinal.mk α) :
    ∃ i : BoundedModel α, ∃ t : A ⟶ i.toObj,
      ∃ t' : i.toObj ⟶ A, t ≫ t' = 𝟙 A := by
  classical
  obtain ⟨e⟩ := (Cardinal.le_def A α).mp h
  let s : Set α := Set.range e
  let q : A ≃ s := Equiv.ofBijective
    (fun a : A => (⟨e a, Set.mem_range_self a⟩ : s))
    ⟨fun a b hab => e.injective (congrArg Subtype.val hab),
      fun b => by obtain ⟨a, ha⟩ := b.property; exact ⟨a, Subtype.ext ha⟩⟩
  let : CommRing s := q.symm.commRing
  let r : A ≃+* s := (q.symm.ringEquiv).symm
  let J : Ideal s := A.ideal.map r
  let δ : DividedPowers J := DividedPowers.ofRingEquiv (e := r) rfl A.dividedPowers
  let i : BoundedModel α :=
    { support := s, ring := inferInstance, ideal := J, dividedPowers := δ }
  refine ⟨i, ?_, ?_, ?_⟩
  · apply DividedPowers.DPMorphism.mk' (f := r.toRingHom)
    show DividedPowers.IsDPMorphism A.dividedPowers δ r.toRingHom
    refine ⟨le_rfl, ?_⟩
    intro n a ha
    show δ.dpow n (r a) = r (A.dividedPowers.dpow n a)
    simp [δ]
  · apply DividedPowers.DPMorphism.mk' (f := r.symm.toRingHom)
    show DividedPowers.IsDPMorphism δ A.dividedPowers r.symm.toRingHom
    refine ⟨le_of_eq (Ideal.map_of_equiv r), ?_⟩
    intro n a ha
    show A.dividedPowers.dpow n (r.symm a) = r.symm (δ.dpow n a)
    simp [δ, DividedPowers.ofRingEquiv]
  · ext a; exact r.symm_apply_apply a

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`, which
-- makes the arrow notation below ambiguous; elaborate this declaration without it.
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A limit-preserving functor on divided power rings is corepresentable when every one of its
elements is obtained from an element over a divided power ring whose underlying type has
uniformly bounded cardinality. -/
@[stacks 07GW]
public theorem isCorepresentable_of_cardinal_solutionSet
    (F : DividedPowerRing.{u} ⥤ Type u)
    [PreservesLimitsOfSize.{u, u} F]
    (hF : ∃ κ : Cardinal.{u}, ∀ (A : DividedPowerRing.{u}) (f : F.obj A),
      ∃ (A' : DividedPowerRing.{u}) (f' : F.obj A') (g : A' ⟶ A),
        F.map g f' = f ∧ Cardinal.mk A' ≤ κ) :
    F.IsCorepresentable := by
  classical
  obtain ⟨κ, hκ⟩ := hF
  let α : Type u := κ.out
  apply CategoryTheory.isCorepresentable_of_solutionSet F
    (fun i : Σ i : BoundedModel α, F.obj i.toObj => i.1.toObj) (fun i => i.2)
  intro A a
  obtain ⟨A', a', g, hg, hs⟩ := hκ A a
  obtain ⟨i, t, t', htt'⟩ := exists_bounded_model α A' (by simpa [α] using hs)
  refine ⟨⟨i, F.map t a'⟩, t' ≫ g, ?_⟩
  calc
    F.map (t' ≫ g) (F.map t a') = F.map g (F.map (t ≫ t') a') := by simp
    _ = F.map g a' := by simp [htt']
    _ = a := hg

end Representability

end DividedPowerRing
