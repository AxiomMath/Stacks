module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.Deformation.FormalObject.HomEquivalenceMain
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Evaluation of morphisms from a represented functor (Stacks 06SK)

For a complete local algebra `R`, morphisms over the Artinian base from the restriction of
the functor represented by `R` to a category cofibered in groupoids are equivalent to formal
objects over `R`. This file contains the first ingredients of that equivalence: a morphism out
of the represented object in the completed category is, by 2-Yoneda, an object of the
completion over `R`, i.e. a formal object over `R`; and the canonical Artinian quotient points
of `R`, at which the equivalence evaluates a morphism.

## Main definitions

* `Deformation.RepresentableMorphismFormalObjectEquivalence` records the equivalence
  together with its based coherent evaluation at the Artinian quotient points and its
  comparison with Stacks 06HA.

## Implementation notes

The restricted represented functor is `Deformation.restrictedCoyoneda`. Its associated
cofibered set is the category of elements.

## References

* [Stacks Project, Tag 06SK](https://stacks.math.columbia.edu/tag/06SK)
-/

@[expose] public section

open CategoryTheory

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The cofibered set represented by a complete local algebra. -/
public abbrev representedProjection (R : CompleteLocalAlgCat.{u, v, w} Λ k) :=
  CategoryOfElements.π (coyoneda.obj (Opposite.op R))

/-- Evaluation at the identity point, in the strict fibre. -/
public def evaluation {G : Type uF} [Category.{vF} G]
    (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
      (BasedCategory.ofFunctor q) ⥤ q.Fiber R where
  obj φ := ⟨φ.obj ⟨R, 𝟙 R⟩, φ.w_obj _⟩
  map t := ⟨t.toNatTrans.app ⟨R, 𝟙 R⟩, t.isHomLift' ⟨R, 𝟙 R⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restricted represented functor as the strict restriction of its category of
elements. This identifies the two presentations used in Tags 06SK and 06HA. -/
public def restrictedRepresentableInclusion (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R))) where
  obj α := ⟨⟨artinianToComplete.obj α.1, α.2⟩, α.1, rfl⟩
  map g :=
    { obj := ⟨artinianToComplete.map g.val, g.property⟩
      base := g.val
      comm := by
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl }
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

/-- Precomposition with the canonical identification of the restricted represented set. -/
public def restrictRepresentedHom {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor p) ⥤
    BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p) where
  obj φ := (restrictedRepresentableInclusion R).comp φ
  map t := BasedCategory.whiskerLeft (restrictedRepresentableInclusion R) t
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The equivalence between represented morphisms and formal objects, with its coherent
value at each canonical Artinian quotient point specified over the identity of that quotient. -/
public structure RepresentableMorphismFormalObjectEquivalence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Type _ where
  /-- The quotient point of `R` at the `n`-th Artinian truncation. -/
  quotientPoint : (n : ℕ) → (restrictedCoyoneda R).obj (AdicTruncation.obj R n)
  /-- The quotient point at level `n` is the quotient map by the `n`-th truncation ideal. -/
  quotientPoint_hom : ∀ n, (quotientPoint n).hom =
    Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)
  /-- The quotient points are compatible with the truncation transition maps. -/
  projectionPoint : ∀ n,
    (restrictedCoyoneda R).map (AdicTruncation.transition R n)
      (quotientPoint (n + 1)) = quotientPoint n
  /-- The equivalence between represented morphisms and formal objects over `R`. -/
  equivalence : (BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) ≌
      (FormalObject.projection (p := p)).Fiber R
  /-- The value of a represented morphism at the `n`-th quotient point is isomorphic to the
  `n`-th level of the corresponding formal object. -/
  levelIso : ∀ (φ : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) (n : ℕ),
      CategoryTheory.Iso (φ.obj ⟨AdicTruncation.obj R n, quotientPoint n⟩)
        ((equivalence.functor.obj φ).1.level n)
  /-- Evaluation is over the identity of the quotient, not a base automorphism. -/
  levelIso_over : ∀ φ n,
    p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (levelIso φ n).hom
  /-- The level isomorphisms commute with the transition maps. -/
  transition_comm : ∀ (φ : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) (n : ℕ),
      φ.map (CategoryOfElements.homMk
        ⟨AdicTruncation.obj R (n + 1), quotientPoint (n + 1)⟩
        ⟨AdicTruncation.obj R n, quotientPoint n⟩
        (AdicTruncation.transition R n) (projectionPoint n)) ≫
        (levelIso φ n).hom =
        (levelIso φ (n + 1)).hom ≫ (equivalence.functor.obj φ).1.transition n
  /-- The level isomorphisms are natural in the represented morphism. -/
  map_comm : ∀ {φ ψ : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)} (t : φ ⟶ ψ) (n : ℕ),
      t.toNatTrans.app ⟨AdicTruncation.obj R n, quotientPoint n⟩ ≫
        (levelIso ψ n).hom =
        (levelIso φ n).hom ≫ ((equivalence.functor.map t).1).app n
  /-- The equivalence is the composite of `Φ` from Tag 06HA and evaluation at
  the identity (2-Yoneda). Equivalently, applying its inverse `Ψ` before this
  equivalence is naturally isomorphic to evaluation. -/
  completionComparison : ∀ (hp : IsCofiberedInGroupoids p)
    (hq : IsCofiberedInGroupoids (representedProjection R)),
    (completionHomEquivalence p
        (representedProjection R) hp hq).equiv.inverse ⋙
        restrictRepresentedHom p R ⋙ equivalence.functor ≅
      evaluation (FormalObject.projection (p := p)) R

/-- The canonical quotient map `R → R/𝔪_R^(n+1)`, as a point of the restricted represented
functor of `R` at the `n`-th Artinian truncation. -/
public noncomputable def canonicalQuotientPoint
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (restrictedCoyoneda R).obj (AdicTruncation.obj R n) := by
  let I := AdicTruncation.ideal R n
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  have hlocal : IsLocalHom q.toRingHom := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  exact ⟨q, hlocal, AdicTruncation.residueEquiv_residue_mk R n⟩

/-- The underlying algebra map of `canonicalQuotientPoint R n` is the quotient map by the
`n`-th truncation ideal. -/
public theorem canonicalQuotientPoint_hom
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (canonicalQuotientPoint R n).hom =
      Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n) := rfl

/-- The canonical quotient points are compatible with the truncation transition maps. -/
public theorem canonicalQuotientPoint_transition
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (restrictedCoyoneda R).map (AdicTruncation.transition R n)
      (canonicalQuotientPoint R (n + 1)) = canonicalQuotientPoint R n := by
  show canonicalQuotientPoint R (n + 1) ≫
      artinianToComplete.map (AdicTruncation.transition R n) =
        canonicalQuotientPoint R n
  exact CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun _ => rfl)

/-- If `φ` lies over `f` for `p`, then `φ.op` lies over `f.op` for `p.op`. -/
public theorem homLift_op
    {G : Type uF} [Category.{vF} G] {C : Type u} [Category.{v} C]
    (p : G ⥤ C) {R S : C} {X Y : G} {f : R ⟶ S} {φ : X ⟶ Y}
    (h : p.IsHomLift f φ) : p.op.IsHomLift f.op φ.op := by
  let : p.IsHomLift f φ := h
  subst_hom_lift p f φ
  exact IsHomLift.map (p := p.op) φ.op

/-- If `φ.op` lies over `f.op` for `p.op`, then `φ` lies over `f` for `p`. -/
public theorem homLift_unop
    {G : Type uF} [Category.{vF} G] {C : Type u} [Category.{v} C]
    (p : G ⥤ C) {R S : C} {X Y : G} {f : R ⟶ S} {φ : X ⟶ Y}
    (h : p.op.IsHomLift f.op φ.op) : p.IsHomLift f φ := by
  let : p.op.IsHomLift f.op φ.op := h
  subst_hom_lift p.op f.op φ.op
  exact IsHomLift.map (p := p) φ

/-- In a category cofibered in groupoids, every morphism lying over `f` is strongly cocartesian. -/
public theorem cofibered_hom_stronglyCocartesian
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p)
    {A B : C} {X Y : F} (f : A ⟶ B) (φ : X ⟶ Y) [p.IsHomLift f φ] :
    p.IsStronglyCocartesian f φ := by
  apply stronglyCocartesian_of_op p f φ
  let : p.op.IsHomLift f.op φ.op := homLift_op p (inferInstance : p.IsHomLift f φ)
  exact hp.isStronglyCartesian_homLift f.op φ.op

/-- The identity element `𝟙 R` of the functor represented by `R`. -/
public def representedIdentityElement
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (coyoneda.obj (Opposite.op R)).Elements := ⟨R, 𝟙 R⟩

/-- The morphism of elements from the identity element `𝟙 R` to an element `α`, given by `α`
itself. -/
public def representedElementFromIdentity
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (α : (coyoneda.obj (Opposite.op R)).Elements) :
    representedIdentityElement R ⟶ α :=
  CategoryOfElements.homMk (representedIdentityElement R) α α.2 (by
    change (𝟙 R ≫ α.2) = α.2
    simp)

/-- A based functor out of the represented set sends `g` to a morphism over `g.val`. -/
private theorem map_isHomLift_of_elements
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (F : BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
      (BasedCategory.ofFunctor p))
    {α β : (coyoneda.obj (Opposite.op R)).Elements} (g : α ⟶ β) :
    p.IsHomLift g.val (F.map g) := by
  let : (BasedCategory.ofFunctor (representedProjection R)).p.IsHomLift g.val g := by
    rw [← show (representedProjection R).map g = g.val from rfl]
    exact IsHomLift.map (p := representedProjection R) g
  exact F.preserves_isHomLift g.val g

/-- A based functor out of the represented set sends the arrow from the identity element to `α`
to a strongly cocartesian arrow over `α.2`. -/
private theorem map_fromIdentity_isStronglyCocartesian
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (F : BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
      (BasedCategory.ofFunctor p))
    (α : (coyoneda.obj (Opposite.op R)).Elements) :
    p.IsStronglyCocartesian α.2 (F.map (representedElementFromIdentity R α)) := by
  have : p.IsHomLift α.2 (F.map (representedElementFromIdentity R α)) :=
    map_isHomLift_of_elements F (representedElementFromIdentity R α)
  exact cofibered_hom_stronglyCocartesian hp α.2 _

/-- Evaluation at the identity point is faithful when the target is cofibered in groupoids. -/
public theorem evaluation_faithful
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (evaluation (q := p) R).Faithful := by
  refine ⟨fun {φ ψ} t t' h => ?_⟩
  have h0 : t.toNatTrans.app (representedIdentityElement R) =
      t'.toNatTrans.app (representedIdentityElement R) := by
    have hh := congrArg Functor.Fiber.fiberInclusion.map h
    change t.app (representedIdentityElement R) =
      t'.app (representedIdentityElement R) at hh
    exact hh
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext α
  let e := representedElementFromIdentity R α
  have hsc : p.IsStronglyCocartesian α.2 (φ.toFunctor.map e) :=
    map_fromIdentity_isStronglyCocartesian hp φ α
  have ht : p.IsHomLift (𝟙 α.1) (t.toNatTrans.app α) := t.isHomLift' α
  have ht' : p.IsHomLift (𝟙 α.1) (t'.toNatTrans.app α) := t'.isHomLift' α
  let : p.IsStronglyCocartesian α.2 (φ.toFunctor.map e) := hsc
  apply Functor.IsStronglyCocartesian.ext p α.2 (φ.toFunctor.map e) (𝟙 α.1)
  calc
    φ.map e ≫ t.app α = t.app (representedIdentityElement R) ≫ ψ.map e :=
      t.toNatTrans.naturality e
    _ = t'.app (representedIdentityElement R) ≫ ψ.map e := by rw [h0]
    _ = φ.map e ≫ t'.app α := (t'.toNatTrans.naturality e).symm

/-- The factorization of `φ' : a ⟶ c` over `f ≫ g` through a strongly cocartesian arrow
`φ : a ⟶ b` over `f`. -/
public noncomputable def cocartesianFactor
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {R S T : C} {a b c : F}
    (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (hsc : p.IsStronglyCocartesian f φ) (φ' : a ⟶ c)
    (hφ' : p.IsHomLift (f ≫ g) φ') : b ⟶ c := by
  letI : p.IsStronglyCocartesian f φ := hsc
  letI : p.IsHomLift (f ≫ g) φ' := hφ'
  exact Functor.IsStronglyCocartesian.map p f φ (g := g) (f' := f ≫ g) rfl φ'

/-- The factorization `cocartesianFactor p f g φ hsc φ' hφ'` lies over `g`. -/
public theorem cocartesianFactor_lift
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {R S T : C} {a b c : F}
    (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (hsc : p.IsStronglyCocartesian f φ) (φ' : a ⟶ c)
    (hφ' : p.IsHomLift (f ≫ g) φ') :
    p.IsHomLift g (cocartesianFactor p f g φ hsc φ' hφ') := by
  let : p.IsStronglyCocartesian f φ := hsc
  let : p.IsHomLift (f ≫ g) φ' := hφ'
  exact Functor.IsStronglyCocartesian.map_isHomLift p f φ
    (g := g) (f' := f ≫ g) rfl φ'

/-- The factorization `cocartesianFactor p f g φ hsc φ' hφ'` composed after `φ` is `φ'`. -/
public theorem cocartesianFactor_fac
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {R S T : C} {a b c : F}
    (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (hsc : p.IsStronglyCocartesian f φ) (φ' : a ⟶ c)
    (hφ' : p.IsHomLift (f ≫ g) φ') :
    φ ≫ cocartesianFactor p f g φ hsc φ' hφ' = φ' := by
  let : p.IsStronglyCocartesian f φ := hsc
  let : p.IsHomLift (f ≫ g) φ' := hφ'
  exact Functor.IsStronglyCocartesian.fac p f φ rfl φ'

/-- Evaluation at the identity point is full when the target is cofibered in groupoids. -/
public theorem evaluation_full
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (evaluation (q := p) R).Full := by
  refine ⟨fun {φ ψ} t => ?_⟩
  let α₀ := representedIdentityElement R
  let t₀ : φ.obj α₀ ⟶ ψ.obj α₀ := Functor.Fiber.fiberInclusion.map t
  have ht₀ : p.IsHomLift (𝟙 R) t₀ := t.2
  have hlift (α : (coyoneda.obj (Opposite.op R)).Elements) :
      p.IsHomLift (α.2 ≫ 𝟙 α.1) (t₀ ≫ ψ.map (representedElementFromIdentity R α)) := by
    let : p.IsHomLift α.2 (ψ.map (representedElementFromIdentity R α)) :=
      (map_fromIdentity_isStronglyCocartesian hp ψ α).toIsHomLift
    let : p.IsHomLift (𝟙 R) t₀ := ht₀
    simpa only [Category.id_comp, Category.comp_id] using
      IsHomLift.comp (p := p) (f := 𝟙 R) (g := α.2) t₀
        (ψ.map (representedElementFromIdentity R α))
  let app (α : (coyoneda.obj (Opposite.op R)).Elements) : φ.obj α ⟶ ψ.obj α :=
    cocartesianFactor p α.2 (𝟙 α.1) (φ.map (representedElementFromIdentity R α))
      (map_fromIdentity_isStronglyCocartesian hp φ α)
      (t₀ ≫ ψ.map (representedElementFromIdentity R α)) (hlift α)
  have app_lift (α : (coyoneda.obj (Opposite.op R)).Elements) :
      p.IsHomLift (𝟙 α.1) (app α) :=
    cocartesianFactor_lift p α.2 (𝟙 α.1) (φ.map (representedElementFromIdentity R α))
      (map_fromIdentity_isStronglyCocartesian hp φ α)
      (t₀ ≫ ψ.map (representedElementFromIdentity R α)) (hlift α)
  have app_fac (α : (coyoneda.obj (Opposite.op R)).Elements) :
      φ.map (representedElementFromIdentity R α) ≫ app α =
        t₀ ≫ ψ.map (representedElementFromIdentity R α) :=
    cocartesianFactor_fac p α.2 (𝟙 α.1) (φ.map (representedElementFromIdentity R α))
      (map_fromIdentity_isStronglyCocartesian hp φ α)
      (t₀ ≫ ψ.map (representedElementFromIdentity R α)) (hlift α)
  let η : φ.toFunctor ⟶ ψ.toFunctor :=
    { app := app
      naturality := by
        intro α β g
        let eα := representedElementFromIdentity R α
        let eβ := representedElementFromIdentity R β
        have hcomp : eα ≫ g = eβ := CategoryOfElements.ext _ _ _ g.property
        have hsc : p.IsStronglyCocartesian α.2 (φ.map eα) :=
          map_fromIdentity_isStronglyCocartesian hp φ α
        let : p.IsStronglyCocartesian α.2 (φ.map eα) := hsc
        have hleft : p.IsHomLift g.val (φ.map g ≫ app β) := by
          let : p.IsHomLift g.val (φ.map g) := map_isHomLift_of_elements φ g
          let : p.IsHomLift (𝟙 β.1) (app β) := app_lift β
          simpa only [Category.comp_id] using
            IsHomLift.comp (p := p) (f := g.val) (g := 𝟙 β.1) (φ := φ.map g) (ψ := app β)
        have hright : p.IsHomLift g.val (app α ≫ ψ.map g) := by
          let : p.IsHomLift (𝟙 α.1) (app α) := app_lift α
          let : p.IsHomLift g.val (ψ.map g) := map_isHomLift_of_elements ψ g
          simpa only [Category.id_comp] using
            IsHomLift.comp (p := p) (f := 𝟙 α.1) (g := g.val) (φ := app α) (ψ := ψ.map g)
        let : p.IsHomLift g.val (φ.map g ≫ app β) := hleft
        let : p.IsHomLift g.val (app α ≫ ψ.map g) := hright
        have htrans :
            φ.map eα ≫ (φ.map g ≫ app β) =
              φ.map eα ≫ app α ≫ ψ.map g := by
          have hmapcomp (F : BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
              (BasedCategory.ofFunctor p)) : F.map eα ≫ F.map g = F.map eβ :=
            (F.toFunctor.map_comp eα g).symm.trans (congrArg F.toFunctor.map hcomp)
          have hφcomp := hmapcomp φ
          have hψcomp := hmapcomp ψ
          calc
            φ.map eα ≫ (φ.map g ≫ app β) =
                (φ.map eα ≫ φ.map g) ≫ app β := by simp [Category.assoc]
            _ = φ.map eβ ≫ app β := by rw [hφcomp]
            _ = t₀ ≫ ψ.map eβ := app_fac β
            _ = (t₀ ≫ ψ.map eα) ≫ ψ.map g := by
              rw [← hψcomp]
              simp [Category.assoc]
            _ = φ.map eα ≫ app α ≫ ψ.map g := by
              have hfa := congrArg (fun f => f ≫ ψ.map g) (app_fac α)
              simpa [Category.assoc] using hfa.symm
        exact @Functor.IsStronglyCocartesian.ext _ _ _ _ p _ _ _ _
          α.2 (φ.map eα) hsc β.1 (ψ.obj β) g.val
          (φ.map g ≫ app β) (app α ≫ ψ.map g) hleft hright htrans
      }
  let ηb : φ ⟶ ψ :=
    { toNatTrans := η
      isHomLift' := app_lift }
  refine ⟨ηb, ?_⟩
  apply Functor.Fiber.hom_ext
  show ηb.toNatTrans.app α₀ = t₀
  have hfac := app_fac α₀
  have he : representedElementFromIdentity R α₀ = 𝟙 α₀ := by
    apply CategoryOfElements.ext (coyoneda.obj (Opposite.op R))
    rfl
  have hφe : φ.map (representedElementFromIdentity R α₀) = 𝟙 (φ.obj α₀) :=
    (congrArg φ.map he).trans (φ.map_id _)
  have hψe : ψ.map (representedElementFromIdentity R α₀) = 𝟙 (ψ.obj α₀) :=
    (congrArg ψ.map he).trans (ψ.map_id _)
  have hcomp : φ.map (representedElementFromIdentity R α₀) ≫ t₀ =
      t₀ ≫ ψ.map (representedElementFromIdentity R α₀) := by
    rw [hφe, hψe, Category.id_comp, Category.comp_id]
  have hsc := map_fromIdentity_isStronglyCocartesian hp φ α₀
  let : p.IsStronglyCocartesian α₀.2
      (φ.map (representedElementFromIdentity R α₀)) := hsc
  let : p.IsHomLift (𝟙 α₀.1) t₀ := ht₀
  apply Functor.IsStronglyCocartesian.ext p α₀.2
    (φ.map (representedElementFromIdentity R α₀)) (𝟙 α₀.1)
  exact hfac.trans hcomp.symm

/-- In a category cofibered in groupoids over complete local algebras, every morphism `f` out of
the image of an object `X` has a strongly cocartesian lift starting at `X`. -/
public theorem cofibered_exists_strong_lift
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {X : G} {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (hX : p.obj X = R) (f : R ⟶ S) :
    ∃ (Y : G) (g : X ⟶ Y), p.IsStronglyCocartesian f g := by
  let : p.op.IsFiberedInGroupoids := hp
  obtain ⟨Y, g, hg⟩ := hp.exists_lift f.op (Opposite.op X) (congrArg Opposite.op hX)
  let Y' := Opposite.unop Y
  let g' := Quiver.Hom.unop g
  have hLift : p.IsHomLift f g' := homLift_unop p hg
  let : p.IsHomLift f g' := hLift
  refine ⟨Y', g', stronglyCocartesian_of_op p f g' ?_⟩
  exact hp.isStronglyCartesian_homLift f.op g

/-- A strongly cocartesian lift of the element `α : R ⟶ S` starting at the object `x` of the fibre
over `R`: a target object together with a strongly cocartesian arrow over `α` into it. -/
public abbrev RepresentedLift
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (x : p.Fiber R)
    (α : (coyoneda.obj (Opposite.op R)).Elements) :=
  Σ' target : G, Σ' arrow : x.1 ⟶ target, p.IsStronglyCocartesian α.2 arrow

/-- The target object of a represented lift. -/
public abbrev RepresentedLift.target
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {x : p.Fiber R}
    {α : (coyoneda.obj (Opposite.op R)).Elements}
    (lift : RepresentedLift R x α) : G := lift.1

/-- The arrow of a represented lift. -/
public abbrev RepresentedLift.arrow
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {x : p.Fiber R}
    {α : (coyoneda.obj (Opposite.op R)).Elements}
    (lift : RepresentedLift R x α) : x.1 ⟶ lift.target := lift.2.1

/-- The arrow of a represented lift is strongly cocartesian over the element. -/
public abbrev RepresentedLift.strong
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {x : p.Fiber R}
    {α : (coyoneda.obj (Opposite.op R)).Elements}
    (lift : RepresentedLift R x α) : p.IsStronglyCocartesian α.2 lift.arrow := lift.2.2

/-- A chosen strongly cocartesian lift of an element `α` starting at `x`. -/
public noncomputable def chosenRepresentedLift
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (x : p.Fiber R)
    (α : (coyoneda.obj (Opposite.op R)).Elements) :
    RepresentedLift R x α := by
  classical
  choose y f hf using cofibered_exists_strong_lift hp x.2 α.2
  exact ⟨y, f, hf⟩

/-- The functor on elements of the functor represented by `R` sending `α` to the target of the
chosen strongly cocartesian lift of `α` starting at `x`. -/
public noncomputable def representedLiftFunctor
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (x : p.Fiber R) :
    (coyoneda.obj (Opposite.op R)).Elements ⥤ G where
  obj α := (chosenRepresentedLift hp R x α).target
  map {α β} g := by
    letI : p.IsStronglyCocartesian α.2
        (chosenRepresentedLift hp R x α).arrow :=
      (chosenRepresentedLift hp R x α).strong
    letI : p.IsHomLift β.2 (chosenRepresentedLift hp R x β).arrow :=
      (chosenRepresentedLift hp R x β).strong.toIsHomLift
    have hcomp : β.2 = α.2 ≫ g.val := g.property.symm
    exact Functor.IsStronglyCocartesian.map p α.2
      (chosenRepresentedLift hp R x α).arrow hcomp
      (chosenRepresentedLift hp R x β).arrow
  map_id α := by
    let : p.IsStronglyCocartesian α.2
        (chosenRepresentedLift hp R x α).arrow :=
      (chosenRepresentedLift hp R x α).strong
    let : p.IsHomLift α.2 (chosenRepresentedLift hp R x α).arrow :=
      (chosenRepresentedLift hp R x α).strong.toIsHomLift
    simp
  map_comp {α β γ} f g := by
    have hβ := (chosenRepresentedLift hp R x β).strong
    have hγ := (chosenRepresentedLift hp R x γ).strong
    let : p.IsStronglyCocartesian α.2
        (chosenRepresentedLift hp R x α).arrow :=
      (chosenRepresentedLift hp R x α).strong
    let : p.IsStronglyCocartesian β.2
        (chosenRepresentedLift hp R x β).arrow := hβ
    let : p.IsStronglyCocartesian γ.2
        (chosenRepresentedLift hp R x γ).arrow := hγ
    have hf : α.2 ≫ f.val = β.2 := f.property
    have hg : β.2 ≫ g.val = γ.2 := g.property
    simp

/-- The functor `representedLiftFunctor hp R x` as a based functor over complete local algebras. -/
public noncomputable def representedLiftBasedFunctor
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (x : p.Fiber R) :
    BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
      (BasedCategory.ofFunctor p) where
  toFunctor := representedLiftFunctor hp R x
  w := by
    refine CategoryTheory.Functor.ext (fun α => ?_) (fun α β g => ?_)
    · let : p.IsStronglyCocartesian α.2
        (chosenRepresentedLift hp R x α).arrow :=
          (chosenRepresentedLift hp R x α).strong
      have hLift := (chosenRepresentedLift hp R x α).strong.toIsHomLift
      let : p.IsHomLift α.2 (chosenRepresentedLift hp R x α).arrow := hLift
      exact @IsHomLift.codomain_eq _ _ _ _ p _ _ _ _ α.2
        (chosenRepresentedLift hp R x α).arrow hLift
    · let : p.IsStronglyCocartesian α.2
          (chosenRepresentedLift hp R x α).arrow :=
        (chosenRepresentedLift hp R x α).strong
      let : p.IsHomLift β.2 (chosenRepresentedLift hp R x β).arrow :=
        (chosenRepresentedLift hp R x β).strong.toIsHomLift
      have hcomp : β.2 = α.2 ≫ g.val := g.property.symm
      let factor := (representedLiftFunctor hp R x).map g
      let : p.IsHomLift g.val factor := by
        dsimp [factor, representedLiftFunctor]
        exact Functor.IsStronglyCocartesian.map_isHomLift p α.2
          (chosenRepresentedLift hp R x α).arrow hcomp
          (chosenRepresentedLift hp R x β).arrow
      change p.map ((representedLiftFunctor hp R x).map g) = _
      have h := IsHomLift.fac' p g.val factor
      change p.map ((representedLiftFunctor hp R x).map g) =
        eqToHom _ ≫ g.val ≫ eqToHom _
      simpa [representedProjection, representedLiftFunctor, factor] using h

/-- The strict fibre over `R` of a category cofibered in groupoids is a groupoid. -/
public theorem cofibered_fiber_isGroupoid
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) : IsGroupoid (p.Fiber R) where
  all_isIso {x y} f := by
    let : p.IsHomLift (𝟙 R) f.1 := f.2
    let : p.IsStronglyCocartesian (𝟙 R) f.1 :=
      cofibered_hom_stronglyCocartesian hp (𝟙 R) f.1
    let : IsIso (𝟙 R) := inferInstance
    let φ₀ := Functor.Fiber.fiberInclusion.map f
    have hφ₀ : IsIso φ₀ :=
      Functor.IsStronglyCocartesian.isIso_of_base_isIso
        (p := p) (f := 𝟙 R) f.1
    have hinv : p.IsHomLift (𝟙 R) (@CategoryTheory.inv _ _ _ _ φ₀ hφ₀) := by
      simpa using IsHomLift.inv (p := p) (f := 𝟙 R) (φ := φ₀)
    refine ⟨⟨⟨@CategoryTheory.inv _ _ _ _ φ₀ hφ₀, hinv⟩, ?_, ?_⟩⟩
    · apply Functor.Fiber.fiberInclusion.map_injective
      simp only [Functor.map_comp]
      show φ₀ ≫ @CategoryTheory.inv _ _ _ _ φ₀ hφ₀ = _
      simp
    · apply Functor.Fiber.fiberInclusion.map_injective
      simp only [Functor.map_comp]
      show @CategoryTheory.inv _ _ _ _ φ₀ hφ₀ ≫ φ₀ = _
      simp

/-- Evaluation at the identity point is essentially surjective when the target is cofibered in
groupoids. -/
public theorem evaluation_essSurj
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (evaluation (q := p) R).EssSurj := by
  refine ⟨fun x => ?_⟩
  let : IsGroupoid (p.Fiber R) := cofibered_fiber_isGroupoid hp R
  let φ := representedLiftBasedFunctor hp R x
  have hsc : p.IsStronglyCocartesian (𝟙 R)
      ((chosenRepresentedLift hp R x (representedIdentityElement R)).arrow) :=
    (chosenRepresentedLift hp R x (representedIdentityElement R)).strong
  have hbase : p.IsHomLift (𝟙 R)
      ((chosenRepresentedLift hp R x (representedIdentityElement R)).arrow) :=
    hsc.toIsHomLift
  let f : x.1 ⟶ φ.obj (representedIdentityElement R) := by
    dsimp [φ, representedLiftBasedFunctor, representedLiftFunctor]
    exact (chosenRepresentedLift hp R x (representedIdentityElement R)).arrow
  let : p.IsHomLift (𝟙 R) f := by
    simpa [f, φ, representedLiftBasedFunctor, representedLiftFunctor] using hbase
  let : p.IsStronglyCocartesian (𝟙 R) f := by
    simpa [f, φ, representedLiftBasedFunctor, representedLiftFunctor] using hsc
  let : IsIso (𝟙 R) := inferInstance
  have hIso : IsIso f :=
    Functor.IsStronglyCocartesian.isIso_of_base_isIso (p := p) (f := 𝟙 R) f
  let : IsIso f := hIso
  have hFiberIso : IsIso (Functor.Fiber.homMk p R f) :=
    (cofibered_fiber_isGroupoid hp R).all_isIso _
  let : IsIso (Functor.Fiber.homMk p R f) := hFiberIso
  let e : x ≅ (evaluation (q := p) R).obj φ := {
    hom := Functor.Fiber.homMk p R f
    inv := @CategoryTheory.inv _ _ _ _ (Functor.Fiber.homMk p R f) hFiberIso
    hom_inv_id := @IsIso.hom_inv_id _ _ _ _ (Functor.Fiber.homMk p R f) hFiberIso
    inv_hom_id := @IsIso.inv_hom_id _ _ _ _ (Functor.Fiber.homMk p R f) hFiberIso }
  exact ⟨φ, ⟨e.symm⟩⟩

/-- **2-Yoneda.** Evaluation at the identity point is an equivalence between based functors out
of the functor represented by `R` and the strict fibre over `R`. -/
public noncomputable def evaluationEquivalence
    {G : Type uF} [Category.{vF} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
      (BasedCategory.ofFunctor p) ≌ p.Fiber R := by
  let e := evaluation (q := p) R
  letI : e.Full := evaluation_full hp R
  letI : e.Faithful := evaluation_faithful hp R
  letI : e.EssSurj := evaluation_essSurj hp R
  letI : e.IsEquivalence := {}
  exact e.asEquivalence

end Deformation
end
