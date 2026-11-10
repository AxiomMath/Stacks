module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Category.ULift
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood

/-!
# The henselian local ring of a decent algebraic space at a point

The henselian local ring of a decent algebraic space at a point is the colimit of the rings
of global sections of its elementary étale neighborhoods. Morphisms of neighborhoods point
from a refinement to a coarser neighborhood, so the diagram of section rings is indexed by
the opposite of the category of elementary étale neighborhoods.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodScheme`: the underlying scheme of an elementary étale
  neighborhood, functorially.
* `AlgebraicGeometry.Space.globalSections`: the contravariant diagram of global-section rings.
* `AlgebraicGeometry.Space.liftedGlobalSections`: the diagram of global-section rings, lifted to
  the universe of the index category.
* `AlgebraicGeometry.Space.henselianLocalRing`: the colimit of the lifted diagram.
* `AlgebraicGeometry.Space.sectionHom`: the canonical homomorphism from the sections over an
  elementary étale neighborhood into the henselian local ring.

## Main results

* `AlgebraicGeometry.Space.sectionHom_naturality`: restricting a section to a finer
  elementary étale neighborhood does not change its canonical image.
* `AlgebraicGeometry.Space.existsUnique_lift`: a family of ring homomorphisms out of the
  section rings which is compatible with restriction factors uniquely through the henselian
  local ring.

## References

* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Lifting a compatible family of ring homomorphisms through a colimit -/

section ColimitLift

universe w

/-- The value on a prequotient element of the homomorphism determined by a family of ring
homomorphisms out of a diagram of commutative rings. -/
def descPrequotient {J : Type w} [SmallCategory J] (F : J ⥤ CommRingCat.{w})
    {R : Type*} [CommRing R] (φ : ∀ j, (F.obj j) →+* R) :
    CommRingCat.Colimits.Prequotient F → R
  | .of j a => φ j a
  | .zero => 0
  | .one => 1
  | .neg a => -descPrequotient F φ a
  | .add a b => descPrequotient F φ a + descPrequotient F φ b
  | .mul a b => descPrequotient F φ a * descPrequotient F φ b

/-- `descPrequotient` takes equal values on related prequotient elements when the family of ring
homomorphisms is compatible with the diagram. -/
theorem descPrequotient_respects {J : Type w} [SmallCategory J]
    (F : J ⥤ CommRingCat.{w}) {R : Type*} [CommRing R] (φ : ∀ j, (F.obj j) →+* R)
    (hφ : ∀ {j j'} (f : j ⟶ j') (a : F.obj j), φ j' (F.map f a) = φ j a)
    {a b : CommRingCat.Colimits.Prequotient F}
    (h : CommRingCat.Colimits.Relation F a b) :
    descPrequotient F φ a = descPrequotient F φ b := by
  induction h <;> simp_all [descPrequotient, mul_add, add_mul] <;> ac_rfl

/-- The homomorphism out of a colimit of commutative rings determined by a family of ring
homomorphisms compatible with the diagram. -/
def descColimit {J : Type w} [SmallCategory J] (F : J ⥤ CommRingCat.{w})
    {R : Type*} [CommRing R] (φ : ∀ j, (F.obj j) →+* R)
    (hφ : ∀ {j j'} (f : j ⟶ j') (a : F.obj j), φ j' (F.map f a) = φ j a) :
    CommRingCat.Colimits.ColimitType F →+* R where
  toFun := Quot.lift (descPrequotient F φ) fun _ _ h ↦ descPrequotient_respects F φ hφ h
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := Quot.induction_on₂ a b fun x y ↦ by
    rw [← CommRingCat.Colimits.quot_add]
    rfl
  map_mul' a b := Quot.induction_on₂ a b fun x y ↦ by
    rw [← CommRingCat.Colimits.quot_mul]
    rfl

private theorem descColimit_ext {J : Type w} [SmallCategory J] (F : J ⥤ CommRingCat.{w})
    {R : Type*} [CommRing R] (ψ ψ' : CommRingCat.Colimits.ColimitType F →+* R)
    (h : ∀ j a, ψ ((CommRingCat.Colimits.coconeMorphism F j).hom a) =
      ψ' ((CommRingCat.Colimits.coconeMorphism F j).hom a)) :
    ψ = ψ' := by
  refine RingHom.ext fun z ↦ ?_
  refine Quot.inductionOn z ?_
  intro a
  induction a with
  | of j a => exact h j a
  | zero => simp
  | one => simp
  | neg a ih => rw [CommRingCat.Colimits.quot_neg, map_neg, map_neg, ih]
  | add a b ih₁ ih₂ => rw [CommRingCat.Colimits.quot_add, map_add, map_add, ih₁, ih₂]
  | mul a b ih₁ ih₂ => rw [CommRingCat.Colimits.quot_mul, map_mul, map_mul, ih₁, ih₂]

private theorem existsUnique_descColimit {J : Type w} [SmallCategory J]
    (F : J ⥤ CommRingCat.{w}) {R : Type*} [CommRing R] (φ : ∀ j, (F.obj j) →+* R)
    (hφ : ∀ {j j'} (f : j ⟶ j') (a : F.obj j), φ j' (F.map f a) = φ j a) :
    ∃! ψ : CommRingCat.Colimits.colimit F →+* R,
      ∀ j a, ψ ((CommRingCat.Colimits.coconeMorphism F j).hom a) = φ j a :=
  ⟨descColimit F φ hφ, fun _ _ ↦ rfl,
    fun ψ hψ ↦ descColimit_ext F ψ _ fun j a ↦ hψ j a⟩

end ColimitLift

/-! ### The diagram of global sections of the elementary étale neighborhoods -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

/-- The scheme underlying an elementary étale neighborhood, functorially. -/
@[implicit_reducible]
def neighborhoodScheme : ElementaryEtaleNeighborhood B S hS X hX x ⥤ Scheme.{u} where
  obj U := U.scheme.left.1
  map f := f.hom.left.1
  map_id _U := rfl
  map_comp _f _g := rfl

/-- The contravariant diagram of the rings of global sections of the elementary étale
neighborhoods of a point. -/
@[implicit_reducible]
def globalSections :
    (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (neighborhoodScheme B S hS X hX x).op ⋙ Scheme.Γ

/-- The diagram of global sections, lifted to the universe of the index category. -/
@[implicit_reducible]
def liftedGlobalSections :
    (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} ((globalSections B S hS X hX x).obj U))
  map f := CommRingCat.ofHom (((globalSections B S hS X hX x).map f).hom.ulift)
  map_id U := by ext s; simp
  map_comp f g := by ext s; simp [RingHom.ulift_apply]

/-- `CommRingCat.{u + 1}` has colimits indexed by the opposite of the category of elementary étale
neighborhoods of a point. -/
instance hasColimitsOfShape_elementaryEtaleNeighborhoodOp :
    HasColimitsOfShape (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ CommRingCat.{u + 1} :=
  hasColimitsOfShape_of_equivalence
    (AsSmall.equiv.{u, u + 1, u + 1}
      (C := (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ)).symm

/-! ### The henselian local ring -/

/-- The henselian local ring of a decent algebraic space at a point: the
colimit of the rings of global sections over the elementary étale neighborhoods of the
point. -/
@[stacks 0BGW "the henselian local ring at a point"]
abbrev henselianLocalRing (_hDecent : IsDecentSpace B S hS X) : CommRingCat.{u + 1} :=
  colimit (liftedGlobalSections B S hS X hX x)

/-- The canonical ring homomorphism from the global sections of an
elementary étale neighborhood into the henselian local ring. -/
@[stacks 0BGW "canonical section homomorphisms"]
def sectionHom (hDecent : IsDecentSpace B S hS X)
    (U : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ) :
    (globalSections B S hS X hX x).obj U →+* henselianLocalRing B S hS X hX x hDecent :=
  (colimit.ι (liftedGlobalSections B S hS X hX x) U).hom.comp
    ULift.ringEquiv.symm.toRingHom

/-- Restricting a section to a finer elementary étale neighborhood does not
change its canonical image in the henselian local ring. -/
@[stacks 0BGW "naturality of section homomorphisms"]
theorem sectionHom_naturality (hDecent : IsDecentSpace B S hS X)
    {U V : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ} (f : U ⟶ V)
    (s : (globalSections B S hS X hX x).obj U) :
    sectionHom B S hS X hX x hDecent V ((globalSections B S hS X hX x).map f s) =
      sectionHom B S hS X hX x hDecent U s :=
  congrArg (fun g ↦ g.hom (ULift.up s))
    (colimit.w (liftedGlobalSections B S hS X hX x) f)

/-- A family of ring homomorphisms out of the global sections of the
elementary étale neighborhoods of a point, compatible with restriction, factors uniquely
through the henselian local ring. -/
@[stacks 0BGW "colimit universal property"]
theorem existsUnique_lift (hDecent : IsDecentSpace B S hS X) (R : Type v) [CommRing R]
    (φ : ∀ U : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ,
      (globalSections B S hS X hX x).obj U →+* R)
    (hφ : ∀ {U V} (f : U ⟶ V) (s : (globalSections B S hS X hX x).obj U),
      φ V ((globalSections B S hS X hX x).map f s) = φ U s) :
    ∃! ψ : henselianLocalRing B S hS X hX x hDecent →+* R,
      ∀ U s, ψ (sectionHom B S hS X hX x hDecent U s) = φ U s := by
  let C := (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ
  let F : C ⥤ CommRingCat.{u + 1} := liftedGlobalSections B S hS X hX x
  let e : C ≌ AsSmall C := AsSmall.equiv.{u, u + 1, u + 1}
  let G : AsSmall C ⥤ CommRingCat.{u + 1} := e.symm.functor ⋙ F
  let φ' : ∀ j, (G.obj j) →+* R := fun j ↦
    (φ (e.symm.functor.obj j)).comp ULift.ringEquiv.toRingHom
  have hφ' : ∀ {j j' : AsSmall C} (f : j ⟶ j') (s : G.obj j), φ' j' (G.map f s) = φ' j s := by
    intro j j' f s
    exact hφ (e.symm.functor.map f) s.down
  obtain ⟨ψ₀, hψ₀, hψ₀_unique⟩ := existsUnique_descColimit (F := G) (φ := φ') hφ'
  let hcSmall := CommRingCat.Colimits.colimitIsColimit G
  let hcActual := IsColimit.whiskerEquivalence (colimit.isColimit F) e.symm
  let eCol : (Cocone.whisker e.symm.functor (colimit.cocone F)).pt ≅
      CommRingCat.Colimits.colimit G :=
    IsColimit.coconePointUniqueUpToIso hcActual hcSmall
  let ψ : henselianLocalRing B S hS X hX x hDecent →+* R := ψ₀.comp eCol.hom.hom
  have hsection : ∀ U s, ψ (sectionHom B S hS X hX x hDecent U s) = φ U s := by
    intro U s
    let j := e.functor.obj U
    let f := e.unitIso.hom.app U
    have he := IsColimit.comp_coconePointUniqueUpToIso_hom hcActual hcSmall j
    have he_apply := congrArg
      (fun g : (G.obj j) ⟶ CommRingCat.Colimits.colimit G ↦ g.hom (F.map f (ULift.up s))) he
    have harg : eCol.hom.hom ((colimit.ι F U).hom (ULift.up s)) =
        (CommRingCat.Colimits.coconeMorphism G j).hom (F.map f (ULift.up s)) := by
      simpa [eCol, j, Cocone.whisker_ι, Functor.whiskerLeft_app,
        CommRingCat.Colimits.colimitCocone, RingHom.comp_apply] using he_apply
    change ψ₀ (eCol.hom.hom ((colimit.ι F U).hom (ULift.up s))) = φ U s
    rw [harg, hψ₀ j (F.map f (ULift.up s))]
    exact hφ f s
  refine ⟨ψ, hsection, ?_⟩
  intro ψ' hψ'
  have hψ'_lift : ∀ U s, ψ' ((colimit.ι F U).hom (ULift.up s)) = φ U s := fun U s ↦ hψ' U s
  have he_inv := IsColimit.comp_coconePointUniqueUpToIso_inv hcActual hcSmall
  have hψ'_explicit : ∀ j s,
      (ψ'.comp eCol.inv.hom) ((CommRingCat.Colimits.coconeMorphism G j).hom s) = φ' j s := by
    intro j s
    cases s with
    | up s =>
      let U := e.symm.functor.obj j
      have he_apply :=
        congrArg (fun g : G.obj j ⟶ colimit F ↦ ψ' (g.hom (ULift.up s))) (he_inv j)
      have he_apply' :
          ψ' (eCol.inv.hom ((CommRingCat.Colimits.coconeMorphism G j).hom (ULift.up s))) =
            ψ' ((colimit.ι F U).hom (ULift.up s)) := by
        simpa [eCol, U, Cocone.whisker_ι, Functor.whiskerLeft_app,
          CommRingCat.Colimits.colimitCocone, RingHom.comp_apply] using he_apply
      rw [RingHom.comp_apply, he_apply']
      exact hψ'_lift U s
  calc ψ' = (ψ'.comp eCol.inv.hom).comp eCol.hom.hom := by ext; simp
    _ = ψ := by rw [hψ₀_unique _ hψ'_explicit]

end AlgebraicGeometry.Space

end
