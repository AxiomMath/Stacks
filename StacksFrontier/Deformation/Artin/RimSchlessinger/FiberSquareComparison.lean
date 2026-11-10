module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.SmallExtensionCriterion

/-!
# The comparison functor of a square of fibres

Lemmas on `Deformation.Artin.fiberSquareComparison`, the comparison functor of condition (RS)
(see `Deformation.Artin.SatisfiesRS`): its value identifies the two composite cartesian lifts of
a commutative square of the base; when it is full and faithful, a compatible pair of morphisms
out of the two chosen pullbacks of an object comes from a unique morphism out of that object; a
square of deformations that is a fibre product on algebras and has the universal property for
morphisms of deformations is a limit cone; and two squares of fibres whose comparison functors
are equivalences paste to a rectangle whose comparison functor is an equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁

namespace Deformation.Artin

open IsLocalRing

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoricalPullback.π₁ CategoricalPullback.π₂
/-- The inclusion of a fibre sends a morphism to its underlying morphism. -/
private lemma fiber_map {C X : Type*} [Category C] [Category X]
    {p : X ⥤ C} {Z : C} {s t : p.Fiber Z} (f : s ⟶ t) :
    Functor.Fiber.fiberInclusion.map f = f.1 := rfl
/-- Composition in a fibre is computed on underlying morphisms. -/
lemma fiber_comp {C X : Type*} [Category C] [Category X]
    {p : X ⥤ C} {Z : C} {s t u : p.Fiber Z} (f : s ⟶ t) (g : t ⟶ u) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl
/-- The comparison isomorphism between the pullback functors along two equal morphisms is
compatible with the two chosen cartesian lifts. -/
private lemma pullback_eq_fac {C X : Type*} [Category C] [Category X]
    {p : X ⥤ C} (c : p.ChoiceOfPullbacks) {V U : C}
    (f g : V ⟶ U) (h : f = g) (x : p.Fiber U) :
    Functor.Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor h)).app x).hom ≫
      c.map g x = c.map f x := by
  cases h
  exact Category.id_comp _

/-- The isomorphism carried by the value of the comparison functor identifies the two
composite cartesian lifts of a commutative square in the base. -/
private lemma square_fac {C X : Type*} [Category C] [Category X]
    (p : X ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) (s : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
      ((fiberSquareComparison p c f g i j h).obj s).iso.hom ≫
      c.map g (c.obj j s) ≫ c.map j s = c.map f (c.obj i s) ≫ c.map i s := by
  change Functor.Fiber.fiberInclusion.map
    (((c.objCompIso f i s).symm ≪≫
      (eqToIso (congrArg c.pullbackFunctor h)).app s ≪≫ c.objCompIso g j s).hom) ≫ _ = _
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [c.objCompIso_hom_fac, pullback_eq_fac c _ _ h]
  rw [← c.objCompIso_hom_fac f i s]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  change (𝟙 _ ≫ _) ≫ _ = _
  simp

/-- A morphism of a fibre commutes with the chosen cartesian lifts, read on underlying
morphisms. -/
@[reassoc] private lemma homMap_fac_val {C X : Type*} [Category C] [Category X]
    {p : X ⥤ C} (c : p.ChoiceOfPullbacks) {V Z : C} (i : V ⟶ Z)
    {s t : p.Fiber Z} (a : s ⟶ t) :
    (c.homMap i a).1 ≫ c.map i t = c.map i s ≫ a.1 :=
  c.homMap_fac i a

/-- The factorization of a commutative square through the comparison functor, read on
underlying morphisms. -/
@[reassoc] lemma square_fac_val {C X : Type*} [Category C] [Category X]
    (p : X ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) (s : p.Fiber Z) :
    ((fiberSquareComparison p c f g i j h).obj s).iso.hom.1 ≫
      c.map g (c.obj j s) ≫ c.map j s = c.map f (c.obj i s) ≫ c.map i s :=
  square_fac p c f g i j h s

/-- When the comparison functor of a square is full and faithful, a compatible pair of
morphisms out of the two chosen pullbacks of an object of the fibre comes from a unique
morphism out of that object. -/
private lemma square_lift {C X : Type*} [Category C] [Category X]
    (p : X ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z T : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j)
    [(fiberSquareComparison p c f g i j h).Full]
    [(fiberSquareComparison p c f g i j h).Faithful]
    (s : p.Fiber Z) (t : p.Fiber T) (r : Z ⟶ T)
    (a : (c.obj i s).1 ⟶ t.1) (b : (c.obj j s).1 ⟶ t.1)
    [p.IsHomLift (i ≫ r) a] [p.IsHomLift (j ≫ r) b]
    (hab : c.map f (c.obj i s) ≫ a =
      Functor.Fiber.fiberInclusion.map
        ((fiberSquareComparison p c f g i j h).obj s).iso.hom ≫
          c.map g (c.obj j s) ≫ b) :
    ∃! l : s.1 ⟶ t.1, p.IsHomLift r l ∧
      c.map i s ≫ l = a ∧ c.map j s ≫ l = b := by
  let E := fiberSquareComparison p c f g i j h
  let t' := c.obj r t
  let d := c.map r t
  let ai : c.obj i s ⟶ c.obj i t' :=
    ⟨Functor.IsCartesian.map p (i ≫ r) (c.map i t' ≫ d) a, inferInstance⟩
  let bj : c.obj j s ⟶ c.obj j t' :=
    ⟨Functor.IsCartesian.map p (j ≫ r) (c.map j t' ≫ d) b, inferInstance⟩
  have ha : ai.1 ≫ c.map i t' ≫ d = a :=
    Functor.IsCartesian.fac p (i ≫ r) (c.map i t' ≫ d) a
  have hb : bj.1 ≫ c.map j t' ≫ d = b :=
    Functor.IsCartesian.fac p (j ≫ r) (c.map j t' ≫ d) b
  let m : E.obj s ⟶ E.obj t' := {
    fst := ai
    snd := bj
    w := by
      apply Functor.fiber_hom_ext_of_cartesian (g ≫ j ≫ r)
        (c.map g (c.obj j t') ≫ c.map j t' ≫ d) inferInstance
      simp only [fiber_map, fiber_comp, Category.assoc]
      change (c.homMap f ai).1 ≫ (E.obj t').iso.hom.1 ≫
          c.map g (c.obj j t') ≫ c.map j t' ≫ d =
        (E.obj s).iso.hom.1 ≫ (c.homMap g bj).1 ≫
          c.map g (c.obj j t') ≫ c.map j t' ≫ d
      rw [square_fac_val_assoc, homMap_fac_val_assoc, homMap_fac_val_assoc, ha, hb]
      exact hab }
  let l₀ := E.preimage m
  have hi : c.homMap i l₀ = ai :=
    congrArg (fun z => z.fst) (E.map_preimage m)
  have hj : c.homMap j l₀ = bj :=
    congrArg (fun z => z.snd) (E.map_preimage m)
  have : p.IsHomLift (𝟙 Z) l₀.1 := l₀.2
  refine ⟨l₀.1 ≫ d, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · have hh := c.homMap_fac i l₀
    simp only [fiber_map, hi] at hh
    rw [← Category.assoc, ← hh]
    simpa only [Category.assoc] using ha
  · have hh := c.homMap_fac j l₀
    simp only [fiber_map, hj] at hh
    rw [← Category.assoc, ← hh]
    simpa only [Category.assoc] using hb
  · intro l hl
    let := hl.1
    let z : s ⟶ t' := ⟨Functor.IsCartesian.map p r d l, inferInstance⟩
    have hz : z.1 ≫ d = l := Functor.IsCartesian.fac p r d l
    have hzi : c.homMap i z = ai := by
      apply Functor.fiber_hom_ext_of_cartesian (i ≫ r) (c.map i t' ≫ d) inferInstance
      simp only [fiber_map, homMap_fac_val_assoc, hz, hl.2.1, ha]
    have hzj : c.homMap j z = bj := by
      apply Functor.fiber_hom_ext_of_cartesian (j ≫ r) (c.map j t' ≫ d) inferInstance
      simp only [fiber_map, homMap_fac_val_assoc, hz, hl.2.2, hb]
    have hz0 : z = l₀ := by
      apply E.map_injective
      rw [E.map_preimage]
      exact CategoricalPullback.Hom.ext hzi hzj
    rw [← hz, hz0]

/-- The compatibility condition on a pair of morphisms out of an object of the two-fibre
product transports backwards along a morphism of two-fibre products. -/
lemma pair_map_condition {C X : Type*} [Category C] [Category X]
    {p : X ⥤ C} (c : p.ChoiceOfPullbacks)
    {U V W : C} (f : U ⟶ V) (g : U ⟶ W)
    {s t : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g)}
    (q : s ⟶ t) {z : X} (a : t.fst.1 ⟶ z) (b : t.snd.1 ⟶ z)
    (h : c.map f t.fst ≫ a = t.iso.hom.1 ≫ c.map g t.snd ≫ b) :
    c.map f s.fst ≫ q.fst.1 ≫ a =
      s.iso.hom.1 ≫ c.map g s.snd ≫ q.snd.1 ≫ b := by
  have hw : (c.homMap f q.fst).1 ≫ t.iso.hom.1 =
      s.iso.hom.1 ≫ (c.homMap g q.snd).1 := by
    have hw' : c.homMap f q.fst ≫ t.iso.hom = s.iso.hom ≫ c.homMap g q.snd := q.w
    simpa only [fiber_comp] using congrArg (fun z => z.1) hw'
  calc
    _ = (c.homMap f q.fst).1 ≫ c.map f t.fst ≫ a := by
      rw [homMap_fac_val_assoc]
    _ = (c.homMap f q.fst).1 ≫ t.iso.hom.1 ≫ c.map g t.snd ≫ b := by rw [h]
    _ = s.iso.hom.1 ≫ (c.homMap g q.snd).1 ≫ c.map g t.snd ≫ b := by
      rw [← Category.assoc, hw, Category.assoc]
    _ = _ := by rw [homMap_fac_val_assoc]

/-- The lifting property of the comparison functor, transported along an isomorphism from
the value of that functor onto an arbitrary object of the two-fibre product. -/
lemma pair_lift {C X : Type*} [Category C] [Category X]
    (p : X ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z T : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j)
    [(fiberSquareComparison p c f g i j h).Full]
    [(fiberSquareComparison p c f g i j h).Faithful]
    (s : p.Fiber Z)
    (v : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g))
    (e : (fiberSquareComparison p c f g i j h).obj s ≅ v)
    (t : p.Fiber T) (r : Z ⟶ T)
    (a : v.fst.1 ⟶ t.1) (b : v.snd.1 ⟶ t.1)
    [p.IsHomLift (i ≫ r) a] [p.IsHomLift (j ≫ r) b]
    (hab : c.map f v.fst ≫ a = v.iso.hom.1 ≫ c.map g v.snd ≫ b) :
    ∃! l : s.1 ⟶ t.1, p.IsHomLift r l ∧
      (e.inv.fst.1 ≫ c.map i s) ≫ l = a ∧
      (e.inv.snd.1 ≫ c.map j s) ≫ l = b := by
  let ei := (CategoricalPullback.π₁ _ _).mapIso e
  let ej := (CategoricalPullback.π₂ _ _).mapIso e
  have hii : ei.inv.1 ≫ ei.hom.1 = 𝟙 _ :=
    congrArg (fun z => z.1) ei.inv_hom_id
  have hij : ei.hom.1 ≫ ei.inv.1 = 𝟙 _ :=
    congrArg (fun z => z.1) ei.hom_inv_id
  have hji : ej.inv.1 ≫ ej.hom.1 = 𝟙 _ :=
    congrArg (fun z => z.1) ej.inv_hom_id
  have hjj : ej.hom.1 ≫ ej.inv.1 = 𝟙 _ :=
    congrArg (fun z => z.1) ej.hom_inv_id
  have : p.IsHomLift (𝟙 V) ei.hom.1 := ei.hom.2
  have : p.IsHomLift (𝟙 W) ej.hom.1 := ej.hom.2
  have : p.IsHomLift (i ≫ r) (ei.hom.1 ≫ a) :=
    IsHomLift.comp_lift_id_left' p V ei.hom.1 (i ≫ r) a
  have : p.IsHomLift (j ≫ r) (ej.hom.1 ≫ b) :=
    IsHomLift.comp_lift_id_left' p W ej.hom.1 (j ≫ r) b
  obtain ⟨l, hl, hu⟩ := square_lift p c f g i j h s t r
    (ei.hom.1 ≫ a) (ej.hom.1 ≫ b) (pair_map_condition c f g e.hom a b hab)
  refine ⟨l, ⟨hl.1, ?_, ?_⟩, ?_⟩
  · change (ei.inv.1 ≫ c.map i s) ≫ l = a
    rw [Category.assoc, hl.2.1, ← Category.assoc, hii, Category.id_comp]
  · change (ej.inv.1 ≫ c.map j s) ≫ l = b
    rw [Category.assoc, hl.2.2, ← Category.assoc, hji, Category.id_comp]
  · intro l' hl'
    apply hu l'
    refine ⟨hl'.1, ?_, ?_⟩
    · have hh := congrArg (fun z => ei.hom.1 ≫ z) hl'.2.1
      change ei.hom.1 ≫ (ei.inv.1 ≫ c.map i s) ≫ l' = ei.hom.1 ≫ a at hh
      simpa only [← Category.assoc, hij, Category.id_comp] using hh
    · have hh := congrArg (fun z => ej.hom.1 ≫ z) hl'.2.2
      change ej.hom.1 ≫ (ej.inv.1 ≫ c.map j s) ≫ l' = ej.hom.1 ≫ b at hh
      simpa only [← Category.assoc, hjj, Category.id_comp] using hh

section
universe v w
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {X : Type v} [Category.{w} X]
  {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The arrow of `𝒞_Λ` attached to a composite of morphisms of deformations is the composite
of the attached arrows. -/
private lemma ringHom_comp (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b c : D.carrier} (f : a ⟶ b) (g : b ⟶ c),
      (D.morphisms a c (f ≫ g)).ringHom =
        (D.morphisms a b f).ringHom ≫ (D.morphisms b c g).ringHom := by
  let := D.category
  intro a b c f g
  rw [← D.morphism_projection, ← D.morphism_projection, ← D.morphism_projection]
  simp [Functor.map_comp, Category.assoc]

/-- The projection to `𝒞_Λ` agrees with the attached arrow of `𝒞_Λ`, up to the identification
of the projection of an object with its algebra. -/
private lemma projection_naturality (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b : D.carrier} (f : a ⟶ b),
      eqToHom (D.object_projection a) ≫ (D.morphisms a b f).ringHom =
        D.projection.map f ≫ eqToHom (D.object_projection b) := by
  let := D.category
  intro a b f
  rw [← D.morphism_projection]
  simp

/-- A square of deformations which is a fibre product on algebras, commutes on arrows, and
has the universal property for morphisms of deformations is a limit cone whose image in
`𝒞_Λ` is again a limit cone. -/
lemma deformationCone_isPullback
    (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {x₁ x₂ x : D.carrier} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    (z : DeformationObject iΛ q x₀ hx₀)
    (g₁ : DeformationMorphism iΛ q x₀ hx₀ z (D.objects x₁))
    (g₂ : DeformationMorphism iΛ q x₀ hx₀ z (D.objects x₂)),
    IsPullback g₁.ringHom g₂.ringHom
      (D.morphisms x₁ x f₁).ringHom (D.morphisms x₂ x f₂).ringHom →
    (D.morphisms x₁ x f₁).arrow ≫ g₁.arrow =
      (D.morphisms x₂ x f₂).arrow ≫ g₂.arrow →
    (∀ (t : DeformationObject iΛ q x₀ hx₀)
      (a : DeformationMorphism iΛ q x₀ hx₀ t (D.objects x₁))
      (b : DeformationMorphism iΛ q x₀ hx₀ t (D.objects x₂)),
      a.ringHom ≫ (D.morphisms x₁ x f₁).ringHom =
        b.ringHom ≫ (D.morphisms x₂ x f₂).ringHom →
      (D.morphisms x₁ x f₁).arrow ≫ a.arrow =
        (D.morphisms x₂ x f₂).arrow ≫ b.arrow →
      ∃! l : DeformationMorphism iΛ q x₀ hx₀ t z,
        (l.ringHom ≫ g₁.ringHom = a.ringHom ∧ g₁.arrow ≫ l.arrow = a.arrow) ∧
        (l.ringHom ≫ g₂.ringHom = b.ringHom ∧ g₂.arrow ≫ l.arrow = b.arrow)) →
    ∃ c : PullbackCone f₁ f₂, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map D.projection)) := by
  let := D.category
  intro x₁ x₂ x f₁ f₂ z g₁ g₂ hpb hw hu
  obtain ⟨c, rfl⟩ := D.objects.surjective z
  let k₁ : c ⟶ x₁ := (D.morphisms c x₁).symm g₁
  let k₂ : c ⟶ x₂ := (D.morphisms c x₂).symm g₂
  have hk₁ : D.morphisms c x₁ k₁ = g₁ := (D.morphisms c x₁).apply_symm_apply _
  have hk₂ : D.morphisms c x₂ k₂ = g₂ := (D.morphisms c x₂).apply_symm_apply _
  have hw' : k₁ ≫ f₁ = k₂ ≫ f₂ := by
    apply (D.morphisms c x).injective
    apply DeformationMorphism.ext_of_components
    · simpa only [ringHom_comp, hk₁, hk₂] using hpb.w
    · simpa only [D.reversed_composition, hk₁, hk₂] using hw
  let cone := PullbackCone.mk k₁ k₂ hw'
  refine ⟨cone, ?_, ?_⟩
  · refine ⟨PullbackCone.isLimitAux' cone ?_⟩
    intro s
    have hex := hu (D.objects s.pt)
      (D.morphisms _ _ s.fst) (D.morphisms _ _ s.snd)
      (by simpa only [ringHom_comp] using
        congrArg (fun f => (D.morphisms _ _ f).ringHom) s.condition)
      (by simpa only [D.reversed_composition] using
        congrArg (fun f => (D.morphisms _ _ f).arrow) s.condition)
    let l := hex.choose
    have hl := hex.choose_spec.1
    have hlu := hex.choose_spec.2
    let ll := (D.morphisms s.pt c).symm l
    have hll : D.morphisms s.pt c ll = l := (D.morphisms s.pt c).apply_symm_apply _
    have hfac₁ : ll ≫ k₁ = s.fst := by
      apply (D.morphisms _ _).injective
      apply DeformationMorphism.ext_of_components
      · simpa only [ringHom_comp, hll, hk₁] using hl.1.1
      · simpa only [D.reversed_composition, hll, hk₁] using hl.1.2
    have hfac₂ : ll ≫ k₂ = s.snd := by
      apply (D.morphisms _ _).injective
      apply DeformationMorphism.ext_of_components
      · simpa only [ringHom_comp, hll, hk₂] using hl.2.1
      · simpa only [D.reversed_composition, hll, hk₂] using hl.2.2
    refine ⟨ll, hfac₁, hfac₂, ?_⟩
    intro m hm₁ hm₂
    change s.pt ⟶ c at m
    change m ≫ k₁ = s.fst at hm₁
    change m ≫ k₂ = s.snd at hm₂
    change (m : s.pt ⟶ c) = ll
    apply (D.morphisms s.pt c).injective
    rw [hll]
    apply hlu
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simpa only [ringHom_comp, hk₁] using
        congrArg (fun f => (D.morphisms _ _ f).ringHom) hm₁
    · simpa only [D.reversed_composition, hk₁] using
        congrArg (fun f => (D.morphisms _ _ f).arrow) hm₁
    · simpa only [ringHom_comp, hk₂] using
        congrArg (fun f => (D.morphisms _ _ f).ringHom) hm₂
    · simpa only [D.reversed_composition, hk₂] using
        congrArg (fun f => (D.morphisms _ _ f).arrow) hm₂
  · have hp' : IsPullback (D.projection.map k₁) (D.projection.map k₂)
        (D.projection.map f₁) (D.projection.map f₂) := by
      apply hpb.of_iso' (eqToIso (D.object_projection c))
        (eqToIso (D.object_projection x₁)) (eqToIso (D.object_projection x₂))
        (eqToIso (D.object_projection x))
      · simpa only [hk₁, eqToIso.hom] using projection_naturality D k₁
      · simpa only [hk₂, eqToIso.hom] using projection_naturality D k₂
      · exact projection_naturality D f₁
      · exact projection_naturality D f₂
    exact ⟨hp'.isLimit⟩

end

/-- A morphism lying over a morphism of the base has the same image as that morphism under
any functor out of the base, up to the identifications of objects. -/
lemma map_lift_fac {C T X : Type*} [Category C] [Category T] [Category X]
    (p : X ⥤ C) (F : C ⥤ T) {a b : C} {x y : X}
    (f : a ⟶ b) (g : x ⟶ y) [p.IsHomLift f g]
    (hx : F.obj (p.obj x) = F.obj a) (hy : F.obj (p.obj y) = F.obj b) :
    eqToHom hx.symm ≫ F.map (p.map g) ≫ eqToHom hy = F.map f := by
  have hh := congrArg F.map (IsHomLift.fac p f g)
  simpa only [Functor.map_comp, eqToHom_map] using hh.symm

universe v w

/-! ### Pasting squares of fibres -/

section Paste

open CategoryTheory.Functor CategoryTheory.Limits.CategoricalPullback

variable {D : Type u} [Category.{v} D] {Y : Type w} [Category Y]
  (q : Y ⥤ D) (c : q.ChoiceOfPullbacks)

/-- The filler of the square of pullback functors attached to a commutative square of the base:
the natural isomorphism carried by `Deformation.Artin.fiberSquareComparison`. -/
private noncomputable def squareFiller {U V W Z : D} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    c.pullbackFunctor i ⋙ c.pullbackFunctor f ≅ c.pullbackFunctor j ⋙ c.pullbackFunctor g :=
  (c.pullbackFunctorCompIso f i).symm ≪≫ eqToIso (congrArg c.pullbackFunctor h) ≪≫
    c.pullbackFunctorCompIso g j

/-- `Deformation.Artin.fiberSquareComparison` is the comparison functor of Stacks 003R attached
to the square of pullback functors and its filler. -/
private lemma fiberSquareComparison_eq {U V W Z : D} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    fiberSquareComparison q c f g i j h =
      squareComparison (c.pullbackFunctor i) (c.pullbackFunctor j)
        (c.pullbackFunctor f) (c.pullbackFunctor g) (squareFiller q c f g i j h) := rfl

/-- The filler of a square identifies the two composite cartesian lifts of that square. -/
@[reassoc]
private lemma squareFiller_hom_app_fac {U V W Z : D} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (x : q.Fiber Z) :
    Fiber.fiberInclusion.map ((squareFiller q c f g i j h).hom.app x) ≫
      c.map g (c.obj j x) ≫ c.map j x = c.map f (c.obj i x) ≫ c.map i x := by
  exact square_fac q c f g i j h x

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.homMap_fac` for the base change along `k` of a
filler, with both chosen pullbacks spelled through `CategoryTheory.Functor.ChoiceOfPullbacks.obj`
rather than through the pullback functors. -/
@[reassoc]
private lemma squareFiller_homMap_fac {U V W Z : D} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (x : q.Fiber Z) {T : D} (k : T ⟶ U) :
    Fiber.fiberInclusion.map (c.homMap k ((squareFiller q c f g i j h).hom.app x)) ≫
        c.map k (c.obj g (c.obj j x)) =
      c.map k (c.obj f (c.obj i x)) ≫
        Fiber.fiberInclusion.map ((squareFiller q c f g i j h).hom.app x) :=
  c.homMap_fac k _

/-- The components of `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorCompIso`. -/
private lemma pullbackFunctorCompIso_hom_app {U' V' W' : D} (g : W' ⟶ V') (f : V' ⟶ U')
    (x : q.Fiber U') :
    (c.pullbackFunctorCompIso g f).hom.app x = (c.objCompIso g f x).hom := rfl

/-- The inverse components of
`CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorCompIso`. -/
private lemma pullbackFunctorCompIso_inv_app {U' V' W' : D} (g : W' ⟶ V') (f : V' ⟶ U')
    (x : q.Fiber U') :
    (c.pullbackFunctorCompIso g f).inv.app x = (c.objCompIso g f x).inv := rfl

/-- The inverse of `CategoryTheory.Functor.ChoiceOfPullbacks.objCompIso` factors the chosen lift
of a composite through the composite of the two chosen lifts. -/
@[reassoc]
private lemma objCompIso_inv_fac {U' V' W' : D} (g : W' ⟶ V') (f : V' ⟶ U') (x : q.Fiber U') :
    Fiber.fiberInclusion.map (c.objCompIso g f x).inv ≫ c.map (g ≫ f) x =
      c.map g (c.obj f x) ≫ c.map f x := by
  rw [← c.objCompIso_hom_fac g f x, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Two squares of fibres paste.** If the left-hand square `(f, g₁, i₁, j₁)` and the right-hand
square `(j₁, g₂, i₂, j₂)` of a commutative rectangle in the base have 2-cartesian comparison
functors, then so does the outer rectangle `(f, g₁ ≫ g₂, i₁ ≫ i₂, j₂)`.

The comparison of the rectangle is the comparison of the right-hand square followed by the
equivalence `CategoryTheory.Limits.CategoricalPullback.pasteCancel`
(`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_paste_iff`), up to
replacing the composite of the two pullback functors on each side of the cospan by the pullback
functor along the composite — which is
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_congr_top` on top and
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer` on the
bottom. -/
theorem isEquivalence_fiberSquareComparison_paste
    {D : Type u} [Category.{v} D] {Y : Type w} [Category Y]
    (q : Y ⥤ D) (c : q.ChoiceOfPullbacks)
    {U V W W₁ Z Z₁ : D}
    (f : U ⟶ V) (g₁ : U ⟶ W₁) (g₂ : W₁ ⟶ W)
    (i₁ : V ⟶ Z₁) (i₂ : Z₁ ⟶ Z) (j₁ : W₁ ⟶ Z₁) (j₂ : W ⟶ Z)
    (w₁ : f ≫ i₁ = g₁ ≫ j₁) (w₂ : j₁ ≫ i₂ = g₂ ≫ j₂)
    (w : f ≫ i₁ ≫ i₂ = (g₁ ≫ g₂) ≫ j₂)
    (h₁ : (fiberSquareComparison q c f g₁ i₁ j₁ w₁).IsEquivalence)
    (h₂ : (fiberSquareComparison q c j₁ g₂ i₂ j₂ w₂).IsEquivalence) :
    (fiberSquareComparison q c f (g₁ ≫ g₂) (i₁ ≫ i₂) j₂ w).IsEquivalence := by
  have hβ : (squareComparison (c.pullbackFunctor i₁) (c.pullbackFunctor j₁)
      (c.pullbackFunctor f) (c.pullbackFunctor g₁)
      (squareFiller q c f g₁ i₁ j₁ w₁)).IsEquivalence := h₁
  have step2 : (squareComparison
      (c.pullbackFunctor i₂ ⋙ c.pullbackFunctor i₁) (c.pullbackFunctor j₂)
      (c.pullbackFunctor f) (c.pullbackFunctor g₂ ⋙ c.pullbackFunctor g₁)
      (pasteFiller (c.pullbackFunctor i₂) (c.pullbackFunctor j₂)
        (c.pullbackFunctor j₁) (c.pullbackFunctor g₂) (squareFiller q c j₁ g₂ i₂ j₂ w₂)
        (c.pullbackFunctor i₁) (c.pullbackFunctor f) (c.pullbackFunctor g₁)
        (squareFiller q c f g₁ i₁ j₁ w₁))).IsEquivalence :=
    (isEquivalence_squareComparison_paste_iff (c.pullbackFunctor i₂) (c.pullbackFunctor j₂)
      (c.pullbackFunctor j₁) (c.pullbackFunctor g₂) (squareFiller q c j₁ g₂ i₂ j₂ w₂)
      (c.pullbackFunctor i₁) (c.pullbackFunctor f) (c.pullbackFunctor g₁)
      (squareFiller q c f g₁ i₁ j₁ w₁)).mpr h₂
  have step3 := (isEquivalence_squareComparison_congr_top
      (c.pullbackFunctor i₂ ⋙ c.pullbackFunctor i₁) (c.pullbackFunctor j₂)
      (c.pullbackFunctor f) (c.pullbackFunctor g₂ ⋙ c.pullbackFunctor g₁)
      (pasteFiller (c.pullbackFunctor i₂) (c.pullbackFunctor j₂)
        (c.pullbackFunctor j₁) (c.pullbackFunctor g₂) (squareFiller q c j₁ g₂ i₂ j₂ w₂)
        (c.pullbackFunctor i₁) (c.pullbackFunctor f) (c.pullbackFunctor g₁)
        (squareFiller q c f g₁ i₁ j₁ w₁))
      (c.pullbackFunctor (i₁ ≫ i₂)) (c.pullbackFunctorCompIso i₁ i₂).symm).mp step2
  refine (isEquivalence_squareComparison_iff_of_transfer
    (c.pullbackFunctor (i₁ ≫ i₂)) (c.pullbackFunctor j₂) (c.pullbackFunctor f)
    (c.pullbackFunctor g₂ ⋙ c.pullbackFunctor g₁) _
    (c.pullbackFunctor j₂) (c.pullbackFunctor f) (c.pullbackFunctor (g₁ ≫ g₂))
    (squareFiller q c f (g₁ ≫ g₂) (i₁ ≫ i₂) j₂ w)
    (𝟭 _) (𝟭 _) (Iso.refl _) (Iso.refl _) (c.pullbackFunctorCompIso g₁ g₂)
    (fun x => ?_)).mp step3
  change (squareFiller q c f (g₁ ≫ g₂) (i₁ ≫ i₂) j₂ w).hom.app x =
    𝟙 (c.obj f (c.obj (i₁ ≫ i₂) x)) ≫
      (c.homMap f (c.objCompIso i₁ i₂ x).hom ≫
          (squareFiller q c f g₁ i₁ j₁ w₁).hom.app (c.obj i₂ x) ≫
            c.homMap g₁ ((squareFiller q c j₁ g₂ i₂ j₂ w₂).hom.app x)) ≫
        (c.objCompIso g₁ g₂ (c.obj j₂ x)).inv ≫ c.homMap (g₁ ≫ g₂) (𝟙 (c.obj j₂ x))
  rw [Category.id_comp, c.homMap_id, Category.comp_id]
  simp only [Category.assoc]
  refine Functor.fiber_hom_ext_of_cartesian ((g₁ ≫ g₂) ≫ j₂)
    (c.map (g₁ ≫ g₂) (c.obj j₂ x) ≫ c.map j₂ x) inferInstance _ _ ?_
  rw [squareFiller_hom_app_fac]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [objCompIso_inv_fac_assoc, squareFiller_homMap_fac_assoc, squareFiller_hom_app_fac,
    squareFiller_hom_app_fac_assoc, c.homMap_fac_assoc, c.objCompIso_hom_fac]

end Paste

end Deformation.Artin
