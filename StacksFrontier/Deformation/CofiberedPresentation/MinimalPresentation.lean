module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.CofiberedPresentation.Morphism
public import StacksFrontier.Deformation.CofiberedPresentation.Prorepresentable
public import StacksFrontier.Deformation.CofiberedPresentation.Smooth
public import StacksFrontier.Deformation.Formal.MinimalVersal.DescentVersality
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalExistence
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism
public import StacksFrontier.Deformation.FormalObject.YonedaEquivalence
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Minimality
public import StacksFrontier.Deformation.Schlessinger.MiniversalExistence
public import StacksFrontier.Deformation.Schlessinger.Prorepresentable
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# A minimal smooth prorepresentable presentation of a deformation category

Let `ℱ` be a deformation category over `𝒞_Λ` whose tangent space and whose space of
infinitesimal automorphisms are finite dimensional over `k`. Then `ℱ` has a minimal versal
formal object `ξ`, say over `R`, and the groupoid in functors `(U, R, s, t, c)` built from the
associated morphism `ξ : U = R̲|_{𝒞_Λ} → ℱ` is a minimal, smooth and prorepresentable groupoid
in functors whose quotient `[U/R]` is equivalent to `ℱ`.

## Main definitions

* `Deformation.MinimalPresentation` bundles the minimal versal formal object, the groupoid in
  functors it presents, and the four properties that groupoid has.

## Main results

* `Deformation.exists_minimalPresentation`: **Stacks Project, Tag 06L2.**

## Implementation notes

Nothing new is proved here. Condition (RS) of a deformation category gives Schlessinger's
conditions (S1) and (S2) by Tag 06J7; Schlessinger's existence theorem, Tag 06IW, and the
descent of Tag 06T5 — chained in Tag 06IX — give the minimal versal formal object `ξ`;
smoothness of the associated morphism is the definition of versality, read through Tag 06HS;
Tag 06L1 gives smoothness of the groupoid and, through the criterion of Tag 06KZ, the
equivalence out of the quotient; Tag 06L7 gives prorepresentability. Minimality is the one
step that needs an argument: the quotient morphism `U → [U/R]` has to be recognised as the
morphism associated to a minimal versal formal object of `[U/R]`, and the minimal versal
object of `[U/R]` is transported from `ξ` along the canonical morphism `[U/R] → ℱ`.

The tangent-space hypothesis is the finite dimensionality of Tag 06IH's canonical `k`-vector
space structure on the tangent space, which instance search obtains from the two `Fact`
instances. Those two carry no mathematical content beyond `hp`: the first is
`⟨hp.predeformation⟩` and the second is
`Deformation.schlessingerConditionS2_of_isIsomorphismClasses` applied to `hp`. They are
instance binders here for exactly the reason they are in Tags 06IW and 06IX.

The infinitesimal-automorphism hypothesis is read at the objects of the special fibre, where
`Inf(ℱ)` is defined, and for every choice of pushforwards there, the choice being immaterial.

## References

* [Stacks Project, Tag 06L2](https://stacks.math.columbia.edu/tag/06L2)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-! ### Auxiliary constructions -/

section Auxiliary
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An identification of objects of a category over a base lies over an identity. -/
private theorem isHomLift_eqToHom {C : Type u₁} [Category.{v₁} C] {X : Type u₂}
    [Category.{v₂} X] (q : X ⥤ C) {x y : X} (e : x = y) {S : C} (hx : q.obj x = S) :
    q.IsHomLift (𝟙 S) (eqToHom e) := by
  cases e
  cases hx
  exact IsHomLift.id rfl

/-- **Essential surjectivity of a smooth morphism, Tag 06HN,** at a value universe
independent of the hom-set universe of `𝒞_Λ`. `Deformation.essSurj_of_isSmooth_of_fiber_essSurj`
is the same statement with the two universes equal, which is not enough for the presentations
of Tag 06KY: the groupoid in functors there takes its values in the maximum of the value
universe and the hom-set universe of the presented category. -/
private theorem essSurj_of_isSmooth_of_fiber_essSurj'
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) (h𝓖 : IsCofiberedInGroupoids 𝓖.p) (hφ : IsSmooth φ)
    (h₀ : (fiberFunctor φ (residueFieldObject.{u, v, w} Λ k)).EssSurj) :
    φ.toFunctor.EssSurj := by
  classical
  refine ⟨fun y => ?_⟩
  let A : ArtinianLocalAlgCat.{u, max v w, w} Λ k := 𝓖.p.obj y
  let q : A ⟶ residueFieldObject.{u, v, w} Λ k := residueMorphism.{u, v, w} A
  have hqsurj : Function.Surjective q.hom := residueMorphism_surjective.{u, v, w} A
  obtain ⟨y₀op, pushop, hpushop⟩ := h𝓖.exists_lift q.op (Opposite.op y) rfl
  let y₀ : 𝓖.obj := Opposite.unop y₀op
  have hy₀ : 𝓖.p.obj y₀ = residueFieldObject.{u, v, w} Λ k :=
    congrArg Opposite.unop (IsHomLift.domain_eq (p := 𝓖.p.op) q.op pushop)
  let push : y ⟶ y₀ := Opposite.unop pushop
  have hpush : 𝓖.p.IsHomLift q push := by
    cases y₀op
    exact CategoryTheory.isHomLift_unop 𝓖.p q.op push.op (inst := hpushop)
  let y₀K : Functor.Fiber 𝓖.p (residueFieldObject.{u, v, w} Λ k) := ⟨y₀, hy₀⟩
  obtain ⟨x₀, ⟨i⟩⟩ := h₀.mem_essImage y₀K
  obtain ⟨x, h, a, hh, ha, hcomm⟩ := hφ q hqsurj y x₀.1 (push ≫ i.inv.val) (by
    let : 𝓖.p.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) i.inv.val := i.inv.property
    let : 𝓖.p.IsHomLift q push := hpush
    exact IsHomLift.comp_lift_id_right' 𝓖.p q push
      (residueFieldObject.{u, v, w} Λ k) i.inv.val)
  have hx : 𝓕.p.obj x = A := IsHomLift.domain_eq (p := 𝓕.p) q h
  let : IsGroupoid (Functor.Fiber 𝓖.p.op (Opposite.op A)) :=
    Functor.IsFiberedInGroupoids.fiber_isGroupoid h𝓖 (Opposite.op A)
  let yAop : Functor.Fiber 𝓖.p.op (Opposite.op A) := ⟨Opposite.op y, rfl⟩
  let φxAop : Functor.Fiber 𝓖.p.op (Opposite.op A) :=
    ⟨Opposite.op (φ.obj x), congrArg Opposite.op (by rw [φ.w_obj, hx])⟩
  have haop : 𝓖.p.op.IsHomLift (𝟙 (Opposite.op A)) a.op := by
    simpa only [op_id] using CategoryTheory.isHomLift_op 𝓖.p (𝟙 A) a (inst := ha)
  let aAop : yAop ⟶ φxAop := ⟨a.op, haop⟩
  let : IsIso aAop := inferInstance
  let iop : Opposite.op y ≅ Opposite.op (φ.obj x) :=
    (Functor.Fiber.fiberInclusion (p := 𝓖.p.op) (S := Opposite.op A)).mapIso (asIso aAop)
  exact ⟨x, ⟨Iso.unop iop⟩⟩

variable {F : Type u₃} [Category.{v₃} F] {G : Type u₂} [Category.{v₂} G]

/-- A commuting square of two morphisms and two identifications of objects is carried by a
functor to a commuting square of their images. -/
private theorem map_eqToHom_comm {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    (c : X ⟶ Y) (c' : X' ⟶ Y') (h : c ≫ eqToHom hY = eqToHom hX ≫ c') :
    F.map c ≫ eqToHom (congrArg F.obj hY) = eqToHom (congrArg F.obj hX) ≫ F.map c' := by
  subst hX hY
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h ⊢
  rw [h]

/-- A formal object of `p` pushes forward along a morphism of categories over `𝒞_Λ`. -/
@[reducible] private def mapFormalObject {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (φ : F ⥤ G) (hφ : φ ⋙ q = p) :
    FormalObject p ⥤ FormalObject q where
  obj ξ :=
    { base := ξ.base
      level := fun n => φ.obj (ξ.level n)
      level_eq := fun n => (Functor.congr_obj hφ (ξ.level n)).trans (ξ.level_eq n)
      transition := fun n => φ.map (ξ.transition n)
      transition_lift := fun n => by
        let := ξ.transition_lift n
        exact Functor.isHomLift_map_of_comp_eq hφ _ _ }
  map f :=
    { base := f.base
      app := fun n => φ.map (f.app n)
      app_lift := fun n => by
        let := f.app_lift n
        exact Functor.isHomLift_map_of_comp_eq hφ _ _
      naturality := fun n => by
        simpa only [Functor.map_comp] using congrArg φ.map (f.naturality n) }
  map_id ξ := FormalObject.Hom.ext rfl (fun n => φ.map_id (ξ.level n))
  map_comp f g := FormalObject.Hom.ext rfl (fun n => φ.map_comp (f.app n) (g.app n))

/-- A formal object reread over a complete local algebra equal to its base. -/
@[reducible] private def formalObjectAtBase {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (h : ξ.base = R) :
    FormalObject p :=
  { base := R
    level := ξ.level
    level_eq := fun n => by rw [← h, ξ.level_eq n]
    transition := ξ.transition
    transition_lift := fun n => by rw [← h]; exact ξ.transition_lift n }

/-- Rereading a formal object over its own base changes nothing. -/
private theorem formalObjectAtBase_eq {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (h : ξ.base = R) :
    formalObjectAtBase ξ R h = ξ := by
  cases h
  rfl

/-- Raising the values of a set-valued functor to a universe they already lie in, as a
`1`-morphism of the categories of elements over `𝒞_Λ`. -/
private def uliftElementsBasedFunctor'
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w)) :
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor
        (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w}))) where
  toFunctor := (uliftElementsEquivalence U).functor
  w := rfl

/-- That `1`-morphism is smooth, being an equivalence over the base. -/
private theorem isSmooth_uliftElementsBasedFunctor'
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w)) :
    IsSmooth (uliftElementsBasedFunctor'.{u, v, w, v₃} U) := by
  let e := uliftElementsEquivalence U
  intro B A f _ y x g hg
  let : (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})).IsHomLift f g := hg
  refine ⟨e.inverse.obj y, e.inverse.map g, e.counitIso.hom.app y, ?_, ?_, ?_⟩
  · refine IsHomLift.of_fac _ _ _
      (by
        change y.1 = B
        exact IsHomLift.domain_eq
          (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})) f g)
      (by
        change x.1 = A
        exact IsHomLift.codomain_eq
          (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})) f g)
      (IsHomLift.fac (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})) f g)
  · change (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})).IsHomLift
      (𝟙 B) (e.counitIso.hom.app y)
    have hy : y.1 = B :=
      IsHomLift.domain_eq (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})) f g
    subst B
    change (Functor.Elements.π (U ⋙ uliftFunctor.{v₃, max v w})).IsHomLift
      (𝟙 y.1) (𝟙 y)
    exact IsHomLift.id rfl
  · apply Functor.Elements.hom_ext
    change g.hom = (𝟙 y.1) ≫ g.hom
    simp only [Category.id_comp]

end Auxiliary

/-! ### Minimal smooth prorepresentable presentations -/

section Presentation
open CategoryTheory
universe u v w u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₃} [Category.{v₃} F]

/-- A minimal smooth prorepresentable presentation of a category cofibered in groupoids `ℱ`
over `𝒞_Λ`: a minimal versal formal object `ξ` of `ℱ` over `R`, a choice of pushforwards, and
the four properties of the groupoid in functors `(U, R, s, t, c)` of Tag 06KY built from the
associated morphism `ξ : U = R̲|_{𝒞_Λ} → ℱ` — it is minimal, smooth and prorepresentable, and
the canonical morphism `[U/R] → ℱ` is an equivalence. -/
public structure MinimalPresentation (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) where
  /-- The minimal versal formal object. -/
  ξ : FormalObject p
  /-- The choice of pushforwards used to form the associated morphism. -/
  pushforwards : ChosenPushforwards p
  /-- The formal object is minimal versal. -/
  minimalVersal : IsMinimalVersal hp ξ
  /-- The groupoid in functors it presents is smooth. -/
  smooth :
    let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
    GroupoidInFunctors.IsSmooth
      ((presentationGroupoid p (restrictedCoyoneda ξ.base)
        f.toFunctor f.w hp).toGroupoidInFunctors)
  /-- The groupoid in functors it presents is prorepresentable. -/
  prorepresentable :
    let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
    GroupoidInFunctors.IsProrepresentable
      ((presentationGroupoid p (restrictedCoyoneda ξ.base)
        f.toFunctor f.w hp).toGroupoidInFunctors)
  /-- The groupoid in functors it presents is minimal. -/
  minimal :
    let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
    GroupoidInFunctors.IsMinimal.{u, max v v₃, w, v₃}
      ((presentationGroupoid p (restrictedCoyoneda ξ.base)
        f.toFunctor f.w hp).toGroupoidInFunctors)
  /-- The canonical morphism from the quotient of the presentation is an equivalence. -/
  quotientEquivalence :
    let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
    (presentationMorphism p (restrictedCoyoneda ξ.base) f.toFunctor f.w
      (presentationGroupoid p (restrictedCoyoneda ξ.base)
        f.toFunctor f.w hp)).1.IsEquivalence

/-- **Every morphism of formal objects into the formal object descended from a minimal versal
one is surjective on bases.** The canonical morphism `g : [U/R] → ℱ` carries a morphism
`t : η → ξQ` of formal objects of `[U/R]` to a morphism `g(η) → ξ` of formal objects of `ℱ`
with the same base map, so minimality of `ξ` gives the surjectivity. The comparison of
`g(ξQ)` with `ξ` is levelwise the one provided by the two evaluation equivalences, and the
two agree on the canonical points of `R` because both are the quotient maps of `R`.

The quotient `[U/R]` enters only through the data listed here, so this is stated for an
arbitrary category `Q` over `𝒞_Λ` with a `1`-morphism `α` from `U` and a `1`-morphism `g`
to `ℱ` compatible with the associated morphism of `ξ`. -/
private theorem surjective_base_of_hom_to_descendedObject
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k} (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) (pushforwards : ChosenPushforwards p)
    (hminimal : IsMinimalVersal hp ξ)
    {Q : Type u₄} [Category.{v₄} Q] {q : Q ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k}
    (α : BasedFunctor (BasedCategory.ofFunctor
      (Functor.Elements.π (restrictedCoyoneda ξ.base))) (BasedCategory.ofFunctor q))
    (E : RepresentableMorphismFormalObjectEquivalence q ξ.base)
    (g : Q ⥤ F) (hg : g ⋙ p = q)
    (hgf : α.toFunctor ⋙ g =
      (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor)
    (η : FormalObject q)
    (t : η ⟶ formalObjectAtBase (E.equivalence.functor.obj α).1 ξ.base
      (E.equivalence.functor.obj α).2) :
    Function.Surjective t.base.hom := by
  classical
  let U := restrictedCoyoneda.{u, max v v₃ w, w} ξ.base
  let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
  let ξQ := formalObjectAtBase (E.equivalence.functor.obj α).1 ξ.base
    (E.equivalence.functor.obj α).2
  let Ep := representableMorphismFormalObjectEquivalence p hp ξ.base
  let ξP' : FormalObject p := (Ep.equivalence.functor.obj f).1
  have hbaseP : ξP'.base = ξ.base := (Ep.equivalence.functor.obj f).2
  let ξP := formalObjectAtBase ξP' ξ.base hbaseP
  have hξP : Ep.equivalence.functor.obj f =
      (⟨ξP, rfl⟩ : (FormalObject.projection (p := p)).Fiber ξ.base) :=
    Subtype.ext (formalObjectAtBase_eq ξP' ξ.base hbaseP).symm
  let hImageP := Classical.choice
    (associatedMorphism_maps_to hp ξ Ep pushforwards)
  let hξPiso : ξP ≅ ξ :=
    Functor.Fiber.fiberInclusion.mapIso (eqToIso hξP.symm ≪≫ hImageP)
  have hbaseiso : hξPiso.hom.base = 𝟙 ξ.base := by
    let _ : (FormalObject.projection (p := p)).IsHomLift (𝟙 ξ.base) hξPiso.hom :=
      (eqToIso hξP.symm ≪≫ hImageP).hom.2
    have hfac : hξPiso.hom.base = eqToHom (rfl : ξ.base = ξ.base) ≫ 𝟙 ξ.base ≫
        eqToHom (rfl : ξ.base = ξ.base) :=
      IsHomLift.fac' (FormalObject.projection (p := p)) (𝟙 ξ.base) hξPiso.hom
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hfac
  have hpoint (n : ℕ) : E.quotientPoint n = Ep.quotientPoint n := by
    apply CompleteLocalAlgCat.Hom.ext
    rw [E.quotientPoint_hom n, Ep.quotientPoint_hom n]
  let d (n : ℕ) : (BasedCategory.ofFunctor (Functor.Elements.π U)).obj :=
    U.elementsMk (AdicTruncation.obj ξ.base n) (E.quotientPoint n)
  let dP (n : ℕ) : (BasedCategory.ofFunctor (Functor.Elements.π U)).obj :=
    U.elementsMk (AdicTruncation.obj ξ.base n) (Ep.quotientPoint n)
  have hd (n : ℕ) : d n = dP n :=
    congrArg (fun z => (U.elementsMk (AdicTruncation.obj ξ.base n) z :
      (BasedCategory.ofFunctor (Functor.Elements.π U)).obj)) (hpoint n)
  have hε (n : ℕ) : g.obj (α.toFunctor.obj (d n)) = f.toFunctor.obj (dP n) :=
    (Functor.congr_obj hgf (d n)).trans (congrArg f.toFunctor.obj (hd n))
  let J (n : ℕ) : g.obj (ξQ.level n) ≅ ξP.level n :=
    g.mapIso (E.levelIso α n).symm ≪≫ eqToIso (hε n) ≪≫ Ep.levelIso f n
  let H := mapFormalObject g hg
  let θ : H.obj ξQ ⟶ ξP :=
    { base := 𝟙 ξ.base
      app := fun n => (J n).hom
      app_lift := by
        intro n
        let : q.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
          (E.levelIso α n).hom := E.levelIso_over α n
        let : q.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
          (E.levelIso α n).inv := by infer_instance
        let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
          (g.map (E.levelIso α n).inv) := Functor.isHomLift_map_of_comp_eq hg _ _
        have hs : p.obj (g.obj (α.toFunctor.obj (d n))) =
            AdicTruncation.obj ξ.base n := by
          calc
            p.obj (g.obj (α.toFunctor.obj (d n))) = p.obj (f.toFunctor.obj (d n)) :=
              congrArg p.obj (Functor.congr_obj hgf (d n))
            _ = (d n).1 := f.w_obj (d n)
            _ = _ := rfl
        let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
          (eqToHom (hε n)) := isHomLift_eqToHom p _ hs
        let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
          (Ep.levelIso f n).hom := Ep.levelIso_over f n
        have hJ0 : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
            (g.map (E.levelIso α n).inv ≫
              eqToHom (hε n) ≫ (Ep.levelIso f n).hom) := by
          infer_instance
        have hJ : p.IsHomLift ((AdicTruncation.functor n).map (𝟙 ξ.base))
            (g.map (E.levelIso α n).inv ≫
              eqToHom (hε n) ≫ (Ep.levelIso f n).hom) := by
          rw [(AdicTruncation.functor n).map_id ξ.base]
          exact hJ0
        exact hJ
      naturality := by
        intro n
        let cE : d (n + 1) ⟶ d n :=
          Functor.Elements.homMk (AdicTruncation.transition ξ.base n)
            (E.projectionPoint n)
        let cP : dP (n + 1) ⟶ dP n :=
          Functor.Elements.homMk (AdicTruncation.transition ξ.base n)
            (Ep.projectionPoint n)
        have hval (m : ℕ) :
            (eqToHom (hd m) : d m ⟶ dP m).hom =
              𝟙 (AdicTruncation.obj ξ.base m) := by
          have hfst : congrArg (Functor.Elements.π U).obj (hd m) = rfl := by
            simp [hd, d]
          exact (eqToHom_map (Functor.Elements.π U) (hd m)).trans (by rw [hfst]; rfl)
        have hc : cE ≫ eqToHom (hd n) = eqToHom (hd (n + 1)) ≫ cP := by
          apply Functor.Elements.hom_ext
          change cE.hom ≫ (eqToHom (hd n) : d n ⟶ dP n).hom =
            (eqToHom (hd (n + 1)) : d (n + 1) ⟶ dP (n + 1)).hom ≫ cP.hom
          rw [hval, hval, Category.comp_id, Category.id_comp]
        have hE : α.map cE ≫ (E.levelIso α n).hom =
            (E.levelIso α (n + 1)).hom ≫ ξQ.transition n := E.transition_comm α n
        have hEi : ξQ.transition n ≫ (E.levelIso α n).inv =
            (E.levelIso α (n + 1)).inv ≫ α.map cE := by
          rw [Iso.comp_inv_eq, Category.assoc, hE, Iso.inv_hom_id_assoc]
        have hEp : f.map cP ≫ (Ep.levelIso f n).hom =
            (Ep.levelIso f (n + 1)).hom ≫ ξP.transition n := Ep.transition_comm f n
        have hhd : f.map cE ≫ eqToHom (congrArg f.toFunctor.obj (hd n)) =
            eqToHom (congrArg f.toFunctor.obj (hd (n + 1))) ≫ f.map cP :=
          map_eqToHom_comm f.toFunctor (hd (n + 1)) (hd n) cE cP hc
        have hbridge : g.map (α.map cE) ≫
              eqToHom (hε n) =
            eqToHom (hε (n + 1)) ≫ f.map cP := by
          have hcongr : g.map (α.map cE) =
              eqToHom (Functor.congr_obj hgf (d (n + 1))) ≫
                f.map cE ≫ eqToHom (Functor.congr_obj hgf (d n)).symm := by
            simpa only [Functor.comp_map] using Functor.congr_hom hgf cE
          rw [hcongr]
          simp only [eqToHom_trans, Category.assoc]
          rw [hhd, ← Category.assoc, eqToHom_trans]
        change g.map (ξQ.transition n) ≫
            (g.map (E.levelIso α n).inv ≫
              eqToHom (hε n) ≫ (Ep.levelIso f n).hom) =
          (g.map (E.levelIso α (n + 1)).inv ≫
            eqToHom (hε (n + 1)) ≫
            (Ep.levelIso f (n + 1)).hom) ≫ ξP.transition n
        rw [← Category.assoc, ← g.map_comp, hEi, g.map_comp]
        simp only [Category.assoc]
        rw [reassoc_of% hbridge, hEp] }
  let ht : H.obj η ⟶ ξ := H.map t ≫ θ ≫ hξPiso.hom
  have hb : ht.base = t.base := by
    change t.base ≫ (𝟙 ξ.base) ≫ hξPiso.hom.base = t.base
    rw [hbaseiso]
    change t.base ≫ 𝟙 ξQ.base = t.base
    exact Category.comp_id _
  rw [← hb]
  exact hminimal.2 (H.obj η) ht

/-- **The presentation groupoid of a minimal versal formal object is minimal.** The quotient
morphism `U → [U/R]` is, up to a vertical isomorphism, the morphism associated to a formal
object `ξQ` of `[U/R]` over the same complete local algebra; `ξQ` is versal because that
quotient morphism is smooth, and every morphism of formal objects into `ξQ` is surjective on
bases because the canonical morphism `[U/R] → ℱ` carries it to a morphism into `ξ`. -/
private theorem isMinimal_presentationGroupoid
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k) (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) (pushforwards : ChosenPushforwards p)
    (hminimal : IsMinimalVersal hp ξ) :
    GroupoidInFunctors.IsMinimal.{u, max v v₃, w, v₃}
      ((presentationGroupoid p (restrictedCoyoneda ξ.base)
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.w hp).toGroupoidInFunctors) := by
  classical
  let U := restrictedCoyoneda.{u, max v v₃ w, w} ξ.base
  let f := (associatedMorphism hp ξ pushforwards).toBasedFunctor
  have hsmooth : GroupoidInFunctors.IsSmooth
      ((presentationGroupoid p U f.toFunctor f.w hp).toGroupoidInFunctors) :=
    isSmooth_presentationGroupoid p U f hp (hminimal.1 pushforwards)
  let G := (presentationGroupoid p U f.toFunctor f.w hp).toGroupoidInFunctors
  let q := Grothendieck.forget (evaluationFunctor G)
  -- The comparison of `U` with the object functor of `G` is named at the type the latter
  -- gives, not at the universe-lifted functor it is built from. The two are definitionally
  -- equal, but only the first makes the composites below typecheck syntactically.
  let e : U.Elements ≌ G.objects.Elements := uliftElementsEquivalence U
  let α : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor q) :=
    { toFunctor := e.functor ⋙ quotientMorphism G
      w := by
        change (e.functor ⋙ quotientMorphism G) ⋙ q = Functor.Elements.π U
        calc
          (e.functor ⋙ quotientMorphism G) ⋙ q =
              e.functor ⋙ (quotientMorphism G ⋙ q) := Functor.assoc _ _ _
          _ = e.functor ⋙ Functor.Elements.π G.objects :=
            congrArg (fun t => e.functor ⋙ t) (quotientMorphism_over G)
          _ = Functor.Elements.π U := rfl }
  let E := representableMorphismFormalObjectEquivalence q
    (quotientProjection_cofibered G) ξ.base
  let ξQ' : FormalObject q := (E.equivalence.functor.obj α).1
  have hbase : ξQ'.base = ξ.base := (E.equivalence.functor.obj α).2
  let ξQ := formalObjectAtBase ξQ' ξ.base hbase
  have hξQ : E.equivalence.functor.obj α =
      (⟨ξQ, rfl⟩ : (FormalObject.projection (p := q)).Fiber ξ.base) :=
    Subtype.ext (formalObjectAtBase_eq ξQ' ξ.base hbase).symm
  let eQ : G.objects.Elements ≌ (restrictedCoyoneda ξQ.base).Elements := e.symm
  change GroupoidInFunctors.IsMinimal.{u, max v v₃, w, v₃} G
  let hq := quotientProjection_cofibered G
  let pushQ : ChosenPushforwards q := chosenPushforwardsOfCofibered q hq
  let assoc := associatedMorphism hq ξQ pushQ
  let hImage := Classical.choice (associatedMorphism_maps_to hq ξQ E pushQ)
  let β : α ≅ assoc.toBasedFunctor :=
    E.equivalence.fullyFaithfulFunctor.preimageIso (eqToIso hξQ ≪≫ hImage.symm)
  refine ⟨ξQ, pushQ, eQ, ⟨?_, ?_⟩, rfl, ?_⟩
  -- the formal object of the quotient is versal
  · have hquot : IsSmooth (quotientBasedFunctor G) :=
      (source_isSmooth_iff_quotient G).mp hsmooth.1
    have hα : IsSmooth α := by
      change IsSmooth (BasedFunctor.comp
        (uliftElementsBasedFunctor' U) (quotientBasedFunctor G))
      exact isSmooth_comp _ _ (isSmooth_uliftElementsBasedFunctor' U) hquot
    have hassoc : IsSmooth assoc.toBasedFunctor := isSmooth_of_iso β.symm hα
    exact (isSmooth_associatedMorphism_iff_isVersal hq ξQ pushQ).mp hassoc
  -- every morphism into it is surjective on bases
  · intro η t
    let M := presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp)
    exact surjective_base_of_hom_to_descendedObject hp ξ pushforwards hminimal α E M.1 M.2.1
      ((Functor.assoc e.functor (quotientMorphism G) M.1).trans M.2.2) η t
  -- the quotient morphism is the associated morphism, up to a vertical isomorphism
  · -- both functors are named at the type the quotient morphism has, so that the whiskered
    -- isomorphisms compose without any unfolding of the presentation
    let αF : U.Elements ⥤ Grothendieck (evaluationFunctor G) :=
      e.functor ⋙ quotientMorphism G
    let assocF : U.Elements ⥤ Grothendieck (evaluationFunctor G) :=
      assoc.toBasedFunctor.toFunctor
    let βU : αF ≅ assocF := (BasedNatTrans.forgetful _ _).mapIso β
    let δ : quotientMorphism G ≅ eQ.functor ⋙ assocF :=
      (Functor.leftUnitor (quotientMorphism G)).symm ≪≫
        Functor.isoWhiskerRight e.counitIso.symm (quotientMorphism G) ≪≫
        Functor.isoWhiskerLeft e.inverse βU
    refine ⟨δ, fun X => ?_⟩
    let _ : (Functor.Elements.π G.objects).IsHomLift (𝟙 X.1) (e.counitIso.inv.app X) := by
      change (Functor.Elements.π G.objects).IsHomLift (𝟙 X.1) (𝟙 X)
      exact IsHomLift.id rfl
    let _ : q.IsHomLift (𝟙 X.1) ((quotientMorphism G).map (e.counitIso.inv.app X)) :=
      Functor.isHomLift_map_of_comp_eq (quotientMorphism_over G) _ _
    let _ : q.IsHomLift (𝟙 X.1) (βU.hom.app (e.inverse.obj X)) := β.hom.isHomLift rfl
    let _ : q.IsHomLift (𝟙 X.1) (𝟙 ((quotientMorphism G).obj X)) := IsHomLift.id rfl
    have hδ : δ.hom.app X = 𝟙 ((quotientMorphism G).obj X) ≫
        (quotientMorphism G).map (e.counitIso.inv.app X) ≫
        βU.hom.app (e.inverse.obj X) := by
      simp only [δ, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.leftUnitor_inv_app]
    rw [hδ]
    infer_instance

/-- **The quotient of the presentation of a versal formal object is equivalent to the
presented category.** By the criterion of Tag 06KZ this is essential surjectivity of the
associated morphism, which follows from its smoothness because the special fibre of a
predeformation category has one object and one morphism. -/
private theorem isEquivalence_presentationMorphism [IsNoetherianRing Λ] [Module.Finite Λ k]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hpre : IsPredeformationCategory.{u, max v v₃, w} p)
    (ξ : FormalObject p) (pushforwards : ChosenPushforwards p)
    (hversal : IsVersal hpre.cofibered ξ) :
    (presentationMorphism p (restrictedCoyoneda ξ.base)
      (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor.toFunctor
      (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor.w
      (presentationGroupoid p (restrictedCoyoneda ξ.base)
        (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor.toFunctor
        (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor.w
        hpre.cofibered)).1.IsEquivalence := by
  classical
  let U := restrictedCoyoneda.{u, max v v₃ w, w} ξ.base
  let f := (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor
  have hU : IsProrepresentable U := ⟨ξ.base, ⟨Iso.refl _⟩⟩
  obtain ⟨hUdef, -, -⟩ := (isProrepresentable_iff_isDeformationFunctor U).mp hU
  let K := residueFieldObject.{u, max v v₃, w} Λ k
  let uK : U.obj K := hUdef.1.some.default
  let x : (Functor.Elements.π U).Fiber K := ⟨U.elementsMk K uK, rfl⟩
  have h₀ : (fiberFunctor f K).EssSurj := by
    let Esp := Classical.choice hpre.specialFiber
    refine ⟨fun y => ?_⟩
    let x' := (fiberFunctor f K).obj x
    have hinv : Esp.inverse.obj (Esp.functor.obj x') =
        Esp.inverse.obj (Esp.functor.obj y) := congrArg Esp.inverse.obj (Subsingleton.elim _ _)
    exact ⟨x, ⟨Esp.unitIso.app x' ≪≫ eqToIso hinv ≪≫ (Esp.unitIso.app y).symm⟩⟩
  exact (presentationMorphism_isEquivalence_iff p U f.toFunctor f.w
    (presentationGroupoid p U f.toFunctor f.w hpre.cofibered) hpre.cofibered).2
      (essSurj_of_isSmooth_of_fiber_essSurj' f hpre.cofibered (hversal pushforwards) h₀)

/-- **Stacks Project, Tag 06L2.** Let `ℱ` be a deformation category over `𝒞_Λ` with
`dim_k Tℱ < ∞` and `dim_k Inf(ℱ) < ∞`. Then there is a minimal versal formal object `ξ` of
`ℱ`, say over `R`, and, with `U = R̲|_{𝒞_Λ}` and `f = ξ : U → ℱ` the associated morphism, the
groupoid in functors `(U, R, s, t, c)` constructed from `f` in Tag 06KY is a minimal smooth
prorepresentable groupoid in functors on `𝒞_Λ` with `[U/R] → ℱ` an equivalence.

The two `Fact` instances carry no content beyond `hp`; they make Tag 06IH's canonical
`k`-vector space structure on the tangent space available, so that the finite dimensionality
of `Tℱ` can be stated. -/
@[stacks 06L2]
public theorem exists_minimalPresentation [IsNoetherianRing Λ] [Module.Finite Λ k]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hp : IsDeformationCategory.{u, max v v₃, w} p)
    [h𝓕 : Fact (IsPredeformationCategory.{u, max v v₃, w} (BasedCategory.ofFunctor p).p)]
    [Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor p) h𝓕.out.cofibered)))]
    [FiniteDimensional k (tangentSpaceArtinian.{u, w, max v v₃} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor p) h𝓕.out.cofibered))]
    (hInf : ∀ (x : F) (_hbase : p.obj x = residueFieldObject.{u, max v v₃, w} Λ k)
      (PF : ChosenPushforwardsAt p x), FiniteDimensional k
        ↥((infinitesimalAutomorphismLinearLift.{u, max v v₃, w} PF hp.satisfiesRS).functor.obj
          (FGModuleCat.of k (ULift.{max v v₃} k)))) :
    Nonempty (MinimalPresentation.{u, v, w, u₃, v₃} p hp.predeformation.cofibered) := by
  classical
  let hpre := hp.predeformation
  have hS1 : SchlessingerConditionS1 p := schlessingerConditionS1_of_satisfiesRS hp.satisfiesRS
  have hS2 : SchlessingerConditionS2 p := schlessingerConditionS2_of_satisfiesRS hp.satisfiesRS
  obtain ⟨ξ, hminimal, -⟩ :=
    exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits.{u, max v v₃, w, u₃, v₃}
      Λ k (BasedCategory.ofFunctor p) hpre hS1 hS2 inferInstance
  let pushforwards : ChosenPushforwards p := chosenPushforwardsOfCofibered p hpre.cofibered
  let U := restrictedCoyoneda.{u, max v v₃ w, w} ξ.base
  let f := (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor
  have hU : IsProrepresentable U := ⟨ξ.base, ⟨Iso.refl _⟩⟩
  refine ⟨⟨ξ, pushforwards, hminimal,
    isSmooth_presentationGroupoid p U f hpre.cofibered (hminimal.1 pushforwards), ?_,
    isMinimal_presentationGroupoid p hpre.cofibered ξ pushforwards hminimal,
    isEquivalence_presentationMorphism p hpre ξ pushforwards hminimal.1⟩⟩
  -- prorepresentability, Tag 06L7
  obtain ⟨hUdef, -, -⟩ := (isProrepresentable_iff_isDeformationFunctor U).mp hU
  let uK : U.obj (residueFieldObject.{u, max v v₃, w} Λ k) := hUdef.1.some.default
  let y₀ : U.Elements := U.elementsMk (residueFieldObject.{u, max v v₃, w} Λ k) uK
  have hy₀ : p.obj (f.toFunctor.obj y₀) = residueFieldObject.{u, max v v₃, w} Λ k :=
    f.w_obj y₀
  let PF : ChosenPushforwardsAt p (f.toFunctor.obj y₀) :=
    chosenPushforwardsAtOfCofibered hpre.cofibered (f.toFunctor.obj y₀)
  exact isProrepresentable_presentationGroupoid.{u, v, w, u₃, v₃} p U f.toFunctor f.w
    hU hp PF (hInf (f.toFunctor.obj y₀) hy₀ PF)

end Presentation

end Deformation

end
