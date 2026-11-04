module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Schlessinger's conditions (S1) and (S2)

Schlessinger's conditions (S1) and (S2) on a functor on the base category,
the lifting of a section from the dual-number corner, and condition (S1) for the functor
associated to a cofibered category.

## Main definitions

* `PullbackCompletion` packages a completion over a prescribed
  square in the base.
* `IsDualNumberProjection` recognizes the map `k[ε] → k` in
  `𝒞_Λ` up to `Λ`-algebra isomorphism.
* `SchlessingerConditionS1` is condition (S1).
* `SchlessingerConditionS2` is condition (S2).

## Main results

* `isDualNumberProjection_iff` gives the coordinate
  characterization of the dual-number projection.
* `exists_section_iff_exists_dualNumberLift` is the section-lifting
  criterion under Schlessinger's condition (S2).
* `schlessingerConditionS1_objectsOverFunctor` transfers (S1).
* `schlessingerConditionS2_objectsOverFunctor` transfers (S2).
* `schlessingerConditionS1_of_isIsomorphismClasses`
  transfers (S1) to the associated functor of isomorphism classes.

## Implementation notes

### Schlessinger's conditions (S1) and (S2)

The completion clauses quantify over every prescribed pullback square in
`𝒞_Λ`.  A `PullbackCompletion` includes an equality from the image of its
apex to the prescribed pullback object and requires both projected arrows to
be the prescribed projections under that equality.  Consequently (S1) and
(S2) do not depend on a choice of pullback, while retaining the displayed
fibre product required in the source.  In the uniqueness clause of (S2), the
two completions use the same prescribed square, and the comparison arrow maps
to the equality-induced identity of its apex.  The dual-number projection is
recognized up to algebra isomorphism, so the condition is invariant under a
change of presentation of the two base objects.

### Lifting a section from the dual-number corner

The displayed fibre product in the source is expressed by `IsPullback` for
the image square. The dual-number projection is specified up to isomorphism
by `IsDualNumberProjection`. Commutativity of the square upstairs
is recorded separately from the pullback condition downstairs.

### Schlessinger conditions for objects over a fixed object

The two independent conditions are stated separately. The transfer uses only
the underlying functor and an object of its source: neither the cofibered-in-
groupoids property nor the requirement that the fixed object lie over the
residue field is needed for this assertion. Specializing the object to the
special fibre recovers the localization of the source.

### Schlessinger's condition (S1) for the associated functor

The associated functor is represented by a based category together with a
based functor realizing the fibrewise isomorphism-class construction.  This
also records the canonical action on morphisms in the base, rather than
choosing representatives of isomorphism classes separately at each object.

## References

* [Stacks Project, Tag 06HW](https://stacks.math.columbia.edu/tag/06HW)
* [Stacks Project, Tag 06I0](https://stacks.math.columbia.edu/tag/06I0)
* [Stacks Project, Tag 06IS](https://stacks.math.columbia.edu/tag/06IS)
* [Stacks Project, Tag 06SQ](https://stacks.math.columbia.edu/tag/06SQ)
-/

@[expose] public section

namespace Deformation

/-! ### Schlessinger's conditions (S1) and (S2) -/

section
open CategoryTheory
universe u v w u₁ v₁


/-- A completion of a cospan in a category over `C` over a prescribed square
in `C`.  The equality `apex_eq` and the two projection equations say that the
image of the completion is that square, not merely an isomorphic pullback
square. -/
public structure PullbackCompletion
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] (p : F ⥤ C) {x₁ x₂ x : F} (f₁ : x₁
      ⟶ x) (f₂ : x₂ ⟶ x) {A₁₂ : C} (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂) where
  /-- The object at the upper-left corner of the completed square. -/
  apex : F
  /-- The image of the apex is the prescribed upper-left base object. -/
  apex_eq : p.obj apex = A₁₂
  /-- The map from the completion to the first object. -/
  toFirst : apex ⟶ x₁
  /-- The map from the completion to the second object. -/
  toSecond : apex ⟶ x₂
  /-- The completed square commutes in the total category. -/
  comm : toSecond ≫ f₂ = toFirst ≫ f₁
  /-- The first arrow maps to the first prescribed projection. -/
  map_toFirst : p.map toFirst = eqToHom apex_eq ≫ g₁
  /-- The second arrow maps to the second prescribed projection. -/
  map_toSecond : p.map toSecond = eqToHom apex_eq ≫ g₂

/-- A morphism of `C_Λ` is the dual-number projection when, after
identifying its source with `k[ε]` and its target with `k`, its underlying
algebra homomorphism is the first projection. -/
public def IsDualNumberProjection
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {Aε A₀ : ArtinianLocalAlgCat.{u,
      v, w} Λ k} (e : Aε ⟶ A₀) : Prop :=
  ∃ (i₀ : A₀ ≃ₐ[Λ] k) (iε : Aε ≃ₐ[Λ] DualNumber k), i₀.toAlgHom.comp e.hom = (TrivSqZeroExt.fstHom Λ
    k k).comp iε.toAlgHom

/-- Characterization of a dual-number projection by compatible algebra
coordinates on its source and target. -/
public theorem isDualNumberProjection_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {Aε A₀ : ArtinianLocalAlgCat.{u,
      v, w} Λ k} (e : Aε ⟶ A₀) :
    IsDualNumberProjection e ↔ ∃ (i₀ : A₀ ≃ₐ[Λ] k) (iε : Aε ≃ₐ[Λ] DualNumber k), i₀.toAlgHom.comp
      e.hom = (TrivSqZeroExt.fstHom Λ k k).comp iε.toAlgHom := Iff.rfl

/-- Dual-number projections are stable under the transports attached to equal base objects. -/
public theorem isDualNumberProjection_eqToHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' B B' : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hA : A = A') (hB : B' = B) (f : A' ⟶ B') (hf : IsDualNumberProjection f) :
    IsDualNumberProjection (eqToHom hA ≫ f ≫ eqToHom hB) := by
  cases hA
  cases hB
  simpa using hf

/-- Schlessinger's condition (S1): every cospan whose second base map is
surjective has a completion over a pullback square in `C_Λ`. -/
@[stacks 06HW "condition (S1)", sga "7 VI 1.16" "(I)"]
public structure SchlessingerConditionS1
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {F : Type u₁} [Category.{v₁} F]
      (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) : Prop where
  /-- A cospan with a surjective second base map has a completion over its
  fibre product. -/
  completion : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x), Function.Surjective (p.map f₂).hom → ∀
    {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k} (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂),
      IsPullback g₂ g₁ (p.map f₂) (p.map f₁) → Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂)

/-- Schlessinger's condition (S2): completions exist when the second map is
the dual-number projection, and any two completions over the same base square
admit the required fibrewise comparison morphism. -/
@[stacks 06HW "condition (S2)"]
public structure SchlessingerConditionS2
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {F : Type u₁} [Category.{v₁} F]
      (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) : Prop where
  /-- A cospan over the dual-number projection has a completion over its
  fibre product. -/
  completion : ∀ {x xε x₀ : F} (d : x ⟶ x₀) (e : xε ⟶ x₀), IsDualNumberProjection (p.map e) → ∀ {Aε
    : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : Aε ⟶ p.obj x) (gε : Aε ⟶ p.obj xε), IsPullback gε g
      (p.map e) (p.map d) → Nonempty (PullbackCompletion p d e g gε)
  /-- Two such completions over the same base square admit a morphism in the
  common fibre through which their maps to `x` factor. -/
  comparison : ∀ {x xε x₀ : F} (d : x ⟶ x₀) (e : xε ⟶ x₀), IsDualNumberProjection (p.map e) → ∀ {Aε
    : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : Aε ⟶ p.obj x) (gε : Aε ⟶ p.obj xε), IsPullback gε g
      (p.map e) (p.map d) → ∀ (P Q : PullbackCompletion p d e g gε), ∃ b : P.apex ⟶ Q.apex,
        (P.toFirst = b ≫ Q.toFirst) ∧ (p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm)

end

/-! ### Lifting a section from the dual-number corner -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁


/-- **Stacks Project, Tag 06IS.** In a square over the pullback of an
Artinian local algebra and the dual numbers over the residue field, a section
of the first projection exists precisely when the bottom arrow lifts across
the dual-number projection. -/
@[stacks 06IS]
public theorem exists_section_iff_exists_dualNumberLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    {y xε x x₀ : F} (b : y ⟶ xε) (a : y ⟶ x)
    (e : xε ⟶ x₀) (d : x ⟶ x₀)
    (hcomm : b ≫ e = a ≫ d)
    (hdual : IsDualNumberProjection (p.map e))
    (hPB : IsPullback (p.map b) (p.map a) (p.map e) (p.map d)) :
    (∃ s : x ⟶ y, s ≫ a = 𝟙 x) ↔
      (∃ sε : x ⟶ xε, sε ≫ e = d) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ b, by rw [Category.assoc, hcomm, ← Category.assoc, hs, Category.id_comp]⟩
  · rintro ⟨sε, hsε⟩
    let σ : p.obj x ⟶ p.obj y :=
      hPB.lift (p.map sε) (𝟙 (p.obj x)) (by
        rw [← p.map_comp, hsε]
        simp)
    have hσb : σ ≫ p.map b = p.map sε := hPB.lift_fst _ _ _
    have hσa : σ ≫ p.map a = 𝟙 (p.obj x) := hPB.lift_snd _ _ _
    obtain ⟨zop, φ, hφ⟩ := hp.exists_lift σ.op (Opposite.op x) rfl
    let z : F := zop.unop
    let f : x ⟶ z := φ.unop
    have hbase : p.obj z = p.obj y := by
      simpa [z] using congrArg Opposite.unop (IsHomLift.domain_eq (p := p.op) σ.op φ)
    have hmap : p.map f = σ ≫ eqToHom hbase.symm := by
      simpa [z, f, Functor.op_map, Category.assoc] using
        congrArg (fun q => q.unop) (IsHomLift.fac' (p := p.op) σ.op φ)
    let ubase : p.obj z ⟶ p.obj xε := eqToHom hbase ≫ p.map b
    let rbase : p.obj z ⟶ p.obj x := eqToHom hbase ≫ p.map a
    have hfactorBase : (p.map f) ≫ ubase = p.map sε := by
      simp [ubase, hmap, Category.assoc, hσb]
    have hreturnBase : (p.map f) ≫ rbase = p.map (𝟙 x) := by
      simp [rbase, hmap, Category.assoc, hσa]
    obtain ⟨u, ⟨hmU, hfu⟩, -⟩ := existsUnique_factor_of_isHomLift hp f sε ubase hfactorBase
    obtain ⟨r, ⟨hmR, hfr⟩, -⟩ := existsUnique_factor_of_isHomLift hp f (𝟙 x) rbase hreturnBase
    let P : PullbackCompletion p d e (p.map a) (p.map b) := by
      refine ⟨z, hbase, r, u, ?_, ?_, ?_⟩
      · let gbase : p.obj z ⟶ p.obj x₀ := rbase ≫ p.map d
        have hgbase : gbase = ubase ≫ p.map e := by
          simpa [gbase, rbase, ubase, Category.assoc] using
            congrArg (fun q => eqToHom hbase ≫ q) hPB.w.symm
        have hfbase : p.map f ≫ gbase = p.map d := by
          simp [gbase, ← Category.assoc, hreturnBase]
        refine ((existsUnique_factor_of_isHomLift hp f d gbase hfbase).unique
          ⟨by simp [gbase, hmR], ?_⟩ ⟨by simpa [hmU] using hgbase.symm, ?_⟩).symm
        · rw [← Category.assoc, hfr, Category.id_comp]
        · rw [← Category.assoc, hfu, hsε]
      · simp [hmR, rbase]
      · simp [hmU, ubase]
    let Q : PullbackCompletion p d e (p.map a) (p.map b) :=
      ⟨y, rfl, a, b, hcomm, rfl, rfl⟩
    obtain ⟨v, hv, _⟩ := hS2.comparison d e hdual
      (p.map a) (p.map b) hPB P Q
    have hv' : r = v ≫ a := by simpa [P, Q] using hv
    exact ⟨f ≫ v, by rw [Category.assoc, ← hv', hfr]⟩

end

/-! ### Schlessinger conditions for objects over a fixed object -/

section
open CategoryTheory
universe u v w u₁ v₁

private def pullbackCompletionOver
    {F : Type u₁} [Category.{v₁} F]
    {C : Type u} [Category.{v} C]
    (p : F ⥤ C) (x : F) {x₁ x₂ x₃ : Over x}
    (f₁ : x₁ ⟶ x₃) (f₂ : x₂ ⟶ x₃)
    {A₁₂ : C} (g₁ : A₁₂ ⟶ p.obj x₁.left)
    (g₂ : A₁₂ ⟶ p.obj x₂.left)
    (H : PullbackCompletion p f₁.left f₂.left g₁ g₂) :
    PullbackCompletion
      (objectsOverFunctor p x)
      f₁ f₂ g₁ g₂ := by
  let z : Over x := Over.mk (H.toFirst ≫ x₁.hom)
  have hz₂ : H.toSecond ≫ x₂.hom = z.hom := by
    dsimp [z]
    simpa only [← f₂.w, ← f₁.w, Category.assoc] using
      congrArg (fun t => t ≫ x₃.hom) H.comm
  refine
    { apex := z
      apex_eq := H.apex_eq
      toFirst := Over.homMk H.toFirst (by rfl)
      toSecond := Over.homMk H.toSecond hz₂
      comm := ?_
      map_toFirst := ?_
      map_toSecond := ?_ }
  · ext; exact H.comm
  · change p.map H.toFirst = _; exact H.map_toFirst
  · change p.map H.toSecond = _; exact H.map_toSecond

/-- Condition (S1) passes to the category of objects over a fixed object. -/
@[stacks 06SQ "condition (S1)"]
public theorem schlessingerConditionS1_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (x : F)
    (hS1 : SchlessingerConditionS1 p) :
    SchlessingerConditionS1
      (objectsOverFunctor p x) := by
  refine ⟨?_⟩
  intro x₁ x₂ x₃ f₁ f₂ hf A₁₂ g₁ g₂ hpull
  obtain ⟨H⟩ := hS1.completion f₁.left f₂.left
    (by simpa only [objectsOverFunctor_map] using hf)
    g₁ g₂ (by simpa only [objectsOverFunctor_map] using hpull)
  exact ⟨pullbackCompletionOver p x f₁ f₂ g₁ g₂ H⟩

/-- Condition (S2) passes to the category of objects over a fixed object. -/
@[stacks 06SQ "condition (S2)"]
public theorem schlessingerConditionS2_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (x : F)
    (hS2 : SchlessingerConditionS2 p) :
    SchlessingerConditionS2
      (objectsOverFunctor p x) := by
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ x₃ f₁ f₂ hdual A₁₂ g₁ g₂ hpull
    obtain ⟨H⟩ := hS2.completion f₁.left f₂.left
      (by simpa only [objectsOverFunctor_map] using hdual)
      g₁ g₂ (by simpa only [objectsOverFunctor_map] using hpull)
    exact ⟨pullbackCompletionOver p x f₁ f₂ g₁ g₂ H⟩
  · intro x₁ x₂ x₃ f₁ f₂ hdual A₁₂ g₁ g₂ hpull P Q
    let P₀ : PullbackCompletion p f₁.left f₂.left g₁ g₂ :=
      ⟨P.apex.left, P.apex_eq, P.toFirst.left, P.toSecond.left,
        congrArg Over.Hom.left P.comm, P.map_toFirst, P.map_toSecond⟩
    let Q₀ : PullbackCompletion p f₁.left f₂.left g₁ g₂ :=
      ⟨Q.apex.left, Q.apex_eq, Q.toFirst.left, Q.toSecond.left,
        congrArg Over.Hom.left Q.comm, Q.map_toFirst, Q.map_toSecond⟩
    obtain ⟨b, hfirst, hmap⟩ := hS2.comparison f₁.left f₂.left
      (by simpa only [objectsOverFunctor_map] using hdual)
      g₁ g₂ (by simpa only [objectsOverFunctor_map] using hpull) P₀ Q₀
    have hfirst' : P.toFirst.left = b ≫ Q.toFirst.left := by simpa only [P₀, Q₀] using hfirst
    refine ⟨Over.homMk b ?_, ?_, ?_⟩
    · calc
        b ≫ Q.apex.hom = b ≫ (Q.toFirst.left ≫ x₁.hom) := by rw [← Q.toFirst.w]
        _ = (b ≫ Q.toFirst.left) ≫ x₁.hom := by rw [Category.assoc]
        _ = P.toFirst.left ≫ x₁.hom := by rw [hfirst']
        _ = P.apex.hom := P.toFirst.w
    · ext
      exact hfirst'
    · show p.map b = _
      exact hmap

end

/-! ### Schlessinger's condition (S1) for the associated functor -/

section
open CategoryTheory
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The associated functor of isomorphism classes of a category cofibered in
groupoids inherits Schlessinger's condition (S1). -/
@[stacks 06I0 "s1_associated_functor", sga "7 VI 1.13" "partial"]
public theorem schlessingerConditionS1_of_isIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    (hφ : IsIsomorphismClasses φ)
    (hS1 : SchlessingerConditionS1 𝓕.p) :
    SchlessingerConditionS1 𝓖.p := by
  let : φ.toFunctor.Full := hφ.full
  refine ⟨?_⟩
  intro y₁ y₂ y f₁ f₂ hf A₁₂ g₁ g₂ hpull
  let y₁f : Fiber 𝓖.p (𝓖.p.obj y₁) := ⟨y₁, rfl⟩
  let y₂f : Fiber 𝓖.p (𝓖.p.obj y₂) := ⟨y₂, rfl⟩
  let yf : Fiber 𝓖.p (𝓖.p.obj y) := ⟨y, rfl⟩
  obtain ⟨x₁, hx₁⟩ := (hφ.fiber_essSurj (𝓖.p.obj y₁)).mem_essImage y₁f
  obtain ⟨x₂, hx₂⟩ := (hφ.fiber_essSurj (𝓖.p.obj y₂)).mem_essImage y₂f
  obtain ⟨x, hx⟩ := (hφ.fiber_essSurj (𝓖.p.obj y)).mem_essImage yf
  let X₁ := Fiber.fiberInclusion.obj x₁
  let X₂ := Fiber.fiberInclusion.obj x₂
  let X := Fiber.fiberInclusion.obj x
  let i₁ : φ.toFunctor.obj X₁ ≅ y₁ :=
    Fiber.fiberInclusion.mapIso (Classical.choice hx₁)
  let i₂ : φ.toFunctor.obj X₂ ≅ y₂ :=
    Fiber.fiberInclusion.mapIso (Classical.choice hx₂)
  let i : φ.toFunctor.obj X ≅ y :=
    Fiber.fiberInclusion.mapIso (Classical.choice hx)
  let e₁ : 𝓖.p.obj (φ.toFunctor.obj X₁) ≅ 𝓖.p.obj y₁ := 𝓖.p.mapIso i₁
  let e₂ : 𝓖.p.obj (φ.toFunctor.obj X₂) ≅ 𝓖.p.obj y₂ := 𝓖.p.mapIso i₂
  let e : 𝓖.p.obj (φ.toFunctor.obj X) ≅ 𝓖.p.obj y := 𝓖.p.mapIso i
  rw [← φ.w] at hS1
  let f₁' : X₁ ⟶ X := φ.toFunctor.preimage (i₁.hom ≫ f₁ ≫ i.inv)
  let f₂' : X₂ ⟶ X := φ.toFunctor.preimage (i₂.hom ≫ f₂ ≫ i.inv)
  have hf₁' : φ.toFunctor.map f₁' = i₁.hom ≫ f₁ ≫ i.inv :=
    Functor.map_preimage _ _
  have hf₂' : φ.toFunctor.map f₂' = i₂.hom ≫ f₂ ≫ i.inv :=
    Functor.map_preimage _ _
  let g₁' : A₁₂ ⟶ (φ.toFunctor ⋙ 𝓖.p).obj X₁ := g₁ ≫ e₁.inv
  let g₂' : A₁₂ ⟶ (φ.toFunctor ⋙ 𝓖.p).obj X₂ := g₂ ≫ e₂.inv
  have hf' : Function.Surjective (((φ.toFunctor ⋙ 𝓖.p).map f₂').hom) := by
    have surj {A B : ArtinianLocalAlgCat Λ k} (j : A ≅ B) :
        Function.Surjective j.hom.hom := by
      intro b
      exact ⟨j.inv.hom b, congrArg (fun f : B ⟶ B => f.hom b) j.inv_hom_id⟩
    simpa [f₂', e₂, e, Functor.comp_map, hf₂', Category.assoc,
      Function.comp_assoc, ArtinianLocalAlgCat.comp_hom] using
      (surj e.symm).comp (hf.comp (surj e₂))
  have hpull' : IsPullback g₂' g₁'
      ((φ.toFunctor ⋙ 𝓖.p).map f₂') ((φ.toFunctor ⋙ 𝓖.p).map f₁') := by
    apply hpull.of_iso' (Iso.refl A₁₂) e₂ e₁ e
    · simp [g₂']
    · simp [g₁']
    · rw [Functor.comp_map, hf₂']
      simp [e₂, e, Functor.map_comp, Category.assoc]
    · rw [Functor.comp_map, hf₁']
      simp [e₁, e, Functor.map_comp, Category.assoc]
  obtain ⟨H⟩ := hS1.completion f₁' f₂' hf' g₁' g₂' hpull'
  refine ⟨{
    apex := φ.toFunctor.obj H.apex
    apex_eq := H.apex_eq
    toFirst := φ.toFunctor.map H.toFirst ≫ i₁.hom
    toSecond := φ.toFunctor.map H.toSecond ≫ i₂.hom
    comm := ?_
    map_toFirst := ?_
    map_toSecond := ?_ }⟩
  · have h₁ : i₁.hom ≫ f₁ = φ.toFunctor.map f₁' ≫ i.hom := by
      simpa [Category.assoc] using (congrArg (fun g => g ≫ i.hom) hf₁').symm
    have h₂ : i₂.hom ≫ f₂ = φ.toFunctor.map f₂' ≫ i.hom := by
      simpa [Category.assoc] using (congrArg (fun g => g ≫ i.hom) hf₂').symm
    simpa [Category.assoc, h₁, h₂, Functor.map_comp] using
      congrArg (fun z => φ.toFunctor.map z ≫ i.hom) H.comm
  · simpa [Functor.comp_map, e₁, g₁', Category.assoc] using
      congrArg (fun z => z ≫ e₁.hom) H.map_toFirst
  · simpa [Functor.comp_map, e₂, g₂', Category.assoc] using
      congrArg (fun z => z ≫ e₂.hom) H.map_toSecond

end

/-! ### Cocartesian lifts in a category cofibered in groupoids -/

section
open CategoryTheory
universe u v uF vF

/-- In a category cofibered in groupoids every morphism lying over `f` is strongly cocartesian
over `f`. -/
public lemma cofibered_strong
    {F : Type uF} [Category.{vF} F] {C : Type u} [Category.{v} C]
    (p : F ⥤ C) (hp : IsCofiberedInGroupoids p)
    {A B : C} {x y : F} (f : A ⟶ B) (i : x ⟶ y)
    (hi : p.IsHomLift f i) : Functor.IsStronglyCocartesian p f i := by
  subst_hom_lift p f i
  refine ⟨?_⟩
  intro z g ψ hψ
  have hcomm : g.op ≫ p.op.map i.op = p.op.map ψ.op := by
    show (p.map i ≫ g).op = (p.map ψ).op
    exact congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p _ ψ)
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := hp.unique_lift i.op ψ.op g.op hcomm
  refine ⟨χ.unop, ⟨?_, ?_⟩, ?_⟩
  · have heq : p.map χ.unop = g := congrArg Quiver.Hom.unop hχ
    rw [← heq]
    infer_instance
  · exact congrArg Quiver.Hom.unop hfac
  · intro θ ⟨hθ, hθfac⟩
    have heq : p.op.map θ.op = g.op :=
      congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p g θ).symm
    exact congrArg Quiver.Hom.unop (huniq θ.op ⟨heq, congrArg Quiver.Hom.op hθfac⟩)

end

/-! ### Pushforward, strictification, and (S1) from a versal formal object -/

section
open CategoryTheory
open IsLocalRing
universe u v w uF vF

/-- A composite of surjective maps of Artinian local algebras is surjective. -/
public lemma surjective_hom_comp
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f.hom) (hg : Function.Surjective g.hom) :
    Function.Surjective (f ≫ g).hom := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  refine ⟨x, ?_⟩
  show g.hom (f.hom x) = z
  exact (congrArg g.hom hx).trans hy

/-- The data of a pushforward of a formal object `X` along a map `f` of its base: a formal object
with base the target of `f`, together with a map from `X` lying over `f`. -/
public structure FormalPushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p)
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : X.base ⟶ S) where
  /-- The pushforward formal object. -/
  object : FormalObject p
  /-- The map from the original formal object. -/
  hom : X ⟶ object
  /-- Its base is the prescribed target. -/
  base_eq : object.base = S
  /-- The formal map lies over the prescribed base map. -/
  hom_base : hom.base = f ≫ eqToHom base_eq.symm

/-- A formal object can be pushed forward along any map of its base, level by level, through the
cocartesian lifts of the opposite functor. -/
public noncomputable def formal_pushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (X : FormalObject p)
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : X.base ⟶ S) : FormalPushforward (X := X) (S := S) f := by
  let a := f
  choose level app happ using fun n ↦
    hp.exists_lift ((AdicTruncation.functor n).map a).op
      (Opposite.op (X.level n)) (congrArg Opposite.op (X.level_eq n))
  let hlevel (n : ℕ) : p.op.obj (level n) =
      Opposite.op ((AdicTruncation.functor n).obj S) :=
    @IsHomLift.domain_eq _ _ _ _ p.op _ _ _ _
      (((AdicTruncation.functor n).map a).op) (app n) (happ n)
  have happUnop (n : ℕ) : p.IsHomLift
      ((AdicTruncation.functor n).map a) (app n).unop := by
    apply IsHomLift.of_fac p _ _ (X.level_eq n)
      (congrArg Opposite.unop (hlevel n))
    simpa using congrArg Quiver.Hom.unop
      (IsHomLift.fac p.op ((AdicTruncation.functor n).map a).op (app n))
  let d (n : ℕ) : p.op.obj (level n) ⟶ p.op.obj (level (n + 1)) :=
    eqToHom (hlevel n) ≫ (AdicTruncation.transition S n).op ≫
      eqToHom (hlevel (n + 1)).symm
  choose transition htransition _ using fun n ↦
    hp.unique_lift (app (n + 1)) (app n ≫ (X.transition n).op)
      (d n) (by
        have := happ n
        have := happ (n + 1)
        have hXt := X.transition_lift n
        have h0 := happUnop n
        have h1 := happUnop (n + 1)
        have := isHomLift_op p
          ((AdicTruncation.transitionNat n).app X.base)
          (X.transition n)
        have : p.op.IsHomLift
            (((AdicTruncation.functor n).map a).op ≫
              ((AdicTruncation.transitionNat n).app X.base).op)
            (app n ≫ (X.transition n).op) := by
          infer_instance
        apply map_comp_eq_of_lifts p.op
          ((AdicTruncation.functor (n + 1)).map a).op
          (((AdicTruncation.functor n).map a).op ≫
            ((AdicTruncation.transitionNat n).app X.base).op)
        apply Quiver.Hom.unop_inj
        exact (AdicTruncation.transitionNat n).naturality a)
  let Y : FormalObject p :=
    { base := S
      level := fun n ↦ (level n).unop
      level_eq := fun n ↦ congrArg Opposite.unop (hlevel n)
      transition := fun n ↦ (transition n).unop
      transition_lift := fun n ↦ by
        have : p.op.IsHomLift (d n) (transition n) := by
          rw [← (htransition n).1]
          infer_instance
        have := isHomLift_unop p (d n) (transition n)
        refine IsHomLift.of_fac' p
          ((AdicTruncation.transitionNat n).app S)
          (transition n).unop ?_ ?_ ?_
        · exact congrArg Opposite.unop (hlevel (n + 1))
        · exact congrArg Opposite.unop (hlevel n)
        · simpa [d, AdicTruncation.transitionNat] using
            (IsHomLift.fac p (d n).unop (transition n).unop).symm }
  let g : X ⟶ Y :=
    { base := a
      app := fun n ↦ (app n).unop
      app_lift := happUnop
      naturality := fun n ↦ by
        simpa [Y] using (congrArg Quiver.Hom.unop (htransition n).2).symm }
  exact ⟨Y, g, rfl, by rfl⟩

/-- Every object of the categorical pullback defining the restriction/completion equivalence is
isomorphic to a *strict* one, whose formal object has base literally `artinianToComplete` of
its Artinian component. -/
public lemma exists_strictified_restriction_object
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (e : RestrictionCompletionEquivalence p)
    (X : CategoryTheory.Limits.CategoricalPullback e.inclusion
      (FormalObject.projection (p := p))) :
    ∃ (P : CategoryTheory.Limits.CategoricalPullback e.inclusion
        (FormalObject.projection (p := p))),
      ∃ hbase : P.snd.base = artinianToComplete.obj P.fst,
        P.fst = X.fst ∧
        P.iso = e.inclusionIso.app P.fst ≪≫ (eqToIso hbase).symm ∧
        Nonempty (X ≅ P) := by
  let q := FormalObject.projection (p := p)
  let f : X.snd.base ⟶ artinianToComplete.obj X.fst :=
    X.iso.inv ≫ e.inclusionIso.hom.app X.fst
  let data := formal_pushforward hp X.snd f
  let Y := data.object
  let g := data.hom
  let hY := data.base_eq
  let f' := q.map g
  have hf' : f' = f ≫ eqToHom hY.symm := by
    simpa [f', q, g] using data.hom_base
  have hgLift : q.IsHomLift f' g := inferInstance
  have : Functor.IsStronglyCocartesian q f' g := cofibered_strong q
    (formalObjectProjection_isCofiberedInGroupoids p hp) f' g hgLift
  have : IsIso f' := by rw [hf']; dsimp [f]; infer_instance
  have : IsIso g := Functor.IsStronglyCocartesian.isIso_of_base_isIso q f' g
  let P : CategoryTheory.Limits.CategoricalPullback e.inclusion q :=
    ⟨X.fst, Y, e.inclusionIso.app X.fst ≪≫ (eqToIso hY).symm⟩
  have hcompat : e.inclusion.map (𝟙 X.fst) ≫ P.iso.hom = X.iso.hom ≫ q.map g := by
    show e.inclusion.map (𝟙 X.fst) ≫ P.iso.hom = X.iso.hom ≫ f'
    rw [hf']
    simp [P, f, Category.assoc]
  exact ⟨P, hY, rfl, by rfl,
    ⟨CategoryTheory.Limits.CategoricalPullback.mkIso (Iso.refl X.fst) (asIso g) hcompat⟩⟩

/-- Every object of `F` is, up to isomorphism, the image under the comparison functor of a strict
object of the categorical pullback. -/
public lemma exists_strict_representative
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (e : RestrictionCompletionEquivalence p) (x : F) :
    ∃ (X : CategoryTheory.Limits.CategoricalPullback e.inclusion
        (FormalObject.projection (p := p))),
      ∃ hbase : X.snd.base = artinianToComplete.obj X.fst,
        X.iso = e.inclusionIso.app X.fst ≪≫ (eqToIso hbase).symm ∧
        Nonempty (e.can.obj X ≅ x) := by
  have : e.can.IsEquivalence := e.isEquivalence
  let E := e.can.asEquivalence
  let X₀ := E.inverse.obj x
  let ε := E.counitIso.app x
  obtain ⟨X, hbase, -, hiso, hX⟩ := exists_strictified_restriction_object p hp e X₀
  rcases hX with ⟨i⟩
  exact ⟨X, hbase, hiso, ⟨(e.can.mapIso i).symm ≪≫ ε⟩⟩

/-- A morphism between strict objects of the categorical pullback lies over
`artinianToComplete.map` of its Artinian component on the nose. -/
public lemma strict_restriction_morphism_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (e : RestrictionCompletionEquivalence p)
    {X₂ X : CategoryTheory.Limits.CategoricalPullback e.inclusion
      (FormalObject.projection (p := p))}
    (g : X₂ ⟶ X)
    (h₂ : X₂.snd.base = artinianToComplete.obj X₂.fst)
    (h : X.snd.base = artinianToComplete.obj X.fst)
    (hi₂ : X₂.iso = e.inclusionIso.app X₂.fst ≪≫ (eqToIso h₂).symm)
    (hi : X.iso = e.inclusionIso.app X.fst ≪≫ (eqToIso h).symm) :
    (FormalObject.projection (p := p)).IsHomLift
      (artinianToComplete.map g.fst) g.snd := by
  let q := FormalObject.projection (p := p)
  have hnat := e.inclusionIso.hom.naturality g.fst
  have hbase : artinianToComplete.map g.fst ≫ eqToHom h.symm =
      eqToHom h₂.symm ≫ q.map g.snd := by
    apply (cancel_epi (e.inclusionIso.hom.app X₂.fst)).mp
    calc
      e.inclusionIso.hom.app X₂.fst ≫
          (artinianToComplete.map g.fst ≫ eqToHom h.symm) =
          (e.inclusion.map g.fst ≫ e.inclusionIso.hom.app X.fst) ≫ eqToHom h.symm := by
            rw [hnat]
            simp [Category.assoc]
      _ = e.inclusion.map g.fst ≫ X.iso.hom := by
            rw [hi]
            simp [Category.assoc]
      _ = X₂.iso.hom ≫ q.map g.snd := g.w
      _ = e.inclusionIso.hom.app X₂.fst ≫
          (eqToHom h₂.symm ≫ q.map g.snd) := by
            rw [hi₂]
            simp [Category.assoc]
  apply IsHomLift.of_fac q (artinianToComplete.map g.fst) g.snd h₂ h
  simpa using congrArg (· ≫ eqToHom h) hbase

/-- A morphism of the categorical pullback whose image under the comparison equivalence is, up to
isomorphisms on both sides, a surjection is surjective on the Artinian component. -/
public lemma surjective_fst_of_equivalence_preimage
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (e : RestrictionCompletionEquivalence p)
    {X₂ X : CategoryTheory.Limits.CategoricalPullback e.inclusion
      (FormalObject.projection (p := p))}
    {x₂ x : F} (d₂ : e.can.obj X₂ ≅ x₂) (d : e.can.obj X ≅ x)
    (f₂ : x₂ ⟶ x) (hf₂ : Function.Surjective (p.map f₂).hom)
    (q : X₂ ⟶ X) (hqmap : e.can.map q = d₂.hom ≫ f₂ ≫ d.inv) :
    Function.Surjective q.fst.hom := by
  have : e.can.IsEquivalence := e.isEquivalence
  have : e.can.Full := e.isEquivalence.full
  have : e.can.Faithful := e.isEquivalence.faithful
  have hα : p.map (e.can.map q) = p.map d₂.hom ≫ p.map f₂ ≫ p.map d.inv := by
    rw [hqmap, Functor.map_comp, Functor.map_comp]
  have hαsurj : Function.Surjective (p.map (e.can.map q)).hom := by
    rw [hα]
    exact surjective_hom_comp (p.map d₂.hom ≫ p.map f₂)
      (p.map d.inv)
      (surjective_hom_comp (p.map d₂.hom) (p.map f₂)
        (surjective_hom_of_isIso (p.map d₂.hom)) hf₂)
      (surjective_hom_of_isIso (p.map d.inv))
  let c₂ := e.canOver.hom.app X₂
  let c := e.canOver.hom.app X
  have hnat : p.map (e.can.map q) ≫ c = c₂ ≫ q.fst := by
    show (e.can ⋙ p).map q ≫ e.canOver.hom.app X =
      e.canOver.hom.app X₂ ≫ (CategoryTheory.Limits.CategoricalPullback.π₁
        e.inclusion (FormalObject.projection (p := p))).map q
    exact e.canOver.hom.naturality q
  intro y
  obtain ⟨z, hz⟩ := surjective_hom_of_isIso c y
  obtain ⟨w, hw⟩ := hαsurj z
  refine ⟨c₂.hom w, ?_⟩
  have hval : c.hom ((p.map (e.can.map q)).hom w) = q.fst.hom (c₂.hom w) :=
    congrArg (fun t => t.hom w) hnat
  exact hval.symm.trans ((congrArg c.hom hw).trans hz)

private theorem pullback_completion_of_common_source
    {F : Type uF} [Category.{vF} F]
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    {A₁₂ : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂)
    (hP : IsPullback g₂ g₁ (p.map f₂) (p.map f₁))
    (hp : IsCofiberedInGroupoids p)
    {z : F} (a₁ : z ⟶ x₁) (a₂ : z ⟶ x₂)
    (hcomm : a₁ ≫ f₁ = a₂ ≫ f₂) :
    Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂) := by
  let t := hP.lift (p.map a₂) (p.map a₁) (by
    simpa only [Functor.map_comp] using (congrArg (p.map) hcomm).symm)
  have ht₂ : t ≫ g₂ = p.map a₂ := by simp [t]
  have ht₁ : t ≫ g₁ = p.map a₁ := by simp [t]
  obtain ⟨yo, iop, hi⟩ := hp.exists_lift t.op (Opposite.op z) rfl
  let y : F := yo.unop
  let i : z ⟶ y := iop.unop
  have hy : p.obj y = A₁₂ := by
    simpa using congrArg (fun X : (ArtinianLocalAlgCat.{u, max v w, w} Λ k)ᵒᵖ => X.unop)
      (IsHomLift.domain_eq p.op t.op iop)
  cases hy
  have hiMap : p.map i = t := by
    simpa [i] using (congrArg Quiver.Hom.unop (IsHomLift.eq_of_isHomLift p.op t.op iop)).symm
  have hbase₁ : p.map i ≫ g₁ = p.map a₁ := by rw [hiMap, ht₁]
  have hbase₂ : p.map i ≫ g₂ = p.map a₂ := by rw [hiMap, ht₂]
  obtain ⟨b₁, hb₁, hfac₁⟩ := (existsUnique_factor_of_isHomLift hp i a₁ g₁ hbase₁).exists
  obtain ⟨b₂, hb₂, hfac₂⟩ := (existsUnique_factor_of_isHomLift hp i a₂ g₂ hbase₂).exists
  have hcomp : b₁ ≫ f₁ = b₂ ≫ f₂ := by
    let s := g₁ ≫ p.map f₁
    have hs : p.map i ≫ s = p.map (a₁ ≫ f₁) := by
      rw [← Category.assoc, hbase₁, Functor.map_comp]
    obtain ⟨c, hc, huniq⟩ := existsUnique_factor_of_isHomLift hp i (a₁ ≫ f₁) s hs
    have hc₁ : b₁ ≫ f₁ = c := huniq _ ⟨by simp [s, hb₁], by
      simpa [Category.assoc] using congrArg (fun q => q ≫ f₁) hfac₁⟩
    have hbase₂' : p.map (b₂ ≫ f₂) = s := by
      simp only [Functor.map_comp, hb₂, s]
      exact hP.w
    have hfac₂' : i ≫ (b₂ ≫ f₂) = a₁ ≫ f₁ := by
      rw [← Category.assoc, hfac₂, hcomm]
    have hc₂ : b₂ ≫ f₂ = c := huniq _ ⟨hbase₂', by
      simpa [Category.assoc] using hfac₂'⟩
    exact hc₁.trans hc₂.symm
  refine ⟨{
    apex := y
    apex_eq := rfl
    toFirst := b₁
    toSecond := b₂
    comm := hcomp.symm
    map_toFirst := ?_
    map_toSecond := ?_ }⟩
  · simpa using hb₁
  · simpa using hb₂

private lemma versal_formal_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (hξ : IsVersal hp ξ)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y x : FormalObject p} (g : y ⟶ x)
    (hg : (FormalObject.projection (p := p)).IsHomLift
      (artinianToComplete.map f) g)
    (a : ξ ⟶ x) : ∃ b : ξ ⟶ y, b ≫ g = a :=
  (isVersal_iff_lifts_artinian hp ξ).mp hξ f hf g hg a

/-- A predeformation category with a versal formal object satisfies
Schlessinger's condition (S1). -/
@[stacks 06SY]
public theorem schlessingerConditionS1_of_versal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) :
    SchlessingerConditionS1 p := by
  constructor
  intro x₁ x₂ x f₁ f₂ hf₂ A₁₂ g₁ g₂ hP
  let e := restrictionCompletionEquivalence p hp.cofibered
  have : e.can.IsEquivalence := e.isEquivalence
  let q := FormalObject.projection (p := p)
  obtain ⟨X₁, hbase₁, hiso₁, ⟨d₁⟩⟩ :=
    exists_strict_representative p hp.cofibered e x₁
  obtain ⟨X₂, hbase₂, hiso₂, ⟨d₂⟩⟩ :=
    exists_strict_representative p hp.cofibered e x₂
  obtain ⟨X, hbase, hiso, ⟨d⟩⟩ :=
    exists_strict_representative p hp.cofibered e x
  let q₁ : X₁ ⟶ X := e.can.preimage (d₁.hom ≫ f₁ ≫ d.inv)
  let q₂ : X₂ ⟶ X := e.can.preimage (d₂.hom ≫ f₂ ≫ d.inv)
  have hq₁ : e.can.map q₁ = d₁.hom ≫ f₁ ≫ d.inv := by simp [q₁]
  have hq₂ : e.can.map q₂ = d₂.hom ≫ f₂ ≫ d.inv := by simp [q₂]
  have hf₂' : Function.Surjective q₂.fst.hom :=
    surjective_fst_of_equivalence_preimage p e d₂ d f₂ hf₂ q₂ hq₂
  have hg₂ := strict_restriction_morphism_lift p e q₂ hbase₂ hbase hiso₂ hiso
  let u₁ : ξ ⟶ X₁.snd := Classical.choice
    (nonempty_hom_of_isVersal hp ξ X₁.snd hξ)
  obtain ⟨b, hb⟩ := versal_formal_lift p hp.cofibered ξ hξ q₂.fst hf₂'
    q₂.snd hg₂ (u₁ ≫ q₁.snd)
  obtain ⟨N₁, hN₁⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal X₁.fst).mp inferInstance
  obtain ⟨N₂, hN₂⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal X₂.fst).mp inferInstance
  obtain ⟨N, hN⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal X.fst).mp inferInstance
  let m := N₁ + N₂ + N
  have hm₁ : maximalIdeal X₁.fst ^ (m + 1) = ⊥ := pow_eq_zero_of_le (by omega) hN₁
  have hm₂ : maximalIdeal X₂.fst ^ (m + 1) = ⊥ := pow_eq_zero_of_le (by omega) hN₂
  have hmX : maximalIdeal X.fst ^ (m + 1) = ⊥ := pow_eq_zero_of_le (by omega) hN
  let l₁ := e.objIsoLevel X₁ m hm₁
  let l₂ := e.objIsoLevel X₂ m hm₂
  let l := e.objIsoLevel X m hmX
  let a₁ : ξ.level m ⟶ x₁ := u₁.app m ≫ l₁.inv ≫ d₁.hom
  let a₂ : ξ.level m ⟶ x₂ := b.app m ≫ l₂.inv ≫ d₂.hom
  have happ : b.app m ≫ q₂.snd.app m = u₁.app m ≫ q₁.snd.app m :=
    congrArg (fun z : ξ ⟶ X.snd => z.app m) hb
  have hrel : ∀ {x' : F} {X' : CategoryTheory.Limits.CategoricalPullback e.inclusion q}
      (d' : e.can.obj X' ≅ x') (f' : x' ⟶ x) (q' : X' ⟶ X) (hq : e.can.map q' = d'.hom ≫ f' ≫ d.inv)
      (hm' : maximalIdeal X'.fst ^ (m + 1) = ⊥),
      q'.snd.app m ≫ l.inv ≫ d.hom = (e.objIsoLevel X' m hm').inv ≫ d'.hom ≫ f' := by
    intro x' X' d' f' q' hq hm'
    have hn' := congrArg (fun k => (e.objIsoLevel X' m hm').inv ≫ k ≫ l.inv ≫ d.hom)
      (e.objIsoLevel_naturality q' m hm' hmX)
    calc
      q'.snd.app m ≫ l.inv ≫ d.hom = (e.objIsoLevel X' m hm').inv ≫
          (e.objIsoLevel X' m hm').hom ≫ q'.snd.app m ≫ l.inv ≫ d.hom := by simp
      _ = (e.objIsoLevel X' m hm').inv ≫ e.can.map q' ≫ l.hom ≫ l.inv ≫ d.hom := by
            simpa [Category.assoc] using hn'.symm
      _ = (e.objIsoLevel X' m hm').inv ≫ d'.hom ≫ f' := by rw [hq]; simp [Category.assoc]
  have hrel₁ : q₁.snd.app m ≫ l.inv ≫ d.hom = l₁.inv ≫ d₁.hom ≫ f₁ := hrel d₁ f₁ q₁ hq₁ hm₁
  have hrel₂ : q₂.snd.app m ≫ l.inv ≫ d.hom = l₂.inv ≫ d₂.hom ≫ f₂ := hrel d₂ f₂ q₂ hq₂ hm₂
  have hcomm : a₁ ≫ f₁ = a₂ ≫ f₂ := by
    simp only [a₁, a₂, Category.assoc, ← hrel₁, ← hrel₂, reassoc_of% happ]
  exact pullback_completion_of_common_source f₁ f₂ g₁ g₂ hP hp.cofibered
    a₁ a₂ hcomm

end

end Deformation
