module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionAction
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of families of cycles on fibres

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, let `r, e ≥ 0`,
let `α` be a family of `r`-cycles on the fibres of `X/Y` and let `β` be a family of `e`-cycles on
the fibres of `Y/S`. The *composition* `α ∘ β` is the family of `(r + e)`-cycles on the fibres of
`X/S` whose member over a point `s` of `S` is `(Y_s → Y)^*α ∩ β_s`: the base change of `α` to the
fibres of `X_s/Y_s` acting on the fibrewise cycle `β_s`, the action being taken over the base
`Spec κ(s)`. This file constructs that family, computes its coefficients, proves it bilinear and
proves it compatible with restriction to open subschemes.

## Main definitions

* `Stacks.Chow.baseChangeFamilyOfResidueIso` — the base change of a family of cycles along a
  morphism that induces an isomorphism on every residue field.
* `Stacks.Chow.compFiberIso` — the canonical isomorphism `X ×_Y Y_s ≅ X_s`.
* `Stacks.Chow.fiberMapOfComp` — the morphism `X_s ⟶ Y_s` of fibres induced by `f`.
* `Stacks.Chow.compFamily` — the composition `α ∘ β`.

## Main results

* `Stacks.Chow.compFamily_apply` — the coefficient of `α ∘ β` over `s` at a point `x` of `X_s` is
  the coefficient of `β_s` at the image of `x` in `Y_s` times the coefficient of `α` on the fibre
  of `f` through the image of `x` in `X`.
* `Stacks.Chow.compFamily_add_left`, `Stacks.Chow.compFamily_add_right` — bilinearity of the
  composition.
* `Stacks.Chow.restrictedFamily_compFamily` — the restriction of `α ∘ β` to `U` is `α|_U ∘ β|_V`.
* `Stacks.Chow.cap_compFamily` — associativity of the action: `(α ∘ β) ∩ γ = α ∩ (β ∩ γ)`.

## Implementation notes

The cycle `(Y_s → Y)^*α ∩ β_s` lives on `X ×_Y Y_s`, while the member over `s` of a family of
cycles on the fibres of `X/S` must live on `X_s`. The two schemes are canonically isomorphic, by
`Stacks.Chow.compFiberIso`, and the composition is the transport of the former cycle along that
isomorphism, which is restriction of cycles along an open immersion.

The base change of `α` needed here is along the inclusion `Y_s ⟶ Y` of a fibre, which is a
preimmersion and hence an isomorphism on residue fields. No base change of cycles along a field
extension therefore enters, and the fibrewise transport of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange` suffices; this is why
`Stacks.Chow.baseChangeFamilyOfResidueIso` is stated under that hypothesis.

Restriction of a family of cycles is formed from opens of both the source and the base, so the
restriction of `α ∘ β`, a family on the fibres of `X/S`, involves an open of `S` as well. The
compatibility with restriction is therefore stated for three opens `U ⊆ X`, `V ⊆ Y`, `W ⊆ S` with
`f(U) ⊆ V` and `g(V) ⊆ W`; the source's statement is the case `W = S`.

The two sides of the associativity relation `(α ∘ β) ∩ γ = α ∩ (β ∩ γ)` live in the groups of
cycles of δ-dimension `↑(r + e) + d` and `↑r + (↑e + d)` for the structure morphisms
`(f ≫ g) ≫ sS` and `f ≫ (g ≫ sS)`. Those groups are equal, but neither the associativity of
composition nor `Nat.cast_add` is a definitional identity, so the relation is stated between the
underlying cycles on `X`, of which both groups are subgroups.

## References

* [Stacks Project, Tag 0H6I](https://stacks.math.columbia.edu/tag/0H6I)
* [Stacks Project, Tag 0H6J](https://stacks.math.columbia.edu/tag/0H6J)
* [Stacks Project, Tag 0H6P](https://stacks.math.columbia.edu/tag/0H6P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Base change along a morphism that is an isomorphism on residue fields -/

/-- The base change of a family of `r`-cycles on the fibres of `X/S` along a morphism
`g : S' ⟶ S` which induces an isomorphism on every residue field: the fibre of the base change
`X ×_S S' ⟶ S'` over `t` is then isomorphic to the fibre of `X/S` over `g t`, and the member of
the base-changed family over `t` is the transport of the member over `g t`. -/
def baseChangeFamilyOfResidueIso {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ)
    (α : FamilyOfCycles f r) : FamilyOfCycles (pullback.snd f g) r :=
  fun t => fiberCycleAddEquiv f g t (hres t) r (α (g t))

/-- The coefficients of the base-changed family on the fibre over `t` are the coefficients of the
original family on the fibre over `g t`, read along the canonical map of fibres. -/
theorem baseChangeFamilyOfResidueIso_apply {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ)
    (α : FamilyOfCycles f r) (t : S') (x : (pullback.snd f g).fiber t) :
    (baseChangeFamilyOfResidueIso f g hres r α t :
        AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) :=
  fiberCycleAddEquiv_apply f g t (hres t) r (α (g t)) x

/-- Base change of families of cycles is additive. -/
theorem baseChangeFamilyOfResidueIso_add {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ)
    (α₁ α₂ : FamilyOfCycles f r) :
    baseChangeFamilyOfResidueIso f g hres r (α₁ + α₂) =
      baseChangeFamilyOfResidueIso f g hres r α₁ +
        baseChangeFamilyOfResidueIso f g hres r α₂ := by
  funext t
  exact (fiberCycleAddEquiv f g t (hres t) r).map_add (α₁ (g t)) (α₂ (g t))

/-! ### Coefficients of a family of cycles along a square -/

/-- The coefficient of a family of cycles on the fibres of `f` transported along an equality of
base points. -/
private theorem familyOfCycles_apply_congr {Z W : Scheme.{u}} (f : Z ⟶ W)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) {y z : W} (h : y = z)
    (x : f.fiber y) :
    (α y : AlgebraicCycle (f.fiber y) ℤ) x =
      (α z : AlgebraicCycle (f.fiber z) ℤ)
        (eqToHom (congrArg (fun t : W => f.fiber t) h) x) := by
  cases h
  rfl

/-- For a commutative square `j ≫ f = fU ≫ i`, the coefficient of a family of cycles on the
fibres of `f` at the image, under the canonical morphism of fibres, of the canonical fibre point
of a point `x` of `U` is its coefficient at the canonical fibre point of the image of `x` in
`X`. -/
theorem familyOfCycles_restrictedFiberMap_asFiber {X Y U V : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (fU : U ⟶ V) (j : U ⟶ X) (i : V ⟶ Y) (h : j ≫ f = fU ≫ i) {r : ℕ}
    (α : FamilyOfCycles f r) (x : U) :
    (α (i (fU x)) : AlgebraicCycle (f.fiber (i (fU x))) ℤ)
        (restrictedFiberMap f fU j i h (fU x) (fU.asFiber x)) =
      (α (f (j x)) : AlgebraicCycle (f.fiber (f (j x))) ℤ) (f.asFiber (j x)) := by
  rw [restrictedFiberMap_asFiber f fU j i h x]
  exact (familyOfCycles_apply_congr f α (congrArg (fun m : U ⟶ Y => m x) h) _).symm

/-- The coefficient of the restriction of a family of cycles to `U/V`, at the canonical point of
the fibre of `f|_U` through a point `x` of `U`, is the coefficient of the family at the canonical
point of the fibre of `f` through the image of `x` in `X`. -/
theorem restrictedFamily_apply_asFiber {X Y U V : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ Y) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (r : ℕ)
    (α : FamilyOfCycles f r) (x : U) :
    ((restrictedFamily f fU j i h r α).1 (fU x) : AlgebraicCycle (fU.fiber (fU x)) ℤ)
        (fU.asFiber x) =
      (α (f (j x)) : AlgebraicCycle (f.fiber (f (j x))) ℤ) (f.asFiber (j x)) := by
  rw [(restrictedFamily f fU j i h r α).2 (fU x) (fU.asFiber x)]
  exact familyOfCycles_restrictedFiberMap_asFiber f fU j i h α x

/-- Two restriction squares compose: if `f(U) ⊆ V` and `g(V) ⊆ W` then `(g ∘ f)(U) ⊆ W`, the
restricted morphism being the composite of the two restrictions. -/
theorem comp_restrictionSquare {D : Type*} [Category D] {X Y S U V W : D} {f : X ⟶ Y} {g : Y ⟶ S}
    {fU : U ⟶ V} {gV : V ⟶ W} {j : U ⟶ X} {i : V ⟶ Y} {k : W ⟶ S} (hU : j ≫ f = fU ≫ i)
    (hV : i ≫ g = gV ≫ k) : j ≫ f ≫ g = (fU ≫ gV) ≫ k := by
  rw [← Category.assoc, hU, Category.assoc, hV, Category.assoc]

/-! ### The two presentations of the fibre of a composite -/

variable {X Y S : Scheme.{u}}

/-- The canonical isomorphism `X ×_Y Y_s ≅ X_s` between the base change of `f : X ⟶ Y` along the
inclusion of the fibre of `g : Y ⟶ S` over `s` and the scheme-theoretic fibre of `f ≫ g` over
`s`. -/
def compFiberIso (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    pullback f (g.fiberι s) ≅ (f ≫ g).fiber s :=
  pullbackRightPullbackFstIso g (S.fromSpecResidueField s) f

/-- The morphism `X_s ⟶ Y_s` of scheme-theoretic fibres over `s` induced by `f : X ⟶ Y`. -/
def fiberMapOfComp (f : X ⟶ Y) (g : Y ⟶ S) (s : S) : (f ≫ g).fiber s ⟶ g.fiber s :=
  pullback.map (f ≫ g) (S.fromSpecResidueField s) g (S.fromSpecResidueField s) f (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The induced morphism of fibres is compatible with the inclusions of the fibres into the total
spaces. -/
@[reassoc]
theorem fiberMapOfComp_comp_fiberι (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberMapOfComp f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f := by
  dsimp only [fiberMapOfComp, Scheme.Hom.fiberι, Scheme.Hom.fiber, pullback.map]
  rw [pullback.lift_fst]

/-- The canonical isomorphism of fibres is compatible with the inclusions into `X`. -/
theorem fst_compFiberIso_inv (f : X ⟶ Y) (g : Y ⟶ S) (s : S) (x : (f ≫ g).fiber s) :
    pullback.fst f (g.fiberι s) ((compFiberIso f g s).inv x) = (f ≫ g).fiberι s x := by
  have h : (compFiberIso f g s).inv ≫ pullback.fst f (g.fiberι s) = (f ≫ g).fiberι s :=
    pullbackRightPullbackFstIso_inv_fst g (S.fromSpecResidueField s) f
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : (f ≫ g).fiber s ⟶ X => m x) h

/-- Read on the fibre `X_s` through the canonical isomorphism, the second projection of
`X ×_Y Y_s` is the induced morphism of fibres. -/
theorem snd_compFiberIso_inv (f : X ⟶ Y) (g : Y ⟶ S) (s : S) (x : (f ≫ g).fiber s) :
    pullback.snd f (g.fiberι s) ((compFiberIso f g s).inv x) = fiberMapOfComp f g s x := by
  apply (g.fiberι s).isEmbedding.injective
  have hcond := congrArg (fun m : pullback f (g.fiberι s) ⟶ Y => m ((compFiberIso f g s).inv x))
    (pullback.condition (f := f) (g := g.fiberι s))
  have hmap := congrArg (fun m : (f ≫ g).fiber s ⟶ Y => m x) (fiberMapOfComp_comp_fiberι f g s)
  simp only [Scheme.Hom.comp_apply] at hcond hmap
  rw [hmap, ← hcond, fst_compFiberIso_inv]

/-! ### The composition of two families of cycles on fibres -/

/-- **Stacks Project, Section 0H6H.** The composition `α ∘ β` of a family `α` of `r`-cycles on
the fibres of `X/Y` with a family `β` of `e`-cycles on the fibres of `Y/S`: the family of
`(r + e)`-cycles on the fibres of `X/S` whose member over `s` is the action `(Y_s → Y)^*α ∩ β_s`
over the base `Spec κ(s)`, read on `X_s` through the canonical isomorphism `X ×_Y Y_s ≅ X_s`. -/
def compFamily (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g]
    (r e : ℕ) (α : FamilyOfCycles f r) (β : FamilyOfCycles g e) :
    FamilyOfCycles (f ≫ g) (r + e) := fun s =>
  letI : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField s)))
  letI : LocallyOfFiniteType ((f ≫ g).fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (f ≫ g) (S.fromSpecResidueField s)))
  cycleGroupRestrict (fieldChowSituation (S.residueField s))
    (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)
    ((f ≫ g).fiberToSpecResidueField s) (compFiberIso f g s).inv
    (by
      dsimp only [compFiberIso, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι,
        Scheme.Hom.fiber]
      exact pullbackRightPullbackFstIso_inv_snd_snd g (S.fromSpecResidueField s) f)
    ((r : ℤ) + (e : ℤ))
    (cap (fieldChowSituation (S.residueField s)) (g.fiberToSpecResidueField s)
      (pullback.snd f (g.fiberι s))
      (baseChangeFamilyOfResidueIso f (g.fiberι s)
        (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) r α) (β s))

/-- The structure morphism of a fibre of a morphism locally of finite type is locally of finite
type. -/
private instance locallyOfFiniteType_fiberToSpecResidueField {Z : Scheme.{u}} (h : Z ⟶ S)
    [LocallyOfFiniteType h] (s : S) : LocallyOfFiniteType (h.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd h (S.fromSpecResidueField s)))

/-- The coefficient of `α ∘ β` over `s` at a point `x` of `X_s`: the coefficient of `β_s` at the
image of `x` in `Y_s`, times the coefficient of the member of `α` over the image `f ξ` of the
point `ξ` of `X` underlying `x`, read at the point of the fibre of `f` determined by `ξ`. -/
theorem compFamily_apply (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r) (β : FamilyOfCycles g e)
    (s : S) (x : (f ≫ g).fiber s) :
    (compFamily f g r e α β s : AlgebraicCycle ((f ≫ g).fiber s) ℤ) x =
      (β s : AlgebraicCycle (g.fiber s) ℤ) (fiberMapOfComp f g s x) *
        (α (f ((f ≫ g).fiberι s x)) :
            AlgebraicCycle (f.fiber (f ((f ≫ g).fiberι s x))) ℤ)
          (f.asFiber ((f ≫ g).fiberι s x)) := by
  have h0 : (compFamily f g r e α β s : AlgebraicCycle ((f ≫ g).fiber s) ℤ) x =
      (β s : AlgebraicCycle (g.fiber s) ℤ)
          (pullback.snd f (g.fiberι s) ((compFiberIso f g s).inv x)) *
        (baseChangeFamilyOfResidueIso f (g.fiberι s)
              (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) r α
              (pullback.snd f (g.fiberι s) ((compFiberIso f g s).inv x)) :
            AlgebraicCycle ((pullback.snd f (g.fiberι s)).fiber
              (pullback.snd f (g.fiberι s) ((compFiberIso f g s).inv x))) ℤ)
          ((pullback.snd f (g.fiberι s)).asFiber ((compFiberIso f g s).inv x)) := rfl
  rw [h0, baseChangeFamilyOfResidueIso_apply,
    familyOfCycles_restrictedFiberMap_asFiber f (pullback.snd f (g.fiberι s))
      (pullback.fst f (g.fiberι s)) (g.fiberι s) pullback.condition α
      ((compFiberIso f g s).inv x),
    fst_compFiberIso_inv, snd_compFiberIso_inv]

/-! ### Bilinearity -/

/-- **Stacks Project, Tag 0H6I.** The composition of families of cycles on fibres is additive in
the family on `X/Y`: `(α₁ + α₂) ∘ β = α₁ ∘ β + α₂ ∘ β`. -/
@[stacks 0H6I "additivity in the family on X/Y"]
theorem compFamily_add_left (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) (α₁ α₂ : FamilyOfCycles f r) (β : FamilyOfCycles g e) :
    compFamily f g r e (α₁ + α₂) β = compFamily f g r e α₁ β + compFamily f g r e α₂ β := by
  funext s
  change cycleGroupRestrict _ _ _ _ _ _
      (cap _ _ _ (baseChangeFamilyOfResidueIso f (g.fiberι s) _ r (α₁ + α₂)) _) = _
  rw [baseChangeFamilyOfResidueIso_add, cap_add_left, map_add]
  rfl

/-- **Stacks Project, Tag 0H6I.** The composition of families of cycles on fibres is additive in
the family on `Y/S`: `α ∘ (β₁ + β₂) = α ∘ β₁ + α ∘ β₂`. -/
@[stacks 0H6I "additivity in the family on Y/S"]
theorem compFamily_add_right (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r) (β₁ β₂ : FamilyOfCycles g e) :
    compFamily f g r e α (β₁ + β₂) = compFamily f g r e α β₁ + compFamily f g r e α β₂ := by
  funext s
  change cycleGroupRestrict _ _ _ _ _ _ (cap _ _ _ _ (β₁ s + β₂ s)) = _
  rw [cap_add_right, map_add]
  rfl

/-! ### Compatibility with restriction to opens -/

/-- A restriction square `j ≫ f = fU ≫ i` with `f` locally of finite type and `j` an open
immersion has `fU` locally of finite type. -/
private theorem locallyOfFiniteType_of_restrictionSquare {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] {j : U ⟶ X} [IsOpenImmersion j] (fU : U ⟶ V) (i : V ⟶ Y)
    [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) : LocallyOfFiniteType fU := by
  have : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
  exact locallyOfFiniteType_of_comp fU i

/-- **Stacks Project, Tag 0H6J.** If `U ⊆ X`, `V ⊆ Y` and `W ⊆ S` are open with `f(U) ⊆ V` and
`g(V) ⊆ W`, then the restriction of the composition `α ∘ β` to `U` is the composition of the
restriction of `α` to the fibres of `U/V` with the restriction of `β` to the fibres of `V/W`.
The source's statement is the case `W = S`. -/
@[stacks 0H6J]
theorem restrictedFamily_compFamily {U V W : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] (fU : U ⟶ V) (gV : V ⟶ W) (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ Y) [IsOpenImmersion i] (k : W ⟶ S) [IsOpenImmersion k]
    (hU : j ≫ f = fU ≫ i) (hV : i ≫ g = gV ≫ k) (r e : ℕ) (α : FamilyOfCycles f r)
    (β : FamilyOfCycles g e) :
    letI : LocallyOfFiniteType fU := by
      let : LocallyOfFiniteType (fU ≫ i) := hU ▸ inferInstance
      exact locallyOfFiniteType_of_comp fU i
    letI : LocallyOfFiniteType gV := by
      let : LocallyOfFiniteType (gV ≫ k) := hV ▸ inferInstance
      exact locallyOfFiniteType_of_comp gV k
    (restrictedFamily (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) (r + e)
        (compFamily f g r e α β)).1 =
      compFamily fU gV r e (restrictedFamily f fU j i hU r α).1
        (restrictedFamily g gV i k hV e β).1 := by
  have := locallyOfFiniteType_of_restrictionSquare fU i hU
  have := locallyOfFiniteType_of_restrictionSquare gV k hV
  funext s
  apply Subtype.ext
  ext x
  have hpoint : (f ≫ g).fiberι (k s)
      (restrictedFiberMap (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) s x) =
      j ((fU ≫ gV).fiberι s x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun φ : (fU ≫ gV).fiber s ⟶ X => φ x)
      (restrictedFiberMap_fiberι (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) s)
  have hfibreMap : fiberMapOfComp f g (k s)
      (restrictedFiberMap (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) s x) =
      restrictedFiberMap g gV i k hV s (fiberMapOfComp fU gV s x) := by
    apply (g.fiberι (k s)).isEmbedding.injective
    have hleft := congrArg (fun φ : (f ≫ g).fiber (k s) ⟶ Y =>
        φ (restrictedFiberMap (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) s x))
      (fiberMapOfComp_comp_fiberι f g (k s))
    have hright := congrArg (fun φ : gV.fiber s ⟶ Y => φ (fiberMapOfComp fU gV s x))
      (restrictedFiberMap_fiberι g gV i k hV s)
    have hlow := congrArg (fun φ : (fU ≫ gV).fiber s ⟶ V => φ x)
      (fiberMapOfComp_comp_fiberι fU gV s)
    have hsquare := congrArg (fun φ : U ⟶ Y => φ ((fU ≫ gV).fiberι s x)) hU
    simp only [Scheme.Hom.comp_apply] at hleft hright hlow hsquare
    rw [hleft, hright, hlow, hpoint]
    exact hsquare
  rw [(restrictedFamily (f ≫ g) (fU ≫ gV) j k (comp_restrictionSquare hU hV) (r + e)
      (compFamily f g r e α β)).2 s x,
    compFamily_apply, compFamily_apply, hfibreMap, hpoint,
    (restrictedFamily g gV i k hV e β).2 s (fiberMapOfComp fU gV s x),
    restrictedFamily_apply_asFiber f fU j i hU r α ((fU ≫ gV).fiberι s x)]

/-! ### Associativity of the action along a composition -/

/-- The morphism of fibres induced by `f` sends the canonical point of the fibre of `f ≫ g`
through `x` to the canonical point of the fibre of `g` through `f x`. -/
theorem fiberMapOfComp_asFiber (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x) = g.asFiber (f x) := by
  apply (g.fiberι ((f ≫ g) x)).isEmbedding.injective
  calc g.fiberι ((f ≫ g) x) (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x))
      = ((f ≫ g).fiberι ((f ≫ g) x) ≫ f) ((f ≫ g).asFiber x) :=
        congrArg (fun m : (f ≫ g).fiber ((f ≫ g) x) ⟶ Y => m ((f ≫ g).asFiber x))
          (fiberMapOfComp_comp_fiberι f g ((f ≫ g) x))
    _ = f x := by
        rw [Scheme.Hom.comp_apply ((f ≫ g).fiberι ((f ≫ g) x)) f ((f ≫ g).asFiber x),
          Scheme.Hom.fiberι_asFiber]
    _ = g.fiberι ((f ≫ g) x) (g.asFiber (f x)) := (Scheme.Hom.fiberι_asFiber g (f x)).symm

/-- The coefficient of `α ∘ β` at the canonical point of the fibre of `f ≫ g` through a point
`x` of `X` is the coefficient of `β` at the canonical point of the fibre of `g` through `f x`
times the coefficient of `α` at the canonical point of the fibre of `f` through `x`. -/
theorem compFamily_apply_asFiber (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r) (β : FamilyOfCycles g e) (x : X) :
    (compFamily f g r e α β ((f ≫ g) x) :
        AlgebraicCycle ((f ≫ g).fiber ((f ≫ g) x)) ℤ) ((f ≫ g).asFiber x) =
      (β ((f ≫ g) x) : AlgebraicCycle (g.fiber ((f ≫ g) x)) ℤ) (g.asFiber (f x)) *
        (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) := by
  rw [compFamily_apply, fiberMapOfComp_asFiber]
  exact congrArg
    (fun t : X => (β ((f ≫ g) x) : AlgebraicCycle (g.fiber ((f ≫ g) x)) ℤ) (g.asFiber (f x)) *
      (α (f t) : AlgebraicCycle (f.fiber (f t)) ℤ) (f.asFiber t))
    (Scheme.Hom.fiberι_asFiber (f ≫ g) x)

/-- **Stacks Project, Tag 0H6P.** Associativity of the action of families of cycles on fibres:
for `α` a family of `r`-cycles on the fibres of `X/Y`, `β` a family of `e`-cycles on the fibres
of `Y/S` and `γ` a `d`-cycle on `S`, we have `(α ∘ β) ∩ γ = α ∩ (β ∩ γ)` in `Z_{r + e + d}(X)`.
Each side carries its δ-dimension in its own type, so the relation is stated between the
underlying cycles on `X`. -/
@[stacks 0H6P]
theorem cap_compFamily (C : ChowSituation.{u}) (sS : S ⟶ C.S) [LocallyOfFiniteType sS]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) {d : ℤ}
    (α : FamilyOfCycles f r) (β : FamilyOfCycles g e) (γ : CycleGroup C sS d) :
    (cap C sS (f ≫ g) (compFamily f g r e α β) γ : AlgebraicCycle X ℤ) =
      (cap C (g ≫ sS) f α (cap C sS g β γ) : AlgebraicCycle X ℤ) := by
  ext x
  have hL : (cap C sS (f ≫ g) (compFamily f g r e α β) γ : AlgebraicCycle X ℤ) x =
      (γ : AlgebraicCycle S ℤ) ((f ≫ g) x) *
        (compFamily f g r e α β ((f ≫ g) x) :
          AlgebraicCycle ((f ≫ g).fiber ((f ≫ g) x)) ℤ) ((f ≫ g).asFiber x) := rfl
  have hR : (cap C (g ≫ sS) f α (cap C sS g β γ) : AlgebraicCycle X ℤ) x =
      (γ : AlgebraicCycle S ℤ) ((f ≫ g) x) *
          (β ((f ≫ g) x) : AlgebraicCycle (g.fiber ((f ≫ g) x)) ℤ) (g.asFiber (f x)) *
        (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) := rfl
  rw [hL, hR, compFamily_apply_asFiber]
  exact (mul_assoc _ _ _).symm

end Stacks.Chow

end
