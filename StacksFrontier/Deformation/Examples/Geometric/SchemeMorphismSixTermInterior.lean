module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismConjugationArrow
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismDerivationTangentArrow
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftConjAction
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftNamedTorsor
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTerm

/-!
# Exactness at the second, third and fourth spots of the sequence of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, let `P` and `Q` be *trivial*
first-order deformations of `X` and of `Y` over the square-zero extension of `k` by a
finite-dimensional vector space `M`, and let `ℓ₀ : P.scheme ⟶ Q.scheme` be a lift of `f` over the
base whose class in `T Def_{X ⟶ Y}` vanishes — the trivial deformation `(f' : X' → Y')` of the
source's proof. This file proves that the three interior spots of the sequence of
[Stacks Project, Tag 0E3V]

`Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X ⟶ Y} → T(Def_X × Def_Y)`

are exact.

The three computations are already in the library, as
`Deformation.exact_triple_of_simplyTransitive`: given a group acting simply transitively on the
lifts of `f`, a second group acting on them, the arrow `b` carrying the base lift where the
second group carries it, and the three geometric inputs — which pairs fix the base lift, when two
lifts give isomorphic deformations of `f`, and which deformations of `f` have trivial endpoints —
exactness at the three spots is formal. All three inputs are available
(`Deformation.Examples.exists_liftDeformationFiberAut_eq_iff`,
`Deformation.Examples.liftClass_eq_zero_iff`, `Deformation.Examples.exists_liftClass_iff`), and
so is the conjugation (`Deformation.Examples.globalLiftsOverBaseConj` with its two laws). The
two further things needed are the *translation* action as a term rather than inside an existential, and
the arrow `b` at the parametrisation those inputs use. This file supplies the second and uses
`Deformation.Examples.globalLiftsOverBaseVAdd` for the first.

## Main definitions

* `Deformation.Examples.globalLiftsOverBaseAutPair`: the acting group of the source's proof, the
  pairs `(α, β)` of infinitesimal automorphisms of the two endpoint deformations, bundled with
  their side conditions so that conjugation is a function of one argument.
* `Deformation.Examples.globalLiftsOverBaseAutPairConj`: conjugation as an action of that group.
* `Deformation.Examples.liftDeformationAutPair`: **the arrow `a`** at the base lift, the pair of
  endpoint components of an automorphism of the deformation of `f` determined by `ℓ₀`.
* `Deformation.Examples.globalLiftsOverBaseDerivationVAdd`: the named translation action of
  `Der_k(𝒪_Y, f_*𝒪_X)` on the lifts, which is
  `Deformation.Examples.globalLiftsOverBaseVAdd` with the acting group carried onto the third
  term of the source's sequence by
  `Deformation.Examples.schemeMorphismDerivationsEquivHom`.
* `Deformation.Examples.globalLiftsOverBaseConjDerivation`: **the arrow `b`** at the pair
  parametrisation — the unique element of the third term carrying `ℓ₀` where `(α, β)` carries it.

## Main results

* `Deformation.Examples.exact_schemeMorphismSixTerm_interior`: **Tag 0E3V, exactness at the
  second, third and fourth spots.**
* `Deformation.Examples.globalLiftsOverBaseAutPairConj_ofDerivations_val` and
  `Deformation.Examples.globalLiftsOverBaseConjDerivation_ofDerivations`: **the reconciliation of
  the two conjugation conventions.** `Deformation.Examples.globalLiftsOverBaseConj` forms
  `α⁻¹ ≫ ℓ ≫ β`, whereas `Stacks.Thickenings.conjugateBaseLift` forms
  `(u ⬝ 𝟙) ≫ a' ≫ (v ⬝ 𝟙)` with the source factor **not** inverted. So the two parametrisations
  of the source side differ by a **sign**: the pair attached to `(u, v)` is
  `((-u) ⬝ 𝟙, v ⬝ 𝟙)`, and at that pair the arrow `b` of this file is the arrow
  `Deformation.Examples.schemeMorphismConjugationArrow`.
* `Deformation.Examples.globalLiftsOverBaseConj_eq_iff` and
  `Deformation.Examples.globalLiftsOverBaseAutPairConj_eq_iff`: which pair carries one lift to
  another.
* `Deformation.Examples.existsUnique_globalLiftsOverBaseDerivationVAdd` and
  `Deformation.Examples.globalLiftsOverBaseDerivationVAdd_conjDerivation`: simple transitivity of
  the named action based at `ℓ₀`, and the characterising property of `b`.

## Implementation notes

**Which presentation of each term the arrows are stated at.** The source's `Inf` terms are
tangent spaces of automorphism functors (`Deformation.localizedAutomorphismFunctorTangent`), and
the arrow `Deformation.Examples.schemeMorphismInfinitesimalPair` is the `k`-linear map
between those. The exactness statement here is **not** stated at that presentation: its first
term is the automorphism group of the deformation of `f` determined by `ℓ₀` in the fibre over the
square-zero extension, and its second is
`Deformation.Examples.globalLiftsOverBaseAutPair`. Both are honest presentations of the two `Inf`
terms — `Deformation.Examples.morphismFiberAutEquivSelfMapPairs` identifies the first with the
compatible pairs of self-maps — and they are the presentations the three geometric inputs are
stated at, so taking them costs no transport. What is *not* claimed is that the arrow between
them is `Deformation.Examples.schemeMorphismInfinitesimalPair`; bridging to that arrow needs the
identification of `Deformation.localizedAutomorphismFunctorTangent` with the self-maps, which is
`Deformation.Examples.localizedTangentEquivSelfMaps`, and is not done here.

The third and fourth terms, by contrast, are the source's on the nose:
`Deformation.Examples.schemeMorphismDerivations f pY` is the third term
`Der_k(𝒪_Y, f_*𝒪_X)`, the arrow out of it is
`Deformation.Examples.schemeMorphismDerivationTangentMap` at the named action, and the arrow out
of `T Def_{X ⟶ Y}` is `Deformation.Examples.schemeMorphismTangentPair`.

**The `k`-linearity of the arrows is not established.** `Function.Exact` is a statement about
bare functions, and that is all that is proved: the second and third terms here carry no
`k`-module structure that the arrows are shown to respect. For the arrow out of the derivations
the obstruction is recorded in the implementation notes of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismDerivationTangentArrow.lean` — the
addition on the tangent module is Schlessinger's and the library has no lemma computing it on
classes of objects of a fibre. So the sequence of the source, which is a sequence of `k`-vector
spaces and `k`-linear maps, is **not** fully established even with these three spots; the
`PARTIAL` Tag 0E3V marker of
`Deformation.Examples.schemeMorphismDeformation_endpointArrows` stays where it is, on the same
statement.

**Why the conormal trivialisation `eC` is carried.** The acting group of
[Stacks Project, Tag 0CK2] is `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/P.scheme})`, and it is the third term
of the source's sequence only once the conormal sheaf of the special-fibre immersion is
trivialised. `Deformation.Examples.deformationConormalIsoUnit` supplies `eC` when the base
carries a dual-number coordinate, which is the source's case; it is a parameter here, exactly as
in `Deformation.Examples.schemeMorphismConjugationArrow`.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The group of pairs of infinitesimal automorphisms of the endpoints -/

/-- **The acting group of the source's proof**: the pairs `(α, β)` of invertible self-maps of
the total spaces of two deformations, each over the base and each fixing its special-fibre
immersion.

The side conditions are bundled with the pair so that conjugating a lift by it is a function of
one argument, which is what the `gact` hypothesis of
`Deformation.exact_triple_of_simplyTransitive` asks for;
`Deformation.Examples.globalLiftsOverBaseConj` takes them as five separate arguments.

That `α` is over the base is listed, although for a pair compatible with a lift it follows
(`Deformation.Examples.comp_deformationAmbientToBase_of_lift_comm`): the group has to be defined
before any lift is chosen. -/
def globalLiftsOverBaseAutPair (P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX))
    (Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)) (e : Q.base ⟶ P.base) :
    Type u :=
  { p : (P.scheme ⟶ P.scheme) × (Q.scheme ⟶ Q.scheme) //
    IsIso p.1 ∧ IsIso p.2 ∧
      p.1 ≫ deformationAmbientToBase P e = deformationAmbientToBase P e ∧
      P.specialMap ≫ p.1 = P.specialMap ∧
      p.2 ≫ Q.toBase = Q.toBase ∧ Q.specialMap ≫ p.2 = Q.specialMap }

section Interior

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} [IsIso e]

omit [IsIso e] in
/-- **A pair carrying one lift to another is over the base on the source side as well.** If
`ℓ.1 ≫ β = α ≫ ℓ'.1` and `β` is over the base, then so is `α`: composing the equation with the
structure morphism of `Q.scheme` turns both sides into the structure morphism of `P.scheme`,
because `ℓ` and `ℓ'` are lifts over the base and `β` is over the base.

This is the condition that `Deformation.Examples.liftClass_eq_zero_iff` and
`Deformation.Examples.liftDeformationFiberAutEquivCompatiblePairs` do not list and
`Deformation.Examples.globalLiftsOverBaseAutPair` does. -/
theorem comp_deformationAmbientToBase_of_lift_comm (ℓ ℓ' : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme}
    (hβb : β ≫ Q.toBase = Q.toBase) (hcomm : ℓ.1 ≫ β = α ≫ ℓ'.1) :
    α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e :=
  calc α ≫ deformationAmbientToBase P e
      = α ≫ ℓ'.1 ≫ Q.toBase := by rw [ℓ'.2.1]
    _ = (α ≫ ℓ'.1) ≫ Q.toBase := (Category.assoc _ _ _).symm
    _ = (ℓ.1 ≫ β) ≫ Q.toBase := by rw [hcomm]
    _ = ℓ.1 ≫ β ≫ Q.toBase := Category.assoc _ _ _
    _ = ℓ.1 ≫ Q.toBase := by rw [hβb]
    _ = deformationAmbientToBase P e := ℓ.2.1

/-- **Conjugating a lift, as an action of the bundled pairs.**
`Deformation.Examples.globalLiftsOverBaseConj` with the five side conditions read off the pair.
This is the `gact` of `Deformation.exact_triple_of_simplyTransitive`; its two action laws are
`Deformation.Examples.globalLiftsOverBaseConj_id` and
`Deformation.Examples.globalLiftsOverBaseConj_comp`, which that theorem does not use. -/
def globalLiftsOverBaseAutPairConj (g : globalLiftsOverBaseAutPair pX pY P Q e)
    (ℓ : globalLiftsOverBase f P Q e) : globalLiftsOverBase f P Q e :=
  globalLiftsOverBaseConj f pX pY ℓ g.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1 g.2.2.2.2.2.2

omit [IsIso e] in
/-- The conjugate is `β ∘ ℓ ∘ α⁻¹`, in the source's notation `β⁻¹ ∘ f' ∘ α` read at the inverse
pair. -/
theorem globalLiftsOverBaseAutPairConj_val (g : globalLiftsOverBaseAutPair pX pY P Q e)
    (ℓ : globalLiftsOverBase f P Q e) :
    (globalLiftsOverBaseAutPairConj f pX pY g ℓ).1 =
      (letI := g.2.1; CategoryTheory.inv g.1.1) ≫ ℓ.1 ≫ g.1.2 := rfl

/-! ### The arrow `a` -/

/-- **The arrow `a` of [Stacks Project, Tag 0E3V] at a lift**: an automorphism of the deformation
of `f` determined by `ℓ₀`, read as the pair of its two endpoint components.

`Deformation.Examples.liftDeformationFiberAutEquivCompatiblePairs` delivers the pair together
with four of the six side conditions and the compatibility `ℓ₀ ∘ α = β ∘ ℓ₀`; the fifth, that
`α` is over the base, is that compatibility read through
`Deformation.Examples.comp_deformationAmbientToBase_of_lift_comm`.

This is **not** `Deformation.Examples.schemeMorphismInfinitesimalPair`, which is the same arrow
between the tangent spaces of the automorphism functors; see the implementation notes of this
file. -/
def liftDeformationAutPair (ℓ₀ : globalLiftsOverBase f P Q e)
    (x : Aut (morphismDeformationFiberObj f pX pY hf (liftDeformationObject f pX pY hf ℓ₀))) :
    globalLiftsOverBaseAutPair pX pY P Q e :=
  ⟨(liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).1,
    (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.1,
    (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.1,
    comp_deformationAmbientToBase_of_lift_comm f pX pY ℓ₀ ℓ₀
      (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.2.1
      (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.2.2.2.2,
    (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.2.2.1,
    (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.2.1,
    (liftDeformationFiberAutEquivCompatiblePairs f pX pY hf ℓ₀ x).2.2.2.2.2.1⟩

/-- **The `ha` input of `Deformation.exact_triple_of_simplyTransitive`.** A pair of
infinitesimal automorphisms of the two endpoint deformations comes from an automorphism of the
deformation of `f` determined by `ℓ₀` exactly when it fixes `ℓ₀` under conjugation — the source's
"`(α, β)` comes from an infinitesimal automorphism of `f'` exactly when it commutes with `f'`".

This is `Deformation.Examples.exists_liftDeformationFiberAut_eq_iff` with the pair bundled: an
equality in `Deformation.Examples.globalLiftsOverBaseAutPair` is an equality of the underlying
pairs, the side conditions being propositions. -/
theorem exists_liftDeformationAutPair_eq_iff (ℓ₀ : globalLiftsOverBase f P Q e)
    (g : globalLiftsOverBaseAutPair pX pY P Q e) :
    (∃ x, liftDeformationAutPair f pX pY hf ℓ₀ x = g) ↔
      globalLiftsOverBaseAutPairConj f pX pY g ℓ₀ = ℓ₀ := by
  rw [globalLiftsOverBaseAutPairConj,
    ← exists_liftDeformationFiberAut_eq_iff f pX pY hf ℓ₀ g.2.1 g.2.2.1 g.2.2.2.1
      g.2.2.2.2.1 g.2.2.2.2.2.1 g.2.2.2.2.2.2]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩,
    fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

omit [IsIso e] in
/-- **The conjugate of a lift, read off an explicit inverse of the source factor.**
`Deformation.Examples.globalLiftsOverBaseConj_val` with `CategoryTheory.inv α` replaced by a
given right inverse of `α`, so that no `CategoryTheory.inv` survives in the conclusion. -/
theorem globalLiftsOverBaseConj_val_of_hom_inv_id (ℓ : globalLiftsOverBase f P Q e)
    {α α' : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase) (hsβ : Q.specialMap ≫ β = Q.specialMap)
    (hinv : α ≫ α' = 𝟙 P.scheme) :
    (globalLiftsOverBaseConj f pX pY ℓ hα hαb hsα hβb hsβ).1 = α' ≫ ℓ.1 ≫ β := by
  rw [globalLiftsOverBaseConj_val, IsIso.inv_eq_of_hom_inv_id hinv]

omit [IsIso e] in
/-- **Which pair of infinitesimal automorphisms carries one lift to another.**
`Deformation.Examples.globalLiftsOverBaseConj_eq_self_iff` with the conjugate compared to a
second lift rather than to `ℓ` itself; at `ℓ' = ℓ` it is that statement. -/
theorem globalLiftsOverBaseConj_eq_iff (ℓ ℓ' : globalLiftsOverBase f P Q e)
    {α : P.scheme ⟶ P.scheme} {β : Q.scheme ⟶ Q.scheme} (hα : IsIso α)
    (hαb : α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e)
    (hsα : P.specialMap ≫ α = P.specialMap)
    (hβb : β ≫ Q.toBase = Q.toBase) (hsβ : Q.specialMap ≫ β = Q.specialMap) :
    globalLiftsOverBaseConj f pX pY ℓ hα hαb hsα hβb hsβ = ℓ' ↔ ℓ.1 ≫ β = α ≫ ℓ'.1 := by
  let := hα
  refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
  · subst h
    rw [globalLiftsOverBaseConj_val, IsIso.hom_inv_id_assoc]
  · rw [globalLiftsOverBaseConj_val, h, IsIso.inv_hom_id_assoc]

omit [IsIso e] in
/-- `Deformation.Examples.globalLiftsOverBaseConj_eq_iff` for the bundled pair. -/
theorem globalLiftsOverBaseAutPairConj_eq_iff (g : globalLiftsOverBaseAutPair pX pY P Q e)
    (ℓ ℓ' : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseAutPairConj f pX pY g ℓ = ℓ' ↔ ℓ.1 ≫ g.1.2 = g.1.1 ≫ ℓ'.1 :=
  globalLiftsOverBaseConj_eq_iff f pX pY ℓ ℓ' g.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1
    g.2.2.2.2.2.2

omit [IsIso e] in
/-- `Deformation.Examples.globalLiftsOverBaseConj_val_of_hom_inv_id` for the bundled pair. -/
theorem globalLiftsOverBaseAutPairConj_val_of_inv (g : globalLiftsOverBaseAutPair pX pY P Q e)
    (ℓ : globalLiftsOverBase f P Q e) {α' : P.scheme ⟶ P.scheme}
    (hinv : g.1.1 ≫ α' = 𝟙 P.scheme) :
    (globalLiftsOverBaseAutPairConj f pX pY g ℓ).1 = α' ≫ ℓ.1 ≫ g.1.2 :=
  globalLiftsOverBaseConj_val_of_hom_inv_id f pX pY ℓ g.2.1 g.2.2.2.1 g.2.2.2.2.1
    g.2.2.2.2.2.1 g.2.2.2.2.2.2 hinv

/-! ### The named action of the third term on the global lifts -/

variable (eC : Stacks.Thickenings.conormalModules P.specialMap ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)

/-- **The named action of the third term `Der_k(𝒪_Y, f_*𝒪_X)` on the global lifts of `f`.**
`Deformation.Examples.globalLiftsOverBaseVAdd` with the acting group carried from
`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/P.scheme})` onto the third term of the source's sequence by
`Deformation.Examples.schemeMorphismDerivationsEquivHom`, which is an isomorphism of additive
groups, so the two action laws and simple transitivity transport unchanged. -/
def globalLiftsOverBaseDerivationVAdd (ℓ₀ : globalLiftsOverBase f P Q e)
    (D : schemeMorphismDerivations f pY) (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBase f P Q e :=
  globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀
    (schemeMorphismDerivationsEquivHom f pY P.specialMap eC D) ℓ

omit [IsIso e] in
/-- **The zero derivation acts trivially**, the `hact0` input of
`Deformation.exact_triple_of_simplyTransitive`. -/
theorem globalLiftsOverBaseDerivationVAdd_zero (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ 0 ℓ = ℓ := by
  rw [globalLiftsOverBaseDerivationVAdd, map_zero, globalLiftsOverBaseVAdd_zero]

omit [IsIso e] in
/-- **The action law**, the `hactadd` input of
`Deformation.exact_triple_of_simplyTransitive`: translating by a sum is translating twice. -/
theorem globalLiftsOverBaseDerivationVAdd_add (ℓ₀ : globalLiftsOverBase f P Q e)
    (D D' : schemeMorphismDerivations f pY) (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ (D + D') ℓ =
      globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ D
        (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ D' ℓ) := by
  rw [globalLiftsOverBaseDerivationVAdd, globalLiftsOverBaseDerivationVAdd,
    globalLiftsOverBaseDerivationVAdd, map_add, globalLiftsOverBaseVAdd_add]

omit [IsIso e] in
/-- **Simple transitivity of the named action, based at `ℓ₀`.** Every lift of `f` to the pair of
deformations is the translate of `ℓ₀` by exactly one element of the third term. This is the
`htrans` input of `Deformation.exact_triple_of_simplyTransitive`, and it is
[Stacks Project, Tag 0CK2] with its acting function named. -/
theorem existsUnique_globalLiftsOverBaseDerivationVAdd (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    ∃! D : schemeMorphismDerivations f pY,
      globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ D ℓ₀ = ℓ := by
  obtain ⟨θ, hθ, huniq⟩ := existsUnique_globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ ℓ
  refine ⟨(schemeMorphismDerivationsEquivHom f pY P.specialMap eC).symm θ, ?_, fun D hD => ?_⟩
  · simpa only [globalLiftsOverBaseDerivationVAdd, AddEquiv.apply_symm_apply] using hθ
  · rw [← huniq _ hD, AddEquiv.symm_apply_apply]

/-! ### The arrow `b` -/

/-- **The arrow `b` of [Stacks Project, Tag 0E3V] at the pair parametrisation**: the unique
element of the third term `Der_k(𝒪_Y, f_*𝒪_X)` carrying `ℓ₀` where the pair `(α, β)` carries it.

In the source's notation: a pair of infinitesimal automorphisms of the two endpoint deformations
differs from compatibility with `f'` by a derivation, and this is that derivation. It is a term
because the translation action is named (`Deformation.Examples.globalLiftsOverBaseVAdd`) and its
bijection with the lifts based at `ℓ₀`
(`Deformation.Examples.globalLiftsOverBaseDerivationEquiv`) can simply be inverted.

`Deformation.Examples.globalLiftsOverBaseConjDerivation_ofDerivations` identifies it with
`Deformation.Examples.schemeMorphismConjugationArrow` — the same arrow parametrised by the
pairs of derivations presenting the two infinitesimal automorphisms, with a sign on the source
side. -/
def globalLiftsOverBaseConjDerivation (ℓ₀ : globalLiftsOverBase f P Q e)
    (g : globalLiftsOverBaseAutPair pX pY P Q e) : schemeMorphismDerivations f pY :=
  (schemeMorphismDerivationsEquivHom f pY P.specialMap eC).symm
    ((globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).symm
      (globalLiftsOverBaseAutPairConj f pX pY g ℓ₀))

omit [IsIso e] in
/-- **The characterising property of `b`**: translating `ℓ₀` by `b(α, β)` carries it exactly
where conjugating it by `(α, β)` carries it. This is the `hb` input of
`Deformation.exact_triple_of_simplyTransitive`. -/
theorem globalLiftsOverBaseDerivationVAdd_conjDerivation (ℓ₀ : globalLiftsOverBase f P Q e)
    (g : globalLiftsOverBaseAutPair pX pY P Q e) :
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
        (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ g) ℓ₀ =
      globalLiftsOverBaseAutPairConj f pX pY g ℓ₀ := by
  rw [globalLiftsOverBaseDerivationVAdd, globalLiftsOverBaseConjDerivation,
    AddEquiv.apply_symm_apply, globalLiftsOverBaseVAdd_base, Equiv.apply_symm_apply]

/-! ### Reconciling the two conjugation conventions -/

variable (hsqj : Q.specialMap.ker ^ 2 = ⊥)

/-- **The pair of infinitesimal automorphisms attached to a pair of derivations, with the sign on
the source side.** A derivation `u` presents the self-map `u ⬝ 𝟙` of the total space, which is
invertible (`Stacks.Thickenings.isIso_derivationActionGlobal_self`), over the base
(`Stacks.Thickenings.derivationActionGlobal_self_comp_base`) and fixes the special fibre
(`Stacks.Thickenings.comp_derivationActionGlobal_self`), so a pair `(u, v)` gives a pair of
infinitesimal automorphisms.

**The source factor is `(-u) ⬝ 𝟙`, not `u ⬝ 𝟙`.** `Deformation.Examples.globalLiftsOverBaseConj`
inverts its source factor and `Stacks.Thickenings.conjugateBaseLift` does not, so the pair whose
conjugation agrees with conjugating by `(u, v)` is the one whose source factor is the self-map of
the *negative* derivation — the inverse of `u ⬝ 𝟙` being `(-u) ⬝ 𝟙`. -/
def globalLiftsOverBaseAutPairOfDerivations
    (u : Stacks.Smooth.pullbackCotangentSheaf (P.specialMap ≫ deformationAmbientToBase P e)
      (𝟙 X) ⟶ Stacks.Thickenings.conormalModules P.specialMap)
    (v : Stacks.Smooth.pullbackCotangentSheaf (Q.specialMap ≫ Q.toBase) (𝟙 Y) ⟶
      Stacks.Thickenings.conormalModules Q.specialMap)
    (comm_i : P.specialMap ≫ (𝟙 P.scheme : P.scheme ⟶ P.scheme) =
      (𝟙 X : X ⟶ X) ≫ P.specialMap)
    (comm_j : Q.specialMap ≫ (𝟙 Q.scheme : Q.scheme ⟶ Q.scheme) =
      (𝟙 Y : Y ⟶ Y) ≫ Q.specialMap) :
    globalLiftsOverBaseAutPair pX pY P Q e :=
  ⟨(Stacks.Thickenings.derivationActionGlobal (ker_specialMap_pow_two_eq_bot P hm) (-u) comm_i,
      Stacks.Thickenings.derivationActionGlobal hsqj v comm_j),
    Stacks.Thickenings.isIso_derivationActionGlobal_self
      (ker_specialMap_pow_two_eq_bot P hm) comm_i (-u),
    Stacks.Thickenings.isIso_derivationActionGlobal_self hsqj comm_j v,
    Stacks.Thickenings.derivationActionGlobal_self_comp_base
      (ker_specialMap_pow_two_eq_bot P hm) (-u) comm_i,
    Stacks.Thickenings.comp_derivationActionGlobal_self
      (ker_specialMap_pow_two_eq_bot P hm) (-u) comm_i,
    Stacks.Thickenings.derivationActionGlobal_self_comp_base hsqj v comm_j,
    Stacks.Thickenings.comp_derivationActionGlobal_self hsqj v comm_j⟩

omit [IsIso e] in
/-- **The two conjugation conventions differ by a sign on the source side.** Conjugating a lift
by the pair of infinitesimal automorphisms attached to `(u, v)` — whose source factor is the
self-map of `-u` — is the thickening-level conjugate
`(u ⬝ 𝟙) ≫ ℓ ≫ (v ⬝ 𝟙)` of `Stacks.Thickenings.conjugateBaseLift`.

This is the direction the arrow `b` is read in: `Deformation.exact_triple_of_simplyTransitive`
consumes conjugation at the pair parametrisation, and the thickening-level arrow is stated
at the derivation parametrisation, so what is needed is the value of the former at the pair the
latter corresponds to. The only input is that the inverse of `u ⬝ 𝟙` is `(-u) ⬝ 𝟙`, which rests
on `Stacks.Thickenings.derivationActionGlobal_zero`. -/
theorem globalLiftsOverBaseAutPairConj_ofDerivations_val (ℓ : globalLiftsOverBase f P Q e)
    (u : Stacks.Smooth.pullbackCotangentSheaf (P.specialMap ≫ deformationAmbientToBase P e)
      (𝟙 X) ⟶ Stacks.Thickenings.conormalModules P.specialMap)
    (v : Stacks.Smooth.pullbackCotangentSheaf (Q.specialMap ≫ Q.toBase) (𝟙 Y) ⟶
      Stacks.Thickenings.conormalModules Q.specialMap)
    (comm_i : P.specialMap ≫ (𝟙 P.scheme : P.scheme ⟶ P.scheme) =
      (𝟙 X : X ⟶ X) ≫ P.specialMap)
    (comm_j : Q.specialMap ≫ (𝟙 Q.scheme : Q.scheme ⟶ Q.scheme) =
      (𝟙 Y : Y ⟶ Y) ≫ Q.specialMap) :
    (globalLiftsOverBaseAutPairConj f pX pY
        (globalLiftsOverBaseAutPairOfDerivations pX pY hm hsqj u v comm_i comm_j) ℓ).1 =
      Stacks.Thickenings.conjugateBaseLift (ker_specialMap_pow_two_eq_bot P hm) hsqj ℓ.1 u v
        comm_i comm_j := by
  have hinv : (globalLiftsOverBaseAutPairOfDerivations pX pY hm hsqj u v comm_i comm_j).1.1 ≫
      Stacks.Thickenings.derivationActionGlobal (ker_specialMap_pow_two_eq_bot P hm) u comm_i =
      𝟙 P.scheme := by
    show Stacks.Thickenings.derivationActionGlobal (ker_specialMap_pow_two_eq_bot P hm) (-u)
        comm_i ≫ Stacks.Thickenings.derivationActionGlobal
          (ker_specialMap_pow_two_eq_bot P hm) u comm_i = 𝟙 P.scheme
    simpa only [neg_neg] using Stacks.Thickenings.derivationActionGlobal_self_comp_neg
      (ker_specialMap_pow_two_eq_bot P hm) comm_i (-u)
  rw [globalLiftsOverBaseAutPairConj_val_of_inv f pX pY _ ℓ hinv]
  rfl

omit [IsIso e] in
/-- **The arrow `b` at the pair parametrisation is the arrow `b` at the derivation
parametrisation.** `Deformation.Examples.globalLiftsOverBaseConjDerivation` at the pair attached
to `(u, v)` is `Deformation.Examples.schemeMorphismConjugationArrow` at `(u, v)`.

Both are the unique element of the third term carrying `ℓ₀` to one and the same lift, by
`Deformation.Examples.globalLiftsOverBaseAutPairConj_ofDerivations_val`; the simple transitivity
of [Stacks Project, Tag 0CK2] then forces them equal. This is what ties the exactness statement
of this file to the arrow `b` the library already carries. -/
theorem globalLiftsOverBaseConjDerivation_ofDerivations (ℓ₀ : globalLiftsOverBase f P Q e)
    (u : Stacks.Smooth.pullbackCotangentSheaf (P.specialMap ≫ deformationAmbientToBase P e)
      (𝟙 X) ⟶ Stacks.Thickenings.conormalModules P.specialMap)
    (v : Stacks.Smooth.pullbackCotangentSheaf (Q.specialMap ≫ Q.toBase) (𝟙 Y) ⟶
      Stacks.Thickenings.conormalModules Q.specialMap)
    (comm_i : P.specialMap ≫ (𝟙 P.scheme : P.scheme ⟶ P.scheme) =
      (𝟙 X : X ⟶ X) ≫ P.specialMap)
    (comm_j : Q.specialMap ≫ (𝟙 Q.scheme : Q.scheme ⟶ Q.scheme) =
      (𝟙 Y : Y ⟶ Y) ≫ Q.specialMap) :
    globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀
        (globalLiftsOverBaseAutPairOfDerivations pX pY hm hsqj u v comm_i comm_j) =
      schemeMorphismConjugationArrow f pY eC (ker_specialMap_pow_two_eq_bot P hm) hsqj
        Q.specialCartesian (specialMap_comp_deformationAmbientToBase (X := Over.mk pX)
          (Y := Over.mk pY) f hf P e) ℓ₀.1 ℓ₀.2.2 ℓ₀.2.1 comm_i comm_j (u, v) := by
  rw [globalLiftsOverBaseConjDerivation, schemeMorphismConjugationArrow]
  refine congrArg (schemeMorphismDerivationsEquivHom f pY P.specialMap eC).symm ?_
  refine (Equiv.symm_apply_eq _).mpr (Subtype.ext ?_)
  refine (globalLiftsOverBaseAutPairConj_ofDerivations_val f pX pY hm hsqj ℓ₀ u v
    comm_i comm_j).trans ?_
  exact (Stacks.Thickenings.derivationActionGlobalEquivOfBase_conjugationDerivation
    (ker_specialMap_pow_two_eq_bot P hm) hsqj Q.specialCartesian
    (specialMap_comp_deformationAmbientToBase (X := Over.mk pX) (Y := Over.mk pY) f hf P e)
    ℓ₀.1 ℓ₀.2.2 ℓ₀.2.1 u v comm_i comm_j).symm

end Interior

/-! ### Exactness at the three interior spots -/

section Exactness

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}

/-- **Stacks 0E3V, exactness at the second, third and fourth spots.** Let `f : X ⟶ Y` be a
morphism of schemes over `k`, let `P` and `Q` be first-order deformations of `X` and of `Y` over
the square-zero extension of `k` by `M` whose classes in the tangent modules of `Def_X` and of
`Def_Y` vanish — the *trivial* deformations of the source's proof — let the maximal ideal of their
common base have square zero, let `eC` trivialise the conormal sheaf of the special fibre of `P`,
and let `ℓ₀` be a lift of `f` to that pair whose class in `T Def_{X ⟶ Y}` vanishes. Then the
three interior spots of the source's sequence

`Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X ⟶ Y} → T(Def_X × Def_Y)`

are exact.

All five maps are in hand: `a` is `Deformation.Examples.liftDeformationAutPair`, `b` is
`Deformation.Examples.globalLiftsOverBaseConjDerivation`, the arrow out of the derivations is
`Deformation.Examples.schemeMorphismDerivationTangentMap` at the named action
`Deformation.Examples.globalLiftsOverBaseDerivationVAdd`, and the arrow out of
`T Def_{X ⟶ Y}` is `Deformation.Examples.schemeMorphismTangentPair`. The content is
`Deformation.exact_triple_of_simplyTransitive` fed with
`Deformation.Examples.exists_liftDeformationAutPair_eq_iff` (`ha`),
`Deformation.Examples.liftClass_eq_zero_iff` (`hcls`) and
`Deformation.Examples.exists_liftClass_iff` (`hc`).

**The two `Inf` terms are presented as automorphism groups, not as tangent spaces of automorphism
functors**, and the arrow between them is therefore not
`Deformation.Examples.schemeMorphismInfinitesimalPair`; and `Function.Exact` is a statement about
bare functions, so no `k`-linearity of any arrow is asserted. See the implementation notes of
this file. -/
theorem exact_schemeMorphismSixTerm_interior
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    (hP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ = 0)
    (eC : Stacks.Thickenings.conormalModules P.specialMap ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)
    (ℓ₀ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)))
    (h0 : liftClass f pX pY hf hM M hQ ℓ₀ = 0) :
    Function.Exact (liftDeformationAutPair f pX pY hf ℓ₀)
        (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀) ∧
      Function.Exact (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀)
          (schemeMorphismDerivationTangentMap f pX pY hf hM M hQ
            (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀) ℓ₀) ∧
        Function.Exact (schemeMorphismDerivationTangentMap f pX pY hf hM M hQ
            (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀) ℓ₀)
          (schemeMorphismTangentPair f pX pY hf hM hX hY M) := by
  have hcls : ∀ θ : schemeMorphismDerivations f pY,
      liftClass f pX pY hf hM M hQ
          (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ θ ℓ₀) = 0 ↔
        ∃ g : globalLiftsOverBaseAutPair pX pY P Q (eqToHom (hQ.trans hP.symm)),
          globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ θ ℓ₀ =
            globalLiftsOverBaseAutPairConj f pX pY g ℓ₀ := by
    intro θ
    refine (liftClass_eq_zero_iff f pX pY hf hM M hQ ℓ₀
      (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ θ ℓ₀) h0).trans ⟨?_, ?_⟩
    · rintro ⟨α, β, hα, hβ, hβb, hsα, hsβ, hcomm⟩
      exact ⟨⟨(α, β), hα, hβ,
          comp_deformationAmbientToBase_of_lift_comm f pX pY ℓ₀ _ hβb hcomm, hsα, hβb, hsβ⟩,
        ((globalLiftsOverBaseAutPairConj_eq_iff f pX pY _ ℓ₀ _).mpr hcomm).symm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1.1, g.1.2, g.2.1, g.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.2,
        (globalLiftsOverBaseAutPairConj_eq_iff f pX pY g ℓ₀ _).mp hg.symm⟩
  exact exact_triple_of_simplyTransitive
    (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀)
    (globalLiftsOverBaseAutPairConj f pX pY) ℓ₀
    (globalLiftsOverBaseDerivationVAdd_zero f pX pY hf eC hm ℓ₀)
    (globalLiftsOverBaseDerivationVAdd_add f pX pY hf eC hm ℓ₀)
    (existsUnique_globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀)
    (liftDeformationAutPair f pX pY hf ℓ₀)
    (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀)
    (liftClass f pX pY hf hM M hQ)
    (schemeMorphismDerivationTangentMap f pX pY hf hM M hQ
      (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀) ℓ₀)
    (schemeMorphismTangentPair f pX pY hf hM hX hY M)
    (globalLiftsOverBaseDerivationVAdd_conjDerivation f pX pY hf eC hm ℓ₀)
    (exists_liftDeformationAutPair_eq_iff f pX pY hf ℓ₀) (fun _ => rfl) hcls
    (exists_liftClass_iff f pX pY hf hM hX hY M hP hQ hP0 hQ0)

end Exactness

end Deformation.Examples

end
