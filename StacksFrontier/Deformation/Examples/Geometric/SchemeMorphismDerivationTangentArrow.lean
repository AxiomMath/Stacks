module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftClass
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftGroup
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftNamedTorsorDerivations

/-!
# The arrow `Der_k(𝒪_Y, f_*𝒪_X) ⟶ T Def_{X ⟶ Y}` of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. The fourth arrow of the six-term
exact sequence of [Stacks Project, Tag 0E3V] goes from the third term `Der_k(𝒪_Y, f_*𝒪_X)` to
the tangent space of the deformation category of `f`: a `k`-derivation translates the lifts of
`f` to a pair of first-order deformations of its endpoints, and the first-order deformation of
`f` that the translate of a base lift carries is the image of the derivation.

This file builds that arrow. The two halves it is assembled from are available: the derivations act
simply transitively on the lifts ([Stacks Project, Tag 0CK2] at a pair of deformations,
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`) and a lift has a
class in the tangent module of `Def_{X ⟶ Y}`
(`Deformation.Examples.liftClass`, the `cls` map of the source's proof).

## Main definitions

* `Deformation.Examples.schemeMorphismDerivationTangentMap`: **the arrow
  `Der_k(𝒪_Y, f_*𝒪_X) ⟶ T Def_{X ⟶ Y}`**, the class of the translate of a base lift.

## Main results

* `Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase`:
  the derivations act simply transitively on the **global** lifts of `f` to a pair of
  deformations, which is the shape `Deformation.Examples.liftClass` consumes. Its witness is the
  named action `Deformation.Examples.schemeMorphismLiftsVAdd`, so the existential is a
  consequence of a definition rather than a second formalization of
  [Stacks Project, Tag 0CK2].
* `Deformation.Examples.schemeMorphismDerivationTangentMap_apply`: the arrow is the class of the
  translate. This is the `hδ` input of
  `Deformation.exact_triple_of_simplyTransitiveVAdd`, supplied by a construction rather than
  carried as a hypothesis.
* `Deformation.Examples.schemeMorphismDerivationTangentMap_zero`: the zero derivation goes to
  the class of the base lift.
* `Deformation.Examples.exists_schemeMorphismDerivationTangentMap_eq_liftClass`: every class of
  a lift of `f` is a value of the arrow.
* `Deformation.Examples.schemeMorphismTangentPair_schemeMorphismDerivationTangentMap`: the
  composite of this arrow with the next one vanishes, when the two endpoint deformations are
  trivial. This is the complex property at the fifth spot of the source's sequence, not
  exactness there.

## Implementation notes

**The action is a parameter of the arrow, but a named action exists and is what callers
supply.** `Deformation.Examples.schemeMorphismDerivationTangentMap` takes the acting function
`act` and the base lift `ℓ₀` as arguments, and the facts proved about it here carry the laws of
the action they use as hypotheses, exactly as
`Deformation.exact_triple_of_simplyTransitive` and `Deformation.map_add_of_simplyTransitive` do.
That is a parametrisation, not an absence: the action of [Stacks Project, Tag 0CK2] on these
lifts **is** named, by `Deformation.Examples.globalLiftsOverBaseVAdd` on the group of global
homomorphisms, by `Deformation.Examples.schemeMorphismLiftsVAdd` on the derivations
`Der_k(𝒪_Y, f_*N)`, and by `Deformation.Examples.globalLiftsOverBaseDerivationVAdd` on the third
term `Der_k(𝒪_Y, f_*𝒪_X)` itself; all three have their laws proved, and
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` is now
*derived* from the second of them.

**Which is why no statement here should be read as being about an arbitrary action.** The three
torsor laws do not pin an acting function — composing one with any automorphism of the acting
group gives another satisfying all three — so a lemma about `schemeMorphismDerivationTangentMap`
quantified over an arbitrary `act` with those laws says nothing about the geometric arrow. The
lemmas below are therefore tools for a caller that has pinned `act`, not statements about the
arrow of the source; the statement about the arrow of the source is
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`, which instantiates `act` at
`Deformation.Examples.globalLiftsOverBaseDerivationVAdd`.

**Why a bare function here, and where the `k`-linear map is.** The source asserts that this
arrow is `k`-linear. The addition on `T Def_{X ⟶ Y}` is the one Schlessinger's condition (S2)
produces, so additivity is not a formal consequence of the torsor laws: it compares that addition
with the action of [Stacks Project, Tag 0CK2], which needs the naturality of the action in the
base object of `𝒞_Λ`. That naturality is now
`Deformation.Examples.globalLiftsOverBasePushforward_vadd` (with the transport
`Deformation.Examples.liftActionTransport` and its value
`Deformation.Examples.liftActionTransport_crossScaling` at the coordinate scaling), in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftBaseNaturality.lean`, and the
arrow is packaged as a `k`-linear map at the trivial data in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismDerivationTangentLinearMap.lean`. The
function here stays parametrised by the action, for the reason in the previous paragraph.

**The coefficient sheaf.** As in
`Deformation.Examples.deformationHomSectionsTopLinearEquiv` and
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`, the conormal sheaf
of the special-fibre immersion is identified with an arbitrary `𝒪_X`-module `N` rather than with
`𝒪_X` on the nose, so that a square-zero base whose maximal ideal has any finite rank is
covered. The source's case is `N = 𝒪_X`, where
`Deformation.Examples.schemeMorphismDerivations f pY` is the domain on the nose and
`Deformation.Examples.deformationConormalIsoUnit` supplies the identification.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (SDerivation)
open Stacks.Thickenings (immersionConormalSheaf)

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The derivations act simply transitively on the global lifts -/

include hf in
/-- **The third term of the sequence of [Stacks Project, Tag 0E3V] acts simply transitively on
the global lifts of `f`.** For deformations `P` of `X` and `Q` of `Y` with a morphism
`e : Q.base ⟶ P.base` of `𝒞_Λ`, a square-zero maximal ideal on `P.base` and a lift `ℓ₀` of `f`
over `baseSpec Q.base`, the derivations `Der_k(𝒪_Y, f_*N)` act simply transitively on the
morphisms `P.scheme ⟶ Q.scheme` over the base that restrict to `f`.

**The witness is a named definition**: it is `Deformation.Examples.schemeMorphismLiftsVAdd`, and
the three clauses are `Deformation.Examples.schemeMorphismLiftsVAdd_zero`,
`Deformation.Examples.schemeMorphismLiftsVAdd_add` and
`Deformation.Examples.existsUnique_schemeMorphismLiftsVAdd`. So the existential here is not an
independent formalization of [Stacks Project, Tag 0CK2] but a consequence of the named action,
which matters because the three clauses do not determine an acting function — see the
implementation notes of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftNamedTorsorDerivations.lean`.

It differs from `Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts` only
in the shape of the set acted on: there the lifts are the elementary rule of
[Stacks Project, Tag 04FK] at `⊤`, here they are the global morphisms
`Deformation.Examples.globalLiftsOverBase`, which is what
`Deformation.Examples.liftClass` consumes.

At `N = 𝒪_X` the acting group is the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's sequence;
the coefficient sheaf is left arbitrary for the reason recorded in the implementation notes of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftGroup.lean`. -/
theorem exists_simplyTransitive_addAction_derivations_globalLiftsOverBase
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (e : Q.base ⟶ P.base) (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)
    (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N) :
    ∃ act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
        globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e,
      (∀ c : globalLiftsOverBase f P Q e, act 0 c = c) ∧
        (∀ (θ η : SDerivation pY.toLRSHom.toShHom
              ((modulePushforward f.toLRSHom.toShHom).obj N))
            (c : globalLiftsOverBase f P Q e), act (θ + η) c = act θ (act η c)) ∧
          ∀ c₀ c₁ : globalLiftsOverBase f P Q e,
            ∃! θ : SDerivation pY.toLRSHom.toShHom
                ((modulePushforward f.toLRSHom.toShHom).obj N), act θ c₀ = c₁ :=
  ⟨schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε, schemeMorphismLiftsVAdd_zero f pX pY hf hm ℓ₀ ε,
    schemeMorphismLiftsVAdd_add f pX pY hf hm ℓ₀ ε,
    existsUnique_schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε⟩

/-! ### The arrow -/

/-- **Stacks 0E3V, the fourth arrow `Der_k(𝒪_Y, f_*𝒪_X) ⟶ T Def_{X ⟶ Y}`.** Let `f : X ⟶ Y` be
a morphism of schemes over `k`, let `P` and `Q` be first-order deformations of `X` and of `Y`
over the square-zero extension of `k` by `M`, let `act` be an action of the derivations on the
lifts of `f` to that pair — the action of [Stacks Project, Tag 0CK2], produced by
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` — and
let `ℓ₀` be a lift. Then a derivation translates `ℓ₀`, and the class of the translate in the
tangent module of `Def_{X ⟶ Y}` is the value of the arrow at it.

This is the source's "a derivation `D` gives the lift `f' + D` of `f`, whose first-order
deformation of `f` is the image of `D`". The class of a lift is
`Deformation.Examples.liftClass`, the `cls` map of the source's proof, so the arrow is
`cls ∘ (· acting on ℓ₀)` and nothing more; its content is in those two inputs.

It is a bare function parametrised by the action; its `k`-linear form at the trivial data is
`Deformation.Examples.schemeMorphismDerivationTangentLinearMap`. See the implementation notes of
this file. -/
def schemeMorphismDerivationTangentMap
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e)
    (ℓ₀ : globalLiftsOverBase f P Q e) :
    SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
        hM M) :=
  fun θ => liftClass f pX pY hf hM M hQ (act θ ℓ₀)

/-- **The arrow is the class of the translate of the base lift.** This is the `hδ` input of
`Deformation.exact_triple_of_simplyTransitiveVAdd`, which that theorem carries as a hypothesis
on an abstract map `δ`: here the map is constructed, and the hypothesis holds by definition. -/
@[simp]
theorem schemeMorphismDerivationTangentMap_apply
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e)
    (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : SDerivation pY.toLRSHom.toShHom
      ((modulePushforward f.toLRSHom.toShHom).obj N)) :
    schemeMorphismDerivationTangentMap f pX pY hf hM M hQ act ℓ₀ θ =
      liftClass f pX pY hf hM M hQ (act θ ℓ₀) := rfl

/-- **The zero derivation goes to the class of the base lift.** The only law of the action this
uses is that `0` acts trivially. -/
theorem schemeMorphismDerivationTangentMap_zero
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e)
    (ℓ₀ : globalLiftsOverBase f P Q e)
    (hact : ∀ c : globalLiftsOverBase f P Q e, act 0 c = c) :
    schemeMorphismDerivationTangentMap f pX pY hf hM M hQ act ℓ₀ 0 =
      liftClass f pX pY hf hM M hQ ℓ₀ :=
  congrArg (fun z => liftClass f pX pY hf hM M hQ z) (hact ℓ₀)

/-- **Every class of a lift of `f` is a value of the arrow.** The lifts of `f` to the pair of
deformations are one orbit of the derivations, so the classes of lifts are exactly the values of
the arrow — this is the half of that statement which needs only transitivity, and it is what
the source's "a derivation displaces the trivial lift to every other one" says about the arrow.

It is not exactness at the fourth spot of the source's sequence: that compares the image of this
arrow with the kernel of the next one, and so needs in addition that a first-order deformation
of `f` killed by the arrow to `T(Def_X × Def_Y)` comes from a lift, which is
`Deformation.Examples.exists_liftClass_iff`. -/
theorem exists_schemeMorphismDerivationTangentMap_eq_liftClass
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e)
    (ℓ₀ : globalLiftsOverBase f P Q e)
    (htrans : ∀ c₀ c₁ : globalLiftsOverBase f P Q e,
      ∃! θ : SDerivation pY.toLRSHom.toShHom
        ((modulePushforward f.toLRSHom.toShHom).obj N), act θ c₀ = c₁)
    (ℓ : globalLiftsOverBase f P Q e) :
    ∃ θ : SDerivation pY.toLRSHom.toShHom
        ((modulePushforward f.toLRSHom.toShHom).obj N),
      schemeMorphismDerivationTangentMap f pX pY hf hM M hQ act ℓ₀ θ =
        liftClass f pX pY hf hM M hQ ℓ := by
  obtain ⟨θ, hθ, -⟩ := htrans ℓ₀ ℓ
  exact ⟨θ, congrArg (fun z => liftClass f pX pY hf hM M hQ z) hθ⟩

/-- **The composite of this arrow with the next one vanishes.** If the two endpoint deformations
`P` and `Q` are trivial — that is, if their classes in the tangent modules of `Def_X` and
`Def_Y` vanish, which is the situation of the source's proof — then every value of the arrow
`Der_k(𝒪_Y, f_*𝒪_X) ⟶ T Def_{X ⟶ Y}` dies in `T(Def_X × Def_Y)`.

This is the assertion that the source's sequence is a *complex* at its fifth spot, not that it
is exact there: exactness at `T Def_{X ⟶ Y}` is the equality of the image of this arrow with the
kernel of `Deformation.Examples.schemeMorphismTangentPair`, whose remaining half is
`Deformation.Examples.exists_liftClass_iff`. The vanishing itself is
`Deformation.Examples.liftClass_mem_ker` at the translate of the base lift: the two endpoints of
the deformation of `f` attached to a lift are `P` and `Q` up to isomorphism in their fibres, and
a derivation translates a lift to a lift. -/
theorem schemeMorphismTangentPair_schemeMorphismDerivationTangentMap
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (hP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ = 0)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (act : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
      globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)) →
        globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)))
    (ℓ₀ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)))
    (θ : SDerivation pY.toLRSHom.toShHom
      ((modulePushforward f.toLRSHom.toShHom).obj N)) :
    schemeMorphismTangentPair f pX pY hf hM hX hY M
        (schemeMorphismDerivationTangentMap f pX pY hf hM M hQ act ℓ₀ θ) = 0 :=
  liftClass_mem_ker f pX pY hf hM hX hY M hP hQ hP0 hQ0 (act θ ℓ₀)

/-! ### The arrow with the action discharged -/

include hf in
/-- **Stacks 0E3V, the fourth arrow of the source's sequence exists**, with no action of
[Stacks Project, Tag 0CK2] appearing in the statement. Let `f : X ⟶ Y` be a morphism of schemes
over `k`, let `P` and `Q` be first-order deformations of `X` and of `Y` over the square-zero
extension of `k` by `M` whose classes in the tangent modules of `Def_X` and of `Def_Y` vanish —
the *trivial* deformations of the source's proof — let the maximal ideal of their common base
have square zero, let `ℓ₀` be a lift of `f` to that pair, and let `ε` identify the conormal
sheaf of the special fibre of `P` with an `𝒪_X`-module `N`. Then there is a map

`Der_k(𝒪_Y, f_*N) ⟶ T Def_{X ⟶ Y}`

which sends `0` to the class of `ℓ₀`, whose values include the class of every lift of `f` to
that pair, and all of whose values die in `T(Def_X × Def_Y)`.

At `N = 𝒪_X` the domain is the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's sequence, and
`Deformation.Examples.deformationConormalIsoUnit` supplies `ε`. The map is
`Deformation.Examples.schemeMorphismDerivationTangentMap` at the action produced by
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase`; the
existential is here only because the library produces that action existentially, and the three
conclusions are
`Deformation.Examples.schemeMorphismDerivationTangentMap_zero`,
`Deformation.Examples.exists_schemeMorphismDerivationTangentMap_eq_liftClass` and
`Deformation.Examples.schemeMorphismTangentPair_schemeMorphismDerivationTangentMap`.

**The `k`-linearity asserted by the source is not part of this statement**: it is
`Deformation.Examples.schemeMorphismDerivationTangentLinearMap`, at the trivial data, built on the
naturality of the action of [Stacks Project, Tag 0CK2] in the base object
(`Deformation.Examples.globalLiftsOverBasePushforward_vadd`). -/
theorem exists_schemeMorphismDerivationTangentMap
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (hP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ = 0)
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)
    (ℓ₀ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)))
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N) :
    ∃ δ : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) →
        ↥(tangentModuleAt.{u, u, u}
          (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
          hM M),
      δ 0 = liftClass f pX pY hf hM M hQ ℓ₀ ∧
        (∀ ℓ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)),
          ∃ θ, δ θ = liftClass f pX pY hf hM M hQ ℓ) ∧
          ∀ θ, schemeMorphismTangentPair f pX pY hf hM hX hY M (δ θ) = 0 := by
  obtain ⟨act, hzero, -, htrans⟩ :=
    exists_simplyTransitive_addAction_derivations_globalLiftsOverBase f pX pY hf
      (eqToHom (hQ.trans hP.symm)) hm ℓ₀ ε
  exact ⟨schemeMorphismDerivationTangentMap f pX pY hf hM M hQ act ℓ₀,
    schemeMorphismDerivationTangentMap_zero f pX pY hf hM M hQ act ℓ₀ hzero,
    fun ℓ => exists_schemeMorphismDerivationTangentMap_eq_liftClass f pX pY hf hM M hQ act ℓ₀
      htrans ℓ,
    fun θ => schemeMorphismTangentPair_schemeMorphismDerivationTangentMap f pX pY hf hM hX hY M
      hP hQ hP0 hQ0 act ℓ₀ θ⟩

end Deformation.Examples

end
