module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftGroup
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftNamedTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The named action of Tag 0CK2 on the global lifts, with the derivations acting

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k`, let `P` be a deformation of
`X` and `Q` a deformation of `Y`, and let `ℓ₀` be a global lift of `f` to that pair.
`Deformation.Examples.globalLiftsOverBaseVAdd` is the translation action of
[Stacks Project, Tag 0CK2] on those lifts **as a named definition**, with the group of global
homomorphisms `f^*Ω_{Y/k} ⟶ 𝒞_{X/P.scheme}` acting.

This file carries that named action onto the **third term `Der_k(𝒪_Y, f_*N)` of the sequence of
[Stacks Project, Tag 0E3V]**, which is the acting group the existential statements
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts` and
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` use, and
it proves the three laws those statements assert. The point is that the arrow `b` of
[Stacks Project, Tag 0E3V] can then be *pinned to a definition* instead of taking an action as a
parameter: a statement quantified over an arbitrary function with the torsor laws says nothing
about the geometric action, because any reparametrisation of the acting group by a group
automorphism satisfies the same laws.

## Main definitions

* `Deformation.Examples.schemeMorphismLiftHomDerivationsAddEquiv`: the acting group of the named
  action is `Der_k(𝒪_Y, f_*N)`, as additive groups.
* `Deformation.Examples.schemeMorphismLiftsVAdd`: **the named action of
  [Stacks Project, Tag 0CK2] with the derivations acting.**

## Main results

* `Deformation.Examples.existsUnique_globalLiftsOverBaseVAdd_eq`: the named action of
  `StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftNamedTorsor.lean` is simply
  transitive from **every** base point, not only from the lift `ℓ₀` it is built at. This is the
  shape the existential statements of the library assert, and
  `Deformation.Examples.existsUnique_globalLiftsOverBaseVAdd` is its case `ℓ₁ = ℓ₀`.
* `Deformation.Examples.schemeMorphismLiftsVAdd_zero`,
  `Deformation.Examples.schemeMorphismLiftsVAdd_add` and
  `Deformation.Examples.existsUnique_schemeMorphismLiftsVAdd`: the three laws, for the
  derivations acting. Together they are exactly the conclusion of
  `Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase`, whose
  witness is now this definition.
* `Deformation.Examples.schemeMorphismLiftsVAdd_base`: the action on the base lift is the
  bijection `Deformation.Examples.globalLiftsOverBaseDerivationEquiv`, so the named action is not
  an arbitrary function with the right laws — it is the modified-lift construction of
  [Stacks Project, Tag 0CK1] read through the two identifications.

## Implementation notes

**Why the laws are not uniqueness.** The three laws do not determine the action: if `act`
satisfies them and `σ` is any automorphism of the acting group then `fun θ => act (σ θ)`
satisfies them too, and the two agree at `θ = 0` because both actions fix every lift there. So
"simply transitive and based at `ℓ₀`" pins an action only up to `Aut` of the acting group, and
the only way to say which action [Stacks Project, Tag 0CK2] produces is to name it. That is what
`Deformation.Examples.globalLiftsOverBaseVAdd` does and what
`Deformation.Examples.schemeMorphismLiftsVAdd_base` records here. (The implementation notes of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftNamedTorsor.lean` claim the laws do
determine the action; that claim is false for the reason just given, and nothing in the library
depends on it.)

**The coefficient sheaf.** As in
`Deformation.Examples.deformationHomSectionsTopDerivationsAddEquiv`, the conormal sheaf of the
special-fibre immersion is identified with an arbitrary `𝒪_X`-module `N` rather than with `𝒪_X`
on the nose, so that a square-zero base whose maximal ideal has any finite rank is covered. The
source's case is `N = 𝒪_X`, where the acting group is the third term `Der_k(𝒪_Y, f_*𝒪_X)` on the
nose and `Deformation.Examples.deformationConormalIsoUnit` supplies the identification.

**Relation to `Deformation.Examples.globalLiftsOverBaseDerivationVAdd`.** That definition is the
same named action with the third term `Der_k(𝒪_Y, f_*𝒪_X)` acting *on the nose*: it fixes the
coefficient sheaf at `𝒪_X` by taking a trivialisation
`𝒞_{X/P.scheme} ≅ 𝒪_X` and carries the acting group across by
`Deformation.Examples.schemeMorphismDerivationsEquivHom`. It is the form the exactness theorem
`Deformation.Examples.exact_schemeMorphismSixTerm_interior` consumes, and it is not generalised
here. `Deformation.Examples.schemeMorphismLiftsVAdd` exists alongside it because the existential
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` is
stated for an arbitrary coefficient sheaf `N`, so discharging that existential from a named
action needs the action at that generality; the two are not interchanged anywhere, and no lemma
identifying them is stated, because they are built through different chains of identifications
of the acting group and nothing needs them to agree.

**The two spellings of the acting group.** `Deformation.Examples.globalLiftsOverBaseVAdd` acts by
`Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules P.specialMap`
while `Deformation.Examples.deformationHomSectionsTopAddEquiv` lands in
`schemeMorphismPullbackCotangent f pY ⟶ immersionConormalSheaf P.specialMap`. These are the same
type — `Deformation.Examples.schemeMorphismPullbackCotangent_eq` is `rfl`, and
`Stacks.Thickenings.conormalModules` is an abbreviation for
`Stacks.Thickenings.immersionConormalSheaf` — but they are not the same *expression*, and a
`rw` whose motive crosses the two is ill-typed at `implicit` transparency.
`Deformation.Examples.schemeMorphismLiftHomDerivationsAddEquiv` is therefore declared at the
spelling `Deformation.Examples.globalLiftsOverBaseVAdd` uses, so that every rewrite below stays
inside one spelling. No bridge is needed and none is introduced.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
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

/-! ### The acting group of the named action is the derivation term -/

/-- **The group acting in `Deformation.Examples.globalLiftsOverBaseVAdd` is
`Der_k(𝒪_Y, f_*N)`.** The named action of [Stacks Project, Tag 0CK2] acts by global
homomorphisms `f^*Ω_{Y/k} ⟶ 𝒞_{X/X'}`; this identifies that group with the third term of the
sequence of [Stacks Project, Tag 0E3V], for any identification `ε` of the conormal sheaf with an
`𝒪_X`-module `N`.

It is `Deformation.Examples.deformationHomSectionsTopDerivationsAddEquiv` read backwards through
`Deformation.Examples.deformationHomSectionsTopAddEquiv`, which identifies the global
homomorphisms with the sections over the whole space; so it is the same identification of the
acting group that the existential statements of the library use, not a second one. -/
@[ega "IV 16.5.14" "Global"]
def schemeMorphismLiftHomDerivationsAddEquiv {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i]
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf i ≅ N) :
    (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules i) ≃+
      SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) :=
  (deformationHomSectionsTopAddEquiv f pY i).symm.trans
    (deformationHomSectionsTopDerivationsAddEquiv f pY i ε)

section NamedTorsor

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)

/-! ### The named action is simply transitive from every base point -/

include hf in
/-- **The named action of [Stacks Project, Tag 0CK2] is simply transitive from every base
point.** For any two global lifts `ℓ₁` and `ℓ₂` of `f` to the pair `(P, Q)`, exactly one element
of the acting group carries `ℓ₁` to `ℓ₂`.

`Deformation.Examples.existsUnique_globalLiftsOverBaseVAdd` is the case `ℓ₁ = ℓ₀`; this is the
shape the existential statements
`Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase` and
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` assert,
and it is what makes the named action a witness for them. The proof is that the action is the
addition of the acting group transported along a bijection, so the unique solution of
`θ ⬝ ℓ₁ = ℓ₂` is the difference of the two coordinates. -/
@[ega "IV 16.5.14" "special case"]
theorem existsUnique_globalLiftsOverBaseVAdd_eq (ℓ₀ ℓ₁ ℓ₂ : globalLiftsOverBase f P Q e) :
    ∃! θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P.specialMap,
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ₁ = ℓ₂ := by
  obtain ⟨κ₁, hκ₁, -⟩ := existsUnique_globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ ℓ₁
  obtain ⟨κ₂, hκ₂, u₂⟩ := existsUnique_globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ ℓ₂
  refine ⟨κ₂ - κ₁, ?_, fun η hη => ?_⟩
  · change globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ (κ₂ - κ₁) ℓ₁ = ℓ₂
    rw [← hκ₁, ← globalLiftsOverBaseVAdd_add, sub_add_cancel]
    exact hκ₂
  · replace hη : globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ η ℓ₁ = ℓ₂ := hη
    rw [← hκ₁, ← globalLiftsOverBaseVAdd_add] at hη
    exact eq_sub_of_add_eq (u₂ _ hη)

/-! ### The named action with the derivations acting -/

include hf in
/-- **The named action of [Stacks Project, Tag 0CK2] on the global lifts of `f`, with the third
term `Der_k(𝒪_Y, f_*N)` of the sequence of [Stacks Project, Tag 0E3V] acting.** This is
`Deformation.Examples.globalLiftsOverBaseVAdd` with its acting group carried onto the derivations
by `Deformation.Examples.schemeMorphismLiftHomDerivationsAddEquiv`.

It is a definition, not a function produced existentially, which is the whole point: the three
torsor laws do not determine an action — see the implementation notes of this file — so a
statement about the arrow of [Stacks Project, Tag 0E3V] quantified over an arbitrary function
with those laws asserts nothing about the geometric action. Pinning the arrow to this definition
is what gives such a statement content.

The laws are `Deformation.Examples.schemeMorphismLiftsVAdd_zero`,
`Deformation.Examples.schemeMorphismLiftsVAdd_add` and
`Deformation.Examples.existsUnique_schemeMorphismLiftsVAdd`, and what the action *is* — rather
than which laws it satisfies — is `Deformation.Examples.schemeMorphismLiftsVAdd_base`. -/
def schemeMorphismLiftsVAdd (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N)
    (θ : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N))
    (ℓ : globalLiftsOverBase f P Q e) : globalLiftsOverBase f P Q e :=
  globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀
    ((schemeMorphismLiftHomDerivationsAddEquiv f pY P.specialMap ε).symm θ) ℓ

include hf in
/-- **The named action with the derivations acting is the named action of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftNamedTorsor.lean`**, at the
derivation read back into the group of global homomorphisms. This holds by definition; it is
stated because it is the only step the laws below need, and stating it avoids unfolding the
definition in each of them. -/
theorem schemeMorphismLiftsVAdd_eq (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N)
    (θ : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N))
    (ℓ : globalLiftsOverBase f P Q e) :
    schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε θ ℓ =
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀
        ((schemeMorphismLiftHomDerivationsAddEquiv f pY P.specialMap ε).symm θ) ℓ := rfl

include hf in
/-- **The zero derivation acts trivially.** This is the first law
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` asserts,
here proved of a named action rather than carried as a hypothesis. -/
@[simp]
theorem schemeMorphismLiftsVAdd_zero (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N) (ℓ : globalLiftsOverBase f P Q e) :
    schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε 0 ℓ = ℓ := by
  rw [schemeMorphismLiftsVAdd_eq, map_zero, globalLiftsOverBaseVAdd_zero]

include hf in
/-- **The action law**: translating by `θ + η` is translating by `η` and then by `θ`. This is the
second law
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` asserts,
here proved of a named action rather than carried as a hypothesis. -/
theorem schemeMorphismLiftsVAdd_add (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N)
    (θ η : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N))
    (ℓ : globalLiftsOverBase f P Q e) :
    schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε (θ + η) ℓ =
      schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε θ
        (schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε η ℓ) := by
  rw [schemeMorphismLiftsVAdd_eq, schemeMorphismLiftsVAdd_eq, schemeMorphismLiftsVAdd_eq,
    map_add, globalLiftsOverBaseVAdd_add]

include hf in
/-- **Simple transitivity of the named action, from every base point.** Exactly one derivation
carries a global lift `ℓ₁` of `f` to another one `ℓ₂`. This is the third law
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase` asserts,
here proved of a named action rather than carried as a hypothesis. -/
@[ega "IV 16.5.14" "special case"]
theorem existsUnique_schemeMorphismLiftsVAdd (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N)
    (ℓ₁ ℓ₂ : globalLiftsOverBase f P Q e) :
    ∃! θ : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N),
      schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε θ ℓ₁ = ℓ₂ := by
  refine ((schemeMorphismLiftHomDerivationsAddEquiv f pY P.specialMap ε).toEquiv.existsUnique_congr
    fun θ => ?_).1 (existsUnique_globalLiftsOverBaseVAdd_eq f pX pY hf hm ℓ₀ ℓ₁ ℓ₂)
  rw [schemeMorphismLiftsVAdd_eq]
  simp

include hf in
/-- **What the named action is**, rather than which laws it satisfies: on the base lift `ℓ₀` it
is the bijection `Deformation.Examples.globalLiftsOverBaseDerivationEquiv`, that is, the
modified-lift construction of [Stacks Project, Tag 0CK1] read through the comparison of the
differentials relative to `Spec k` and relative to the base, and through the identification `ε`
of the conormal sheaf.

This is the lemma that distinguishes this action from an arbitrary function with the same three
laws, and so the one that makes a statement pinned to it non-vacuous. -/
theorem schemeMorphismLiftsVAdd_base (ℓ₀ : globalLiftsOverBase f P Q e)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf P.specialMap ≅ N)
    (θ : SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N)) :
    schemeMorphismLiftsVAdd f pX pY hf hm ℓ₀ ε θ ℓ₀ =
      globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀
        ((schemeMorphismLiftHomDerivationsAddEquiv f pY P.specialMap ε).symm θ) :=
  (schemeMorphismLiftsVAdd_eq f pX pY hf hm ℓ₀ ε θ ℓ₀).trans
    (globalLiftsOverBaseVAdd_base f pX pY hf hm ℓ₀ _)

end NamedTorsor

end Deformation.Examples

end
