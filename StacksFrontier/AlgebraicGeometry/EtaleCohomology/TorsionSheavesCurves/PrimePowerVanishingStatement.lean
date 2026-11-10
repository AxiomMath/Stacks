module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# Item (3) of Situation 0A52: characteristic-primary vanishing

Stacks Project Tag 0A52 fixes an algebraically closed field `k`, a separated finite-type scheme
`X` of dimension at most one over `k`, and a torsion abelian sheaf `F` on `X_étale`, and then
lists eight statements one wants to prove for such data. The third of them is Tag 0A55, which in
the chapter source reads

> `H^q_étale(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion,

The source asserts nothing at that tag: the item is a label on an entry of the list, and the
theorem that items (1) to (8) hold for every torsion sheaf in the situation is Tag 03SC, whose
proof is the whole of the section. The faithful formalization of such an item is therefore a
definition — a predicate that later results can say *holds* in a given instance, as Tag 0A5B does
for a smooth `X` with constant coefficients of prime order, Tag 0A5C for an extension of sheaves,
Tag 0A5D for a finite direct image and Tag 0GJA for a dense open. The repository already reads
the enclosing situation that way: `Stacks.EtaleCohomology.TorsionSheafSituation` is a structure
and carries `@[stacks_fixed 0A52]`.

## Main definitions

* `Stacks.EtaleCohomology.IsPrimePowerTorsionVanishing` is Tag 0A55: for a scheme `X` over a
  field `k` of characteristic `p` and an abelian sheaf `F` on the small étale site of `X`, if `p`
  is positive and `F` is `p`-power torsion then `H^q_étale(X, F)` vanishes in every degree above
  one.

## Main results

* `Stacks.EtaleCohomology.isPrimePowerTorsionVanishing_of_curveCohomologyStatements`: the item is
  the third field of `Stacks.EtaleCohomology.CurveCohomologyStatements`, the conjunction of the
  eight items already used in this directory, once the free natural number there is the
  characteristic of the base field.
* `Stacks.EtaleCohomology.isPrimePowerTorsionVanishing_of_charP_zero`: in characteristic zero the
  item is vacuous, its hypothesis `p = char(k) > 0` being unsatisfiable.
* `Stacks.Torsion.isPrimePowerTorsion_of_isLocallySurjective` and
  `Stacks.Torsion.isPrimePowerTorsion_constantSheaf`: an abelian sheaf receiving a locally
  surjective map from a presheaf all of whose sections are killed by `l` is `l`-power torsion,
  and hence so is a constant sheaf whose value is killed by `l`.
* `Stacks.Torsion.isPrimePowerTorsion_etaleConstantZMod`: the constant sheaf `𝐙/p𝐙` on the small
  étale site of a scheme is `p`-power torsion. This is the item's side condition for the
  coefficients the Artin–Schreier argument of Tag 0A3N computes with.

## Implementation notes

**Generality.** The item names only `X`, `F`, the characteristic of the base field and the degree.
That `k` is algebraically closed, that `X` is separated of finite type of dimension at most one
over `k` and that `F` is torsion are the hypotheses of the enclosing situation, and they are what
makes the item a *theorem* at Tag 03SC rather than part of the item. The definition below
therefore quantifies over an arbitrary scheme `X` with a morphism to the spectrum of an arbitrary
field and an arbitrary abelian sheaf on its small étale site, and specialises to the source by
taking the data of `Stacks.EtaleCohomology.TorsionSheafSituation`: for a situation `S` the
source's item is `IsPrimePowerTorsionVanishing k p S.F` for the base field `k` of `S`. Nothing
is weakened — no hypothesis of the item is dropped and no conclusion is restricted.

The predicate takes the field `k` explicitly and no structure morphism to `Spec k`: its body does
not mention such a morphism, so the predicate does not depend on it. That `k` is *the base field
of* `X` is part of the data the predicate is applied to, as in
`isPrimePowerTorsionVanishing_of_curveCohomologyStatements`, where the morphism appears in the
hypothesis.

**What is and is not proved here.** Nothing in this file asserts that the item holds. That is Tag
03SC, and it is not formalized in this library. For the `p`-power torsion coefficients of this
item the source's route is the chain 03SC ← 03SD ← 0A3Q ← 03SG ← 0A5B ← 0A3N, together with Tag
0GJA and the reduction of a torsion sheaf to constructible coefficients. Of these Tag 0A3N is
available — `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAlgClosed`, which for
`dim(X) ≤ 1` gives exactly vanishing above degree one, with the Artin–Schreier sequence, the
étale-Zariski comparison of Tag 03P2 and the top-degree finite dimensionality of Tag 0A3M carried
as hypotheses — and so are Tags 03SA (2) and 03Q5. But Tags 03SD, 0A3Q and 03SG have no carrier
at all; Tag 0GJA is available only with the cohomology of the closed complement of the dense open
assumed, by `Stacks.EtaleCohomology.curveCohomologyStatements_extensionByZero_iff`, which
deliberately carries no tag; and Tag 03SA is stated on the small étale site of Tag 021B rather
than on Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`, which is the site this chapter's
cohomology is taken on. No declaration in this file claims any part of that chain.

**Relation to the unquantified form already present.**
`Stacks.EtaleCohomology.CurveCohomologyStatements.vanishing_of_isPrimePowerTorsion` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/FiniteDirectImage.lean` is
the same assertion as a field of the eight-fold conjunction, but with the exponent a free natural
number `l` that is only *intended* to be the characteristic of the base field; the structure
imposes no relation between the two, which is why it carries no tag. The definition below pins
the exponent to `char(k)` through a `CharP` instance, and
`isPrimePowerTorsionVanishing_of_curveCohomologyStatements` is the resulting implication.

**`p`-power torsion.** `Stacks.Torsion.IsPrimePowerTorsion` asks every local section to be
annihilated, locally on a covering sieve, by a positive power of `p`. It is the predicate the
other items of the situation already use, so no second notion is introduced, and it is consistent
with the situation's standing torsion hypothesis rather than independent of it: `p`-power torsion
implies torsion for positive `p`, by
`Stacks.Torsion.torsionSheafProperty_of_isPrimePowerTorsion`.

**Well-definedness classes.** `CategoryTheory.HasExt` is what makes `CategoryTheory.Sheaf.H` — an
`Ext`-group out of the constant sheaf `ℤ` — defined; it is deliberately not an instance in
Mathlib, so it is carried, and it is not vacuous: `CategoryTheory.HasExt.standard` supplies it.
Nothing else has to be assumed at this coefficient universe. In particular abelian sheaves on
`AlgebraicGeometry.Scheme.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{max (u + 1) v}` admit sheafification and are abelian without hypothesis, which is
why no `HasSheafify` argument appears; `Stacks.Torsion.isPrimePowerTorsion_etaleConstantZMod`
likewise needs neither `CategoryTheory.HasWeakSheafify` nor
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` as a hypothesis, both being found
for that site by `AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology` and the
chapter's sheafification instance.

Vanishing is spelled `Subsingleton`, matching Mathlib's `CategoryTheory.Sheaf.H`, which has no
canonical zero element to compare against. The coefficient universe is
`AddCommGrpCat.{max (u + 1) v}` for `X : Scheme.{u}`, the family of universes in which étale
cohomology of such a scheme is computed, as elsewhere in this chapter.

## References

* [Stacks Project, Tag 0A55](https://stacks.math.columbia.edu/tag/0A55)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A3N](https://stacks.math.columbia.edu/tag/0A3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.Torsion

section UniformAnnihilator

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A uniform annihilator passes to a sheaf along a locally surjective map.** If every section
of a presheaf `P` of abelian groups is killed by `l` and `η : P ⟶ F` is locally surjective onto
an abelian sheaf, then `F` is `l`-power torsion: a section of `F` is, on the image sieve of `η`,
the image of a section of `P`, and that is killed by `l = l ^ 1`.

No transitivity of the topology is needed, unlike for
`Stacks.Torsion.isLocallyTorsion_of_isLocallySurjective`, because the annihilator here does not
vary over the members of the sieve. -/
theorem isPrimePowerTorsion_of_isLocallySurjective {P : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {F : Sheaf J AddCommGrpCat.{w}} (η : P ⟶ F.obj)
    [Presheaf.IsLocallySurjective J η] (l : ℕ)
    (hP : ∀ (V : C) (t : P.obj (op V)), l • t = 0) :
    IsPrimePowerTorsion J l F := by
  intro U y
  refine ⟨Presheaf.imageSieve η y, Presheaf.imageSieve_mem J η y, fun V f hf => ?_⟩
  obtain ⟨t, ht⟩ := hf
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [pow_one, ← ht, ← _root_.map_nsmul, hP V t, map_zero]

/-- **A constant abelian sheaf whose value is killed by `l` is `l`-power torsion.** The constant
presheaf has that value as its sections over every object, and the unit of sheafification is
locally surjective. -/
theorem isPrimePowerTorsion_constantSheaf [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (l : ℕ) (E : AddCommGrpCat.{w})
    (hE : ∀ x : E, l • x = 0) :
    IsPrimePowerTorsion J l ((constantSheaf J AddCommGrpCat.{w}).obj E) :=
  isPrimePowerTorsion_of_isLocallySurjective J
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj E)) l fun _ t => hE t

end UniformAnnihilator

/-- **The constant sheaf `𝐙/p𝐙` on the small étale site of a scheme is `p`-power torsion.** Its
value `𝐙/p𝐙` is killed by `p`, so this is
`Stacks.Torsion.isPrimePowerTorsion_constantSheaf`. These are the coefficients the Artin–Schreier
argument of Tag 0A3N computes with, and this is the side condition that item (3) of Situation
0A52 imposes on them. -/
theorem isPrimePowerTorsion_etaleConstantZMod (X : Scheme.{u}) (p : ℕ) :
    IsPrimePowerTorsion X.smallEtaleTopology p (Stacks.ArtinSchreier.etaleConstantZMod X p) :=
  isPrimePowerTorsion_constantSheaf X.smallEtaleTopology p
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))) fun x => by
      ext
      simp

end Stacks.Torsion

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Stacks Project, Tag 0A55**, item (3) of Situation 0A52:

> `H^q_étale(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion.

Here `X` is a scheme over a field `k` of characteristic `p` (the predicate does not depend on the
structure morphism, which is therefore not an argument), and `F` is an abelian sheaf on the
small étale site of `X`. The source states this as one entry of the list of eight statements
that Situation 0A52 asks for, not as an assertion, so it is a predicate on the data; the
situation's further hypotheses — `k` algebraically closed, `X` separated of finite type of
dimension at most one, `F` torsion — are what make the item a theorem at Tag 03SC, and are not
imposed here. -/
@[stacks 0A55 "item (3) of 0A52: H^q(X, F) = 0 for q > 1 if p = char(k) > 0 and F is p-power \
  torsion"]
def IsPrimePowerTorsionVanishing (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] : Prop :=
  0 < p → Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p F →
    ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} F q)

/-- Item (3) of Situation 0A52 is the third field of
`Stacks.EtaleCohomology.CurveCohomologyStatements`, whose exponent is a free natural number, once
that exponent is the characteristic of the base field. The remaining arguments of that structure
are inert here: the item mentions neither the morphism of items (6), (7) and (8), nor the
exponential characteristic of items (4) and (6), nor the constructibility predicate of items (4)
and (5). -/
theorem isPrimePowerTorsionVanishing_of_curveCohomologyStatements {X' : Scheme.{u}}
    (i : X' ⟶ X) (π : X ⟶ Spec (.of k)) (p p' : ℕ) [CharP k p]
    {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h : CurveCohomologyStatements.{u, v, w} i π p p' constructible F) :
    IsPrimePowerTorsionVanishing.{u, v, w} k p F :=
  fun _ => h.vanishing_of_isPrimePowerTorsion

/-- **Item (3) of Situation 0A52 is vacuous in characteristic zero.** Its hypothesis is that the
characteristic of the base field is positive, and in characteristic zero the only `p` with
`CharP k p` is `0`. -/
theorem isPrimePowerTorsionVanishing_of_charP_zero (k : Type u) [Field k] [CharP k 0]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    IsPrimePowerTorsionVanishing.{u, v, w} k 0 F :=
  fun h => absurd h (lt_irrefl 0)

end Stacks.EtaleCohomology

end
