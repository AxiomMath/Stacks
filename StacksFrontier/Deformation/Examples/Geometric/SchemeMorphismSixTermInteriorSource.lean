module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationTangentFiberAut
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermInterior

/-!
# The interior of the sequence of Stacks 0E3V, at the source's `Inf` terms

`Deformation.Examples.exact_schemeMorphismSixTerm_interior` proves exactness at the second, third
and fourth spots of the sequence of [Stacks Project, Tag 0E3V]

`Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X ⟶ Y} → T(Def_X × Def_Y)`

but with the second term presented as `Deformation.Examples.globalLiftsOverBaseAutPair`, the
bundled pairs of invertible self-maps of the two endpoint total spaces, rather than as the
source's `Inf(Def_X × Def_Y)`. The source's term is the product
`Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY`
of the tangent spaces at the identity of the two endpoint automorphism functors — the term the
arrow `Deformation.Examples.schemeMorphismInfinitesimalPair` is stated between.

This file bridges the two presentations and restates the exactness at the **second** spot with the
second term the source's. The bridge is
`Deformation.Examples.localizedTangentEquivSelfMaps` on each factor: that bijection presents the
`Inf` term of a single deformation category as the invertible self-maps of the chosen first-order
pushforward over the base fixing the special-fibre immersion, which is exactly one component of
`Deformation.Examples.globalLiftsOverBaseAutPair`.

The third and fourth spots are **not** restated here; the implementation notes say exactly what
blocks them at the dual-number pushforwards this file uses, and
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismSixTermInteriorSourceCross.lean`
restates them at the *re-based* ones.

## Main definitions

* `Deformation.Examples.globalLiftsOverBaseAutPairEquivSelfMapsProd`: the bundled pairs are the
  product of the two sets of self-maps. The only thing to check is that the source-side condition
  `α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e`, which the bundled pairs
  carry, is the condition `α ≫ P.toBase = P.toBase` that
  `Deformation.Examples.localizedTangentEquivSelfMaps` produces.
* `Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPair`: **the bridge.** The
  source's second term `Inf(Def_X × Def_Y)` is the acting group of the proof of
  [Stacks Project, Tag 0E3V], when the two endpoint deformations are the chosen first-order
  pushforwards.
* `Deformation.Examples.liftDeformationLocalizedTangentPair`: **the arrow `a`**, read into the
  source's second term.
* `Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangent`: **the arrow `b`**,
  read out of the source's second term.

## Main results

* `Deformation.Examples.comp_deformationAmbientToBase_iff`: for an invertible `e`, being over
  the ambient base of `Deformation.Examples.deformationAmbientToBase` is being over the structure
  morphism of the deformation.
* `Deformation.Examples.exists_liftDeformationLocalizedTangentPair_eq_iff`: **the image of the
  arrow `a`, in the source's second term, is the source's own description of it.** A pair of
  infinitesimal automorphisms of the two endpoint deformations — read through
  `Deformation.Examples.localizedTangentEquivSelfMaps` as a pair of self-maps `(α, β)` — comes
  from an automorphism of the deformation of `f` determined by `ℓ₀` exactly when
  `ℓ₀ ∘ α = β ∘ ℓ₀`, the source's "`(α, β)` comes from an infinitesimal automorphism of `f'`
  exactly when it commutes with `f'`".
* `Deformation.Examples.exact_schemeMorphismSixTerm_secondSpot_localizedTangent`: **Tag 0E3V,
  exactness at the second spot with the second term the source's `Inf(Def_X × Def_Y)`.**

## Implementation notes

**Why the two endpoint deformations are the chosen first-order pushforwards.**
`Deformation.Examples.localizedTangentEquivSelfMaps` presents the `Inf` term as self-maps of
`Deformation.Examples.firstOrderPushforward`, the chosen pushforward of the base point to the dual
numbers under its own base object; no other deformation has a self-map set attached to it. So the
two deformations `P` and `Q` of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior` are taken to be those two
pushforwards, rather than carried as arbitrary deformations with an identification. The two
predeformation hypotheses this forces, inherited from
`Deformation.Examples.localizedTangentEquivSelfMaps`, are theorems of the library
(`Deformation.Examples.schemeDeformationCategoryProjection_isPredeformationCategory`), and the
comparison `e` of the two base objects is an `eqToHom` whenever the two chosen points lie over the
same object of `𝒞_Λ`, which is the source's case; nothing below is conditional on anything the
library cannot supply.

**Why only the second spot.** Exactness at the second spot needs none of the square-zero data:
`Deformation.exact_fst_of_simplyTransitive` consumes only the simply transitive translation action
of the third term on the lifts, the characterising property of `b`, and the description of the
image of `a`. The third and fourth spots run through
`Deformation.Examples.liftClass` and
`Deformation.Examples.schemeMorphismDerivationTangentMap`, which exist only once the common base
of `P` and `Q` is `(Deformation.squareZeroExtensionArtinian Λ k).obj M` for a finite-dimensional
`M` — the hypotheses `hP` and `hQ` of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`.

At `P = firstOrderPushforward QX` that equation is **not** available, and the obstruction is not a
missing proof but a mismatch of objects. The base of the chosen first-order pushforward is
`(Deformation.dualNumbersUnder).right`, the dual numbers read as an algebra *under* the base
object `A` of the point — `Deformation.algebrasUnder` endows the carrier with the `Λ`-algebra
structure obtained by composing `Λ → A → k[ε]`. The square-zero extension of `𝒞_Λ` itself carries
the direct `Λ`-algebra structure instead. The two objects of `ArtinianLocalAlgCat Λ k` have the
same carrier and differ in the `algebra` instance field; what the library relates them by is an
*isomorphism* and not an equality — `Deformation.squareZeroCrossUnderIso`, which is the identity
on carriers — and `Deformation.squareZeroCrossUnder` is the re-based object introduced for exactly
this reason, whose `right` is `(Deformation.squareZeroExtensionArtinian Λ k).obj M` on the nose
(`Deformation.squareZeroCrossUnder_right`).

So restating the third and fourth spots at the source's second term needs the `Inf`-term
presentation of `Deformation.Examples.localizedTangentEquivSelfMaps` transported from
`Deformation.dualNumbersUnder` to `Deformation.squareZeroCrossUnder A (FGModuleCat.of k (ULift k))`
along `Deformation.squareZeroCrossUnderIso`, i.e. a self-map presentation of the `Inf` term at the
chosen pushforward to the *re-based* dual numbers. That companion of
`Deformation.Examples.localizedTangentEquivSelfMaps` is
`Deformation.Examples.localizedTangentEquivSelfMapsCross`, and with it the third and fourth spots
are restated in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismSixTermInteriorSourceCross.lean`, at
`Deformation.Examples.firstOrderPushforwardCross` in place of
`Deformation.Examples.firstOrderPushforward`. What stays impossible is the restatement at the
pushforwards *this* file uses: writing the hypothesis
`(firstOrderPushforward QX).base = (squareZeroExtensionArtinian Λ k).obj M` down would make it
vacuous, and it is not written down here.

**The arrow into the second term is not `schemeMorphismInfinitesimalPair`.** That arrow is
`Deformation.inducedInfinitesimalLinearMapOfEq` of the two endpoint-forgetting functors, and
`Deformation.inducedInfinitesimalLinearMapOfEq_spec` describes it only up to conjugation by a
comparison arrow `H` between the chosen dual-number pushforwards of the deformation of `f` and of
its endpoints. Identifying the two needs the first term in its fibre-automorphism presentation,
i.e. an analogue of `Deformation.Examples.localizedTangentEquivFiberAut` for
`Deformation.Examples.schemeMorphismDeformationCategory`, and that in turn needs
`Deformation.IsPredeformationCategory` for
`Deformation.Examples.schemeMorphismDeformationCategoryProjection` and an analogue of
`Deformation.Examples.autFiberBaseMulEquiv` for the fibres of that projection. Neither is in the
library. What stands in its place here is
`Deformation.Examples.exists_liftDeformationLocalizedTangentPair_eq_iff`, which pins the *image*
of the arrow `a` — all that exactness at the second spot is about — as the source's compatible
pairs, read in the source's term.

**No `k`-linearity is asserted.** As in
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`, exactness is `Function.Exact`, a
statement about bare functions. The second term now *carries* a `k`-module structure — it is a
product of tangent spaces — but nothing here says the two arrows respect it, and
`Deformation.Examples.localizedTangentEquivSelfMaps` is a bijection of sets only. The `PARTIAL`
Tag 0E3V marker of `Deformation.Examples.schemeMorphismDeformation_endpointArrows` stays where it
is.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

/-! ### Being over the ambient base is being over the structure morphism -/

section AmbientToBase

variable {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
variable {Z : Over (Spec (CommRingCat.of κ))}

/-- **For an invertible `e`, a self-map of the total space of a deformation is over the ambient
base of `Deformation.Examples.deformationAmbientToBase` exactly when it is over the structure
morphism of the deformation.** The ambient structure morphism is `P.toBase ≫ baseSpecMap e`, and
`baseSpecMap e` is an isomorphism (`Deformation.Examples.isIso_baseSpecMap`), hence a
monomorphism, so it cancels.

This is the one discrepancy between the side conditions carried by
`Deformation.Examples.globalLiftsOverBaseAutPair` and those produced by
`Deformation.Examples.localizedTangentEquivSelfMaps`. -/
theorem comp_deformationAmbientToBase_iff
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) Z)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ κ} (e : A ⟶ P.base) [IsIso e]
    (α : P.scheme ⟶ P.scheme) :
    α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e ↔
      α ≫ P.toBase = P.toBase := by
  show α ≫ P.toBase ≫ baseSpecMap e = P.toBase ≫ baseSpecMap e ↔ _
  rw [← Category.assoc]
  exact cancel_mono (baseSpecMap e)

end AmbientToBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-! ### The bundled pairs are a product of two sets of self-maps -/

section SelfMapsProd

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} [IsIso e]

/-- **The acting group of the source's proof is the product of the two sets of self-maps.**
`Deformation.Examples.globalLiftsOverBaseAutPair` is a subtype of a product of morphism types;
this reads it as the product of the two subtypes that
`Deformation.Examples.fiberAutEquivSelfMaps` — and hence
`Deformation.Examples.localizedTangentEquivSelfMaps` — produces.

The side conditions match clause by clause, except that the pair carries
`α ≫ deformationAmbientToBase P e = deformationAmbientToBase P e` where the self-map subtype asks
for `α ≫ P.toBase = P.toBase`; `Deformation.Examples.comp_deformationAmbientToBase_iff` is that
equivalence. -/
def globalLiftsOverBaseAutPairEquivSelfMapsProd :
    globalLiftsOverBaseAutPair pX pY P Q e ≃
      ({ a : P.scheme ⟶ P.scheme //
          a ≫ P.toBase = P.toBase ∧ P.specialMap ≫ a = P.specialMap ∧ IsIso a } ×
        { b : Q.scheme ⟶ Q.scheme //
          b ≫ Q.toBase = Q.toBase ∧ Q.specialMap ≫ b = Q.specialMap ∧ IsIso b }) where
  toFun g :=
    (⟨g.1.1, (comp_deformationAmbientToBase_iff P e g.1.1).mp g.2.2.2.1, g.2.2.2.2.1, g.2.1⟩,
      ⟨g.1.2, g.2.2.2.2.2.1, g.2.2.2.2.2.2, g.2.2.1⟩)
  invFun p :=
    ⟨(p.1.1, p.2.1), p.1.2.2.2, p.2.2.2.2,
      (comp_deformationAmbientToBase_iff P e p.1.1).mpr p.1.2.1, p.1.2.2.1, p.2.2.1, p.2.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SelfMapsProd

/-! ### The source's second term is the acting group of its proof -/

section Bridge

variable
  (hpX : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hpY : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) y₀)

/-- **Stacks 0E3V: the second term of the source's sequence is the acting group of its proof.**
`Inf(Def_X × Def_Y)` is the product `Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY`
of the tangent spaces at the identity of the two endpoint automorphism functors — the term
`Deformation.Examples.schemeMorphismInfinitesimalPair` maps into. This identifies it with
`Deformation.Examples.globalLiftsOverBaseAutPair` at the two chosen first-order pushforwards,
which is the group that acts on the lifts of `f` in the source's proof and the second term of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`.

It is `Deformation.Examples.localizedTangentEquivSelfMaps` on each factor followed by
`Deformation.Examples.globalLiftsOverBaseAutPairEquivSelfMapsProd`. As a bijection of sets only:
each factor of the left-hand side is a `k`-vector space and nothing here transports that
structure, for the reasons recorded in
`StacksFrontier/Deformation/Examples/Geometric/SchemeDeformationTangentFiberAut.lean`. -/
def localizedTangentPairEquivGlobalLiftsOverBaseAutPair
    (e : (firstOrderPushforward QY).base ⟶ (firstOrderPushforward QX).base) [IsIso e] :
    localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY ≃
      globalLiftsOverBaseAutPair pX pY (firstOrderPushforward QX)
        (firstOrderPushforward QY) e :=
  ((localizedTangentEquivSelfMaps hpX QX).prodCongr
      (localizedTangentEquivSelfMaps hpY QY)).trans
    (globalLiftsOverBaseAutPairEquivSelfMapsProd pX pY (e := e)).symm

/-- The source component of the bridge is the self-map of the first tangent vector. -/
@[simp]
theorem localizedTangentPairEquivGlobalLiftsOverBaseAutPair_fst_val
    (e : (firstOrderPushforward QY).base ⟶ (firstOrderPushforward QX).base) [IsIso e]
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e t).1.1 =
      (localizedTangentEquivSelfMaps hpX QX t.1).1 := rfl

/-- The target component of the bridge is the self-map of the second tangent vector. -/
@[simp]
theorem localizedTangentPairEquivGlobalLiftsOverBaseAutPair_snd_val
    (e : (firstOrderPushforward QY).base ⟶ (firstOrderPushforward QX).base) [IsIso e]
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e t).1.2 =
      (localizedTangentEquivSelfMaps hpY QY t.2).1 := rfl

end Bridge

/-! ### The two interior arrows at the source's second term -/

section Arrows

variable (hf : f ≫ pY = pX)
  (hpX : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hpY : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) y₀)
  {e : (firstOrderPushforward QY).base ⟶ (firstOrderPushforward QX).base} [IsIso e]

/-- **The arrow `a` of [Stacks Project, Tag 0E3V], landing in the source's second term.**
`Deformation.Examples.liftDeformationAutPair` — the pair of endpoint components of an
automorphism of the deformation of `f` determined by `ℓ₀` — carried along
`Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPair` into
`Inf(Def_X × Def_Y)`.

This is **not** asserted to be `Deformation.Examples.schemeMorphismInfinitesimalPair`, which has
the same target but whose source is the tangent space of the automorphism functor of the
deformation category of `f` rather than the automorphism group of one of its objects; see the
implementation notes of this file. Its *image*, which is what exactness at the second spot is
about, is identified in the source's own terms by
`Deformation.Examples.exists_liftDeformationLocalizedTangentPair_eq_iff`. -/
def liftDeformationLocalizedTangentPair
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforward QX) (firstOrderPushforward QY) e)
    (x : Aut (morphismDeformationFiberObj f pX pY hf
      (liftDeformationObject f pX pY hf ℓ₀))) :
    localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY :=
  (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e).symm
    (liftDeformationAutPair f pX pY hf ℓ₀ x)

/-- A pair of tangent vectors is in the image of the arrow `a` exactly when the conjugation by
its bundled pair fixes `ℓ₀`. -/
private theorem exists_liftDeformationLocalizedTangentPair_eq_iff_conj_eq
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforward QX) (firstOrderPushforward QY) e)
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (∃ x, liftDeformationLocalizedTangentPair f pX pY hf hpX hpY QX QY ℓ₀ x = t) ↔
      globalLiftsOverBaseAutPairConj f pX pY
        (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e t) ℓ₀ = ℓ₀ :=
  (exists_congr fun _ => Equiv.symm_apply_eq _).trans
    (exists_liftDeformationAutPair_eq_iff f pX pY hf ℓ₀ _)

/-- **The image of the arrow `a`, in the source's second term, is the source's own description of
it.** A pair of infinitesimal automorphisms of the two endpoint deformations — a pair of tangent
vectors of the two automorphism functors, read through
`Deformation.Examples.localizedTangentEquivSelfMaps` as a pair of invertible self-maps `(α, β)` of
the two total spaces — comes from an automorphism of the deformation of `f` determined by `ℓ₀`
exactly when `ℓ₀ ∘ α = β ∘ ℓ₀`.

This is the source's "`(α, β)` comes from an infinitesimal automorphism of `f'` exactly when it
commutes with `f'`", stated at the source's second term. It is
`Deformation.Examples.exists_liftDeformationAutPair_eq_iff` transported along the bridge and read
through `Deformation.Examples.globalLiftsOverBaseAutPairConj_eq_iff`. -/
theorem exists_liftDeformationLocalizedTangentPair_eq_iff
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforward QX) (firstOrderPushforward QY) e)
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (∃ x, liftDeformationLocalizedTangentPair f pX pY hf hpX hpY QX QY ℓ₀ x = t) ↔
      ℓ₀.1 ≫ (localizedTangentEquivSelfMaps hpY QY t.2).1 =
        (localizedTangentEquivSelfMaps hpX QX t.1).1 ≫ ℓ₀.1 := by
  rw [exists_liftDeformationLocalizedTangentPair_eq_iff_conj_eq,
    globalLiftsOverBaseAutPairConj_eq_iff f pX pY _ ℓ₀ ℓ₀,
    localizedTangentPairEquivGlobalLiftsOverBaseAutPair_fst_val,
    localizedTangentPairEquivGlobalLiftsOverBaseAutPair_snd_val]

variable (eC : Stacks.Thickenings.conormalModules (firstOrderPushforward QX).specialMap ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  (hm : IsLocalRing.maximalIdeal (firstOrderPushforward QX).base ^ 2 = ⊥)

/-- **The arrow `b` of [Stacks Project, Tag 0E3V], starting from the source's second term.**
`Deformation.Examples.globalLiftsOverBaseConjDerivation` — the unique derivation carrying `ℓ₀`
where a pair of infinitesimal automorphisms of the endpoints carries it — precomposed with
`Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPair`, so that its source is
`Inf(Def_X × Def_Y)` and its target the source's third term `Der_k(𝒪_Y, f_*𝒪_X)`. -/
def globalLiftsOverBaseConjDerivationLocalizedTangent
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforward QX) (firstOrderPushforward QY) e)
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    schemeMorphismDerivations f pY :=
  globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e t)

/-- **Stacks 0E3V, exactness at the second spot of the source's sequence, with the second term
the source's `Inf(Def_X × Def_Y)`.** The image of the arrow `a` is the kernel of the arrow `b`:
a pair of infinitesimal automorphisms of the two endpoint deformations is carried to the zero
derivation exactly when it comes from an automorphism of the deformation of `f` determined by
`ℓ₀`.

The second term is the source's: the product `Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY`
of the tangent spaces at the identity of the two endpoint automorphism functors, the term the
arrow `Deformation.Examples.schemeMorphismInfinitesimalPair` maps into. The third term is the
source's `Deformation.Examples.schemeMorphismDerivations f pY` on the nose.

`Deformation.exact_fst_of_simplyTransitive` fed with the simply transitive translation action of
the third term on the lifts
(`Deformation.Examples.existsUnique_globalLiftsOverBaseDerivationVAdd`), the characterising
property of `b` (`Deformation.Examples.globalLiftsOverBaseDerivationVAdd_conjDerivation`) and the
description of the image of `a`
(`Deformation.Examples.exists_liftDeformationLocalizedTangentPair_eq_iff`). None of the three
mentions the square-zero coordinate module `M`, which is why this spot — unlike the third and the
fourth — can be stated at the chosen first-order pushforwards at all; see the implementation
notes of this file.

The arrow into the second term is `Deformation.Examples.liftDeformationLocalizedTangentPair`,
whose source is the automorphism group of the deformation of `f` determined by `ℓ₀` rather than
`Deformation.localizedAutomorphismFunctorTangent` of the automorphism functor of the deformation
category of `f`, so it is not asserted to be
`Deformation.Examples.schemeMorphismInfinitesimalPair`; its image is the source's own description
of the image of `a`. Exactness is `Function.Exact`, about bare functions, so no `k`-linearity of
either arrow is asserted. -/
theorem exact_schemeMorphismSixTerm_secondSpot_localizedTangent
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforward QX) (firstOrderPushforward QY) e) :
    Function.Exact
      (liftDeformationLocalizedTangentPair f pX pY hf hpX hpY QX QY ℓ₀)
      (globalLiftsOverBaseConjDerivationLocalizedTangent f pX pY hf hpX hpY QX QY eC hm ℓ₀) := by
  refine exact_fst_of_simplyTransitive
    (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀)
    (fun t => globalLiftsOverBaseAutPairConj f pX pY
      (localizedTangentPairEquivGlobalLiftsOverBaseAutPair pX pY hpX hpY QX QY e t))
    ℓ₀
    (globalLiftsOverBaseDerivationVAdd_zero f pX pY hf eC hm ℓ₀)
    (existsUnique_globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀)
    (liftDeformationLocalizedTangentPair f pX pY hf hpX hpY QX QY ℓ₀)
    (globalLiftsOverBaseConjDerivationLocalizedTangent f pX pY hf hpX hpY QX QY eC hm ℓ₀)
    (fun t => globalLiftsOverBaseDerivationVAdd_conjDerivation f pX pY hf eC hm ℓ₀ _)
    (exists_liftDeformationLocalizedTangentPair_eq_iff_conj_eq f pX pY hf hpX hpY QX QY ℓ₀)

end Arrows

end Deformation.Examples

end
