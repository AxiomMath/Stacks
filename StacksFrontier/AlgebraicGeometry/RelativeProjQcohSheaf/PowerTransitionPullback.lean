module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionColimit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# The transitions are maps of functors

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `a ≥ 1`. The transition
`...PowerTransitionDescent.Fd.scale` sends a class of `F_d(T)` to the class of
`(a d, f, L^{⊗ a}, ψ^{(a)})` in `F_{a d}(T)`. This file proves that it **commutes with the map
`F_d(T) → F_d(T')` of a morphism `g : T' ⟶ T` of test schemes**, so that the transitions are
morphisms `F_d ⟶ F_{a d}` of the functors `...UnionFunctor.Fd.functor`, not merely maps of their
values; that morphism is `Fd.scaleNat`.

## The comparison this does *not* need

What has to be compared is the pullback of the transition with the transition of the pullback:
the first has invertible module `g^*(L^{⊗ a})`, the second `(g^*L)^{⊗ a}`. Those are **not** the
same sheaf, and the obvious route is to build the comparison `g^*(L^{⊗ a}) ≅ (g^*L)^{⊗ a}` of
Laurent algebras and check it against the power-of-a-power comparison `...powPowIso` on both
sides — a coherence that is genuinely not in the repository.

That route is not taken, and it is not needed. A quadruple `P` of degree `d` is compatible at
`(a, 1)` with its transition `P.scale` (`...Quadruple.compatibleAt_scale`), and
`...Quadruple.CompatibleAt.pullback` carries a compatibility along `g`. So `g` turns that one
compatibility into a compatibility of `P.pullback g` with `(P.scale).pullback g` at `(a, 1)` —
while `compatibleAt_scale` applied to `P.pullback g` gives a compatibility of `P.pullback g`
with `(P.pullback g).scale` at `(a, 1)`. The two candidates are thus both compatible at `(a, 1)`
with the *same* quadruple, and the theorem below says that already makes them strictly
equivalent.

## Why compatibility at `(a, 1)` pins a quadruple down

A comparison at `(a, a')` has a component only in the degrees `(n a, n a')`, so for general `a'`
it says nothing about the degrees of the second Laurent algebra that `a'` does not divide. For
`a' = 1` it has a component `L^{⊗ (n a)} ≅ (L')^{⊗ n}` in **every** degree `n`, and the
components are multiplicative and carry `ψ` to `ψ'`. Two such comparisons out of one quadruple
therefore compose, after one is read backwards, to an isomorphism of the Laurent algebras of the
two second modules carrying one `ψ` to the other — which is exactly a strict equivalence. That
composite is `comparePairIso`, and the only bookkeeping is that a comparison at `(a, 1)` is
indexed by the degree `n · 1` where a strict equivalence wants `n`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.comparePairIso`: **the isomorphism of the
  Laurent algebras of two modules whose quadruples are both compatible at `(a, 1)` with a
  third.**
* `...RelativeProjQcohSheaf.Fd.scaleNat`: **the transition `F_d ⟶ F_{a d}` as a morphism of
  functors.**

## Main results

* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_of_compatibleAt_one`: **two quadruples
  compatible at `(a, 1)` with one and the same quadruple are strictly equivalent** — a quadruple
  determines its transition up to strict equivalence.
* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_pullback_scale` and
  `...RelativeProjQcohSheaf.Fd.pullback_scale`: **the transition commutes with the pullback along
  a morphism of test schemes.**

## What is not here

Representability is not proved and nothing is assumed: there is no scheme representing anything
anywhere below. The remaining steps of Tag 01NY are recorded on
`...PowerTransitionColimit.Fd.scale_eq_of_equivalent`.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] isInvertible_piece

/-! ### Conjugating two multiplicativity squares over a common source -/

/-- **Two multiplicative comparisons of one grading differ by a multiplicative comparison**:
`conj_mul_square` at the identity, which is the only case the comparison of two quadruples
compatible with a third needs. -/
private theorem conj_mul_square_id {C : Type*} [Category C] [MonoidalCategory C]
    {A₁ A₂ A₃ B₁ B₂ B₃ D₁ D₂ D₃ : C}
    (p₁ : A₁ ≅ B₁) (p₂ : A₂ ≅ B₂) (p₃ : A₃ ≅ B₃)
    (q₁ : A₁ ≅ D₁) (q₂ : A₂ ≅ D₂) (q₃ : A₃ ≅ D₃)
    (mA : A₁ ⊗ A₂ ⟶ A₃) (mB : B₁ ⊗ B₂ ⟶ B₃) (mD : D₁ ⊗ D₂ ⟶ D₃)
    (hp : mA ≫ p₃.hom = (p₁.hom ⊗ₘ p₂.hom) ≫ mB)
    (hq : mA ≫ q₃.hom = (q₁.hom ⊗ₘ q₂.hom) ≫ mD) :
    mB ≫ p₃.inv ≫ q₃.hom = ((p₁.inv ≫ q₁.hom) ⊗ₘ (p₂.inv ≫ q₂.hom)) ≫ mD := by
  have h := conj_mul_square p₁ p₂ p₃ q₁ q₂ q₃ mA mB mA mD
    (CategoryStruct.id A₁) (CategoryStruct.id A₂) (CategoryStruct.id A₃) hp hq (by simp)
  simp only [Category.id_comp] at h
  exact h

/-! ### The comparison of two quadruples compatible at `(a, 1)` with a third -/

section ComparePair

variable {T : Scheme.{u}}
  {L LY LZ : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) LY]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) LZ]
  {a : ℤ}

/-- **The component at `(i a, i)` of a comparison at `(a, 1)`.** The degrees at which a
comparison at `(a, 1)` has a component are the pairs `(i a, i · 1)`, so the family covers
*every* degree of the Laurent algebra of the second module; this is the component read at the
spelling `i` of the degree `i · 1`. -/
abbrev oneFamilyAt (γ : ScaledFamily L LY a 1) (i : ℤ) :
    (laurent L).piece (i * a) ≅ (laurent LY).piece i :=
  familyAt γ i ≪≫ reindexIso LY (show i * 1 = i by ring)

/-- **A comparison at `(a, 1)` is multiplicative from the bidegree `(i a, j a)` of the first
Laurent algebra to the bidegree `(i, j)` of the second.** This is `mulPairIso_familyAt`, with the
three degrees `(i · 1, j · 1, (i + j) · 1)` of the target transported to `(i, j, i + j)` by
`mulPairIso_reindex`. -/
theorem mulSheaf_oneFamilyAt (γ : ScaledFamily L LY a 1) (hmul : IsMulScaledFamily γ) (i j : ℤ) :
    (mulPairIso L (degMul (rfl : i + j = i + j) a)).hom ≫ (oneFamilyAt γ (i + j)).hom =
      ((oneFamilyAt γ i).hom ⊗ₘ (oneFamilyAt γ j).hom) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent LY) i j := by
  have hre := mulPairIso_reindex LY (show i * 1 = i by ring) (show j * 1 = j by ring)
    (show (i + j) * 1 = i + j by ring) (degMul (rfl : i + j = i + j) (1 : ℤ))
    (rfl : i + j = i + j)
  show (mulPairIso L (degMul (rfl : i + j = i + j) a)).hom ≫
      (familyAt γ (i + j)).hom ≫ (reindexIso LY (show (i + j) * 1 = i + j by ring)).hom =
    (((familyAt γ i).hom ≫ (reindexIso LY (show i * 1 = i by ring)).hom) ⊗ₘ
        ((familyAt γ j).hom ≫ (reindexIso LY (show j * 1 = j by ring)).hom)) ≫
      SheafOfModules.GradedAlgebra.mulSheaf (laurent LY) i j
  rw [mulSheaf_laurent, ← Category.assoc, mulPairIso_familyAt γ hmul i j, Category.assoc, hre,
    ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [mulPairIso, Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.comp_id]

/-- **The degreewise comparison of two quadruples both compatible at `(a, 1)` with a third**: the
component of the first comparison read backwards followed by the component of the second. -/
def comparePairApp (γ : ScaledFamily L LY a 1) (δ : ScaledFamily L LZ a 1) (i : ℤ) :
    (laurent LY).piece i ⟶ (laurent LZ).piece i :=
  (oneFamilyAt γ i).inv ≫ (oneFamilyAt δ i).hom

/-- **The degreewise comparison is multiplicative in every integral bidegree**, which is the
`map_mul` law of a homomorphism of sheaves of graded algebras: both comparisons are multiplicative
out of the same bidegree `(i a, j a)` of the Laurent algebra of the first module. -/
theorem comparePairApp_mulSheaf (γ : ScaledFamily L LY a 1) (hγ : IsMulScaledFamily γ)
    (δ : ScaledFamily L LZ a 1) (hδ : IsMulScaledFamily δ) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent LY) i j ≫ comparePairApp γ δ (i + j) =
      (comparePairApp γ δ i ⊗ₘ comparePairApp γ δ j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent LZ) i j :=
  conj_mul_square_id (oneFamilyAt γ i) (oneFamilyAt γ j) (oneFamilyAt γ (i + j))
    (oneFamilyAt δ i) (oneFamilyAt δ j) (oneFamilyAt δ (i + j)) _ _ _
    (mulSheaf_oneFamilyAt γ hγ i j) (mulSheaf_oneFamilyAt δ hδ i j)

/-- **The isomorphism of the Laurent algebras of two modules whose quadruples are both compatible
at `(a, 1)` with a third.** -/
def comparePairIso (γ : ScaledFamily L LY a 1) (hγ : IsMulScaledFamily γ)
    (δ : ScaledFamily L LZ a 1) (hδ : IsMulScaledFamily δ) : laurent LY ≅ laurent LZ where
  hom := homOfMulSheaf _ _ (comparePairApp γ δ) (comparePairApp_mulSheaf γ hγ δ hδ)
  inv := homOfMulSheaf _ _ (comparePairApp δ γ) (comparePairApp_mulSheaf δ hδ γ hγ)
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun i => by
    change comparePairApp γ δ i ≫ comparePairApp δ γ i =
      CategoryStruct.id ((laurent LY).piece i)
    simp only [comparePairApp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun i => by
    change comparePairApp δ γ i ≫ comparePairApp γ δ i =
      CategoryStruct.id ((laurent LZ).piece i)
    simp only [comparePairApp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-- The component in degree `i` of `comparePairIso γ hγ δ hδ` is `comparePairApp γ δ i`. -/
@[simp] theorem comparePairIso_hom_app (γ : ScaledFamily L LY a 1) (hγ : IsMulScaledFamily γ)
    (δ : ScaledFamily L LZ a 1) (hδ : IsMulScaledFamily δ) (i : ℤ) :
    (comparePairIso γ hγ δ hδ).hom.app i = comparePairApp γ δ i :=
  rfl

end ComparePair

/-! ### A quadruple determines its transition up to strict equivalence -/

namespace Quadruple

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d e a : ℤ}

/-- **The `ψ`-clause of a comparison at `(a, 1)`, read at the spelling `i` of the degree
`i · 1`.** -/
private theorem app_comp_oneFamilyAt (X : Quadruple f A d) (Y : Quadruple f A e)
    (hm : a * d = 1 * e) (γ : ScaledFamily X.L Y.L a 1)
    (hψ : ∀ (p q : ℤ) (h : IsScaledPair a 1 p q),
      X.twisting.app p ≫ (γ p q h).hom =
        (pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (h.degree_eq hm))) ≫ Y.twisting.app q)
    (n : ℤ) :
    X.twisting.app (n * a) ≫ (oneFamilyAt γ n).hom =
      (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece
            (show n * a * d = n * e by rw [mul_assoc, hm, one_mul]))) ≫
        Y.twisting.app n := by
  have h1 := hψ (n * a) (n * 1) ⟨n, rfl, rfl⟩
  have h2 := Y.twisting.app_reindex (show n * 1 = n by ring)
  show X.twisting.app (n * a) ≫
      (γ (n * a) (n * 1) ⟨n, rfl, rfl⟩).hom ≫
        (reindexIso Y.L (show n * 1 = n by ring)).hom = _
  rw [← Category.assoc, h1, Category.assoc, h2]
  simp only [CategoryTheory.eqToHom_map, eqToHom_trans_assoc]

/-- **A quadruple determines its transition to a multiple of its degree up to strict
equivalence.** Two quadruples `Y` and `Z` of degree `e` that are both compatible at `(a, 1)` with
one quadruple `X` of degree `d` — which is what `Quadruple.compatibleAt_scale` says of the
transition `X.scale` — are strictly equivalent.

A comparison at `(a, 1)` has a component in *every* degree of the Laurent algebra of the second
module, so the two comparisons compose to an isomorphism `comparePairIso` of the Laurent algebras
of `Y.L` and `Z.L`; it carries `ψ_Y` to `ψ_Z` because both are carried from `ψ_X` by the same
transport of the degree. -/
theorem strictlyEquivalent_of_compatibleAt_one {X : Quadruple f A d} {Y Z : Quadruple f A e}
    (hY : CompatibleAt X Y a 1) (hZ : CompatibleAt X Z a 1) : StrictlyEquivalent Y Z := by
  obtain ⟨hm, γ, hγ, -, hψY⟩ := hY
  obtain ⟨hm', δ, hδ, -, hψZ⟩ := hZ
  refine (strictlyEquivalent_iff_exists_hom _ _).mpr ⟨comparePairIso γ hγ δ hδ, fun n => ?_⟩
  have hY' := app_comp_oneFamilyAt X Y hm γ hψY n
  have hZ' := app_comp_oneFamilyAt X Z hm' δ hψZ n
  have hdeg : n * a * d = n * e := by rw [mul_assoc, hm, one_mul]
  refine (CategoryTheory.cancel_epi ((pullbackFunctor (ringedSpaceHom f)).map
    (eqToHom (congrArg A.piece hdeg)))).mp ?_
  show (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hdeg)) ≫
      Y.twisting.app n ≫ comparePairApp γ δ n = _
  rw [← Category.assoc, ← hY', Category.assoc]
  simp only [comparePairApp, Iso.hom_inv_id_assoc]
  exact hZ'

/-- **The transition commutes with the pullback along a morphism of test schemes.** The
transition of the pullback and the pullback of the transition are both compatible at `(a, 1)`
with the pullback of the quadruple — the first by `Quadruple.compatibleAt_scale`, the second
because `CompatibleAt.pullback` carries the compatibility of the quadruple with its transition
along `g` — so they are strictly equivalent. -/
theorem strictlyEquivalent_pullback_scale {T' : Scheme.{u}} (P : Quadruple f A d) {a : ℤ}
    (ha : 0 < a) (g : T' ⟶ T) :
    StrictlyEquivalent ((P.scale ha).pullback g) ((P.pullback g).scale ha) :=
  strictlyEquivalent_of_compatibleAt_one ((P.compatibleAt_scale ha).pullback g)
    ((P.pullback g).compatibleAt_scale ha)

end Quadruple

/-! ### The transitions as maps of functors -/

/-- **The transition `F_d(T) → F_{a d}(T)` commutes with the map `F_d(T) → F_d(T')` of a
morphism `g : T' ⟶ T` of test schemes.** On classes of quadruples this is
`Quadruple.strictlyEquivalent_pullback_scale`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   the representability of F is NOT proved here and nothing is assumed: the transitions
--   F_d → F_{a d} COMMUTE with the maps F_d(T) → F_d(T') of morphisms of test schemes, so they are
--   maps of the FUNCTORS F_d of Tag 01NS and not only of their values; `Fd.scaleNat` is the
--   resulting morphism of functors. This closes residue (ii) recorded on
--   `Fd.scale_eq_of_equivalent`, and REFUTES the route recorded there: the comparison
--   g^*(L^{⊗ a}) ≅ (g^*L)^{⊗ a} of Laurent algebras is NOT needed the pulled-back transition and
--   the transition of the pullback are both compatible at (a, 1) with the pullback of the
--   quadruple (Quadruple.compatibleAt_scale and Quadruple.CompatibleAt.pullback, both already in
--   the tree), and `Quadruple.strictlyEquivalent_of_compatibleAt_one` shows that already forces
--   strict equivalence. NOTHING IS MISSING for Tag 01NY any more: residue (i), the
--   representability of each F_d by a scheme U_d over S, is Tag 01NU proved over an affine base as
--   AffineFdRepresentable.Fd.representableByDegreeOpen and descended to a general base as
--   ChartDegreeOpenEquiv.ProjDegreeRepresentation.ofCharts and residue (iii), the nesting and
--   covering of the U_d, is RelativeProjData.isOpenCover_degreeOpen; the tag itself is
--   RelativeProjRepresents.F.representableByRelativeProjOfCharts, unconditional over an arbitrary
--   base
theorem Fd.pullback_scale {T' T S : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d a : ℤ}
    (ha : 0 < a) (g : T' ⟶ T) (ξ : Fd A d T) :
    Fd.pullback g (Fd.scale ha ξ) = Fd.scale ha (Fd.pullback g ξ) := by
  obtain ⟨f, x⟩ := ξ
  induction x using Quotient.ind with
  | _ P => exact (Fd.mk_eq_mk_iff _ _).mpr (P.strictlyEquivalent_pullback_scale ha g)

/-- **The transition `F_d → F_{a d}` as a morphism of the functors of Tag 01NS**: on each test
scheme it is `Fd.scale`, and its naturality is `Fd.pullback_scale`.

This is the sense in which the Stacks proof of Tag 01NY uses the transitions: it builds the
scheme representing `F` as a union of schemes representing the `F_d` along *morphisms of
functors* `F_d → F_{d'}`, which have to exist before they can correspond to morphisms of
schemes. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   the representability of F is NOT proved here and nothing is assumed: the transition
--   F_d → F_{a d} packaged as a MORPHISM OF THE FUNCTORS of Tag 01NS, whose naturality is
--   Fd.pullback_scale. Stated with F_d the functor
--   StacksDraft.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor, which is Tag 01NS and not this
--   tag; nothing here represents any functor by a scheme. Part of the covering set of residue (ii)
--   together with Fd.pullback_scale
def Fd.scaleNat {S : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    {a : ℤ} (ha : 0 < a) : Fd.functor A d ⟶ Fd.functor A (a * d) where
  app _ := TypeCat.ofHom (Fd.scale (A := A) (d := d) ha)
  naturality _ _ φ :=
    TypeCat.homEquiv.injective (funext fun ξ => (Fd.pullback_scale ha φ.unop ξ).symm)

/-- On a test scheme `T`, the component of `Fd.scaleNat A d ha` is `Fd.scale ha`. -/
@[simp] theorem Fd.scaleNat_app {S T : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    {a : ℤ} (ha : 0 < a) (ξ : Fd A d T) :
    (Fd.scaleNat A d ha).app (Opposite.op T) ξ = Fd.scale ha ξ :=
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
