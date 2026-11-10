module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.EquivalenceDescent

/-!
# The power of a power, and the transition from degree `d` to a multiple of `d`

Let `T` be a scheme and `L` an invertible `𝒪_T`-module. For an integer `a` the module `L^{⊗ a}`
is again invertible, so it has a Laurent algebra of its own, and the two Laurent algebras are
related by the **power-of-a-power comparison**

`L^{⊗ (i a)} ≅ (L^{⊗ a})^{⊗ i)`,  `i : ℤ`,

which is multiplicative and carries the unit to the unit. This file constructs that comparison
in every integer index, with those two laws, and uses it to build the **transition of a quadruple
of Section 01NS from the degree `d` to a positive multiple `a d` of `d`**: the quadruple
`(d, f, L, ψ)` is carried to `(a d, f, L^{⊗ a}, ψ^{(a)})`, where the degree-`i` component of
`ψ^{(a)}` is the degree-`i a` component of `ψ` followed by the comparison. This is the map the
Stacks source calls `F_d → F_{d'}` for `d ∣ d'`, at the level of quadruples.

## Why it is not a recursion

For `i ≥ 0` the comparison can be built by induction, but the negative integral tensor powers of
Tag 01CU are iterates of a *chosen* quasi-inverse of right tensoring and there is no reason for a
chosen quasi-inverse on the `L^{⊗ a}` side to agree with the `a`-fold iterate on the `L` side. So
the comparison in the negative indices is not a computation but a cancellation, and that
cancellation is exactly what
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaledIso` already performs: it builds, out of a
single isomorphism `L^{⊗ a} ≅ (L')^{⊗ a'}`, a comparison `L^{⊗ i a} ≅ (L')^{⊗ i a'}` in every
integer index together with its multiplicativity in every pair of indices
(`...scaledIso_mul`). The power of a power is the instance `L' = L^{⊗ a}`, `a' = 1` of that
machinery, with the generating isomorphism the identification `(L^{⊗ a})^{⊗ 1} = L^{⊗ a}` of
Tag 01CU.

The indices on the two sides are therefore `i a` on the `L` side and `i * 1` on the `L^{⊗ a}`
side, and `i * 1 = i` only propositionally; `powPowIso` absorbs that reindexing, and
`mulPairIso_reindex` is the bookkeeping lemma that lets a multiplicativity square be moved across
a reindexing of its three degrees.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powModule`: the module `L^{⊗ a}`, in the
  spelling the Laurent algebra of Section 01NS is graded by.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPowIso`: **the power-of-a-power comparison
  `L^{⊗ (i a)} ≅ (L^{⊗ a})^{⊗ i}`**, for every integer `i`, as data, and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPairIso`, the same comparison with its
  source degree prescribed.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.scale`: **the transition of the map
  `ψ` of a quadruple from the degree `d` to the degree `a d`**, and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.scale`: **the transition of a
  quadruple**, for `a` positive.

## What is not here

The descent of the transition to the set `F_d(T)` of strict equivalence classes is not here but
in `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionDescent`. What it needs is
the comparison read as *natural in `L`*: for an isomorphism `γ` of the Laurent algebras of `L`
and `L'` witnessing a strict equivalence, a square relating `powPowIso` for `L` and for `L'`
across `γ` has to commute. Strict equivalence asks only that *some* isomorphism of the Laurent
algebras of the two `a`-th powers exist, so that square is taken there as the definition of its
components and only the multiplicativity of the resulting family is left to prove; the
multiplicativity below is what proves it.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPowIso_mul`: **the comparison is
  multiplicative**, in every pair of integer indices, in the `mulSheaf` vocabulary a
  homomorphism of sheaves of graded algebras is stated at.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPairIso_zero_hom`: the component in the
  index `0` is the identity of the structure sheaf, and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPairIso_oneHom`: **the comparison carries
  the unit of the Laurent algebra of `L` to the unit of the Laurent algebra of `L^{⊗ a}`**.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.scaleApp_mul` and
  `...Twisting.scaleApp_one`: **the transition of `ψ` is again a map of a quadruple**, which is
  what makes the transition well defined.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
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

variable {T : Scheme.{u}}

/-! ### Moving a multiplicativity square across a reindexing -/

section Reindex

variable (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]

/-- **A homogeneous multiplication of the Laurent algebra read across a reindexing of all three
of its degrees.** Multiplying in the degrees `(p, p')` into the degree `s` and then reindexing to
`t` agrees with reindexing the two factors to `(q, q')` and multiplying there. Both sides are
determined by the equalities of integers alone, so the proof is a substitution. -/
theorem mulPairIso_reindex {p p' s q q' t : ℤ} (hp : p = q) (hp' : p' = q') (hs : s = t)
    (h : p + p' = s) (h' : q + q' = t) :
    (mulPairIso M h).hom ≫ (reindexIso M hs).hom =
      ((reindexIso M hp).hom ⊗ₘ (reindexIso M hp').hom) ≫ (mulPairIso M h').hom := by
  subst hp
  subst hp'
  subst hs
  simp only [reindexIso_self, Iso.refl_hom, Category.comp_id, id_tensorHom_id, Category.id_comp]

end Reindex

/-! ### An isomorphism of the unit object which is multiplicative is the identity -/

/-- **An isomorphism of the monoidal unit which is multiplicative for the right unitor is the
identity.** Both unitors agree on the unit object, so the two whiskerings of `g` by the unit are
carried to `g` by the unitor; the multiplicativity then reads `g ∘ g = g`, and `g` is
invertible. -/
private theorem unitIso_hom_eq_id {C : Type*} [Category C] [MonoidalCategory C]
    (g : (𝟙_ C) ≅ (𝟙_ C))
    (h : (g.hom ⊗ₘ g.hom) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ g.hom) :
    g.hom = 𝟙 (𝟙_ C) := by
  have h1 : (g.hom ⊗ₘ g.hom) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ g.hom ≫ g.hom := by
    rw [tensorHom_def, Category.assoc, ← MonoidalCategory.unitors_equal,
      MonoidalCategory.leftUnitor_naturality, MonoidalCategory.unitors_equal, ← Category.assoc,
      MonoidalCategory.rightUnitor_naturality, Category.assoc]
  rw [h1] at h
  have h2 : g.hom ≫ g.hom = g.hom := (Iso.cancel_iso_hom_left (ρ_ (𝟙_ C)) _ _).mp h
  have : IsIso g.hom := g.isIso_hom
  exact (cancel_epi g.hom).mp (h2.trans (Category.comp_id g.hom).symm)

/-! ### The power of a power -/

section PowPow

variable (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The module `L^{⊗ a}`**, in the spelling the Laurent algebra of Section 01NS is graded by:
the degree-`a` piece of the Laurent algebra of `L`. It is again invertible, by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isInvertible_piece`, so it has a Laurent algebra
of its own. -/
abbrev powModule (a : ℤ) : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  (laurent L).piece a

/-- **The generating isomorphism of the power-of-a-power comparison**:
`L^{⊗ (1 a)} ≅ (L^{⊗ a})^{⊗ (1 · 1)}`. Both sides are `L^{⊗ a}` after a reindexing, the
identification of the middle term with the first power being `oneIsoL` of Tag 01CU.

The two degrees are written `1 * a` and `1 * 1` rather than `a` and `1` because that is the shape
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaledIso` anchors its recursion at: the
index-`1` component of the family it builds is then this isomorphism on the nose. -/
def powBeta (a : ℤ) :
    (laurent L).piece (1 * a) ≅ (laurent (powModule L a)).piece (1 * 1) :=
  reindexIso L (one_mul a) ≪≫ (oneIsoL (powModule L a)).symm ≪≫
    reindexIso (powModule L a) (show (1 : ℤ) = 1 * 1 by ring)

/-- **The power-of-a-power comparison `L^{⊗ (i a)} ≅ (L^{⊗ a})^{⊗ i}`**, for every integer `i`,
as data.

For `i ≥ 0` this could be built by iterating the multiplication of Tag 01CU, but the negative
integral tensor powers are iterates of a chosen quasi-inverse of right tensoring and the choice
made for `L^{⊗ a}` need not be the `a`-fold iterate of the one made for `L`; the comparison in a
negative index is therefore obtained by cancellation, which is what `scaledIso` does. -/
def powPowIso (a i : ℤ) : (laurent L).piece (i * a) ≅ (laurent (powModule L a)).piece i :=
  scaledIso (powBeta L a) i ≪≫ reindexIso (powModule L a) (mul_one i)

/-- **The index-`1` component of the comparison is the generating isomorphism**, reindexed: this
is what anchoring the recursion of `scaledIso` at the index `1` buys. -/
theorem powPowIso_one (a : ℤ) :
    powPowIso L a 1 = powBeta L a ≪≫ reindexIso (powModule L a) (mul_one 1) := by
  rw [powPowIso, scaledIso_one]

/-- **The power-of-a-power comparison is multiplicative**, in every pair of integer indices: the
multiplication `L^{⊗ (i a)} ⊗ L^{⊗ (j a)} ⟶ L^{⊗ ((i + j) a)}` of Tag 01CU followed by the
comparison in the index `i + j` agrees with comparing in the indices `i` and `j` and multiplying
in the Laurent algebra of `L^{⊗ a}`.

This is `scaledIso_mul` at `a' = 1` with the reindexing `i * 1 = i` of all three degrees of the
square carried out by `mulPairIso_reindex`. -/
theorem powPowIso_mul (a i j : ℤ) :
    (mulPairIso L (degMul (rfl : i + j = i + j) a)).hom ≫ (powPowIso L a (i + j)).hom =
      ((powPowIso L a i).hom ⊗ₘ (powPowIso L a j).hom) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L a)) i j := by
  have key := scaledIso_mul (powBeta L a) i j (i + j) rfl rfl
  have hre := mulPairIso_reindex (powModule L a) (mul_one i) (mul_one j) (mul_one (i + j))
    (degMul (rfl : i + j = i + j) (1 : ℤ)) (rfl : i + j = i + j)
  change (mulPairIso L (degMul (rfl : i + j = i + j) a)).hom ≫
      (scaledIso (powBeta L a) (i + j)).hom ≫
        (reindexIso (powModule L a) (mul_one (i + j))).hom = _
  rw [← Category.assoc, key, Category.assoc, hre, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, mulSheaf_laurent]
  simp only [mulPairIso, Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.comp_id]
  rfl

/-- **The power-of-a-power comparison in a degree presented as a multiple of `a`**: the
comparison in the index `i`, with its source transported to the prescribed degree `p`.

This is the shape in which the comparison meets a consumer: the degrees of the Laurent algebra
of `L` that it relates to the degrees of the Laurent algebra of `L^{⊗ a}` are those divisible by
`a`, and a consumer presents such a degree together with its cofactor rather than as a
product. -/
def powPairIso (a : ℤ) {p i : ℤ} (hp : p = i * a) :
    (laurent L).piece p ≅ (laurent (powModule L a)).piece i :=
  reindexIso L hp ≪≫ powPowIso L a i

/-- **The comparison is multiplicative, in the degrees a consumer prescribes.** This is
`powPowIso_mul` with the three degrees of the square on the `L` side transported, by
`mulPairIso_reindex`, from `(i a, j a, (i + j) a)` to the prescribed `(p, p', s)`. -/
theorem powPairIso_mul (a : ℤ) {p p' s i j : ℤ} (hp : p = i * a) (hp' : p' = j * a)
    (hs : s = (i + j) * a) (h : p + p' = s) :
    (mulPairIso L h).hom ≫ (powPairIso L a hs).hom =
      ((powPairIso L a hp).hom ⊗ₘ (powPairIso L a hp').hom) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L a)) i j := by
  have hre := mulPairIso_reindex L hp hp' hs h (degMul (rfl : i + j = i + j) a)
  have hpm := powPowIso_mul L a i j
  rw [mulSheaf_laurent] at hpm
  rw [mulSheaf_laurent]
  change (mulPairIso L h).hom ≫ (reindexIso L hs).hom ≫ (powPowIso L a (i + j)).hom = _
  rw [← Category.assoc, hre, Category.assoc, hpm, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rfl

/-- **The component of the comparison in the index `0` is the identity of the structure sheaf.**
The degree-zero pieces of the two Laurent algebras are both the monoidal unit of Tag 01CA, and
the multiplicativity of the comparison in the bidegree `(0, 0)` — where the multiplication of a
Laurent algebra is the right unitor (`mulIso_zero_zero`) — forces an isomorphism of the unit to
be the identity. -/
theorem powPairIso_zero_hom (a : ℤ) :
    (powPairIso L a (show (0 : ℤ) = 0 * a from (zero_mul a).symm)).hom =
      𝟙 (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) := by
  have h0 : (0 : ℤ) = 0 * a := (zero_mul a).symm
  have hs : (0 : ℤ) = (0 + 0) * a := (zero_mul a).symm
  refine unitIso_hom_eq_id (powPairIso L a h0) ?_
  have hmul := powPairIso_mul L a h0 h0 hs (rfl : (0 : ℤ) + 0 = 0)
  have e1 : SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L a)) 0 0 =
      (ρ_ (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))).hom :=
    (mulSheaf_laurent (powModule L a) 0 0).trans (mulIso_zero_zero (powModule L a))
  have e2 : (mulPairIso L (rfl : (0 : ℤ) + 0 = 0)).hom =
      (ρ_ (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))).hom := by
    simp only [mulPairIso, Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.comp_id]
    exact mulIso_zero_zero L
  -- `rw` cannot substitute `e1` and `e2` into `hmul`: the Laurent pieces in degree zero are the
  -- monoidal unit only up to default transparency, so the target is not type-correct at the
  -- `implicit` transparency level that `rw`'s motive is built at, and the pattern is rejected
  -- even though it occurs. Composing the two equalities as terms unifies at default transparency.
  exact (congrArg (fun z => ((powPairIso L a h0).hom ⊗ₘ (powPairIso L a h0).hom) ≫ z) e1).symm.trans
    (hmul.symm.trans (congrArg (· ≫ (powPairIso L a hs).hom) e2))

/-- **The power-of-a-power comparison carries the unit of the Laurent algebra of `L` to the unit
of the Laurent algebra of `L^{⊗ a}`**, which is the remaining law of a homomorphism of sheaves of
graded algebras. Both units are the identity of the structure sheaf (`oneHom_laurent`), so this
is `powPairIso_zero_hom`. -/
theorem powPairIso_oneHom (a : ℤ) :
    SheafOfModules.GradedAlgebra.oneHom (laurent L) ≫
        (powPairIso L a (show (0 : ℤ) = 0 * a from (zero_mul a).symm)).hom =
      SheafOfModules.GradedAlgebra.oneHom (laurent (powModule L a)) :=
  ((congrArg (fun z => SheafOfModules.GradedAlgebra.oneHom (laurent L) ≫ z)
          (powPairIso_zero_hom L a)).trans
        (Category.comp_id (SheafOfModules.GradedAlgebra.oneHom (laurent L)))).trans
    ((oneHom_laurent L).trans (oneHom_laurent (powModule L a)).symm)

end PowPow

/-! ### The transition from the degree `d` to a multiple of `d` -/

section Scale

variable {S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **A multiplication of `f^*𝒜` read across a reindexing of the two degrees it multiplies and of
the degree it lands in.** The comparison of Tag 01CD is taken at the reindexed degrees on one side
and at the original ones on the other, and the two sides are identified by transporting the three
degrees; since every transport is the pullback of an `eqToHom`, the whole identity is determined
by the equalities of integers and the proof is a substitution.

This is the only bookkeeping the transition below needs, and it is stated with the trailing
morphism `z` a free variable so that it applies to the composite the transition presents without
any reassociation. -/
private theorem pullbackMulSheaf_transport
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    {p q p' q' t t' w : ℤ} (hp : p = p') (hq : q = q')
    (u : p + q = t) (v : t = w) (u' : p' + q' = t') (v' : t' = w)
    {Y : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (z : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece w) ⟶ Y) :
    ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ⊗ₘ
          (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hq))) ≫
        inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece p') (A.piece q')) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
              (SheafOfModules.GradedAlgebra.mulSheaf A p' q' ≫
                eqToHom (congrArg A.piece u')) ≫
            (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece v')) ≫ z =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece p) (A.piece q)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (SheafOfModules.GradedAlgebra.mulSheaf A p q ≫ eqToHom (congrArg A.piece u)) ≫
          (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece v)) ≫ z := by
  subst hp
  subst hq
  subst v'
  subst v
  simp

namespace Twisting

/-- **The components of `ψ` are compatible with reindexing the degree.** -/
theorem app_reindex (ψ : Twisting f A d L) {m n : ℤ} (h : m = n) :
    ψ.app m ≫ (reindexIso L h).hom =
      (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (congrArg (fun k => k * d) h))) ≫ ψ.app n := by
  subst h
  simp only [reindexIso_self, Iso.refl_hom, Category.comp_id, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The degree-`i` component of the transition of `ψ` from the degree `d` to the degree
`a d`**: the component of `ψ` in the degree `i a` of the Veronese regrading, followed by the
power-of-a-power comparison `L^{⊗ (i a)} ≅ (L^{⊗ a})^{⊗ i}`.

The Stacks source describes the transition `F_d → F_{a d}` as sending `(d, f, L, ψ)` to
`(a d, f, L^{⊗ a}, ψ^{(a)})`, and this is `ψ^{(a)}`. -/
def scaleApp (ψ : Twisting f A d L) (a i : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * (a * d))) ⟶
      (laurent (powModule L a)).piece i :=
  (pullbackFunctor (ringedSpaceHom f)).map
      (eqToHom (congrArg A.piece (by ring : i * (a * d) = i * a * d))) ≫
    ψ.app (i * a) ≫ (powPowIso L a i).hom

/-- **The transition of `ψ` is multiplicative**, which is the `app_mul` law of a `Twisting` over
the degree `a d` with invertible module `L^{⊗ a}`.

Three facts meet: the multiplicativity `powPowIso_mul` of the power-of-a-power comparison, the
multiplicativity `Twisting.app_mul` of `ψ` in the bidegree `(i a, j a)`, and `app_reindex`, which
moves `ψ` across the identification of the degree `i a + j a` with `(i + j) a`. What is left is
the transport of the degrees `i (a d)` and `j (a d)` to `(i a) d` and `(j a) d`, which is
`pullbackMulSheaf_transport`. -/
theorem scaleApp_mul (ψ : Twisting f A d L) (a i j : ℤ) :
    (ψ.scaleApp a i ⊗ₘ ψ.scaleApp a j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L a)) i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * (a * d)))
          (A.piece (j * (a * d)))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (SheafOfModules.GradedAlgebra.mulSheaf A (i * (a * d)) (j * (a * d)) ≫
              eqToHom (congrArg A.piece
                (by ring : i * (a * d) + j * (a * d) = (i + j) * (a * d)))) ≫
          ψ.scaleApp a (i + j) := by
  have hpm := powPowIso_mul L a i j
  rw [mulSheaf_laurent] at hpm
  have hmul := ψ.app_mul (i * a) (j * a)
  rw [mulSheaf_laurent] at hmul
  have hmul' := congrArg (fun z => z ≫
    (reindexIso L (degMul (rfl : i + j = i + j) a)).hom ≫ (powPowIso L a (i + j)).hom) hmul
  have hre' := congrArg (fun z => z ≫ (powPowIso L a (i + j)).hom)
    (ψ.app_reindex (degMul (rfl : i + j = i + j) a))
  simp only [Category.assoc] at hmul' hre'
  rw [mulSheaf_laurent]
  simp only [scaleApp, ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  rw [← hpm]
  simp only [mulPairIso, Iso.trans_hom, Category.assoc]
  rw [hmul', hre']
  exact pullbackMulSheaf_transport A (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) _

/-- **The transition of `ψ` preserves the distinguished degree-zero unit**, which is the
`app_one` law of a `Twisting` over the degree `a d`. The degree-zero component of the transition
is the degree-zero component of `ψ` followed by the degree-zero component of the comparison, and
the latter is the identity (`powPairIso_zero_hom`). -/
theorem scaleApp_one (ψ : Twisting f A d L) (a : ℤ) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * (a * d)))) ≫
        ψ.scaleApp a 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent (powModule L a)) := by
  have hzero : (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * (a * d)))) ≫ ψ.scaleApp a 0 =
      (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ ψ.app 0 ≫
        (powPairIso L a (show (0 : ℤ) = 0 * a from (zero_mul a).symm)).hom := by
    have hr := congrArg (fun z => z ≫ (powPowIso L a 0).hom)
      (ψ.app_reindex (show (0 : ℤ) = 0 * a from (zero_mul a).symm))
    simp only [Category.assoc] at hr
    simp only [scaleApp, powPairIso, Iso.trans_hom]
    rw [hr]
    simp only [← Functor.map_comp_assoc, eqToHom_trans]
  rw [hzero, powPairIso_zero_hom]
  refine Eq.trans ?_ ψ.app_one
  exact congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
    (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ z)
    (Category.comp_id (ψ.app 0))

/-- **The transition of `ψ` from the degree `d` to the degree `a d`**, as the map `ψ` of a
quadruple over the degree `a d` with invertible module `L^{⊗ a}`. -/
def scale (ψ : Twisting f A d L) (a : ℤ) : Twisting f A (a * d) (powModule L a) where
  app i := ψ.scaleApp a i
  app_mul i j := ψ.scaleApp_mul a i j
  app_one := ψ.scaleApp_one a

/-- The components of the transition are `Twisting.scaleApp`. -/
@[simp] theorem scale_app (ψ : Twisting f A d L) (a i : ℤ) :
    (ψ.scale a).app i = ψ.scaleApp a i := rfl

end Twisting

namespace Quadruple

/-- **The transition of a quadruple from the degree `d` to the degree `a d`**, for `a` positive:
`(d, f, L, ψ)` is carried to `(a d, f, L^{⊗ a}, ψ^{(a)})`.

The surjectivity Section 01NS requires of the degree-one component is the only thing beyond
`Twisting.scale` that has to be checked, and it holds because `ψ_a` is surjective as soon as
`ψ_1` is (`Twisting.epi_app_of_pos`, which is where the positivity of `a` is used), the
power-of-a-power comparison is an isomorphism, and so is the reindexing of the degree. -/
def scale (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) : Quadruple f A (a * d) where
  L := powModule P.L a
  isInvertible := isInvertible_piece P.L a
  twisting := P.twisting.scale a
  epi_app_one := by
    have h1 : Epi (P.twisting.app (1 * a)) :=
      P.twisting.epi_app_of_pos P.epi_app_one (by rw [one_mul]; exact ha)
    change Epi ((pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg A.piece (by ring : (1 : ℤ) * (a * d) = 1 * a * d))) ≫
      P.twisting.app (1 * a) ≫ (powPowIso P.L a 1).hom)
    infer_instance

/-- The invertible module of the transition is `L^{⊗ a}`. -/
@[simp] theorem scale_L (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) :
    (P.scale ha).L = powModule P.L a := rfl

/-- The components of the map `ψ` of the transition are `Twisting.scaleApp`. -/
@[simp] theorem scale_twisting_app (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) (i : ℤ) :
    (P.scale ha).twisting.app i = P.twisting.scaleApp a i := rfl

end Quadruple

end Scale

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
