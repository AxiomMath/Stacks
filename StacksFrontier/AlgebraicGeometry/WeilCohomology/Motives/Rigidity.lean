module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Duality
public import StacksCore.CategoryTheory.Monoidal.Rigid.Retract
public import Mathlib.CategoryTheory.Retract
public import StacksCore.Tactic.StacksAttribute

/-!
# Rigidity of the category of motives

Every object of the category `M_k` of Chow motives has a left dual, so `M_k` is a rigid
category.

The source's proof is formal once duality for the motive of a smooth projective scheme is
available, and it is carried out here in a monoidal category. A motive `M = (X, p, m)` is a
summand of `(X, 1, m) = h(X)(m) = h(X) ⊗ 1(m)`; a summand of a dualizable object is dualizable
(Stacks 0FFU); a tensor product of dualizable objects is dualizable (Stacks 0FFS); the Tate
object `1(m)` is invertible, hence dualizable with dual `1(-m)`; and `h(X)` is dualizable by
Stacks 0FGI.

## Main definitions

* `Stacks.WeilCohomology.hasRightDualTwist`: an invertible Tate object `1(m)` is dualizable,
  with `1(-m)` as its dual.

## Main results

* `Stacks.WeilCohomology.nonempty_hasRightDual_of_retract_twist` and
  `Stacks.WeilCohomology.hasRightDualOfRetractTwist`: every object which is a retract of some
  `h(X) ⊗ 1(m)` has a left dual.
* `Stacks.WeilCohomology.rightRigidCategoryOfRetractTwist`: **Stacks 0FGJ**, every object of
  `M_k` has a left dual.
* `Stacks.WeilCohomology.rightRigidCategoryOfDiagonalPairingData`: the same conclusion with the
  duality of the motives `h(X)` supplied by this repository's Stacks 0FGI, i.e. by
  `Stacks.WeilCohomology.DiagonalPairingData`, rather than assumed.

## Implementation notes

**Which duality.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Duality`, Stacks 0FFP calls `Y` a *left
dual* of `X` when there are `η : 1 ⟶ X ⊗ Y` and `ε : Y ⊗ X ⟶ 1` whose two triangle composites
are the identity; that datum is Mathlib's `CategoryTheory.ExactPairing X Y`, which Mathlib names
`CategoryTheory.HasRightDual X`. So "every object has a left dual" is Mathlib's
`CategoryTheory.RightRigidCategory`.

**Where the statement lives.** The category `M_k` of motives of Stacks 0FGA is
`Stacks.WeilCohomology.CorrespondenceStructure.Motive`, the Karoubi envelope of the category of
correspondences. Its symmetric monoidal structure is Stacks 0FGC, which is *not* constructed in
this repository, so `h(X) ⊗ 1(m)` cannot be written there at all. Accordingly the result is
stated in an arbitrary monoidal category `Mot` — to be read as `M_k` — with a family
`h : D → Mot` of the motives of the smooth projective schemes over `k`, untwisted, and with the
Tate objects `1(m)` supplied separately as a family `T : ℤ → Mot`. This is the setting of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ManinIdentityPrinciple`, and the
hypotheses below are written to match it verbatim: `T` is its
`Stacks.WeilCohomology.ChowRepresentability.unitTwist`, `hT` its `tateExactPairing`, and `hgen`
its own generation hypothesis. The statement specialises to the source's setting the moment
0FGC lands. No motive, no `h(X)`, no tensor product of motives is redefined here.

**The carried hypotheses.** Three inputs of the source's proof are unavailable in this
repository and are carried as explicit hypotheses.

* The *invertibility of the Tate motive*: `1(m)` is a left dual of `1(-m)`, the hypothesis `hT`.
  This is the input of Stacks 0FFS below.
* The *generating property* of the motives of smooth projective schemes: every object of `M_k`
  is a direct summand of some twist `h(X)(m)`, the hypothesis `hgen`. For the Karoubi envelope
  this is immediate — `(X, p, m)` is cut out of `(X, 1, m)` by `p` — but it is a statement about
  the monoidal structure of 0FGC, which is absent. "Direct summand" is taken in the weakest
  useful sense, as `CategoryTheory.Retract`: a pair `i : L ⟶ L'`, `r : L' ⟶ L` with
  `i ≫ r = 𝟙 L`, which makes the theorem stronger.
* *Stacks 0FGI*, duality for the motive of a smooth projective scheme, the hypothesis `hh`. The
  repository proves this — `Stacks.WeilCohomology.hasRightDual_motiveOf` — from the carried
  `Stacks.WeilCohomology.DiagonalPairingData`, whose content is the source's two composition
  formulas for the diagonal; `rightRigidCategoryOfDiagonalPairingData` below feeds exactly that
  in, so `hh` is not an extra assumption beyond what 0FGI already costs. Note also that 0FGI
  applies to an `X` equidimensional of dimension `d`, whereas `hgen` ranges over all smooth
  projective `X`; the source bridges the two by writing `X = ⨿ Xᵢ`, whence
  `h(X) = ⨁ h(Xᵢ)`, and invoking Stacks 0FFT. That step is
  `CategoryTheory.hasRightDualBiprod` of `StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts`, and
  it is a statement about the biproducts of `M_k`, so like the rest of the additive structure of
  0FGC it is absorbed into `hh` rather than reproved.

**Karoubian.** Stacks 0FFU, that a summand of a dualizable object is dualizable, needs the
category to be Karoubian; here that is `CategoryTheory.IsIdempotentComplete Mot`, which for the
Karoubi envelope `M_k` holds. It is the only typeclass hypothesis added to the monoidal
structure.

## References

* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FFS](https://stacks.math.columbia.edu/tag/0FFS)
* [Stacks Project, Tag 0FFT](https://stacks.math.columbia.edu/tag/0FFT)
* [Stacks Project, Tag 0FFU](https://stacks.math.columbia.edu/tag/0FFU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe w v u

namespace Stacks.WeilCohomology

/-! ### Duals of the Tate objects -/

variable {Mot : Type u} [Category.{v} Mot] [MonoidalCategory Mot]

/-- The invertibility of the Tate motive is symmetric in the sign of the twist: if `1(m)` is a
left dual of `1(-m)` for every `m`, then `1(-m)` is a left dual of `1(m)` as well — apply the
hypothesis at `-m`. -/
@[instance_reducible]
def exactPairingTwistNeg (T : ℤ → Mot) (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m)) (m : ℤ) :
    ExactPairing (T m) (T (-m)) := by
  have h := hT (-m)
  rwa [neg_neg] at h

/-- An invertible Tate object is dualizable: `1(-m)` is a left dual of `1(m)`. -/
@[instance_reducible]
def hasRightDualTwist (T : ℤ → Mot) (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m)) (m : ℤ) :
    HasRightDual (T m) where
  rightDual := T (-m)
  exact := exactPairingTwistNeg T hT m

/-! ### Every motive has a left dual -/

variable [IsIdempotentComplete Mot] {D : Type w}

/-- An object which is a retract of a twist `h(X)(m) = h(X) ⊗ 1(m)` of a dualizable `h(X)` has a
left dual.

This is the whole of Stacks 0FGJ: `h(X) ⊗ 1(m)` is dualizable by Stacks 0FFS
(`CategoryTheory.hasRightDualTensor`) since `h(X)` is dualizable by hypothesis and `1(m)` is
invertible, and a retract of a dualizable object is dualizable by Stacks 0FFU
(`CategoryTheory.nonempty_hasRightDual_of_retract`). -/
theorem nonempty_hasRightDual_of_retract_twist (h : D → Mot)
    (hh : ∀ X : D, HasRightDual (h X)) (T : ℤ → Mot)
    (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m))
    (hgen : ∀ L : Mot, ∃ (X : D) (m : ℤ), Nonempty (Retract L (h X ⊗ T m)))
    (L : Mot) : Nonempty (HasRightDual L) := by
  obtain ⟨X, m, ⟨ρ⟩⟩ := hgen L
  let _dualh := hh X
  let _dualT := hasRightDualTwist T hT m
  let _dual : HasRightDual (h X ⊗ T m) := hasRightDualTensor
  exact nonempty_hasRightDual_of_retract ρ

/-- `Stacks.WeilCohomology.nonempty_hasRightDual_of_retract_twist` as data: the left dual of a
retract of a twist `h(X)(m)`. -/
@[instance_reducible]
def hasRightDualOfRetractTwist (h : D → Mot) (hh : ∀ X : D, HasRightDual (h X)) (T : ℤ → Mot)
    (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m))
    (hgen : ∀ L : Mot, ∃ (X : D) (m : ℤ), Nonempty (Retract L (h X ⊗ T m)))
    (L : Mot) : HasRightDual L :=
  (nonempty_hasRightDual_of_retract_twist h hh T hT hgen L).some

/-- **Stacks Project, Tag 0FGJ.** Every object of the category `M_k` of motives has a left dual,
i.e. `M_k` is a rigid category.

Here `Mot` is the category `M_k` of motives of Stacks 0FGA, monoidal by Stacks 0FGC, `h X` is the
motive of a smooth projective scheme `X` over `k`, and `T m` is the Tate object `1(m)`. The
hypothesis `hh` is Stacks 0FGI, that `h(X)` has a left dual — supplied from this repository's
own 0FGI by `Stacks.WeilCohomology.rightRigidCategoryOfDiagonalPairingData` below; `hT` is the
invertibility of the Tate motive, that `1(m)` is a left dual of `1(-m)`; and `hgen` says that
every motive is a direct summand of a twist `h(X)(m)`. See the implementation notes of this file
for why each is carried rather than used. -/
@[stacks 0FGJ "every object of M_k has a left dual, i.e. M_k is right rigid in Mathlib's naming.
STATED IN AN ABSTRACT MONOIDAL CATEGORY, not on this library's category of motives, because the
monoidal structure on Karoubi S.Obj is Stacks 0FGC, which is not yet formalized in this repository,
so the twist h(X)(m) = h(X) tensor 1(m) cannot be written on `S.Motive` at all. The
statement specialises to the source's setting as soon as 0FGC is formalized, and h : D → Mot is kept
untwisted on purpose, the Tate objects being supplied separately as T : Z → Mot, exactly as in
the 0FGN statement of ManinIdentityPrinciple whose `hdual` hypothesis this discharges. Three
pieces of data are carried rather than used, each named in the signature: Stacks 0FGI that h(X)
has a left dual (hh), which this repository does prove from DiagonalPairingData and which
rightRigidCategoryOfDiagonalPairingData feeds in; invertibility of the Tate motive, that 1(m) is
a left dual of 1(-m) in the Stacks 0FFP sense (hT); and generation, that every motive is a
retract of a twist h(X)(m) (hgen), taken in the weak Retract sense so the theorem is stronger.
Karoubianness of M_k is the typeclass IsIdempotentComplete. Reused rather than reproved: Stacks
0FFS as Mathlib's hasRightDualTensor and Stacks 0FFU as this library's
nonempty_hasRightDual_of_retract", instance_reducible]
def rightRigidCategoryOfRetractTwist (h : D → Mot) (hh : ∀ X : D, HasRightDual (h X))
    (T : ℤ → Mot) (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m))
    (hgen : ∀ L : Mot, ∃ (X : D) (m : ℤ), Nonempty (Retract L (h X ⊗ T m))) :
    RightRigidCategory Mot where
  rightDual := hasRightDualOfRetractTwist h hh T hT hgen

/-! ### The duality of the motives `h(X)` supplied by Stacks 0FGI -/

section Correspondences

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]

/-- Stacks 0FGJ with the duality of the motives `h(X)` not assumed but taken from this
repository's Stacks 0FGI: for each smooth projective `X`, equidimensional of dimension `e X`,
the datum `P X` of `Stacks.WeilCohomology.DiagonalPairingData` — the source's two composition
formulas for the diagonal class — makes `h(X)(e X)` a left dual of `h(X)` through
`Stacks.WeilCohomology.hasRightDual_motiveOf`.

The ambient category here is the category `S.Obj` of correspondences, whose objects are the
motives with trivial projector; the Tate objects `T` and the generating property `hgen` are
still carried, for the reasons given in the implementation notes. -/
@[instance_reducible]
def rightRigidCategoryOfDiagonalPairingData (S : CorrespondenceStructure.{v, u, w} D)
    [IsIdempotentComplete S.Obj] (L : S.Obj) (e : D → ℕ)
    (P : ∀ X : D, DiagonalPairingData (S.motiveOf X) (S.motiveTwist L X (e X)))
    (T : ℤ → S.Obj) (hT : ∀ m : ℤ, ExactPairing (T (-m)) (T m))
    (hgen : ∀ M : S.Obj, ∃ (X : D) (m : ℤ),
      Nonempty (Retract M (S.motiveOf X ⊗ T m))) :
    RightRigidCategory S.Obj :=
  rightRigidCategoryOfRetractTwist S.motiveOf
    (fun X => hasRightDual_motiveOf S L X (e X) (P X)) T hT hgen

end Correspondences

end Stacks.WeilCohomology

end
