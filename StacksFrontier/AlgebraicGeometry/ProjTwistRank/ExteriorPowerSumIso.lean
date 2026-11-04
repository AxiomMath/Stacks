module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum

/-!
# The exterior powers of the middle term of the Euler sequence

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = ℙⁿ_R` for
`Proj` of that grading. The middle term of the Euler sequence of `X` is the direct sum
`E = 𝒪_X(-1)^{⊕ (n+1)}` of `n + 1` copies of the Serre twist `𝒪_X(-1)`, and this file computes all
of its exterior powers:

`⋀^p E ≅ 𝒪_X(-p)^{⊕ binom(n+1, p)}`.

The computation is an induction on the number of summands. The Künneth decomposition of an
exterior power of a direct sum collapses, for a direct sum of line bundles, to the two-term
*Pascal recursion*

`⋀^{q+1}(L ⊕ M) ≅ ⋀^{q+1} M ⊕ (L ⊗ ⋀^q M)`,

proved as `Stacks.AlgebraicGeometry.ProjTwistRank.exteriorPowerSplitIso`; peeling one copy of
`𝒪_X(-1)` off `𝒪_X(-1)^{⊕ (N+2)}` and feeding the recursion the two values
`⋀^{q+1}(𝒪_X(-1)^{⊕ (N+1)})` and `⋀^q(𝒪_X(-1)^{⊕ (N+1)})` of the inductive hypothesis gives

`𝒪_X(-(q+1))^{⊕ binom(N+1, q+1)} ⊕ (𝒪_X(-1) ⊗ 𝒪_X(-q)^{⊕ binom(N+1, q)})`,

and the two collapsing facts about Serre twists — that tensoring distributes over a finite direct
sum, and that `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a+b)` — turn the second block into `binom(N+1, q)` further copies
of `𝒪_X(-(q+1))`. Pascal's rule `binom(N+1, q+1) + binom(N+1, q) = binom(N+2, q+1)` closes the
step.

The induction starts at *one* summand, not none: the base case is the single line bundle
`𝒪_X(-1)`, whose exterior powers are `𝒪_X(0)` in degree zero, `𝒪_X(-1)` in degree one, and zero
above — matching `binom(1, 0) = binom(1, 1) = 1` and `binom(1, q) = 0` for `q ≥ 2`. Degree zero is
the only degree the recursion does not reach, and there `⋀⁰ F ≅ 𝒪(0)` holds for every sheaf of
modules `F`, independently of the number of summands.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistRank.twistSum`: the direct sum `𝒪_X(d)^{⊕k}` of `k` copies of
  a Serre twist, and `twistObj`, `twistFamily`, `tensorObj`, `wedge` the remaining abbreviations
  that pin the spelling of the ambient category.
* `Stacks.AlgebraicGeometry.ProjTwistRank.biprodFinCongr`: reindexing a direct sum of copies of a
  fixed object along an equality of the number of copies.
* `Stacks.AlgebraicGeometry.ProjTwistRank.wedgeMapIso`: the exterior power of an isomorphism, and
  `tensorObjMapIso`: an isomorphism tensored with a fixed left factor.
* `Stacks.AlgebraicGeometry.ProjTwistRank.wedgeZeroIso`: `⋀⁰ F ≅ 𝒪_X(0)^{⊕1}`.
* `Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistSumIso`:
  `𝒪_X(d) ⊗ 𝒪_X(e)^{⊕k} ≅ 𝒪_X(d+e)^{⊕k}`, and
  `Stacks.AlgebraicGeometry.ProjTwistRank.twistSumAddIso`:
  `𝒪_X(d)^{⊕a} ⊕ 𝒪_X(d)^{⊕b} ≅ 𝒪_X(d)^{⊕(a+b)}`.
* `Stacks.AlgebraicGeometry.ProjTwistRank.wedgeTwistSumSuccIso`: **the inductive step**, the
  Pascal recursion with both of its inputs already computed.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistRank.choose_succ_add_choose`: Pascal's rule, in the form the
  induction consumes.
* `Stacks.AlgebraicGeometry.ProjTwistRank.isZero_biproductFin`: a direct sum of no copies of an
  object is a zero object.
* `Stacks.AlgebraicGeometry.ProjTwistRank.nonempty_wedgeTwistSingletonIso`: the exterior powers of
  a single copy of `𝒪_X(-1)`, the base case.
* `Stacks.AlgebraicGeometry.ProjTwistRank.nonempty_wedgeTwistSumIso`:
  **`⋀^q(𝒪_X(-1)^{⊕(N+1)}) ≅ 𝒪_X(-q)^{⊕ binom(N+1, q)}`** for all `N` and `q`.
* `Stacks.AlgebraicGeometry.ProjTwistRank.nonempty_exteriorPower_twistMinusOneSumIso` and
  `nonempty_exteriorPower_twistMinusOneSum_isoZeroTwistSum`: the same statement for the middle
  term `Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum` of the Euler sequence, with
  the degree of the twist written `-p` and `0 - p` respectively.

## Implementation notes

**Everything is written at one spelling of the sheaf of rings.** The structure sheaf of `ℙⁿ_R`
has three definitionally equal descriptions — `CategoryTheory.Sheaf.toRingCat` of the `Proj`
structure sheaf, the `CategoryTheory.sheafCompose` of it that the twisting sheaves are indexed by,
and `AlgebraicGeometry.Scheme.ringCatSheaf` through which `AlgebraicGeometry.Scheme.Modules`
unfolds — and instance search matches the head syntactically, so a direct sum formed at one of
them is not recognized at another. The abbreviations `twistObj`, `twistFamily`, `twistSum`,
`tensorObj` and `wedge` below therefore *ascribe* the `toRingCat` spelling, which is the one
`StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum` is stated at; every direct sum in
the file is formed from a named family with that ascribed codomain, as
`Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.eulerWedgeFamily` does for the
`AlgebraicGeometry.Scheme.Modules` spelling. Mixing is what has to be avoided and not merely
inelegant: in a goal whose category argument comes from one spelling while its
`CategoryTheory.Limits.HasZeroMorphisms` argument comes from another, no instance of
`CategoryTheory.Limits.HasBiproduct` applies, even though both descriptions of the goal are
individually solvable.

**The biproduct instance is named rather than searched for.** The finite-biproduct statement
`hasFiniteBiproducts_toRingCat` below is declared a local instance, and the biproducts indexed by
`Fin k` and the binary biproducts the file forms are read off it; the library's universally
quantified forms are stated for `SheafOfModules.{max u v}` and `max ?u ?v =?= u` is not a
constraint the universe unifier solves, so instance search never applies them in a single
universe. It is named at the `toRingCat` spelling, while the tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor` is indexed by the plain
definition `Stacks.SheafOfModules.Tensor.ringSheaf`; that name is therefore declared
`implicit_reducible` for this file, and the one biproduct whose category is already pinned to it
— the reindexing of `tensorTwistSumIso` — takes `ProjModules` explicitly instead.

**The exterior power of an isomorphism is taken at the site level.**
`AlgebraicGeometry.Scheme.Modules.exteriorPowerMap` is stated for sheaves of modules on a scheme,
hence at the `Scheme.Modules` spelling; `wedgeMapIso` uses
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap` instead, which is stated at the
`toRingCat` spelling and so needs no transport.

**No `@[stacks]` attribute.** The closed form proved here is not an assertion of a Stacks tag:
Tag 01CB is the Künneth decomposition of an exterior power of a direct sum and Tag 01MT is the
invertibility of the Serre twists, of which this is a consequence rather than a formalization.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.AlgebraicGeometry.ProjTwistRank

open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### The spelling of the ambient category -/

/-- Finite biproducts in the category of sheaves of modules on a scheme, at the
`CategoryTheory.Sheaf.toRingCat` spelling of its structure sheaf. This is the form
`Stacks.AlgebraicGeometry.ProjTwistRank.biprodFinIso` consumes. -/
theorem hasFiniteBiproducts_toRingCat (Y : Scheme.{u}) :
    HasFiniteBiproducts (SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥Y) Y.sheaf)) :=
  inferInstanceAs (HasFiniteBiproducts Y.Modules)

attribute [local instance] hasFiniteBiproducts_toRingCat

/-! ### Direct sums of copies of one object -/

section ConstantFamilies

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- **A direct sum of no copies of an object is a zero object**: a morphism out of it is
determined by its composites with the inclusions of the summands, of which there are none, so its
identity agrees with its zero morphism. -/
theorem isZero_biproductFin (L : C) {k : ℕ} (hk : k = 0)
    [HasBiproduct fun _ : Fin k => L] : IsZero (⨁ fun _ : Fin k => L) := by
  subst hk
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i => i.elim0)

/-- **Reindexing a direct sum of copies of a fixed object along an equality of the number of
copies.** The two objects are equal, the number of copies occurring in the index type alone. -/
def biprodFinCongr (L : C) {a b : ℕ} (h : a = b)
    [HasBiproduct fun _ : Fin a => L] [HasBiproduct fun _ : Fin b => L] :
    (⨁ fun _ : Fin a => L) ≅ ⨁ fun _ : Fin b => L :=
  eqToIso (by subst h; rfl)

end ConstantFamilies

/-- **Pascal's rule**, in the form the induction below consumes: the number of `q+1`-element
subsets of an `N+2`-element set is the number of those avoiding a fixed element plus the number of
those containing it. -/
theorem choose_succ_add_choose (N q : ℕ) :
    (N + 1).choose (q + 1) + (N + 1).choose q = (N + 2).choose (q + 1) :=
  (Nat.add_comm _ _).trans (Nat.choose_succ_succ' (N + 1) q).symm

/-! ### The twists of projective space and their direct sums -/

section Twists

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The category of sheaves of modules on `ℙⁿ_R`, at the `CategoryTheory.Sheaf.toRingCat`
spelling of its structure sheaf. -/
abbrev ProjModules :=
  SheafOfModules.{u} (Sheaf.toRingCat
    (Opens.grothendieckTopology ↥(_root_.AlgebraicGeometry.Proj (polyGrading R n)))
    (_root_.AlgebraicGeometry.Proj (polyGrading R n)).sheaf)

/-- The Serre twist `𝒪(d)` on `ℙⁿ_R`, read in `ProjModules`. -/
abbrev twistObj (d : ℤ) : ProjModules R n := twistingSheaf (polyGrading R n) d

/-- The constant family of `k` copies of the Serre twist `𝒪(d)` on `ℙⁿ_R`. -/
abbrev twistFamily (d : ℤ) (k : ℕ) : Fin k → ProjModules R n := fun _ => twistObj R n d

/-- The direct sum `𝒪(d)^{⊕k}` of `k` copies of the Serre twist `𝒪(d)` on `ℙⁿ_R`. -/
abbrev twistSum (d : ℤ) (k : ℕ) : ProjModules R n := ⨁ twistFamily R n d k

/-- The tensor product of two sheaves of modules on `ℙⁿ_R`, at the spelling the Künneth summands
of `StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum` are written with. -/
abbrev tensorObj (A B : ProjModules R n) : ProjModules R n :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ((_root_.AlgebraicGeometry.Proj (polyGrading R
    n)).sheaf)).obj A).obj B

/-- The degree-`q` exterior power `⋀^q F` of a sheaf of modules on `ℙⁿ_R`, taken in the chosen
exterior algebra of `F`. -/
abbrev wedge (F : ProjModules R n) (q : ℕ) : ProjModules R n :=
  (_root_.SheafOfModules.algebras _ F).exteriorPower q

/-- **The exterior power of an isomorphism is an isomorphism.** The induced map on exterior
powers is produced by the universal property of the exterior algebra, and the map induced by an
isomorphism is invertible in every degree. -/
def wedgeMapIso {F G : ProjModules R n} (e : F ≅ G) (q : ℕ) : wedge R n F q ≅ wedge R n G q :=
  @asIso _ _ _ _
    ((_root_.SheafOfModules.algebras _ F).exteriorPowerMap
      (_root_.SheafOfModules.algebras _ G) e.hom (q : ℤ))
    ((_root_.SheafOfModules.algebras _ F).exterior_isExteriorAlgebra.isIso_pieceMap
      (_root_.SheafOfModules.algebras _ G).exterior_isExteriorAlgebra e.hom
      e.isIso_hom (q : ℤ))

/-- Tensoring with a fixed left factor on `ℙⁿ_R` carries an isomorphism to an isomorphism. -/
def tensorObjMapIso (A : ProjModules R n) {B B' : ProjModules R n} (e : B ≅ B') :
    tensorObj R n A B ≅ tensorObj R n A B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((_root_.AlgebraicGeometry.Proj (polyGrading R n))).presheaf, ((_root_.AlgebraicGeometry.Proj (polyGrading R n))).IsSheaf⟩).obj A).mapIso e

/-- **`𝒪(d) ⊗ 𝒪(e)^{⊕k} ≅ 𝒪(d+e)^{⊕k}` on `ℙⁿ_R`**: tensoring with a fixed sheaf distributes
over a finite direct sum, and the product of two Serre twists is the twist by the sum of their
degrees. -/
def tensorTwistSumIso (d e : ℤ) (k : ℕ) :
    tensorObj R n (twistObj R n d) (twistSum R n e k) ≅ twistSum R n (d + e) k :=
  tensorBiproductIso (Y := _root_.AlgebraicGeometry.Proj (polyGrading R n)) (twistObj R n d)
      (twistFamily R n e k) ≪≫
    biproduct.mapIso (C := ProjModules R n) fun _ => tensorTwistingSheafIso R n d e

/-- **`a` copies of `𝒪(d)` together with `b` copies make `a + b` copies** on `ℙⁿ_R`. -/
def twistSumAddIso (d : ℤ) (a b : ℕ) :
    (twistSum R n d a ⊞ twistSum R n d b) ≅ twistSum R n d (a + b) :=
  biprodFinIso (twistObj R n d) a b

/-! ### The exterior powers in degree zero and of a single twist -/

/-- **`⋀⁰ F ≅ 𝒪(0)^{⊕1}` for every sheaf of modules on `ℙⁿ_R`**: the zeroth homogeneous piece of
an exterior algebra is the structure sheaf, the structure sheaf is the zeroth Serre twist, and a
direct sum of one copy of an object is that object. This is the one degree the Pascal recursion
does not reach, and it is independent of `F`. -/
def wedgeZeroIso (F : ProjModules R n) :
    wedge R n F 0 ≅ twistSum R n (-((0 : ℕ) : ℤ)) 1 :=
  (_root_.SheafOfModules.algebras _ F).exteriorPieceZeroIsoUnit ≪≫
    (twistingSheafZeroIsoUnit (polyGrading R n)).symm ≪≫
    eqToIso (congrArg (twistObj R n) (by norm_num : (0 : ℤ) = -((0 : ℕ) : ℤ))) ≪≫
    (biproductUniqueIso (twistFamily R n (-((0 : ℕ) : ℤ)) 1)).symm

/-- **`⋀¹(𝒪(-1)^{⊕1}) ≅ 𝒪(-1)^{⊕1}`**: nothing is divided out of an exterior algebra in degree
one, so the first exterior power of a sheaf of modules is that sheaf. -/
def wedgeOneSingletonIso :
    wedge R n (twistSum R n (-1) 1) 1 ≅ twistSum R n (-((1 : ℕ) : ℤ)) 1 :=
  (_root_.SheafOfModules.algebras _ (twistSum R n (-1) 1)).exteriorPowerOneIso ≪≫
    eqToIso (congrArg (fun c : ℤ => twistSum R n c 1)
      (by norm_num : (-1 : ℤ) = -((1 : ℕ) : ℤ)))

/-- **`⋀^{q+2}(𝒪(-1)^{⊕1}) ≅ 𝒪(-(q+2))^{⊕ binom(1, q+2)}`**: both sides are zero objects. A
single copy of `𝒪(-1)` is `𝒪(-1)`, whose exterior powers above degree one vanish because it has
rank one, and `binom(1, q+2) = 0`. -/
def wedgeHighSingletonIso (q : ℕ) :
    wedge R n (twistSum R n (-1) 1) (q + 2) ≅
      twistSum R n (-((q + 2 : ℕ) : ℤ)) (Nat.choose 1 (q + 2)) :=
  IsZero.iso
    ((isZero_exteriorPower_twistingSheaf R n (-1) (by omega : 1 < q + 2)).of_iso
      (wedgeMapIso R n (F := twistSum R n (-1) 1) (G := twistObj R n (-1))
        (biproductUniqueIso _) (q + 2)))
    (isZero_biproductFin (twistObj R n (-((q + 2 : ℕ) : ℤ)))
      (Nat.choose_eq_zero_of_lt (by omega)))

/-- **The exterior powers of a single copy of `𝒪(-1)` on `ℙⁿ_R`**, the base case of the induction:
`𝒪(0)` in degree zero, `𝒪(-1)` in degree one, and zero in every higher degree, matching
`binom(1, 0) = binom(1, 1) = 1` and `binom(1, q) = 0` for `q ≥ 2`. -/
theorem nonempty_wedgeTwistSingletonIso : ∀ q : ℕ,
    Nonempty (wedge R n (twistSum R n (-1) 1) q ≅
      twistSum R n (-((q : ℕ) : ℤ)) (Nat.choose 1 q)) := by
  intro q
  rcases q with _ | q
  · exact ⟨wedgeZeroIso R n _⟩
  rcases q with _ | q
  · exact ⟨wedgeOneSingletonIso R n⟩
  · exact ⟨wedgeHighSingletonIso R n q⟩

/-! ### The induction on the number of summands -/

/-- **The inductive step: the Pascal recursion with both of its inputs already computed.** Peeling
one copy of `𝒪(-1)` off `𝒪(-1)^{⊕(N+2)}` and collapsing the two surviving Künneth summands gives

`⋀^{q+1}(𝒪(-1)^{⊕(N+2)}) ≅ 𝒪(-(q+1))^{⊕ binom(N+1,q+1)} ⊕ (𝒪(-1) ⊗ 𝒪(-q)^{⊕ binom(N+1,q)})`,

and `𝒪(-1) ⊗ 𝒪(-q) ≅ 𝒪(-(q+1))`, so the right-hand side is `binom(N+1,q+1) + binom(N+1,q)`
copies of `𝒪(-(q+1))`, which is `binom(N+2,q+1)` copies by Pascal's rule. -/
def wedgeTwistSumSuccIso (N q : ℕ)
    (e1 : wedge R n (twistSum R n (-1) (N + 1)) (q + 1) ≅
      twistSum R n (-((q + 1 : ℕ) : ℤ)) ((N + 1).choose (q + 1)))
    (e0 : wedge R n (twistSum R n (-1) (N + 1)) q ≅
      twistSum R n (-((q : ℕ) : ℤ)) ((N + 1).choose q)) :
    wedge R n (twistSum R n (-1) (N + 2)) (q + 1) ≅
      twistSum R n (-((q + 1 : ℕ) : ℤ)) ((N + 2).choose (q + 1)) :=
  (exteriorPowerSplitIso (Y := _root_.AlgebraicGeometry.Proj (polyGrading R n))
        (twistFamily R n (-1) (N + 2))
        (fun _ hk => isZero_exteriorPower_twistingSheaf R n (-1) hk) q).symm ≪≫
    biprod.mapIso e1
      (tensorObjMapIso R n (twistObj R n (-1)) e0 ≪≫
        tensorTwistSumIso R n (-1) (-((q : ℕ) : ℤ)) ((N + 1).choose q) ≪≫
        eqToIso (congrArg (fun c : ℤ => twistSum R n c ((N + 1).choose q))
          (by push_cast; ring : (-1 : ℤ) + -((q : ℕ) : ℤ) = -((q + 1 : ℕ) : ℤ)))) ≪≫
    twistSumAddIso R n (-((q + 1 : ℕ) : ℤ)) ((N + 1).choose (q + 1)) ((N + 1).choose q) ≪≫
    biprodFinCongr (twistObj R n (-((q + 1 : ℕ) : ℤ))) (choose_succ_add_choose N q)

/-- **The exterior powers of a finite direct sum of copies of `𝒪(-1)` on `ℙⁿ_R`**:

`⋀^q(𝒪(-1)^{⊕(N+1)}) ≅ 𝒪(-q)^{⊕ binom(N+1, q)}`

for every `N` and every `q`. The induction is on `N`, with base case a single copy; degree zero is
`wedgeZeroIso` and every positive degree is the Pascal recursion `wedgeTwistSumSuccIso` fed the
inductive hypothesis in the two degrees `q+1` and `q`. -/
theorem nonempty_wedgeTwistSumIso (N : ℕ) : ∀ q : ℕ,
    Nonempty (wedge R n (twistSum R n (-1) (N + 1)) q ≅
      twistSum R n (-((q : ℕ) : ℤ)) ((N + 1).choose q)) := by
  induction N with
  | zero => exact nonempty_wedgeTwistSingletonIso R n
  | succ N ih =>
    intro q
    rcases q with _ | q
    · exact ⟨wedgeZeroIso R n _⟩
    · exact ⟨wedgeTwistSumSuccIso R n N q (ih (q + 1)).some (ih q).some⟩

/-! ### The middle term of the Euler sequence -/

/-- **`⋀^p(𝒪(-1)^{⊕(n+1)}) ≅ 𝒪(-p)^{⊕ binom(n+1, p)}` on `ℙⁿ_R`**, for the middle term
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum` of the Euler sequence and the
exterior power `AlgebraicGeometry.Scheme.Modules.exteriorPower` of a sheaf of modules on a
scheme. -/
theorem nonempty_exteriorPower_twistMinusOneSumIso (p : ℕ) :
    Nonempty (Scheme.Modules.exteriorPower
        (X := _root_.AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n)
        ((p : ℕ) : ℤ) ≅ twistSum R n (-((p : ℕ) : ℤ)) ((n + 1).choose p)) :=
  nonempty_wedgeTwistSumIso R n n p

/-- The same identification with the degree of the twist written `0 - p`, which is the form the
`k = 0` specialization of a twisted direct sum of `binom(n+1, p)` copies of `𝒪(k - p)` takes. -/
theorem nonempty_exteriorPower_twistMinusOneSum_isoZeroTwistSum (p : ℕ) :
    Nonempty (Scheme.Modules.exteriorPower
        (X := _root_.AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n)
        ((p : ℕ) : ℤ) ≅ twistSum R n (0 - ((p : ℕ) : ℤ)) ((n + 1).choose p)) :=
  ⟨(nonempty_wedgeTwistSumIso R n n p).some ≪≫
    eqToIso (congrArg (fun c : ℤ => twistSum R n c ((n + 1).choose p))
      (zero_sub ((p : ℕ) : ℤ)).symm)⟩

end Twists

end Stacks.AlgebraicGeometry.ProjTwistRank

end
