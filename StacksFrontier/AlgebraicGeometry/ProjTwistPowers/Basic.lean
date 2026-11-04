module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.ProjTwistQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor powers of `𝒪(1)` on `Proj 𝒜` are the twisting sheaves

Let `𝒜` be a nonnegatively graded ring generated in degree one over `𝒜 0`, and `X = Proj 𝒜`.
This file proves

`𝒪(1) ^⊗ n ≅ 𝒪(n)` for every `n : ℤ`,

with the powers taken as `Stacks.Ample.tensorPowModule`, the family [Stacks, Tag 01CU] that the
ampleness development of this repository is written over. This is *literally* the hypothesis
`htw` of `Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute`
`.exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists` (`:161`) and
`.exists_epi_coproduct_twistingSheaf_of_isCoherent` (`:199`), and it is the second half of the
absolute residue of Stacks Tag 01VN recorded in
`StacksFrontier/AlgebraicGeometry/ChartBasis/Basic.lean`.

## The route: one base case and an equivalence, not an induction on a product formula

The two ingredients named in the records are
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` — the
multiplication `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` is an isomorphism in all integer degrees under
generation in degree one — and the addition law `Stacks.Ample.tensorPowModuleAddIso`. Composing
them needs no arithmetic of degrees at all, and in particular needs **no separate treatment of
the negative powers**, because of one observation:

> both families are orbits of the **same autoequivalence**, and they meet in degree one.

Write `G` for tensoring on the right by `𝒪(1)`
(`Stacks.SheafOfModules.TensorPower.tensorRightFunctor`), which is an equivalence exactly because
`𝒪(1)` is invertible, which under degree-one generation it is. Then

* `G (𝒪(1) ^⊗ n) ≅ 𝒪(1) ^⊗ (n + 1)` is the addition law at `(n, 1)` (`twistPowSuccIso`), and
* `G (𝒪(n)) ≅ 𝒪(n + 1)` is the multiplication map at `(n, 1)` (`twistMulIso`),

so `nonempty_iso_of_shift` — a statement about an arbitrary fully faithful endofunctor of an
arbitrary category — propagates a single degreewise isomorphism in **both** directions: upwards by
applying `G`, downwards by `CategoryTheory.Functor.preimageIso`, which is where full faithfulness
is used and where the usual "compare the chosen tensor inverses" argument is avoided. The
degreewise isomorphism to start from is degree one, `Stacks.Ample.tensorPowModuleOneIso`, which is
free: `𝒪(1) ^⊗ 1 ≅ 𝒪(1)`.

That the base case is degree **one** rather than degree zero is the point. The records expected the
induction to start at `𝒪(0) ≅ 𝒪_X`, which is not available (`Stacks.AlgebraicGeometry`
`.ProjTwistCompare.twistUnitMap` is a morphism `𝒪_X ⟶ 𝒪(0)` and nothing proves it invertible); here
`𝒪(0) ≅ 𝒪_X` comes out instead as the corollary `unitModuleIsoTwistingSheafZero`, which
[`§8.263`'s residue list] asks for separately.

## Main definitions

All names below live in the namespace `Stacks.AlgebraicGeometry.ProjTwistPowers`.

* `twistRight`: tensoring on the right by `𝒪(1)` on `Proj 𝒜`.
* `twistMulIso`: the multiplication `𝒪(n) ⊗ 𝒪(1) ⟶ 𝒪(n + 1)` as an isomorphism.
* `twistPowSuccIso`: the addition law `𝒪(1) ^⊗ n ⊗ 𝒪(1) ≅ 𝒪(1) ^⊗ (n + 1)`.
* `tensorPowModuleIsoTwistingSheaf`: **`𝒪(1) ^⊗ n ≅ 𝒪(n)`.**
* `unitModuleIsoTwistingSheafZero`: `𝒪_X ≅ 𝒪(0)`.

## Main results

* `nonempty_iso_of_shift`: the abstract shift principle.
* `isEquivalence_twistRight`: tensoring by `𝒪(1)` is an equivalence.
* `nonempty_tensorPowModule_iso_twistingSheaf`: `𝒪(1) ^⊗ n ≅ 𝒪(n)`, as a `Nonempty`; the data
  form `tensorPowModuleIsoTwistingSheaf` is its `Classical.choice`.
* `htw_of_adjoin`: the same, stated in exactly the shape of the `htw` hypothesis of the two
  Tag 0B5Q theorems, so that it can be passed to them directly.
* `exists_epi_coproduct_twistingSheaf_of_isCoherent_of_adjoin`: those theorems with `htw`
  discharged, leaving `hamp` as the only hypothesis beyond degree-one generation.

## Implementation notes

**Three spellings of one tensor product meet here, and all three bridges are definitional.**
`ProjInvertibleLocus.twistMultiplicationMap` has source
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`;
`Stacks.Ample.tensorPowModuleAddIso` is stated over
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`; and
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor` has `.obj A` equal to
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 A L`. All three agree by `rfl` — the
  first two by
`Stacks.TensorSheafDedup.tensorSheaf_eq`, the third by unfolding the functor — so the
isomorphisms below are stated at the functor spelling and no comparison morphism appears. **No
monoidal instance is used anywhere in this file**, deliberately: `Stacks.RelativeVeryAmple`
`.tensorModulesMapIso` supplies the functoriality of the tensor product in both arguments with an
instance-free type, which is all the addition law needs.

**The two invertibility classes both occur.** `Stacks.Ample.tensorPowModule` is keyed on
`Stacks.Ample.IsInvertibleModule`, which is `AlgebraicGeometry.SheafOfModules.IsInvertible`;
`isEquivalence_tensorRightFunctor` is keyed on `Stacks.SheafOfModules.IsInvertible`. The crossing
is `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, done once in
`isEquivalence_twistRight`. Note that
`Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one` states its
generation hypothesis as `Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤`, and
feeding it the `Algebra.adjoin (𝒜 0) ↑(𝒜 1) = ⊤` spelling used here — the spelling of Tag 01VN's
`ProjOneBasisClause` and of `isIso_twistMultiplicationMap_of_adjoin` — is a **deterministic
`isDefEq` timeout at 200000 heartbeats**. The route taken instead goes through
`TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin`, which is already stated at the
coercion spelling, and crosses classes afterwards; no budget is raised.

**`asIso` is applied with its instance argument explicit.** `haveI : IsIso
(twistMultiplicationMap 𝒜 n 1) := …` followed by `asIso (twistMultiplicationMap 𝒜 n 1)` fails to
synthesize the very instance just introduced. `@asIso _ _ _ _ f h` elaborates at once.

**`twistRight_obj` is applied, never unfolded.** `twistRight` is a `def`, so asking the unifier
for `(twistRight 𝒜).obj (𝒪(1) ^⊗ n) =?= tensorModules (Proj 𝒜) (𝒪(1) ^⊗ n) 𝒪(1)` while a term is
being elaborated against it lets `whnf` descend into `Stacks.Ample.tensorPowModule`, that is into
the integer power of the autoequivalence `- ⊗ 𝒪(1)`, which has no normal form worth computing:
471347 heartbeats, against the 200000 budget. The equation holds with the module an
opaque variable for 582, which is what `twistRight_obj` records once; `twistPowSuccIso` therefore
states its term at the `tensorModules` spelling (2070) and crosses to the functor spelling by
`eqToIso (twistRight_obj 𝒜 _)`, a substitution into that lemma rather than a defeq check — 2122
heartbeats for the whole declaration. No budget is raised.

**The result is produced as a `Nonempty` and chosen.** `Int.induction_on` eliminates into a
`Prop`, and an isomorphism is data, so the propagation is carried out for
`Nonempty (A n ≅ B n)` and the data form is `Classical.choice` of it. The axiom list is therefore
`[propext, Classical.choice, Quot.sound]`.

## What is not done

No `stacks` attribute is attached. Tag 01CU's multiplication isomorphisms are asserted here only
in the degrees `(n, 1)`, which is all the identification needs, and nothing is said about the
commutativity and associativity constraints; and the identification is stated under generation of
`𝒜` in degree one, which neither Tag 01CU nor Tag 0B5Q grants. Tag 0B5Q's label
`eventual_higher_cohomology_vanishing` is **not** earned: `hamp` — the two halves of Tag 01Q3
clause (7) for `𝒪(1)` on `Proj 𝒜` — remains a hypothesis, and the statement assumes `𝒜` merely
Noetherian.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v w

namespace Stacks.AlgebraicGeometry.ProjTwistPowers

/-! ### The abstract shift principle -/

/-- **Two `ℤ`-indexed families carried one step by one fully faithful functor, and agreeing in a
single degree, agree in every degree.**

Upwards the functor is applied; downwards `CategoryTheory.Functor.preimageIso` cancels it. Stated
for a bare fully faithful endofunctor because that is all the application needs: no monoidal
structure, no invertible object, and no comparison of chosen tensor inverses. -/
theorem nonempty_iso_of_shift {C : Type u} [Category.{v} C] (G : C ⥤ C) [G.Full] [G.Faithful]
    (A B : ℤ → C) (a : ∀ n : ℤ, G.obj (A n) ≅ A (n + 1))
    (b : ∀ n : ℤ, G.obj (B n) ≅ B (n + 1)) {k : ℤ} (e : A k ≅ B k) :
    ∀ n : ℤ, Nonempty (A n ≅ B n) := by
  have main : ∀ m : ℤ, Nonempty (A (k + m) ≅ B (k + m)) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
        exact ⟨(by rw [add_zero] : A (k + 0) = A k) ▸
          (by rw [add_zero] : B (k + 0) = B k) ▸ e⟩
    | succ i ih =>
        obtain ⟨f⟩ := ih
        have hk : k + ((i : ℤ) + 1) = (k + (i : ℤ)) + 1 := by ring
        exact ⟨hk ▸ ((a (k + (i : ℤ))).symm ≪≫ G.mapIso f ≪≫ b (k + (i : ℤ)))⟩
    | pred i ih =>
        obtain ⟨f⟩ := ih
        have hk : (k + (-(i : ℤ) - 1)) + 1 = k + (-(i : ℤ)) := by ring
        exact ⟨G.preimageIso (a (k + (-(i : ℤ) - 1)) ≪≫ (hk ▸ f) ≪≫
          (b (k + (-(i : ℤ) - 1))).symm)⟩
  intro n
  have := main (n - k)
  rwa [show k + (n - k) = n by ring] at this

/-! ### Tensoring by `𝒪(1)` on an absolute `Proj` -/

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The sheaf condition on the structure presheaf of rings of `Proj 𝒜`, at the spelling
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` takes as a value. -/
abbrev projSheafCond :
    Presheaf.IsSheaf (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜))
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (AlgebraicGeometry.Proj
        𝒜).presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒜)

/-- **Tensoring on the right by the degree-one twist `𝒪(1)` on `Proj 𝒜`.** Its value on an
object is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 A 𝒪(1)`, by `rfl`. -/
@[ega "II 2.5.10" "(2.5.10.2), special case"]
def twistRight : (AlgebraicGeometry.Proj 𝒜).Modules ⥤ (AlgebraicGeometry.Proj 𝒜).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
    ⟨(AlgebraicGeometry.Proj 𝒜).presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ ((AlgebraicGeometry.Proj 𝒜).presheaf)
        (forget₂ CommRingCat RingCat) ((projSheafCond 𝒜))⟩).flip.obj ((twistingSheaf 𝒜 1)))

/-- The value of `twistRight` is the tensor product sheaf, definitionally. -/
theorem twistRight_obj (A : (AlgebraicGeometry.Proj 𝒜).Modules) :
    (twistRight 𝒜).obj A =
      Stacks.RelativeVeryAmple.tensorModules (AlgebraicGeometry.Proj 𝒜) A (twistingSheaf 𝒜 1) :=
  rfl

/-- **Under generation in degree one, tensoring by `𝒪(1)` is an equivalence.**

`𝒪(1)` is invertible by `TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin`, in the
`AlgebraicGeometry.SheafOfModules.IsInvertible` class; the equivalence is keyed on the other
Tag 01CS class, and the crossing is
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
@[ega "II 3.2.5" "special case"]
theorem isEquivalence_twistRight (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) :
    (twistRight 𝒜).IsEquivalence :=
  let : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (projSheafCond 𝒜) (twistingSheaf 𝒜 1) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        (AlgebraicGeometry.Proj 𝒜).presheaf (projSheafCond 𝒜) (twistingSheaf 𝒜 1)).mpr
      (TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin 𝒜 hgen 1)
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- **The multiplication `𝒪(n) ⊗ 𝒪(1) ⟶ 𝒪(n + 1)` as an isomorphism**, in the functor spelling:
this is `ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` at `(n, 1)`, with the
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` source read as `(twistRight 𝒜).obj
  (𝒪(n))`, which it is by `rfl`. -/
@[ega "II 2.5.14" "special case"]
def twistMulIso (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) (n : ℤ) :
    (twistRight 𝒜).obj (twistingSheaf 𝒜 n) ≅ twistingSheaf 𝒜 (n + 1) :=
  @asIso _ _ _ _ (ProjInvertibleLocus.twistMultiplicationMap 𝒜 n 1)
    (ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin 𝒜 hgen n 1)

variable [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)]

/-- **The successor law for the tensor powers of `𝒪(1)`**, in the same functor spelling: the
addition law `Stacks.Ample.tensorPowModuleAddIso` at `(n, 1)`, with the second factor rewritten
from `𝒪(1) ^⊗ 1` to `𝒪(1)` by functoriality of the tensor product.

The value of `twistRight` is reached through `twistRight_obj` rather than by definitional
unfolding; see the implementation note on that below. -/
def twistPowSuccIso (n : ℤ) :
    (twistRight 𝒜).obj
        (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n) ≅
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) (n + 1) :=
  eqToIso (twistRight_obj 𝒜
      (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n)) ≪≫
    (Stacks.RelativeVeryAmple.tensorModulesMapIso (AlgebraicGeometry.Proj 𝒜) (Iso.refl _)
        (Stacks.Ample.tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 1)).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n 1)

/-! ### The identification -/

/-- **`𝒪(1) ^⊗ n ≅ 𝒪(n)` on the `Proj` of a graded ring generated in degree one**, for every
integer `n`. The two families are orbits of the one equivalence `twistRight 𝒜` and agree in
degree one, so `nonempty_iso_of_shift` identifies them in every degree, positive and negative
alike. -/
@[ega "II 2.5.14" "(2.5.14.2)"]
theorem nonempty_tensorPowModule_iso_twistingSheaf
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) (n : ℤ) :
    Nonempty (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
      twistingSheaf 𝒜 n) :=
  let := isEquivalence_twistRight 𝒜 hgen
  nonempty_iso_of_shift (twistRight 𝒜)
    (fun m => Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) m)
    (fun m => twistingSheaf 𝒜 m) (fun m => twistPowSuccIso 𝒜 m) (fun m => twistMulIso 𝒜 hgen m)
    (k := 1)
    (Stacks.Ample.tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)) n

/-- `𝒪(1) ^⊗ n ≅ 𝒪(n)` as data. -/
def tensorPowModuleIsoTwistingSheaf (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) (n : ℤ) :
    Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
      twistingSheaf 𝒜 n :=
  (nonempty_tensorPowModule_iso_twistingSheaf 𝒜 hgen n).some

/-- **The `htw` hypothesis of the two Tag 0B5Q theorems, discharged.** Written in exactly the
shape those theorems bind it, so that it can be passed to them without any transport. -/
def htw_of_adjoin (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) :
    ∀ n : ℤ,
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
        twistingSheaf 𝒜 n :=
  tensorPowModuleIsoTwistingSheaf 𝒜 hgen

/-- **`𝒪_X ≅ 𝒪(0)`**, the degree-zero case: `𝒪(1) ^⊗ 0` is the structure sheaf on the one side
and `𝒪(0)` on the other. Nothing in either tree proved this before — the morphism
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap` existed and was not known to be
invertible — and it is an input the records asked for on its own. -/
def unitModuleIsoTwistingSheafZero (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) :
    Stacks.Ample.unitModule (AlgebraicGeometry.Proj 𝒜) ≅ twistingSheaf 𝒜 0 :=
  (Stacks.Ample.tensorPowModuleZeroIso (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)).symm ≪≫
    tensorPowModuleIsoTwistingSheaf 𝒜 hgen 0

/-! ### Tag 0B5Q assertion (1) with `htw` removed -/

/-- **Tag 0B5Q assertion (1)'s conclusion for a quasi-coherent module of finite type**, with the
`htw` hypothesis of `Tag0B5QAmpleRoute`
`.exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists` discharged. `hamp` is the
only hypothesis left beyond generation in degree one. -/
theorem exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists_of_adjoin
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤)
    (hamp : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hqc : F.IsQuasicoherent) (hft : SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (r : ℕ) (d : Fin r → ℤ),
      ∃ φ : (∐ fun j : Fin r => twistingSheaf 𝒜 (d j)) ⟶ F, Epi φ :=
  Tag0B5QAmpleRoute.exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists 𝒜
    (htw_of_adjoin 𝒜 hgen) hamp F hqc hft

/-- **The same under the hypothesis of the tagged statement**, a coherent module. -/
theorem exists_epi_coproduct_twistingSheaf_of_isCoherent_of_adjoin
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤)
    (hamp : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ (r : ℕ) (d : Fin r → ℤ),
      ∃ φ : (∐ fun j : Fin r => twistingSheaf 𝒜 (d j)) ⟶ F, Epi φ :=
  Tag0B5QAmpleRoute.exists_epi_coproduct_twistingSheaf_of_isCoherent 𝒜
    (htw_of_adjoin 𝒜 hgen) hamp F hF

end Stacks.AlgebraicGeometry.ProjTwistPowers

end
