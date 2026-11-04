module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness and tensor powers: the isomorphism invariance, and half of Stacks Tag 01PT

Three facts about `Stacks.Ample.IsAmple` that the ampleness theory in this repository records as
missing, and that the relative-ampleness/relative-very-ampleness comparison of Stacks Tags 01VN
and 01VU consumes.

* **Ampleness depends only on the isomorphism class of the module.**
  `StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean` states in its module documentation
  that "ampleness is not known in the repository to depend only on the isomorphism class of the
  module", and works around that for a unit-isomorphic module by transporting a global basis
  degreewise. The general statement is `Stacks.RelativeVeryAmple.isAmple_congr` below, and the
  relative one is `Stacks.RelativeVeryAmple.isRelativelyAmple_congr`.
* **Half of Stacks Tag 01PT**: if `L ^⊗ d` is ample for some `d ≥ 1` then `L` is ample, absolutely
  (`Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule`) and relative to a morphism
  (`Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`). Tag 01PT is
  listed under "What is not done" in `StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean`. The
  relative form is the implication (2) ⟹ (1) of Stacks Tag 01VU once Tag 01VN is available; see
  the sibling file `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean`.
* **Pullback commutes with the tensor powers of an invertible module**,
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. This is Stacks Tag 01CD iterated.
  `StacksFrontier/AlgebraicGeometry/AmpleLocallyClosed/Basic.lean` names
  `(i^* L) ^⊗ n ≅ i^* (L ^⊗ n)` as one of the reasons its Tag 0H78 input has to be taken as a
  hypothesis; that isomorphism is proved here.

## Main definitions

* `Stacks.RelativeVeryAmple.tensorModules`: the tensor product of two `𝒪_X`-modules, at the
  spelling `Stacks.Ample.tensorPowModuleAddIso` is stated in. An `abbrev`, so that it unifies with
  both that spelling and `Stacks.RingedSpace.tensorSheaf`.
* `Stacks.RelativeVeryAmple.tensorModulesMapIso`: functoriality of the tensor product in both
  arguments.
* `Stacks.RelativeVeryAmple.pullbackTensorModulesIso`: **Stacks Tag 01CD** on a morphism of
  schemes.
* `Stacks.RelativeVeryAmple.tensorPowModuleCongr`: reindexing of the tensor powers along an
  equality of exponents.
* `Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`: isomorphic invertible modules have
  isomorphic tensor powers, in every nonnegative degree.
* `Stacks.RelativeVeryAmple.tensorPowModulePowIso`: `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d * n)`.
* `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`: `f^* (L ^⊗ n) ≅ (f^* L) ^⊗ n`.
* `Stacks.RelativeVeryAmple.cardTensorPowerIso`: **the comparison of the repository's two
  constructions of the integer tensor powers**, in every nonnegative degree —
  `Stacks.SheafOfModules.TensorPower.tensorPower`, which carries the Tag 01CU attribute, and
  `Stacks.Ample.tensorPowModule`, which the ampleness theory is written over. No comparison
  existed; `StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean` records its
  absence as the reason Tag 01VS has to be stated once for each family.

## Main results

* `Stacks.RelativeVeryAmple.isAmpleForPowers_congr_nat`: the ampleness predicate only looks at the
  nonnegative degrees of its family, so a degreewise isomorphism in nonnegative degrees already
  transfers it. This is what makes the three results above reachable with no statement about the
  negative powers.
* `Stacks.RelativeVeryAmple.isAmple_congr`, `isRelativelyAmple_congr`: ampleness and relative
  ampleness are invariants of the isomorphism class.
* `Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule`: Stacks Tag 01QE for a
  module merely isomorphic to `𝒪_X`, now a two-line corollary of the isomorphism invariance.
* `Stacks.RelativeVeryAmple.stacksIsInvertible`,
  `isEquivalence_tensorRightFunctor_of_isInvertibleModule`: the two hypotheses Tag 01CU's own
  tensor powers are stated with, supplied from the ampleness theory's invertibility class.
* `Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule`,
  `isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`: half of Stacks Tag 01PT.
* `Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_isRelativelyAmple_tensorPowModule`: the
  same in the existential shape condition (2) of Stacks Tag 01VU is written in.

## Implementation notes

**Only the nonnegative powers are ever compared.** `Stacks.Ample.IsAmpleForPowers` quantifies over
`n : ℕ` and uses its family at `(n : ℤ)`, so `Stacks.Ample.isAmpleForPowers_congr`, which asks for
an isomorphism in every *integer* degree, is stronger than anything the predicate can consume.
`Stacks.RelativeVeryAmple.isAmpleForPowers_congr_nat` asks only for the nonnegative degrees. That
matters: `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)` and `f^* (L ^⊗ n) ≅ (f^* L) ^⊗ n` are proved by induction on
`n`, so they reach exactly the nonnegative degrees; in a negative degree both would need a
comparison of the chosen tensor inverses, which is a different argument and is not needed here.

**No monoidal instance is used anywhere, and that is deliberate.** `Stacks.SheafInternalHom`'s
`monoidalCategory` and `braidedCategory` are `def`s, and bringing them in as local
instances does *not* make `A ⊗ B` elaborate for `A B : X.Modules`: they are stated for
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)`, `Scheme.Modules`
  is a `def` that instance search
does not unfold, and the search fails with `MonoidalCategoryStruct X.Modules`. So every step below
is taken in the `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling instead, through
`Stacks.RelativeVeryAmple.tensorModules`. Two consequences, both good: the inductive steps are
`Stacks.Ample.tensorPowModuleAddIso` at `(n, 1)` rather than
`AlgebraicGeometry.SheafOfModules.tensorPowSuccIso`, which is monoidal-spelled; and every
declaration in this file has an instance-free type, so no consumer needs a local instance either.

**Functoriality comes from the bifunctor, and the bifunctor is used curried.**
`Stacks.SheafOfModules.Tensor.sheafTensor` is a curried bifunctor, and
`Stacks.RelativeVeryAmple.tensorModulesMapIso` is the composite of its two legs: `Functor.mapIso`
in the left variable, read at `B` by `CategoryTheory.Iso.app`, followed by `Functor.mapIso` of
`(sheafTensor _).obj A'` in the right variable. That composite's `hom` is the morphism the
uncurried bifunctor would produce from a `CategoryTheory.Iso.prod` — `Functor.uncurry`'s `map` on
a pair is `(F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2`, which is these two legs in this order — so
nothing is lost by not uncurrying.

Uncurrying is in fact not usable here: `Functor.mapIso` of
`Functor.uncurry.obj (sheafTensor _)` at an `Iso.prod` has to unify the product category over
`SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, _⟩)` with
`X.Modules × X.Modules`, and `Tensor.ringSheaf` is a plain `def` — unlike
`Stacks.RingedSpace.structureSheafRing`, which carries `@[instance_reducible]` — so the two
category instances have no reducible path between them and the comparison exhausts the heartbeat
budget in `whnf`. Pinning the universes and spelling the sheaf argument exactly as
`tensorModules` spells it does not help; only dropping the product category does. Each leg on its
own merely applies a functor to an object, which is the one unification `tensorModules` already
pays. This is also why `Stacks.RelativeVeryAmple.tensorModules` is an `abbrev`: the two spellings
have to unify when the isomorphisms are composed.

**Reindexing is `eqToIso`, and is only ever composed.** The exponent bookkeeping
`↑(n + 1) = ↑n + 1` and `d * ↑n + d = d * ↑(n + 1)` is carried by
`Stacks.RelativeVeryAmple.tensorPowModuleCongr`, an `eqToIso`; as in
`StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean` it is composed in `Iso` and
never asked to convert, so no transport of `tensorPowModule` is forced open. Each equation is given
by an explicit `show`: left to be solved from the surrounding composition the exponent is a
metavariable and `push_cast` reports being stuck on it.

**Stacks Tag 01CD is used at the scheme-level spelling directly.**
`Stacks.PullbackTensorIso.pullbackTensorIso` is stated for a morphism of ringed spaces and
`Stacks.RingedSpace.tensorSheaf`; for a scheme those are the same objects as
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` and
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf _`, which was checked by
  elaborating the identity, so no bridge
is needed.

## What is not done

The converse half of Stacks Tag 01PT — that `L` ample implies `L ^⊗ d` ample — is not proved. It
needs a global section of `L ^⊗ (d n)` with the same nonvanishing locus as a given global section
of `L ^⊗ n`, that is the `d`-th power of a section, and the product formula
`Stacks.SectionProduct.nonvanishingLocus_mul` is stated for the elements of the graded ring of
sections (`Stacks.GradedSections.powSections`) rather than for arbitrary global sections, so a
surjection of `Stacks.GradedSections.powSections L n` onto `Γ(L ^⊗ n, ⊤)` would be needed first.
Only the direction Stacks Tag 01VU uses is proved.

## References

* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeVeryAmple

/-! ### The tensor product of `𝒪_X`-modules, with no monoidal instance -/

/-- The tensor product of two `𝒪_X`-modules, at the spelling
`Stacks.Ample.tensorPowModuleAddIso` is stated in. Deliberately an `abbrev`: it has to unify both
with that spelling and with `(Stacks.RingedSpace.tensorSheaf X.toRingedSpace).obj (A, B)`, which is
where its functoriality comes from. -/
abbrev tensorModules (X : Scheme.{u}) (A B : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj (A)).obj (B))

/-- **The tensor product of `𝒪_X`-modules is functorial in both arguments**, read off the two
legs of the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
def tensorModulesMapIso (X : Scheme.{u}) {A A' B B' : X.Modules} (e : A ≅ A') (g : B ≅ B') :
    tensorModules X A B ≅ tensorModules X A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).mapIso e).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj A').mapIso g

/-- **Stacks Tag 01CD for a morphism of schemes**, `f^* (A ⊗ B) ≅ f^* A ⊗ f^* B`. This is
`Stacks.PullbackTensorIso.pullbackTensorIso` at the pair `(A, B)`; the ringed-space spelling it is
stated in and the scheme spelling used here are the same objects. -/
def pullbackTensorModulesIso {X S : Scheme.{u}} (f : X ⟶ S) (A B : S.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj (tensorModules S A B) ≅
      tensorModules X ((modulePullback f.toLRSHom.toShHom).obj A)
        ((modulePullback f.toLRSHom.toShHom).obj B) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (A, B)

/-! ### Reindexing, and the degrees the ampleness predicate can see -/

/-- Reindexing of the tensor powers along an equality of exponents. -/
def tensorPowModuleCongr (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] {n m : ℤ}
    (h : n = m) : tensorPowModule X L n ≅ tensorPowModule X L m :=
  eqToIso (by rw [h])

/-- Ampleness transfers along isomorphisms `pow n ≅ pow' (m n)` with `m` preserving positivity. -/
private theorem isAmpleForPowers_of_iso_comp {X : Scheme.{u}} {pow pow' : ℤ → X.Modules}
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ n → 1 ≤ m n) (e : ∀ n : ℕ, pow (n : ℤ) ≅ pow' (m n : ℤ)) :
    IsAmpleForPowers X pow → IsAmpleForPowers X pow' := by
  rintro ⟨hc, h⟩
  refine ⟨hc, fun x => ?_⟩
  obtain ⟨n, hn, s, U, hU, hxU, hUaff⟩ := h x
  exact ⟨m n, hm n hn, (e n).hom.app ⊤ s, U, hU.trans (nonvanishingLocus_congr (e n) s).symm,
    hxU, hUaff⟩

/-- **Ampleness only looks at the nonnegative degrees of its family of powers.** A degreewise
isomorphism in the degrees `(n : ℤ)` for `n : ℕ` already transfers `Stacks.Ample.IsAmpleForPowers`,
because those are the only degrees at which the predicate evaluates its argument. Compare
`Stacks.Ample.isAmpleForPowers_congr`, which asks for an isomorphism in every integer degree. -/
theorem isAmpleForPowers_congr_nat {X : Scheme.{u}} {pow pow' : ℤ → X.Modules}
    (e : ∀ n : ℕ, pow (n : ℤ) ≅ pow' (n : ℤ)) :
    IsAmpleForPowers X pow ↔ IsAmpleForPowers X pow' :=
  ⟨isAmpleForPowers_of_iso_comp id (fun _ => id) e,
    isAmpleForPowers_of_iso_comp id (fun _ => id) fun n => (e n).symm⟩

/-! ### The three isomorphisms of tensor powers -/

/-- **Isomorphic invertible modules have isomorphic tensor powers**, in every nonnegative degree.
By induction on the degree: the degree-zero powers are both `𝒪_X`, and the step splits
`N ^⊗ (n + 1)` as `N ^⊗ n ⊗ N ^⊗ 1` with `Stacks.Ample.tensorPowModuleAddIso` and applies the given
isomorphism to each factor. -/
def tensorPowModuleIsoOfIso (X : Scheme.{u}) (N N' : X.Modules) [IsInvertibleModule X N]
    [IsInvertibleModule X N'] (e : N ≅ N') :
    (n : ℕ) → tensorPowModule X N (n : ℤ) ≅ tensorPowModule X N' (n : ℤ)
  | 0 => tensorPowModuleZeroIso X N ≪≫ (tensorPowModuleZeroIso X N').symm
  | (n + 1) =>
      tensorPowModuleCongr X N (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X N (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowModuleIsoOfIso X N N' e n)
          (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm) ≪≫
        tensorPowModuleAddIso X N' (n : ℤ) 1 ≪≫
        tensorPowModuleCongr X N' (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **`(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)`**, for a nonnegative outer exponent and an arbitrary integer
inner one. By induction on `n`: the step splits the outer power as `(L ^⊗ d) ^⊗ n ⊗ (L ^⊗ d) ^⊗ 1`,
rewrites the first factor by the inductive hypothesis and the second as `L ^⊗ d`, and closes with
the addition law `L ^⊗ (d n) ⊗ L ^⊗ d ≅ L ^⊗ (d n + d)`. -/
def tensorPowModulePowIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (d : ℤ) :
    (n : ℕ) →
      tensorPowModule X (tensorPowModule X L d) (n : ℤ) ≅ tensorPowModule X L (d * (n : ℤ))
  | 0 =>
      tensorPowModuleZeroIso X (tensorPowModule X L d) ≪≫
        (tensorPowModuleZeroIso X L).symm ≪≫
        tensorPowModuleCongr X L (show (0 : ℤ) = d * ((0 : ℕ) : ℤ) by push_cast; ring)
  | (n + 1) =>
      tensorPowModuleCongr X (tensorPowModule X L d)
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X (tensorPowModule X L d) (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowModulePowIso X L d n)
          (tensorPowModuleOneIso X (tensorPowModule X L d)) ≪≫
        tensorPowModuleAddIso X L (d * (n : ℤ)) d ≪≫
        tensorPowModuleCongr X L
          (show d * (n : ℤ) + d = d * ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **Pullback commutes with the tensor powers of an invertible module**, in every nonnegative
degree: `f^* (M ^⊗ n) ≅ (f^* M) ^⊗ n`. The degree-zero case is
`Stacks.RelativeAmple.pullbackUnitModuleIso`, `f^* 𝒪_S ≅ 𝒪_X`, and the step is Stacks Tag 01CD.
Invertibility of `f^* M` is Stacks Tag 0B8L, an instance, so it is never written down. -/
def pullbackTensorPowModuleIso {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [IsInvertibleModule S M] :
    (n : ℕ) →
      (modulePullback f.toLRSHom.toShHom).obj (tensorPowModule S M (n : ℤ)) ≅
        tensorPowModule X ((modulePullback f.toLRSHom.toShHom).obj M) (n : ℤ)
  | 0 =>
      (modulePullback f.toLRSHom.toShHom).mapIso (tensorPowModuleZeroIso S M) ≪≫
        Stacks.RelativeAmple.pullbackUnitModuleIso f ≪≫
        (tensorPowModuleZeroIso X ((modulePullback f.toLRSHom.toShHom).obj M)).symm
  | (n + 1) =>
      (modulePullback f.toLRSHom.toShHom).mapIso
          (tensorPowModuleCongr S M (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
            (tensorPowModuleAddIso S M (n : ℤ) 1).symm) ≪≫
        pullbackTensorModulesIso f (tensorPowModule S M (n : ℤ)) (tensorPowModule S M 1) ≪≫
        tensorModulesMapIso X (pullbackTensorPowModuleIso f M n)
          ((modulePullback f.toLRSHom.toShHom).mapIso (tensorPowModuleOneIso S M) ≪≫
            (tensorPowModuleOneIso X ((modulePullback f.toLRSHom.toShHom).obj M)).symm) ≪≫
        tensorPowModuleAddIso X ((modulePullback f.toLRSHom.toShHom).obj M) (n : ℤ) 1 ≪≫
        tensorPowModuleCongr X ((modulePullback f.toLRSHom.toShHom).obj M)
          (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-! ### The two constructions of the tensor powers agree -/

/-- The Tag 01CS class that Tag 01CU's own tensor powers ask for, obtained from the one the
ampleness theory uses by the bridge
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
theorem stacksIsInvertible (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).mpr ‹_›

/-- Tensoring on the right by an invertible `𝒪_X`-module is an equivalence, which is the
hypothesis `Stacks.SheafOfModules.TensorPower.tensorPower` is stated with. This is
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` with its Tag 01CS hypothesis
supplied by `Stacks.RelativeVeryAmple.stacksIsInvertible`. -/
theorem isEquivalence_tensorRightFunctor_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).flip.obj
        (L))).IsEquivalence := by
  let _ := stacksIsInvertible X L
  exact Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- **The two constructions of the integer tensor powers of an invertible `𝒪_X`-module agree in
every nonnegative degree.** `Stacks.SheafOfModules.TensorPower.tensorPower` is the one carrying the
Tag 01CU attribute — the image of `𝒪_X` under the `n`-th power of the autoequivalence "tensor on
the right by `L`" — and `Stacks.Ample.tensorPowModule` is the one the ampleness theory of Tags
01PS, 01VH and 0891 is written over, an iterated tensor product. No comparison between them existed
(`StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean` records its absence as the
reason Tag 01VS has to be stated twice, once for each family).

By induction on the degree: both are `𝒪_X` in degree zero, and both step by tensoring with `L`,
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` on one side and
`Stacks.Ample.tensorPowModuleAddIso` at `(n, 1)` on the other.

The hypothesis on the left-hand side is the one `tensorPower` itself asks for, that tensoring on
the right by `L` is an equivalence; it is supplied from invertibility by
`Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule`, so nothing is
assumed twice. It is taken as the hypothesis rather than
`Stacks.SheafOfModules.IsInvertible` because instance search does not get from the
latter to the former here: the Grothendieck topology is an implicit argument of
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` to be recovered from the type
of the sheaf condition, and `Scheme.Modules` does not unfold during that unification. -/
def cardTensorPowerIso (X : Scheme.{u}) (L : X.Modules)
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).flip.obj
        (L))).IsEquivalence]
    [IsInvertibleModule X L] :
    (n : ℕ) →
      Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L (n : ℤ) ≅
        tensorPowModule X L (n : ℤ)
  | 0 => (tensorPowModuleZeroIso X L).symm
  | (n + 1) =>
      Stacks.SheafOfModules.TensorPower.tensorPowerReindex X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L (n : ℤ)).symm ≪≫
        tensorModulesMapIso X (cardTensorPowerIso X L n) (tensorPowModuleOneIso X L).symm ≪≫
        tensorPowModuleAddIso X L (n : ℤ) 1 ≪≫
        tensorPowModuleCongr X L (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-! ### Ampleness is an invariant of the isomorphism class -/

/-- **Ampleness depends only on the isomorphism class of the invertible module.** The module
documentation of `StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean` records this as not
available; it follows from `Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso` and
`Stacks.RelativeVeryAmple.isAmpleForPowers_congr_nat`. -/
theorem isAmple_congr {X : Scheme.{u}} (N N' : X.Modules) [hN : IsInvertibleModule X N]
    [hN' : IsInvertibleModule X N'] (e : N ≅ N') : IsAmple X N ↔ IsAmple X N' :=
  isAmpleForPowers_congr_nat (tensorPowModuleIsoOfIso X N N' e)

/-- **Relative ampleness depends only on the isomorphism class of the invertible module.** The
restriction to the preimage of an affine open of the base is a functor, so it carries the
isomorphism along, and `Stacks.RelativeVeryAmple.isAmple_congr` finishes on each preimage. -/
theorem isRelativelyAmple_congr {X S : Scheme.{u}} (f : X ⟶ S) (N N' : X.Modules)
    [IsInvertibleModule X N] [IsInvertibleModule X N'] (e : N ≅ N') :
    Stacks.RelativeAmple.IsRelativelyAmple f N ↔
      Stacks.RelativeAmple.IsRelativelyAmple f N' := by
  have key : ∀ P P' : X.Modules, ∀ _ : IsInvertibleModule X P, ∀ _ : IsInvertibleModule X P',
      (P ≅ P') → Stacks.RelativeAmple.IsRelativelyAmple f P →
        Stacks.RelativeAmple.IsRelativelyAmple f P' := by
    rintro P P' hP hP' g ⟨hqc, h⟩
    exact ⟨hqc, fun V hV => (isAmple_congr _ _
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso g)).mp (h V hV)⟩
  exact ⟨key N N' ‹_› ‹_› e, key N' N ‹_› ‹_› e.symm⟩

/-- **Stacks Tag 01QE for any module isomorphic to the structure sheaf**, as a corollary of
`Stacks.RelativeVeryAmple.isAmple_congr`.
`Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule` proves the same statement the
long way round — by transporting a nowhere-vanishing global basis into every tensor degree with
`Stacks.RelativeAmple.unitLikeTensorPowBasis` and feeding it to
`Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` — precisely because the isomorphism invariance of
ampleness was not available. It is now, so that route and its two auxiliary definitions are no
longer needed. -/
@[ega "II 5.1.2" "more general"]
theorem isQuasiAffine_iff_isAmple_of_iso_unitModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (e : L ≅ unitModule X) : X.IsQuasiAffine ↔ IsAmple X L :=
  (isQuasiAffine_iff_isAmple X).trans (isAmple_congr _ _ e.symm)

/-! ### Half of Stacks Tag 01PT -/

/-- **Half of Stacks Tag 01PT.** If a positive tensor power of an invertible module is ample then
the module is ample. The section of `(L ^⊗ d) ^⊗ n` whose nonvanishing locus is the affine open
produced by ampleness of `L ^⊗ d` is carried by `Stacks.RelativeVeryAmple.tensorPowModulePowIso` to
a section of `L ^⊗ (d n)`, with `d n ≥ 1`, and `Stacks.Ample.nonvanishingLocus_congr` says the
nonvanishing locus does not move. -/
theorem isAmple_of_isAmple_tensorPowModule {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d)
    (h : IsAmple X (tensorPowModule X L (d : ℤ))) : IsAmple X L := by
  refine isAmpleForPowers_of_iso_comp (fun n => d * n)
    (fun n hn => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
    (fun n => tensorPowModulePowIso X L (d : ℤ) n ≪≫
      tensorPowModuleCongr X L (show (d : ℤ) * (n : ℤ) = ((d * n : ℕ) : ℤ) by push_cast; ring))
    h

/-- **Half of Stacks Tag 01PT, relative to a morphism.** If a positive tensor power of an
invertible module is ample relative to `f` then the module is ample relative to `f`. This is the
implication (2) ⟹ (1) of Stacks Tag 01VU once Tag 01VN has supplied relative ampleness of the very
ample power.

On the preimage of an affine open `V` of the base the hypothesis gives ampleness of
`(f⁻¹V).ι^* (L ^⊗ d)`, which `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` identifies with
the `d`-th tensor power of `(f⁻¹V).ι^* L`; the absolute statement then applies on that
subscheme. -/
@[ega "II 4.6.9" "Clause (i)"]
theorem isRelativelyAmple_of_isRelativelyAmple_tensorPowModule {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d)
    (h : Stacks.RelativeAmple.IsRelativelyAmple f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine ⟨h.1, fun V hV => isAmple_of_isAmple_tensorPowModule _ d hd ?_⟩
  exact (isAmple_congr _ _ (hN' := isInvertibleModule_tensorPowModule _ _ (d : ℤ))
    (pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι L d)).mp (h.2 V hV)

/-- **Stacks Tag 01VU, the implication (2) ⟹ (1), with the very ampleness input abstracted.** If
*some* positive tensor power of `L` is ample relative to `f`, then `L` is. Stated existentially
because that is the shape condition (2) of the source has. -/
@[ega "II 4.6.9" "Clause (i)"]
theorem isRelativelyAmple_of_exists_isRelativelyAmple_tensorPowModule {X S : Scheme.{u}}
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (h : ∃ d : ℕ, 1 ≤ d ∧
      Stacks.RelativeAmple.IsRelativelyAmple f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hL⟩ := h
  exact isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd hL

end Stacks.RelativeVeryAmple

end
