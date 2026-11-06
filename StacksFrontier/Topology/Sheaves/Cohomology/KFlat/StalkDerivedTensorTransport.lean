module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.Homology.KFlat.AcyclicModule
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.StalkTotalComplex

/-!
# The derived tensor product commutes with the stalk functor, on arbitrary objects

Let `(X, 𝒪)` be a ringed site of the opens of a topological space and `x : X`. The stalk
functor `(-)_x : Mod(𝒪) ⥤ Mod(𝒪_x)` is exact, strong monoidal (Stacks 01CB) and preserves
K-flatness (Stacks 06YB), so

`(K ⊗^𝐋_𝒪 L)_x ≅ K_x ⊗^𝐋_{𝒪_x} L_x`

as an isomorphism of **bifunctors on the unbounded derived categories**: on arbitrary objects
`K`, `L` of `D(𝒪)`, and natural in both of them. That statement is
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso` below, and it is this
file's only piece of mathematics in the sense of a new theorem: everything is an instance of
the bifunctor transport engine `CochainComplex.KFlatBifunctor.derivedTransportIso`, whose
descent off the K-flat representatives is already proved there.

What this file supplies is the engine's hypotheses at the stalk functor, which is entirely a
matter of putting four existing statements at one and the same spelling of the stalk
ring.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso`: the comparison as an
  isomorphism of bifunctors on `D(𝒪)`.
* `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkObjIso`: its value at a pair of
  objects, `(K ⊗^𝐋 L)_x ≅ K_x ⊗^𝐋 L_x`.

## Main results

* `Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft`: the converse of
  `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` — left K-flatness for `⊗_𝒪` implies
  K-flatness, again by the symmetry of `⊗_𝒪`.
* `Stacks.SheafOfModules.DerivedTensorStalk.kFlat_stalkComplex` and `kFlatLeft_stalkComplex`:
  **Stacks 06YB in the form the engine consumes** — the stalk complex of a (left) K-flat
  complex is (left) K-flat for the tensor product of `𝒪_x`-modules.
* `Stacks.SheafOfModules.DerivedTensorStalk.stalkKFlatQ_isLocalization` and
  `stalkKFlatQLeft_isLocalization`: `D(𝒪_x)` is the localization of the (left) K-flat
  complexes of `𝒪_x`-modules.

## Implementation notes

**The one obstruction, and how it is cleared.** `ModuleCat` takes a `Ring` instance as a
*parameter of its type*, and for the stalk ring instance search returns `RingCat`'s, whereas
the K-flat resolutions
`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions` and
`moduleKFlatLocalizerLeft_hasLeftResolutions` and Mathlib's monoidal structure on `ModuleCat`
are keyed on the `Ring` derived from a `CommRing`. The two instances are definitionally equal —
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf` is built from the `RingCat` one by adding
`mul_comm`, so `CommRing.toRing` of it reduces back to it by structure eta — but they are not
syntactically equal, so instance search does not cross.
`Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat` already declares the
monoidal structure at the `RingCat` spelling. The two resolution statements are transported
inside the proofs of `stalkKFlatQ_isLocalization` and `stalkKFlatQLeft_isLocalization`. Each
proof states the resolutions at the `RingCat` spelling and proves them by the
`CommRing`-spelling instance, leaving the crossing to the *conversion check*; then
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` or its left mirror
gives the localization. The resolutions do not involve the derived category, so its
`HasDerivedCategory` instance is the one at the `RingCat` spelling throughout.

**Both variables of K-flatness.** The engine asks for transport of left K-flatness as well as
of K-flatness, and the stalk criterion Stacks 06YB is stated for the right variable only. The
left statement is obtained by passing through the symmetry of the tensor product twice: at
`⊗_𝒪` by `Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft`, and back at `⊗_{𝒪_x}` by
`CochainComplex.KFlat.kFlatLeft_of_kFlat`. No braiding of total complexes is needed; both
steps are `CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip` composed with an
isomorphism of bifunctors.

**The exactness and colimit-preservation hypotheses.** `PreservesFiniteLimits` is
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` and is found by
synthesis. `PreservesFiniteColimits` and the antidiagonal coproducts are not: the stalk functor
preserves all colimits, but `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` is
a lemma, and the shrinking step `preservesColimitsOfSize_shrink` is a lemma too, so neither form
is reachable by search. They are `letI`-ed from
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesAntidiagonalCoproducts`, which is
seated for exactly this purpose.

## References

* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Lemma 20.26.4 (Tag 079U)](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory Opposite
open AlgebraicGeometry.SheafOfModules

universe u

/-! ### K-flatness in the left variable of the tensor product of sheaves of modules -/

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **A complex of `𝒪`-modules which is K-flat in the left variable of `⊗_𝒪` is K-flat.**

This is the converse of `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` and has the same
proof read backwards: left K-flatness for `⊗_𝒪` is K-flatness for `(⊗_𝒪)ᶠˡᶦᵖ`, and K-flatness
is invariant under the isomorphism of bifunctors
`Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`. It is what lets the stalk criterion for
K-flatness, which constrains the right variable, be applied to the engine's left-variable
hypothesis. -/
theorem kFlat_of_kFlatLeft
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlatLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor R) K) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K :=
  CochainComplex.KFlatBifunctor.kFlat_of_natIso _ _
    (Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso R).symm
    ((CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ K).1 hK)

end Stacks.DerivedTensor.RingedSite

namespace Stacks.SheafOfModules.DerivedTensorStalk

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)

/-- The stalk ring at `x`, as the `RingCat`-valued stalk of the sheaf of rings — the ring
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over. -/
abbrev stalkRing : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x

attribute [local instance] Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat
  Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat

/-! ### The two K-flat localizations over the stalk ring -/

/-- **`D(𝒪_x)` is the localization of the K-flat complexes of `𝒪_x`-modules at the
quasi-isomorphisms**, at the `RingCat`-valued spelling of the stalk ring.

The K-flat resolutions are the instance
`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions`, stated at the
`CommRing`-derived `Ring` instance. That instance and the `RingCat` one are definitionally but
not syntactically equal, so the proof restates the resolutions at the `RingCat` spelling, leaves
the crossing to the conversion check, and applies
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions`. -/
theorem stalkKFlatQ_isLocalization
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (stalkRing R x))] :
    (CochainComplex.KFlatBifunctor.kFlatQ
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIso
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))) :=
  have : (CochainComplex.KFlatBifunctor.kFlatLocalizer
      (curriedTensor (ModuleCat.{u} (stalkRing R x)))).HasLeftResolutions :=
    CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions
      (stalkRing R x : Type u)
  CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions _

/-- **`D(𝒪_x)` is the localization of the complexes of `𝒪_x`-modules which are K-flat in the
first variable of the tensor product**, at the `RingCat`-valued spelling of the stalk ring.
See `Stacks.SheafOfModules.DerivedTensorStalk.stalkKFlatQ_isLocalization`. -/
theorem stalkKFlatQLeft_isLocalization
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (stalkRing R x))] :
    (CochainComplex.KFlatBifunctor.kFlatQLeft
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIsoLeft
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))) :=
  have : (CochainComplex.KFlatBifunctor.kFlatLocalizerLeft
      (curriedTensor (ModuleCat.{u} (stalkRing R x)))).HasLeftResolutions :=
    CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizerLeft_hasLeftResolutions
      (stalkRing R x : Type u)
  CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions _

/-- The stalk functor preserves finite colimits. It preserves all of them
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Stacks 01AH), but that is
a lemma and not an instance, so the finite form is named here for consumers to `letI`. -/
theorem stalkFunctor_preservesFiniteColimits :
    PreservesFiniteColimits
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
  let := stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  inferInstance

/-! ### Stacks 06YB in the two forms the transport engine consumes -/

section

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The stalk complex of a K-flat complex is K-flat**, in the bifunctor-relative form at the
curried tensor product of `𝒪_x`-modules. This is
`Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise` — Stacks 06YB — read at one
point, together with `CochainComplex.kFlat_iff_kFlatBifunctor`. -/
theorem kFlat_stalkComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K) :
    letI : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor (ModuleCat.{u} (stalkRing R x)))
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)
        x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise R K).1 hK x

/-- **The stalk complex of a left K-flat complex is left K-flat.** The stalk criterion
Stacks 06YB constrains the right variable of the tensor product, so the statement is obtained
by passing through the symmetry of the tensor product on each side:
`Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft` upstairs and
`CochainComplex.KFlat.kFlatLeft_of_kFlat` over the stalk ring. -/
theorem kFlatLeft_stalkComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlatLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor R) K) :
    letI : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    CochainComplex.KFlatBifunctor.KFlatLeft (curriedTensor (ModuleCat.{u} (stalkRing R x)))
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)
        x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlat.kFlatLeft_of_kFlat.{u, u}
    ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise R K).1
      (Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft R hK) x)

end

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-! ### The comparison on the derived categories -/

variable [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} (stalkRing R x))]

attribute [local instance] stalkKFlatQ_isLocalization stalkKFlatQLeft_isLocalization

/-- **The derived tensor product commutes with the stalk functor, on arbitrary objects of
`D(𝒪)` and naturally in both variables:**

`(K ⊗^𝐋_𝒪 L)_x ≅ K_x ⊗^𝐋_{𝒪_x} L_x`.

This is the statement that
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso` does not supply — there the
isomorphism is produced at chosen K-flat representatives, with no naturality and no coherence —
and it is an instance of `CochainComplex.KFlatBifunctor.derivedTransportIso` at the stalk
functor, whose hypotheses are: exactness and colimit preservation of `(-)_x`, the underived
comparison `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso` of Stacks 01CB with its
two naturality squares, the two K-flat localizations, and transport of K-flatness in both
variables by Stacks 06YB. -/
def derivedTensorStalkNatIso :
    letI : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesFiniteLimits
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesFiniteColimits
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      stalkFunctor_preservesFiniteColimits R x
    CochainComplex.KFlatBifunctor.derivedTransportSource
        (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) ≅
      CochainComplex.KFlatBifunctor.derivedTransportTarget
        (curriedTensor (ModuleCat.{u} (stalkRing R x)))
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
  let : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let : PreservesFiniteLimits
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let : PreservesFiniteColimits
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    stalkFunctor_preservesFiniteColimits R x
  let := fun n : ℤ => stalkFunctor_preservesAntidiagonalCoproducts
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x n
  CochainComplex.KFlatBifunctor.derivedTransportIso
    (Stacks.SheafOfModules.Tensor.sheafTensor R)
    (curriedTensor (ModuleCat.{u} (stalkRing R x)))
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
    (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso (ringedSpaceOfSheaf R) x)
    (fun f N => Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso_naturality_left
      (ringedSpaceOfSheaf R) x f N)
    (fun M {_ _} g => Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso_naturality_right
      (ringedSpaceOfSheaf R) x M g)
    (fun K hK => kFlatLeft_stalkComplex R x K hK)
    (fun L hL => kFlat_stalkComplex R x L hL)

/-- **`(K ⊗^𝐋_𝒪 L)_x ≅ K_x ⊗^𝐋_{𝒪_x} L_x`** at a pair of objects of `D(𝒪)`, read off
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkNatIso`. Unlike
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso` this is the value of a natural
isomorphism, so it commutes with morphisms in each variable. -/
def derivedTensorStalkObjIso
    (K L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))) :
    letI : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesFiniteLimits
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesFiniteColimits
        (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      stalkFunctor_preservesFiniteColimits R x
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (((CochainComplex.KFlatBifunctor.derivedBifunctor
          (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj K).obj L) ≅
      ((CochainComplex.KFlatBifunctor.derivedBifunctor
            (curriedTensor (ModuleCat.{u} (stalkRing R x)))).obj
          ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            R) x).mapDerivedCategory.obj K)).obj
        ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          R) x).mapDerivedCategory.obj L) :=
  let : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let : PreservesFiniteLimits
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let : PreservesFiniteColimits
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    stalkFunctor_preservesFiniteColimits R x
  ((derivedTensorStalkNatIso R x).app K).app L

end Stacks.SheafOfModules.DerivedTensorStalk

end
