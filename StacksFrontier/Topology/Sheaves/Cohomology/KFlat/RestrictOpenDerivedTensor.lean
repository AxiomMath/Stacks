module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.RestrictOpenKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkDerivedTensorTransport

/-!
# The derived tensor product commutes with restriction to an open subspace

Let `(W, 𝒪_W)` be a ringed space and `U ⊆ W` open. Restriction to the open subspace,
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, is exact, carries `⊗_{𝒪_W}` to
`⊗_{𝒪_U}` (Stacks 01CU, as
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`) and preserves K-flatness
(Stacks 06YC, as `Stacks.Cohomology.RestrictOpenKFlat.kFlat_moduleRestriction`). Therefore

`(K ⊗^𝐋_{𝒪_W} L)|_U ≅ K|_U ⊗^𝐋_{𝒪_U} L|_U`

as an isomorphism of **bifunctors on the unbounded derived categories**: on arbitrary objects
`K`, `L` of `D(𝒪_W)` and natural in both of them. That is
`Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictNatIso`, and it is the
restriction form of the bifunctor transport engine
`CochainComplex.KFlatBifunctor.derivedTransportIso`, whose descent off the K-flat
representatives is proved there.

## Main definitions

* `Stacks.Cohomology.RestrictOpenDerivedTensor.restrictFunctor`: `moduleRestriction W U` with
  its two categories named at the spelling the tensor product uses (see the implementation
  notes).
* `Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictNatIso`: the comparison as
  an isomorphism of bifunctors on `D(𝒪_W)`.
* `Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictObjIso`: its value at a
  pair of objects, `(K ⊗^𝐋 L)|_U ≅ K|_U ⊗^𝐋 L|_U`.

## Main results

* `Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatLeft_moduleRestriction`: **Stacks 06YC in
  the left variable** — the restriction of a complex which is K-flat in the first variable of
  `⊗_{𝒪_W}` is K-flat in the first variable of `⊗_{𝒪_U}`. The engine asks for transport of
  K-flatness in both variables and the stalk criterion constrains only the second, so this is
  obtained by passing through the symmetry of the tensor product on each side.
* `Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatQ_isLocalization` and
  `kFlatQLeft_isLocalization`: `D(Mod(𝒪_Z))` is the localization of the (left) K-flat complexes
  of `𝒪_Z`-modules, for a ringed space `Z`.
* `Stacks.Cohomology.RestrictOpenDerivedTensor.restrictTensorIso_naturality_left` and
  `_right`: Stacks 01CU's comparison in the shape the engine consumes, one variable at a time.

## Implementation notes

**The one obstruction, and how it is cleared.** The category of `𝒪_W`-modules has two names
in the tree: `SheafOfModules (structureSheafRing W)`, which is the type of
`moduleRestriction`, and `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)`,
which is the type of `Stacks.SheafOfModules.Tensor.sheafTensor`. They are equal by `rfl`
(`Stacks.RingedSpaceModule.ringSheaf_eq_structureSheaf`), but not syntactically, so the
`Preadditive` and `Abelian` instances found at one are not the instances found at the other.
Handing `moduleRestriction W U` to the engine directly therefore produces a goal
`Functor.Additive (moduleRestriction W U)` whose source category is named one way — it comes
from the tensor bifunctor — and whose target category is named the other — it comes from the
restriction functor. No instance exists at that mixed naming, and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction_additive` is not it.

`restrictFunctor` is the fix: the same functor, with *both* categories named at the tensor
product's spelling. Every instance the engine needs is then stated at one naming and seated
here — additivity by transporting `moduleRestriction_additive` across the `rfl`, which
`exact`'s conversion check crosses where instance search does not, and exactness and the
adjunction by `inferInstance` through the same conversion.

**The antidiagonal coproducts.** `restrictFunctor` preserves all colimits, being a left
adjoint (Stacks 00A7 (2)), but `PreservesColimitsOfSize.{0,0}` is reached from that only
through `preservesColimitsOfSize_shrink`, which is a lemma; both it and the resulting
`PreservesColimitsOfShape (Discrete _)` are named here for the engine to `letI`.

**The total complex of the transported bicomplex.** The engine also asks that
`Φ(F(K, L))` have a total complex. At the stalk this is found by instance search, because
there the bifunctor is a `curriedTensor` and
`CochainComplex.hasTotal_mapBicomplex_curriedTensor` applies; `sheafTensor` is not a
`curriedTensor`, so `hasTotal_mapBicomplex_restrictFunctor` supplies it, by transporting the
total complex of `F'(Φ K, Φ L)` along `Functor.mapBifunctorBicomplexIso`.

**The two K-flat localizations.** The K-flat resolutions are an instance,
`Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions` and its left companion, for a
ring `R : Sheaf J CommRingCat`; but `Z.sheaf` is a `TopCat.Sheaf`, a semireducible definition that
instance search does not unfold to that type, so it does not take `Z.sheaf` for `R` and does not
find the localizations at a ringed space. They are seated at `Z.sheaf` here, from
`Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` and its left companion, as
`OnARingedSpace.lean` seats the additivity instances. The
seating has to be repeated at `restrictToOpen W U`, because `restrictToOpen` is `@[reducible]`
and unfolds to a `SheafedSpace.mk`, so the general instance's `Z.sheaf` can no longer be
matched: instance search would have to solve `?Z.presheaf =?= U.isOpenEmbedding.functor.op ⋙
W.presheaf` for `?Z`. The specialized instances are the general one applied to
`restrictToOpen W U` by hand.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 079U)](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 00A7](https://stacks.math.columbia.edu/tag/00A7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.SheafOfModules.TensorPower (restrictTensorSheafIso restrictTensorSheafIso_naturality)

open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Cohomology.RestrictOpenDerivedTensor

/-! ### The two K-flat localizations on a ringed space -/

section Localization

variable (Z : RingedSpace.{u, u})
  [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf))]

/-- **`D(Mod(𝒪_Z))` is the localization of the K-flat complexes of `𝒪_Z`-modules at the
quasi-isomorphisms**, on a ringed space. This is
`Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` seated at the ring `Z.sheaf`, a
`TopCat.Sheaf`, which instance search does not unfold to the `Sheaf J CommRingCat` at which the
K-flat resolutions are an instance; see the implementation notes. -/
instance kFlatQ_isLocalization :
    (CochainComplex.KFlatBifunctor.kFlatQ
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization (C := Opens Z.carrier) Z.sheaf

/-- **`D(Mod(𝒪_Z))` is the localization of the complexes of `𝒪_Z`-modules which are K-flat in
the first variable of `⊗_{𝒪_Z}`.** See
`Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatQ_isLocalization`. -/
instance kFlatQLeft_isLocalization :
    (CochainComplex.KFlatBifunctor.kFlatQLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIsoLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQLeft_isLocalization (C := Opens Z.carrier) Z.sheaf

end Localization

variable (W : RingedSpace.{u, u}) (U : Opens W.carrier)

/-! ### Restriction to an open, named at the tensor product's spelling -/

/-- **Restriction of `𝒪_W`-modules to the open subspace `U`**, with its source and target
categories named as `Stacks.SheafOfModules.Tensor.sheafTensor` names them. This is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction W U` and nothing else — the two namings
of the category of `𝒪_W`-modules are equal by `rfl` — but it is the naming at which the
transport engine's instance arguments can be stated; see the implementation notes. -/
abbrev restrictFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (restrictToOpen W U).sheaf) :=
  moduleRestriction W U

/-- **Restriction to an open subspace is additive**, with the two additive structures the ones
the tensor product's naming of the categories carries. This is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction_additive`, whose statement names the
same two structures through the other naming of the categories; the `Preadditive` instances
are definitionally equal and the conversion check crosses between them, where instance search
does not. -/
instance restrictFunctor_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (restrictFunctor W U) :=
  moduleRestriction_additive W U

/-- Restriction to an open subspace preserves finite limits, being a right adjoint
(Stacks 00A7 (2)). -/
instance restrictFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (restrictFunctor W U) :=
  inferInstanceAs (PreservesFiniteLimits (moduleRestriction W U))

/-- Restriction to an open subspace is a left adjoint, namely the left adjoint of pushforward
along the open immersion. This is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction_isLeftAdjoint`, which is a theorem
there and is registered as an instance here. -/
instance restrictFunctor_isLeftAdjoint : (restrictFunctor W U).IsLeftAdjoint :=
  moduleRestriction_isLeftAdjoint W U

/-- Restriction to an open subspace preserves finite colimits, being a left adjoint. -/
instance restrictFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (restrictFunctor W U) :=
  inferInstance

/-- Restriction to an open subspace preserves colimits of diagrams indexed by a category in
`Type 0`. It preserves all colimits, being a left adjoint, but the shrinking step
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` is a lemma and not an instance, so this
form is named for consumers to `letI`. -/
lemma restrictFunctor_preservesColimitsOfSize_zero :
    PreservesColimitsOfSize.{0, 0} (restrictFunctor W U) :=
  let : PreservesColimits (restrictFunctor W U) := inferInstance
  preservesColimitsOfSize_shrink (restrictFunctor W U)

/-- **Restriction to an open subspace preserves the coproducts occurring in the total complex
of a double cochain complex over `ℤ`**: those indexed by an antidiagonal
`ComplexShape.π (up ℤ) (up ℤ) (up ℤ) ⁻¹' {n}`. This is the hypothesis of
`CategoryTheory.Functor.mapBifunctorTotalIso`, so it is what makes the total tensor complex
transport along `-|_U` at all. -/
lemma restrictFunctor_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (restrictFunctor W U) :=
  let := restrictFunctor_preservesColimitsOfSize_zero W U
  inferInstance

section LocalizationRestrict

variable [HasDerivedCategory.{u + 1}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
    (restrictToOpen W U).sheaf))]

/-- `Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatQ_isLocalization` at the open subspace,
which instance search does not reach there: `restrictToOpen` is `@[reducible]` and unfolds to a
`SheafedSpace.mk`, so matching the general instance would mean solving `?Z.presheaf` against a
concrete presheaf. -/
instance kFlatQ_isLocalization_restrictToOpen :
    (CochainComplex.KFlatBifunctor.kFlatQ
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (restrictToOpen W U).sheaf)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)) :=
  kFlatQ_isLocalization (restrictToOpen W U)

/-- `Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatQLeft_isLocalization` at the open
subspace. See
`Stacks.Cohomology.RestrictOpenDerivedTensor.kFlatQ_isLocalization_restrictToOpen`. -/
instance kFlatQLeft_isLocalization_restrictToOpen :
    (CochainComplex.KFlatBifunctor.kFlatQLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (restrictToOpen W U).sheaf)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIsoLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)) :=
  kFlatQLeft_isLocalization (restrictToOpen W U)

end LocalizationRestrict

/-! ### The underived comparison, in the shape the engine consumes -/

/-- **`(M ⊗_{𝒪_W} L)|_U ≅ M|_U ⊗_{𝒪_U} L|_U`**, the underived comparison of Stacks 01CU, at
the tensor product's naming of the categories. This is
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`; the objectwise tensor product
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` it is stated with is the value of
`Stacks.SheafOfModules.Tensor.sheafTensor` by `rfl`. -/
abbrev restrictTensorIso
    (M L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) :
    (restrictFunctor W U).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf).obj
          ((restrictFunctor W U).obj M)).obj ((restrictFunctor W U).obj L) :=
  restrictTensorSheafIso W U M L

/-- **The comparison is natural in the first variable.** This is
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality` at `g = 𝟙 L`; the
functor identity laws cancel the identity factors. -/
theorem restrictTensorIso_naturality_left
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)}
    (f : M ⟶ M')
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) :
    (restrictFunctor W U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map f).app L) ≫
        (restrictTensorIso W U M' L).hom =
      (restrictTensorIso W U M L).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf).map
          ((restrictFunctor W U).map f)).app ((restrictFunctor W U).obj L) :=
  by
    have naturality :
        (restrictFunctor W U).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map f).app L ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M').map
                (𝟙 L)) ≫ (restrictTensorIso W U M' L).hom =
          (restrictTensorIso W U M L).hom ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (restrictToOpen W U).sheaf).map ((restrictFunctor W U).map f)).app
                ((restrictFunctor W U).obj L) ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (restrictToOpen W U).sheaf).obj ((restrictFunctor W U).obj M')).map
                  ((restrictFunctor W U).map (𝟙 L))) :=
      restrictTensorSheafIso_naturality W U f (𝟙 L)
    have sourceIdentity :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M').map_id L
    have restrictionIdentity := (restrictFunctor W U).map_id L
    have targetIdentity :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (restrictToOpen W U).sheaf).obj ((restrictFunctor W U).obj M')).map_id
          ((restrictFunctor W U).obj L)
    simpa only [sourceIdentity, restrictionIdentity, targetIdentity, Category.comp_id] using
      naturality

/-- **The comparison is natural in the second variable.** See
`Stacks.Cohomology.RestrictOpenDerivedTensor.restrictTensorIso_naturality_left`. -/
theorem restrictTensorIso_naturality_right
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf))
    {L L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)}
    (g : L ⟶ L') :
    (restrictFunctor W U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).map g) ≫
        (restrictTensorIso W U M L').hom =
      (restrictTensorIso W U M L).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf).obj
          ((restrictFunctor W U).obj M)).map ((restrictFunctor W U).map g) :=
  by
    have naturality :
        (restrictFunctor W U).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map (𝟙 M)).app
                L ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).map
                  g) ≫ (restrictTensorIso W U M L').hom =
          (restrictTensorIso W U M L).hom ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (restrictToOpen W U).sheaf).map ((restrictFunctor W U).map (𝟙 M))).app
                ((restrictFunctor W U).obj L) ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (restrictToOpen W U).sheaf).obj ((restrictFunctor W U).obj M)).map
                  ((restrictFunctor W U).map g)) :=
      restrictTensorSheafIso_naturality W U (𝟙 M) g
    have sourceIdentity :
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map (𝟙 M)).app L =
          𝟙 _ :=
      NatTrans.congr_app
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map_id M) L
    have restrictionIdentity := (restrictFunctor W U).map_id M
    have targetIdentity :
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (restrictToOpen W U).sheaf).map (𝟙 ((restrictFunctor W U).obj M))).app
            ((restrictFunctor W U).obj L) = 𝟙 _ :=
      NatTrans.congr_app
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (restrictToOpen W U).sheaf).map_id ((restrictFunctor W U).obj M))
        ((restrictFunctor W U).obj L)
    simpa only [sourceIdentity, restrictionIdentity, targetIdentity, Category.id_comp] using
      naturality

/-- **The restriction of the tensor double complex has a total complex.** It is isomorphic, by
`CategoryTheory.Functor.mapBifunctorBicomplexIso` applied to the underived comparison, to the
double complex computing `K|_U ⊗_{𝒪_U} L|_U`, which has one. At the stalk functor the
corresponding instance is found by search, because there the bifunctor is a `curriedTensor`;
`Stacks.SheafOfModules.Tensor.sheafTensor` is not, so it is supplied. -/
instance hasTotal_mapBicomplex_restrictFunctor
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) ℤ) :
    HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.mapBicomplex (restrictFunctor W U)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            W.sheaf).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso
    (Functor.mapBifunctorBicomplexIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)
      (restrictFunctor W U) (restrictFunctor W U) (restrictFunctor W U)
      (restrictTensorIso W U) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (fun f N => restrictTensorIso_naturality_left W U f N)
      (fun M {_ _} g => restrictTensorIso_naturality_right W U M g) K L).symm
    (ComplexShape.up ℤ)

/-! ### Stacks 06YC in the left variable of the tensor product -/

/-- **The restriction to `U` of a complex of `𝒪_W`-modules which is K-flat in the first
variable of `⊗_{𝒪_W}` is K-flat in the first variable of `⊗_{𝒪_U}`.**

The transport engine asks for transport of K-flatness in both variables, and
`Stacks.Cohomology.RestrictOpenKFlat.kFlat_moduleRestriction` — Stacks 06YC by the stalk
criterion — constrains the second only, the stalk criterion Stacks 06YB being a statement about
that variable. The left statement is obtained by passing through the symmetry of the tensor
product on each side: at `⊗_{𝒪_W}` by
`Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft` and back at `⊗_{𝒪_U}` by
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`. No braiding of total complexes is
needed; both steps are `CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip` composed with
`Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`. -/
theorem kFlatLeft_moduleRestriction
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlatLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) K) :
    CochainComplex.KFlatBifunctor.KFlatLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)
      (((restrictFunctor W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat (restrictToOpen W U).sheaf
    (Stacks.Cohomology.RestrictOpenKFlat.kFlat_moduleRestriction W U K
      (Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft W.sheaf hK))

/-! ### The comparison on the derived categories -/

section Derived

variable
  [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf))]
  [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (restrictToOpen W U).sheaf))]

/-- **The derived tensor product commutes with restriction to an open subspace, on arbitrary
objects of `D(𝒪_W)` and naturally in both variables:**

`(K ⊗^𝐋_{𝒪_W} L)|_U ≅ K|_U ⊗^𝐋_{𝒪_U} L|_U`.

This is `CochainComplex.KFlatBifunctor.derivedTransportIso` at `moduleRestriction W U`, whose
hypotheses are: exactness and colimit preservation of `-|_U`, the underived comparison
`Stacks.Cohomology.RestrictOpenDerivedTensor.restrictTensorIso` of Stacks 01CU with its two
naturality squares, the two K-flat localizations over `𝒪_W` and over `𝒪_U`, and transport of
K-flatness in both variables by Stacks 06YC. -/
def derivedTensorRestrictNatIso :
    CochainComplex.KFlatBifunctor.derivedTransportSource
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) (restrictFunctor W U) ≅
      CochainComplex.KFlatBifunctor.derivedTransportTarget
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)
        (restrictFunctor W U) (restrictFunctor W U) :=
  letI := fun n : ℤ => restrictFunctor_preservesAntidiagonalCoproducts W U n
  CochainComplex.KFlatBifunctor.derivedTransportIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)
    (restrictFunctor W U) (restrictFunctor W U) (restrictFunctor W U)
    (restrictTensorIso W U)
    (fun f L => restrictTensorIso_naturality_left W U f L)
    (fun M {_ _} g => restrictTensorIso_naturality_right W U M g)
    (fun K hK => kFlatLeft_moduleRestriction W U K hK)
    (fun L hL => Stacks.Cohomology.RestrictOpenKFlat.kFlat_moduleRestriction W U L hL)

/-- **`(K ⊗^𝐋_{𝒪_W} L)|_U ≅ K|_U ⊗^𝐋_{𝒪_U} L|_U`** at a pair of objects of `D(𝒪_W)`, read off
`Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictNatIso`. Unlike a comparison
produced at chosen K-flat representatives this is the value of a natural isomorphism, so it
commutes with morphisms in each variable. -/
def derivedTensorRestrictObjIso
    (K L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf))) :
    (restrictFunctor W U).mapDerivedCategory.obj
        (((CochainComplex.KFlatBifunctor.derivedBifunctor
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)).obj K).obj L) ≅
      ((CochainComplex.KFlatBifunctor.derivedBifunctor
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (restrictToOpen W U).sheaf)).obj
          ((restrictFunctor W U).mapDerivedCategory.obj K)).obj
        ((restrictFunctor W U).mapDerivedCategory.obj L) :=
  ((derivedTensorRestrictNatIso W U).app K).app L

end Derived

end Stacks.Cohomology.RestrictOpenDerivedTensor

end
