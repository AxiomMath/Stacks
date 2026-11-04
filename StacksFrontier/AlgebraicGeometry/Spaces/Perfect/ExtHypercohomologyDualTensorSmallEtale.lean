module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.HypercohomologyUnitHomSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv

/-!
# `Ext` out of a perfect object as the hypercohomology of the dual tensor

Let `X` be an algebraic space over a scheme `S`, let `E` be a perfect object of `D(𝒪_X)`
(Stacks 08G5) and let `M` be an arbitrary object of `D(𝒪_X)`.  This file identifies

`Ext^i_{𝒪_X}(E, M) ≅ H^i(X, E^∨ ⊗^𝐋_{𝒪_X} M)`,

the cohomology on the right being that of the abelian-group valued derived global sections
`AlgebraicGeometry.Space.derivedGlobalSectionsAb`.  That identification is the `hExt` input of the
`Ext`-clause of Stacks 0CRU, and it is proved here with **no hypothesis beyond perfectness of
`E`**: it is Stacks 08JJ in the form
`AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual` composed with Stacks 08JA at the
structure sheaf in every degree,
`AlgebraicGeometry.Space.derivedGlobalSectionsAbUnitHomNatIso`.

It is then used to prove the `Ext`-clause of Stacks 0CRU **over `X` itself**:
`Ext^i_{𝒪_X}(E, K)` is countable when `X` is quasi-compact and absolutely quasi-separated and the
cohomology sheaves of `E^∨ ⊗^𝐋 K` are quasi-coherent with countable sets of sections over the
affine étale charts of `X`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleExtDerivedGlobalSectionsAbEquiv`:
  `Ext^i(E, M) ≃+ H^i(X, E^∨ ⊗^𝐋 M)` for perfect `E`.

## Main results

* `AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_of_countable_sections`:
  the dévissage of Stacks 0CRU read at the identity étale object, so that it speaks about
  `H^i(X, L)` itself.
* `AlgebraicGeometry.Space.countable_ext_of_countable_sections_derivedDualTensor`: the
  `Ext`-clause of Stacks 0CRU over `X`.

## The hypotheses that are carried, and why

`smallEtaleExtDerivedGlobalSectionsAbEquiv` carries only `hE`, perfectness of `E`, which is part
of the statement of Stacks 08JJ and of Stacks 0CRU.

`hasCountableCohomology_derivedGlobalSectionsAb_of_countable_sections` carries only the tag's own
hypotheses: `hZ`, `hXqc`, `hXqs` on the base and on `X`, and `hqc`, `hcount` on `L`.

`countable_ext_of_countable_sections_derivedDualTensor` carries, besides those, two hypotheses
about `E^∨ ⊗^𝐋 K` which are **inputs** and not part of the conclusion:

* `hqcL`: the cohomology sheaves of `E^∨ ⊗^𝐋 K` are quasi-coherent.  This is a *theorem* — it is
  Stacks 0A8A, `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom`, for `R𝓗om(E, K)`,
  carried across Stacks 08JJ — but that carrier **depends on `sorryAx`** in this library, so
  invoking it would contaminate everything here.  It is therefore carried as data, in the shape
  in which `AlgebraicGeometry.Space.countable_sections_homology_derivedTensor_of_isPerfect` also
  takes it, so that whoever discharges it does so once.
* `hcount`: the cohomology sheaves of `E^∨ ⊗^𝐋 K` have countable sets of sections over the affine
  étale charts of `X`.  The tag hypothesises countable sections for the cohomology sheaves of `K`;
  the passage across the perfect factor — a refinement of the chart over which `E` has a strictly
  perfect model, by Stacks 0218, and a dévissage on that model — is the content of
  `AlgebraicGeometry.Space.countable_sections_homology_derivedTensor_of_isPerfect`, which this
  library does not contain.  It is carried rather than proved so that no part of that proof is
  duplicated.  Note that lemma produces the tensor in the order `K ⊗^𝐋 E'` with the perfect
  factor `E'` on the right, while the identification above produces `E^∨ ⊗^𝐋 K`; the two are
  identified by the commutativity constraint of Stacks 0FPT,
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`, and `E^∨` is perfect by
  `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual`.

## What is *not* here

The clause is proved over `X`, that is at the identity object of the spaces-étale site, and not
over an arbitrary quasi-compact quasi-separated étale `U ⟶ X`.  The dévissage
`AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_restrict` already gives
`H^i(U, (E^∨ ⊗^𝐋 K)|_U)` for every such `U` from the same data; what is missing is the
identification

`(E|_U)^∨ ⊗^𝐋_{𝒪_U} (K|_U) ≅ (E^∨ ⊗^𝐋_{𝒪_X} K)|_U`

which is what turns that into the `Ext`-group over `U`.  Its three ingredients are all in this
library — `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackDualIso` (Stacks 08I3 at the
structure sheaf, for perfect `E`), `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso`
(Stacks 07A4) and
`AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback`
(the comparison of `Lg^*` with the exact `g^*` along an étale `g`) — but they are not assembled.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A8A](https://stacks.math.columbia.edu/tag/0A8A)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AddCommGrpCat (HasCountableCohomology)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **`Ext^i(E, M) ≃+ H^i(X, E^∨ ⊗^𝐋 M)` for a perfect `E`.**  This is the identification the
`Ext`-clause of Stacks 0CRU rests on, and it is unconditional given perfectness of `E`: Stacks 08JJ
in the form `AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual`,
`Ext^i(E, M) ≃+ Hom(𝒪_X, (E^∨ ⊗^𝐋 M)⟦i⟧)`, followed by Stacks 08JA at the structure sheaf in
degree `i`, `AlgebraicGeometry.Space.derivedGlobalSectionsAbDegreeEquiv`.

The intermediate group is written out as the type of the `have` rather than left to unification:
the two factors are stated in different files, whose instance environments resolve the abelian
structure of the `𝒪_X`-modules to different terms, and an ascription in *this* file's environment
is what lets `AddEquiv.trans` synthesize the addition on the `Ext`-group. -/
def smallEtaleExtDerivedGlobalSectionsAbEquiv
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    (E ⟶ M⟦i⟧) ≃+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).obj
        ((derivedGlobalSectionsAb B S hS X).obj
          (((smallEtaleDerivedTensor B S hS X).obj
            (smallEtaleDerivedDual B S hS X E)).obj M)) : Type (u + 1)) :=
  have e : (E ⟶ M⟦i⟧) ≃+ (structureDerived X ⟶
      (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj M)⟦i⟧) :=
    smallEtaleExtAddEquivUnitTensorDual B S hS X E hE M i
  e.trans (derivedGlobalSectionsAbDegreeEquiv B S hS X
    (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj M) i).symm

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The dévissage of Stacks 0CRU read over `X` itself.**  If `X` is quasi-compact and
absolutely quasi-separated and `L` has quasi-coherent cohomology sheaves with countable sets of
sections over the affine étale charts, then `H^i(X, L)` is countable in every degree.

This is `AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_restrict` — the
induction principle of Stacks 08GP with the affine case of Stacks 0BKZ and the Mayer–Vietoris
step of Stacks 0CRS — evaluated at the identity object `(X, 𝟙_X)` of the spaces-étale site, whose
restriction functor is the identity on `D(𝒪_X)` by
`AlgebraicGeometry.Space.etaleRestrictIdIso`.  No hypothesis is added: `𝟙_X` is étale, and `X` is
quasi-compact and quasi-separated over itself by assumption. -/
theorem hasCountableCohomology_derivedGlobalSectionsAb_of_countable_sections
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj L).val.obj (op v))) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS X).obj L) := by
  have hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom := fun _ _ hφ => by simpa using hφ
  have h := hasCountableCohomology_derivedGlobalSectionsAb_restrict B S hS hZ X hXqc hXqs L hqc
    hcount ⟨Over.mk (𝟙 X), hid⟩ hXqc hXqs
  exact h.of_iso ((derivedGlobalSectionsAb B S hS X).mapIso
    ((etaleRestrictIdIso B S hS X hid).app L))

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The `Ext`-clause of Stacks 0CRU over `X`.**  Let `X` be a quasi-compact absolutely
quasi-separated algebraic space over `S`, let `E` be a perfect object of `D(𝒪_X)` and let `K` be
an object of `D(𝒪_X)`.  If the cohomology sheaves of `E^∨ ⊗^𝐋 K` are quasi-coherent and have
countable sets of sections over the affine étale charts of `X`, then `Ext^i_{𝒪_X}(E, K)` is
countable.

The proof is the identification
`AlgebraicGeometry.Space.smallEtaleExtDerivedGlobalSectionsAbEquiv` of the `Ext`-group with
`H^i(X, E^∨ ⊗^𝐋 K)`, whose countability is the dévissage
`AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_of_countable_sections`
applied to `L = E^∨ ⊗^𝐋 K`.

`hqcL` and `hcount` are the two hypotheses here that are not the tag's own, and both are inputs
rather than part of the conclusion; both are carried in the shape in which the lemmas that supply
them produce them.  See the module documentation. -/
theorem countable_ext_of_countable_sections_derivedDualTensor
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hqcL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        (smallEtaleDerivedDual B S hS X E)).obj K)).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).obj K)).val.obj (op v)))
    (i : ℤ) :
    Countable (DerivedCategory.Ext E K i) :=
  have := hasCountableCohomology_derivedGlobalSectionsAb_of_countable_sections B S hS X hZ hXqc
    hXqs (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj K)
    hqcL hcount i
  (smallEtaleExtDerivedGlobalSectionsAbEquiv B S hS X E hE K i).injective.countable

end AlgebraicGeometry.Space

end
