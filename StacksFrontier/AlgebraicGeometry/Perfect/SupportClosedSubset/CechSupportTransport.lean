module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinFractionDeRham
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechLocalCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCounitComparison

/-!
# The two readings of `Coker(lastDif) ≅ i_*ℋ ᶜ_Z(ℱ)` agree

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations and let `Z` be their common
zero locus; the cokernel statements below need `c = n + 1`, the comparison of the two readings of
the degree-`c` cohomology itself needs nothing of the sort and is proved for every `c`,
`c = 0` included.  The identification of the cokernel of the last Čech differential with
`i_*ℋ ᶜ_Z(ℱ)` of [Stacks, Tag 0G7L] and [Stacks, Tag 0G7M] is built twice in this repository.

* `Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` reads it through the canonical
  comparison `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` of [Stacks, Tag 0G7L], which
  inverts `Stacks.Perfect.SupportedFraction.supportPushCounit`, the counit of [Stacks, Tag 0G72]
  obtained from the universal property of the right derived functor, and then takes degree-`c`
  cohomology **in `D(𝒪_X)`**, i.e. after the direct image from `Z`.  This is the spelling
  [Stacks, Tag 0G7S] is proved in, and the spelling
  `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` is stated for.
* `Stacks.Perfect.GysinFractionDeRham.cokernelLastDifToPushforward` reads it through
  `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso`, which inverts `R𝓗_Z` applied
  to the augmentation *inside* `D(𝒪_X|_Z)`, transports along
  `Stacks.Cohomology.SupportedComplexes.derivedPushforwardSupportedSectionsIso` — the counit of
  the adjunction of [Stacks, Tag 0A3B] — and takes degree-`c` cohomology **before** the direct
  image.  This is the spelling the Gysin map of [Stacks, Tag 0G83] is built in.

This file identifies the two.  It is pure transport: the two counits the two constructions invert
were shown to be the same natural transformation by the comparison
`derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit` of
`Stacks.Perfect.SupportCounitComparison`, and the two places at which the degree-`c` cohomology
is taken are related by the exactness of the direct image from a closed subset.

## Main definitions

* `Stacks.Perfect.CechSupportTransport.pushHomologyIso` and `supportCohomologyToPushforward`: the
  comparison `H ᶜ(i_* R𝓗_Z(K)) ≅ i_*(ℋ ᶜ_Z(K))` between taking the degree-`c` cohomology after and
  before the direct image from `Z`, i.e. [Stacks, Tag 0G74] part (2) for the exact functor `i_*`,
  at the canonical derived functors of this tree, and its value at a module placed in degree `0`.

## Main results

* `Stacks.Perfect.CechSupportTransport.cokernelLastDifToPushforward_eq`: **the two
  identifications agree** —

  `cokernelLastDifToPushforward f ℱ`
  `  = cokernelLastDifToSupport f ℱ ≫ supportCohomologyToPushforward f ℱ`.

  This is the declaration that transfers every statement proved about `cechToDerivedSupport` — in
  particular `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` and the
  determinant identity `Stacks.Perfect.SupportedFraction.supportedFractionClass_eq_det_smul` of
  [Stacks, Tag 0G7S] — into the spelling the Gysin map is built in.
* `Stacks.Perfect.CechSupportTransport.isIso_cokernelLastDifToPushforward`: consequently the
  identification the Gysin map is built from is invertible, which is
  `Stacks.Perfect.SupportedFraction.isIso_cokernelLastDifToSupport` transported.
* `Stacks.Perfect.CechSupportTransport.cechToSupport_eq`: the comparison of [Stacks, Tag 0G7L] is
  the inverse of the comparison of the two constructions of the Čech complex, then the inverse of
  the counit of [Stacks, Tag 0A3B] at the complex of
  `AlgebraicGeometry.ExtendedAlternatingCech.data`, then `i_* R𝓗_Z` applied to that complex's
  augmentation.  This is where the identification of the two counits is used.

## Implementation notes

**Carried hypotheses.**  `cokernelLastDifToPushforward_eq` carries exactly a nonempty family of
global equations `f : Fin (n + 1) → Γ(X, 𝒪_X)` and `[F.IsQuasicoherent]`; the nonemptiness is
carried by it and not by `homologyMap_cplxIsoInv_comp_pflIso_inv`, which it is built from and
which holds for every `c`.  The closed subset is
specialised to the common zero locus of the equations, which is a specialisation and not a
hypothesis (`Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet` supplies the
closedness and the containment of the zero locus in itself is `subset_rfl`).  Quasi-coherence is
what both sides need: it is where [Stacks, Tag 0G7M] enters on either side.

**Why the step away from the counit is proved for an abstract endofunctor.**
`eq_inv_comp_of_counit` quantifies over a category, an endofunctor and a transformation to the
identity rather than being stated at `i_* R𝓗_Z`.  The reason is mechanical and is the one recorded
in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechDerivedSquare`: `i_* R𝓗_Z`
is a right derived functor, so a unification step that has to decide an equation between two of
its values unfolds the whole localization.  At an abstract endofunctor the naturality square and
the two cancellations are decided at once, and the result is instantiated afterwards.  For the same
reason the invertibility of the counit at the Čech complex is an explicit argument of that lemma
and not an instance: the two spellings `X.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` of one category carry two different
`HasDerivedCategory` instance terms, so instance synthesis does not find the hypothesis, whereas
`exact` — which works up to default transparency — does.

**Why the comparison of the two complexes is re-spelled.**  The two constructions of the extended
alternating Čech complex are `Stacks.Perfect.ExtendedAlternatingCech.cplx` and
`AlgebraicGeometry.ExtendedAlternatingCech.complex`, and the comparison
`Stacks.Perfect.CechComparison.complexIso` is stated with the former spelled through
`Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech`.  That spelling is definitionally
but not reducibly `cplx`, so a rewrite with `HomologicalComplex.extendHomologyIso_hom_naturality`
produces an `extendHomologyIso` at the other spelling and the subsequent cancellation no longer
matches.  `cplxIsoInv` is the comparison with its source spelled by `cplx`, after which every
rewrite happens in one vocabulary.

**Why the factorization of `pushforwardLocalCohomologyIso` is given by `rfl`.**  `pflIso_inv_eq`
states the five factors of that isomorphism, inverted, in the exact bracketing `Iso.trans`
produces, so that it holds by `rfl`; the reassociation is done by `assembly_formal`.
Taking the factors apart with `simp` instead does not work: the goal carries terms that are
type-correct only up to default transparency, and a `simp` lemma whose left-hand side has a
functor metavariable — `Iso.trans_inv`, `CategoryTheory.Functor.map_comp` — fails to match there.
That is also why `homologyFunctor_map_cechToSupport` and
`pushHomologyIso_hom_naturality_single` exist: they are the two steps that would otherwise need
such a rewrite, carried out in a goal that has no such term.

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech (cplx)
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechSupportTransport

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The counit of Stacks 0G72 determines the comparison of Stacks 0G7L -/

section Formal

/-- **The comparison of [Stacks, Tag 0G7L], as an explicit composite of inverses.**  Let `G` be an
endofunctor of a category with a transformation `ε : G ⟶ 𝟭` — the shape of the counit
`i_* R𝓗_T(K) ⟶ K` of [Stacks, Tag 0G72] — and let `b : W' ≅ W` carry an augmentation
`aug' : W' ⟶ S` to an augmentation `aug : W ⟶ S`.  A map `cts : W ⟶ G.obj S` satisfying
`ε.app W ≫ cts = G.map aug`, with `ε.app W` invertible, is the inverse of `b`, then the inverse of
`ε.app W'`, then `G` applied to `aug'`.

This is the only place the counit enters, and it is stated at an abstract endofunctor because
`i_* R𝓗_T` is a right derived functor: a unification step deciding an equation between two of its
values unfolds the localization and does not terminate within the heartbeat budget. -/
public lemma eq_inv_comp_of_counit {C : Type*} [Category* C] (G : C ⥤ C)
    (ε : G ⟶ Functor.id C) {W W' S : C} (b : W' ≅ W) (aug : W ⟶ S) (aug' : W' ⟶ S)
    (haug : aug' = b.hom ≫ aug) (cts : W ⟶ G.obj S)
    (hcts : ε.app W ≫ cts = G.map aug) (hW : IsIso (ε.app W))
    (e : G.obj W' ≅ W') (he : e.hom = ε.app W') :
    cts = b.inv ≫ e.inv ≫ G.map aug' := by
  have := hW
  have hnat : G.map b.hom ≫ ε.app W = ε.app W' ≫ b.hom := ε.naturality b.hom
  have key : G.map b.hom ≫ G.map aug =
      G.map b.hom ≫ ε.app W ≫ b.inv ≫ e.inv ≫ G.map aug' := by
    rw [← Functor.map_comp, ← haug, ← Category.assoc (G.map b.hom) (ε.app W), hnat, ← he]
    simp
  refine (cancel_epi (ε.app W)).mp ?_
  rw [hcts]
  exact (cancel_epi (G.map b.hom)).mp key

/-- **The assembly of the transport, at an abstract category.**  Written with the five factors of
`Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso` on the left in the bracketing
`Iso.trans` produces and the three factors of
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport` on the right, the identity to be proved
is a reassociation of the three squares `h₁`, `h₂`, `h₃` and the factorization `h₄`.

It is stated at an abstract category because the goal it is instantiated at carries types that are
type-correct only up to default transparency: the abbreviation
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology` is reducible and applies a functor on
`SheafOfModules (structureSheafRing X.toRingedSpace)` to an object of `X.Modules`, and `simp` will
not reassociate a composite at such a node, whereas `exact` checks the instantiation at default
transparency and succeeds. -/
private lemma assembly_formal {C : Type*} [Category* C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : C}
    (m : O₀ ⟶ O₁) (p : O₁ ⟶ O₂) (q : O₂ ⟶ O₃) (r : O₃ ⟶ O₄) (u : O₄ ⟶ O₅) (v : O₅ ⟶ O₆)
    (eF : O₀ ⟶ O₇) (hm : O₇ ⟶ O₂) (dF : O₇ ⟶ O₈) (bb : O₈ ⟶ O₃) (gg : O₄ ⟶ O₉) (ss : O₉ ⟶ O₆)
    (ctsm : O₈ ⟶ O₉) (h₁ : m ≫ p = eF ≫ hm) (h₂ : hm ≫ q = dF ≫ bb)
    (h₃ : gg ≫ ss = u ≫ v) (h₄ : ctsm = bb ≫ r ≫ gg) :
    m ≫ (((p ≫ q) ≫ r) ≫ u) ≫ v = (eF ≫ dF ≫ ctsm) ≫ ss := by
  simp only [Category.assoc, h₄]
  rw [← h₃, ← Category.assoc m p, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc hm q, h₂]
  simp only [Category.assoc]

/-- A naturality square for two isomorphisms `a`, `b` gives the one for their inverses. -/
private lemma comp_inv_eq_inv_comp_of_naturality {C : Type*} [Category* C] {A B A' B' : C}
    (g : A ⟶ B) (a : A' ≅ A) (b : B' ≅ B) (h : A' ⟶ B') (w : h ≫ b.hom = a.hom ≫ g) :
    g ≫ b.inv = a.inv ≫ h := by
  rw [Iso.comp_inv_eq, Category.assoc, w, Iso.inv_hom_id_assoc]

end Formal

section GeneralCount

/- The declarations of this section are general in the NUMBER of equations, including zero,
and their degree is that number.  They are kept apart from the `Fin (n + 1)` section at the end
of the file, which genuinely needs a top degree: `cokernelLastDifToPushforward_eq` and its
neighbour quotient by the LAST differential of the extended alternating Čech complex, and an
empty family of equations gives a complex with only degree `0` and no such differential.
Nothing in this section touches that complex, so nothing in it needs `n + 1`.  Do not merge
the two apart: the `c = 0` case of [Stacks, Tag 0G86] needs these at `c = 0`, and every
consumer at `c = d + 1` still unifies.

The block between the two is general in `c` as well: every ingredient of
`cechToSupport_eq`, `pflIso_inv_eq` and `homologyMap_cplxIsoInv_comp_pflIso_inv` is general in
the number of equations and in the degree, so those hold at every `c`; it is only
`cokernelLastDifToSupport` and `cokernelLastDifIsoHomology`, which the final section consumes,
that need a top differential. -/

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-! ### The direct image commutes with the degree-`c` cohomology -/

/-- **[Stacks, Tag 0G74] part (2) for the exact direct image from a closed subset**, at the
canonical derived functors of this tree: the degree-`c` cohomology of `i_* R𝓗_Z(K)` is the direct
image of the degree-`c` local cohomology sheaf of `K`.  The direct image along the inclusion of a
closed subset is exact ([Stacks, Tag 08KS]), and an exact functor commutes with the cohomology
functors of the derived categories. -/
public def pushHomologyIso (K : DerivedCategory X.Modules) :
    (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).obj
        ((supportPush (isClosed_equationsClosedSet f)).obj K) ≅
      (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f) (c : ℤ) K) :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  letI := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  ((modulePushforward (closedSubsetInclusion X.toRingedSpace
      (equationsClosedSet f))).mapDerivedCategoryHomologyFunctorIso (c : ℤ)).app
    ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)).obj K)

/-- The comparison of [Stacks, Tag 0G74] part (2) is natural in the complex. -/
public lemma pushHomologyIso_hom_naturality {K L : DerivedCategory X.Modules} (g : K ⟶ L) :
    (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
          ((supportPush (isClosed_equationsClosedSet f)).map g) ≫ (pushHomologyIso f L).hom =
      (pushHomologyIso f K).hom ≫
        (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).map
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (structureSheafRing
                (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f))))
                (c : ℤ)).map
            ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
              (isClosed_equationsClosedSet f)).map g)) :=
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  ((modulePushforward (closedSubsetInclusion X.toRingedSpace
      (equationsClosedSet f))).mapDerivedCategoryHomologyFunctorIso
        (c : ℤ)).hom.naturality
    ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)).map g)

/-! ### The two counits are one -/

/-- **The counit of [Stacks, Tag 0G72] that `cechToDerivedSupport` inverts is the counit of the
adjunction of [Stacks, Tag 0A3B].**  This is the comparison
`derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit` of
`Stacks.Perfect.SupportCounitComparison` read at a scheme:
`Stacks.Perfect.SupportedFraction.supportPush` and `supportPushCounit` are reducible
abbreviations of the two arguments of its left-hand side. -/
public lemma supportPushCounit_eq :
    supportPushCounit (isClosed_equationsClosedSet f) =
      (derivedPushforwardAdjunction X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f)).counit :=
  SupportCounitComparison.derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit
    X.toRingedSpace (equationsClosedSet f) (isClosed_equationsClosedSet f)

variable (F : X.Modules)

/-- **The comparison between the two places at which the degree-`c` cohomology sheaf is taken.**
On the left `i_*ℋ ᶜ_Z(ℱ)` is read as the degree-`c` cohomology of `i_* R𝓗_Z(ℱ[0])` in `D(𝒪_X)`,
which is the spelling of [Stacks, Tag 0G7S]; on the right as the direct image of the degree-`c`
cohomology of `R𝓗_Z(ℱ[0])`, which is the spelling of the Gysin map of [Stacks, Tag 0G83].  The two
agree because the direct image from a closed subset is exact. -/
public def supportCohomologyToPushforward :
    supportCohomologySheaf (isClosed_equationsClosedSet f) F (c : ℤ) ≅
      AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F :=
  pushHomologyIso f ((DerivedCategory.singleFunctor X.Modules 0).obj F)

/-- The naturality of the comparison of [Stacks, Tag 0G74] part (2), at a map into the coefficient
module placed in degree `0`. -/
public lemma pushHomologyIso_hom_naturality_single {K : DerivedCategory X.Modules}
    (g : K ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj F) :
    (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
          ((supportPush (isClosed_equationsClosedSet f)).map g) ≫
        (supportCohomologyToPushforward f F).hom =
      (pushHomologyIso f K).hom ≫
        (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).map
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (structureSheafRing
                (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f))))
                (c : ℤ)).map
            ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
              (isClosed_equationsClosedSet f)).map g)) :=
  pushHomologyIso_hom_naturality f g

end GeneralCount

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-! ### The two constructions of the Čech complex -/

/-- The comparison [Stacks, Tag 0G7I] of the two constructions of the extended alternating Čech
complex, inverted, with its source spelled by
`Stacks.Perfect.ExtendedAlternatingCech.cplx`. -/
public def cplxIsoInv :
    cplx f F ⟶ (AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex :=
  (CechComparison.complexIso f F).inv

/-- `cplxIsoInv` is the inverse of the comparison of the two constructions.  It is that by
definition, and the lemma exists so that a caller holding the comparison in the
`Stacks.Perfect.CechComparison.complexIso` spelling — which is the spelling
`Stacks.Perfect.FractionClass.cokernelπ_comp_quotientClassMapData` produces — can rewrite into
the spelling the results below are stated at. -/
public lemma cplxIsoInv_eq : cplxIsoInv f F = (CechComparison.complexIso f F).inv := rfl

/-- The comparison of the two constructions, extended from `ℕ`- to `ℤ`-degrees and read in the
derived category. -/
public def cechBridge :
    DerivedCategory.Q.obj ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
        ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat) :=
  DerivedCategory.Q.mapIso (CechComparison.extendBridge f F)

/-- The inverse of the comparison of the two constructions is the localization of the extension
of `cplxIsoInv`. -/
public lemma cechBridge_inv :
    (cechBridge f F).inv =
      DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxIsoInv f F)
        ComplexShape.embeddingUpNat) := rfl

/-- The comparison of the two constructions carries one augmentation to the other; this is
`Stacks.Perfect.CechComparison.augmentation_eq`. -/
public lemma cechBridge_hom_augmentation :
    AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F =
      (cechBridge f F).hom ≫
        Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F :=
  CechComparison.augmentation_eq f F

/-- **[Stacks, Tag 0AEF] part (2) at the extended alternating Čech complex.**  The counit
`i_* R𝓗_Z(𝓕^•) ⟶ 𝓕^•` is invertible at the complex of
`AlgebraicGeometry.ExtendedAlternatingCech.data`, whose cohomology sheaves are supported on the
common zero locus of the equations by [Stacks, Tag 0G7K]. -/
public def dataCounitIso :
    (supportPush (isClosed_equationsClosedSet f)).obj
        (DerivedCategory.Q.obj
          ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
            ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj
        ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
          ComplexShape.embeddingUpNat) :=
  derivedPushforwardSupportedSectionsIso X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
    (DerivedCategory.Q.obj
      ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
        ComplexShape.embeddingUpNat))
    (CechLocalCohomology.cohomologySupportedOn_extendedAlternatingCech f F)

/-- The isomorphism of [Stacks, Tag 0AEF] part (2) at the Čech complex is the counit of
[Stacks, Tag 0G72] there. -/
public lemma dataCounitIso_hom :
    (dataCounitIso f F).hom =
      (supportPushCounit (isClosed_equationsClosedSet f)).app
        (DerivedCategory.Q.obj
          ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
            ComplexShape.embeddingUpNat)) := by
  rw [supportPushCounit_eq f]
  rfl

/-! ### The comparison of Stacks 0G7L in the counit of Stacks 0A3B -/

variable [F.IsQuasicoherent]

omit [F.IsQuasicoherent] in
/-- **The comparison of [Stacks, Tag 0G7L] in terms of the counit of [Stacks, Tag 0A3B].**  The
canonical map `𝓕^• ⟶ i_* R𝓗_Z(ℱ)` of [Stacks, Tag 0G7L] is the inverse of the comparison of the
two constructions of the Čech complex, then the inverse of the counit at the complex of
`AlgebraicGeometry.ExtendedAlternatingCech.data`, then `i_* R𝓗_Z` applied to that complex's
augmentation.

This is `eq_inv_comp_of_counit` instantiated at `i_* R𝓗_Z`, and it is the one step that uses the
identification `supportPushCounit_eq` of the two counits. -/
public theorem cechToSupport_eq :
    cechToSupport f F (isClosed_equationsClosedSet f) subset_rfl =
      (cechBridge f F).inv ≫ (dataCounitIso f F).inv ≫
        (supportPush (isClosed_equationsClosedSet f)).map
          (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F) :=
  eq_inv_comp_of_counit (supportPush (isClosed_equationsClosedSet f))
    (supportPushCounit (isClosed_equationsClosedSet f)) (cechBridge f F)
    (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F)
    (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F)
    (cechBridge_hom_augmentation f F)
    (cechToSupport f F (isClosed_equationsClosedSet f) subset_rfl)
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport f F
      (isClosed_equationsClosedSet f) subset_rfl)
    (isIso_derivedSupportedSectionsToId_cech f F (isClosed_equationsClosedSet f) subset_rfl)
    (dataCounitIso f F) (dataCounitIso_hom f F)

omit [F.IsQuasicoherent] in
/-- `cechToSupport_eq` after the degree-`c` cohomology functor, with the three factors
separated. -/
public lemma homologyFunctor_map_cechToSupport :
    (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
        (cechToSupport f F (isClosed_equationsClosedSet f) subset_rfl) =
      (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map (cechBridge f F).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
            (dataCounitIso f F).inv ≫
          (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
            ((supportPush (isClosed_equationsClosedSet f)).map
              (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F)) :=
  by rw [cechToSupport_eq]; erw [Functor.map_comp, Functor.map_comp]; rfl

/-! ### The two identifications agree -/

/-- The five factors of `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso`, read in
the inverse direction, in the bracketing `Iso.trans` produces. -/
public lemma pflIso_inv_eq :
    (CechLocalCohomology.pushforwardLocalCohomologyIso f F c).inv =
      ((((HomologicalComplex.extendHomologyIso
                  (AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex
                    ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv ≫
                (derivedQHomologyIso
                  ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
                    ComplexShape.embeddingUpNat) (c : ℤ)).inv) ≫
              (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
                (dataCounitIso f F).inv) ≫
            (pushHomologyIso f (DerivedCategory.Q.obj
              ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
                ComplexShape.embeddingUpNat))).hom) ≫
          (modulePushforward (closedSubsetInclusion X.toRingedSpace
              (equationsClosedSet f))).map
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
                (structureSheafRing
                  (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f))))
                  (c : ℤ)).map
              ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
                (isClosed_equationsClosedSet f)).map
                  (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F))) := rfl

/-- **The degree-`c` cohomology of the comparison of [Stacks, Tag 0G7L], followed by the exchange
of the cohomology with the direct image, is the identification of
`Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso`.** -/
public lemma homologyMap_cplxIsoInv_comp_pflIso_inv :
    HomologicalComplex.homologyMap (cplxIsoInv f F) c ≫
        (CechLocalCohomology.pushforwardLocalCohomologyIso f F c).inv =
      cechHomologyToSupport f F (isClosed_equationsClosedSet f) subset_rfl c ≫
        (supportCohomologyToPushforward f F).hom := by
  have hehi : HomologicalComplex.homologyMap (cplxIsoInv f F) c ≫
        (HomologicalComplex.extendHomologyIso
          (AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex
            ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv =
      (HomologicalComplex.extendHomologyIso (cplx f F) ComplexShape.embeddingUpNat
          (embeddingUpNat_f c)).inv ≫
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxIsoInv f F)
          ComplexShape.embeddingUpNat) (c : ℤ) := by
    exact comp_inv_eq_inv_comp_of_naturality _ _ _ _
      (HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)
  have hdq : HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxIsoInv f F)
          ComplexShape.embeddingUpNat) (c : ℤ) ≫
        (derivedQHomologyIso
            ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
              ComplexShape.embeddingUpNat) (c : ℤ)).inv =
      (derivedQHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
          (c : ℤ)).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxIsoInv f F)
            ComplexShape.embeddingUpNat)) := by
    exact comp_inv_eq_inv_comp_of_naturality _ _ _ _ (derivedQHomologyIso_hom_naturality _ _)
  exact assembly_formal (HomologicalComplex.homologyMap (cplxIsoInv f F) c)
    (HomologicalComplex.extendHomologyIso
      (AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex
        ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv
    (derivedQHomologyIso
      ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
        ComplexShape.embeddingUpNat) (c : ℤ)).inv
    ((DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map (dataCounitIso f F).inv)
    (pushHomologyIso f (DerivedCategory.Q.obj
      ((AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.extend
        ComplexShape.embeddingUpNat))).hom
    ((modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (structureSheafRing
            (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f))))
            (c : ℤ)).map
        ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f)).map
            (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F))))
    (HomologicalComplex.extendHomologyIso (cplx f F) ComplexShape.embeddingUpNat
      (embeddingUpNat_f c)).inv
    (HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxIsoInv f F)
      ComplexShape.embeddingUpNat) (c : ℤ))
    (derivedQHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
      (c : ℤ)).inv
    ((DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map (cechBridge f F).inv)
    ((DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
      ((supportPush (isClosed_equationsClosedSet f)).map
        (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F)))
    (supportCohomologyToPushforward f F).hom
    ((DerivedCategory.homologyFunctor X.Modules (c : ℤ)).map
      (cechToSupport f F (isClosed_equationsClosedSet f) subset_rfl))
    hehi hdq
    (pushHomologyIso_hom_naturality_single f F
      (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F))
    (homologyFunctor_map_cechToSupport f F)

section TopDegree

variable {X : Scheme.{u}} {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (F : X.Modules)
  [F.IsQuasicoherent]

/-- **The two identifications of the Čech cokernel with `i_*ℋ ᶜ_Z(ℱ)` agree.**  The identification
`Stacks.Perfect.GysinFractionDeRham.cokernelLastDifToPushforward` that the Gysin map of
[Stacks, Tag 0G83] is built from is the identification
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` of [Stacks, Tag 0G7S], followed by the
comparison `supportCohomologyToPushforward` of the two places at which the degree-`c` cohomology
sheaf is taken.

This is pure transport.  The two constructions invert the same natural transformation — the counit
`i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0G72], which is the counit of the adjunction of
[Stacks, Tag 0A3B] by `supportPushCounit_eq` — and differ only in the order in which the degree-`c`
cohomology and the direct image from `Z` are taken, which the exactness of that direct image
interchanges. -/
public theorem cokernelLastDifToPushforward_eq :
    GysinFractionDeRham.cokernelLastDifToPushforward f F =
      cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl ≫
        (supportCohomologyToPushforward f F).hom :=
  Eq.trans
      (congrArg (fun ψ => (cokernelLastDifIsoHomology f F).hom ≫ ψ)
        (homologyMap_cplxIsoInv_comp_pflIso_inv f F))
    (Category.assoc _ _ _).symm

/-- **The identification the Gysin map is built from is invertible.**  This is
`Stacks.Perfect.SupportedFraction.isIso_cokernelLastDifToSupport`, which is [Stacks, Tag 0G7M],
transported across `cokernelLastDifToPushforward_eq`. -/
public theorem isIso_cokernelLastDifToPushforward :
    IsIso (GysinFractionDeRham.cokernelLastDifToPushforward f F) := by
  have h := isIso_cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl
    subset_rfl
  rw [cokernelLastDifToPushforward_eq f F]
  exact IsIso.comp_isIso' h (Iso.isIso_hom _)

end TopDegree

end Stacks.Perfect.CechSupportTransport

end

