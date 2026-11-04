module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stein factorization of a proper morphism of algebraic spaces: the general case

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S`.  Stacks 0A1C is the
general form of Stein factorization: nothing is assumed about `Y`, and the factorization
`X ⟶ Y' ⟶ Y` of `f` through the normalization `Y'` of `Y` in `X` (Stacks 0822) is asserted to
have the five properties

1. `f' : X ⟶ Y'` is proper and its geometric fibres are connected;
2. `π : Y' ⟶ Y` is **integral**;
3. the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` of Stacks 03G8 is invertible;
4. `Y' = \underline{Spec}_Y(f_* 𝒪_X)`;
5. `Y'` is the normalization of `Y` in `X`.

Clause (2) is where the general case differs from the locally Noetherian case Stacks 0A1B,
which strengthens it to finiteness of `π`.  Stacks 0A1C asks only integrality, and that needs no
finiteness input at all — which is why the general case gets further here than Stacks 0A1B does
in `StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization`.

The factorization is the one built by
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs` for a quasi-compact and
quasi-separated `f`:  `AlgebraicGeometry.Space.normalizationInQcqs` is `Y'`,
`AlgebraicGeometry.Space.normalizationInQcqsHom` is `π` and
`AlgebraicGeometry.Space.toNormalizationInQcqs` is `f'`.  A proper morphism is quasi-compact and
quasi-separated, so the construction applies;  `hfqc` and `hfqs` appear as arguments only because
`Y'` is indexed by them, and `AlgebraicGeometry.Space.isQuasiCompact_isQuasiSeparated_of_isProper`
produces them from properness.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_isQuasiSeparated_of_isProper`: a proper morphism of
  algebraic spaces is quasi-compact and quasi-separated.
* `AlgebraicGeometry.Space.isProper_toNormalizationInQcqs`: the properness assertion of
  clause (1) of Stacks 0A1C.
* `AlgebraicGeometry.Space.isSurjective_toNormalizationInQcqs`: `f'` is surjective, which is the
  remaining assertion of clause (1) of Stacks 0A19.
* `AlgebraicGeometry.Space.steinFactorization_general`: clauses (1) properness, (2), (4) and (5)
  of Stacks 0A1C together, for a proper `f` over an arbitrary base.
* `AlgebraicGeometry.Space.steinFactorization_general_of_connectedFibres`: all five clauses, with
  the two statements this library does not reach stated as named inputs.

## Implementation notes

**Why this module does not use `AlgebraicGeometry.Space.normalizationIn`.**
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization` states Stacks 0A19 and Stacks 0A1B for
`AlgebraicGeometry.Space.normalizationIn`, which is indexed by an
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`.  That structure is refuted —
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart` — so
every statement taking an inhabitant of it has no case, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRepresentable` record.  The
`AlgebraicGeometry.Space.normalizationInQcqs` construction of the same Stacks 0822
factorization takes no such parameter, and Stacks 0823 is proved for it
(`AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs`), so Stacks 0A1C is
stated here against that one.

**Where each proved clause comes from.**  A proper `f` is universally closed and separated, so it
is quasi-compact (Stacks 04XW) and quasi-separated (Stacks 03KK);  the structure morphism `π` is
affine by the typing of `AlgebraicGeometry.Space.normalizationInQcqsAffineOver`, hence separated
(Stacks 03KM) and so quasi-separated (Stacks 03KK).  With `f = f' ≫ π`:

* `f'` is proper by Stacks 04NX part (2), because `f` is and `π` is separated — the properness
  assertion of clause (1);
* `f'` is universally closed by Stacks 04NX part (1) and quasi-compact by Stacks 03KS, which is
  what surjectivity needs;
* `f'` is surjective by `AlgebraicGeometry.Space.isSurjective_of_isRelativeNormalization`, the
  argument from the characterization of Stacks 0823 that
  `StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization` proves for any factorization with
  that property;
* `π` is integral by `AlgebraicGeometry.Space.isIntegralHom_normalizationInQcqsHom`, clause (1)
  of Stacks 0823 — this is clause (2) in the form the general case asserts it;
* clause (4) is, in the namespace `AlgebraicGeometry.Space` and written without the prefix so
  that it fits, `isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed`,
  the second sentence of Stacks 0A0Q, which rests on the first sentence of that tag,
  `AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_of_universallyClosed`;
* clause (5) is `AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs`.

Both sentences of Stacks 0A0Q are therefore theorems rather than inputs here, whereas
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization` and
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral` carry the first sentence
of Stacks 0A0Q as the hypothesis `hint`.

**The two statements that are not reached.**  Clause (3), invertibility of
`𝒪_{Y'} ⟶ f'_* 𝒪_X`, would need the identification of the sections of `f_* 𝒪_X` over an affine
étale chart `V` of `Y` with the global regular functions on `X ×_Y V` as an *isomorphism*.  The
comparison homomorphism exists —
`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`, proved injective — but its
surjectivity, which is what clause (3) turns on, is not proved.  The connectedness half of
clause (1) is the theorem on formal functions for algebraic spaces, Stacks 08B1;  what is proved
towards that tag, in
`StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsGeometricStalk`, carries the conclusion of
Stacks 08AZ as an input, and the source's route for the general case is anyway a limit argument
over proper finitely presented morphisms with Noetherian affine base, for which the limit
presentation of Stacks 09ZM is absent for algebraic spaces.  Stacks 0A1A,
`AlgebraicGeometry.Space.connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood`, is
the right reduction of the connectedness statement to scheme-valued étale neighbourhoods, but
nothing is proved on the far side of it.  Both missing statements appear in
`AlgebraicGeometry.Space.steinFactorization_general_of_connectedFibres` as named inputs, which
therefore records no tag.

## References

* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### Properness gives the hypotheses of the Stacks 0822 construction -/

/-- **A proper morphism of algebraic spaces is quasi-compact and quasi-separated.**  It is
universally closed, hence quasi-compact by Stacks 04XW, and separated, hence quasi-separated by
Stacks 03KK.  These are the two hypotheses under which
`AlgebraicGeometry.Space.normalizationInQcqs` builds the factorization of Stacks 0822. -/
theorem isQuasiCompact_isQuasiSeparated_of_isProper (hf : IsProper B S hS f.hom) :
    IsQuasiCompact B S hS f.hom ∧ IsQuasiSeparated B S hS f.hom :=
  ⟨isQuasiCompact_of_universallyClosed B S hS X.2 Y.2 f.hom hf.universallyClosed,
    isQuasiSeparated_of_isSeparated B S hS hf.isSeparated⟩

variable (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-! ### The structure morphism of the normalization -/

/-- The structure morphism `π : Y' ⟶ Y` of the normalization of `Y` in `X` is separated: it is
affine (`AlgebraicGeometry.Space.isAffineHom_normalizationInQcqsHom`), and an affine morphism of
algebraic spaces is separated (**Stacks 03KM**). -/
theorem isSeparated_normalizationInQcqsHom :
    IsSeparated B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  isSeparated_of_isAffineHom B S hS _ (normalizationInQcqs B S hS f hfqc hfqs).2 Y.2
    (isAffineHom_normalizationInQcqsHom B S hS f hfqc hfqs)

/-- The structure morphism `π : Y' ⟶ Y` of the normalization of `Y` in `X` is quasi-separated,
being separated (**Stacks 03KK**). -/
theorem isQuasiSeparated_normalizationInQcqsHom :
    IsQuasiSeparated B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_normalizationInQcqsHom B S hS f hfqc hfqs)

/-- The factorization `f = f' ≫ π` of Stacks 0822, read on the underlying morphisms of
presheaves. -/
theorem toNormalizationInQcqs_comp_hom :
    (toNormalizationInQcqs f hfqc hfqs).hom ≫
        (normalizationInQcqsHom B S hS f hfqc hfqs).hom = f.hom :=
  congrArg (fun k => k.hom) (toNormalizationInQcqs_comp f hfqc hfqs)

/-! ### Clause (1): `f'` is proper, universally closed, quasi-compact and surjective -/

/-- **Clause (1) of Stacks 0A1C: `f'` is proper.**  By Stacks 04NX part (2), since the composite
`f = f' ≫ π` is proper and `π` is separated. -/
@[stacks 0A1C "clause (1): the morphism f' : X ⟶ Y' to the normalization of Y in X is proper, \
for a proper f and an arbitrary base Y"]
theorem isProper_toNormalizationInQcqs (hf : IsProper B S hS f.hom) :
    IsProper B S hS (toNormalizationInQcqs f hfqc hfqs).hom := by
  refine isProper_of_comp_of_isSeparated B S hS X.2
    (normalizationInQcqs B S hS f hfqc hfqs).2 Y.2 _ _ ?_
    (isSeparated_normalizationInQcqsHom B S hS f hfqc hfqs)
  rwa [toNormalizationInQcqs_comp_hom B S hS f hfqc hfqs]

/-- `f'` is universally closed, by Stacks 04NX part (1), since `f = f' ≫ π` is universally
closed and `π` is separated. -/
theorem universallyClosed_toNormalizationInQcqs (hfuc : UniversallyClosed B S hS f.hom) :
    UniversallyClosed B S hS (toNormalizationInQcqs f hfqc hfqs).hom := by
  refine universallyClosed_of_comp_of_isSeparated B S hS X.2
    (normalizationInQcqs B S hS f hfqc hfqs).2 Y.2 _ _ ?_
    (isSeparated_normalizationInQcqsHom B S hS f hfqc hfqs)
  rwa [toNormalizationInQcqs_comp_hom B S hS f hfqc hfqs]

/-- `f'` is quasi-compact, by Stacks 03KS, since `f = f' ≫ π` is quasi-compact and `π` is
quasi-separated. -/
theorem isQuasiCompact_toNormalizationInQcqs :
    IsQuasiCompact B S hS (toNormalizationInQcqs f hfqc hfqs).hom := by
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ X.2 Y.2 ?_
    (isQuasiSeparated_normalizationInQcqsHom B S hS f hfqc hfqs)
  rwa [toNormalizationInQcqs_comp_hom B S hS f hfqc hfqs]

/-- **`f'` is surjective**, which is the remaining assertion of clause (1) of Stacks 0A19.  The
factorization `f = f' ≫ π` has the characterizing property of Stacks 0823
(`AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs`), and `f'` is
quasi-compact and universally closed, so
`AlgebraicGeometry.Space.isSurjective_of_isRelativeNormalization` applies. -/
@[stacks 0A19 "clause (1): the morphism f' : X ⟶ Y' to the normalization of Y in X is \
surjective, for a universally closed f"]
theorem isSurjective_toNormalizationInQcqs (hfuc : UniversallyClosed B S hS f.hom) :
    IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom :=
  isSurjective_of_isRelativeNormalization B S hS
    (isRelativeNormalization_normalizationInQcqs f hfqc hfqs) X.2
    (normalizationInQcqs B S hS f hfqc hfqs).2
    (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
    (universallyClosed_toNormalizationInQcqs B S hS f hfqc hfqs hfuc)

/-! ### The clauses of Stacks 0A1C that hold at properness of `f` alone -/

/-- **Stacks 0A1C, clauses (1) properness, (2), (4) and (5).**  Let `f : X ⟶ Y` be a proper
morphism of algebraic spaces over `S`, let `Y'` be the normalization of `Y` in `X` and let
`f = f' ≫ π` be the factorization of Stacks 0822.  Then

* `f'` is proper, and surjective — the properness assertion of clause (1), together with the
  surjectivity that clause (1) of Stacks 0A19 states separately;
* `π : Y' ⟶ Y` is integral, clause (2) in the form the general case asserts it;
* `Y' = \underline{Spec}_Y(f_* 𝒪_X)`, clause (4), in the form of Stacks 0A0Q: the map
  `π_* 𝒪_{Y'} ⟶ f_* 𝒪_X` of `𝒪_Y`-algebras induced by `f'` is invertible;
* `Y'` is the normalization of `Y` in `X`, clause (5), in the sense of
  `AlgebraicGeometry.Space.IsRelativeNormalization`.

The conclusion also records the factorization equation itself.

Nothing is assumed about `Y`;  no finiteness enters, which is the point of the general case
against Stacks 0A1B.  The two statements of the tag that do not appear here are clause (3) and
the connectedness of the geometric fibres of `f'` in clause (1);  the module documentation says
what each would need, and
`AlgebraicGeometry.Space.steinFactorization_general_of_connectedFibres` adds them as named
inputs. -/
@[stacks 0A1C "clause (1) properness together with the surjectivity of f', clause (2) \
integrality of pi, clause (4) and clause (5), for a proper morphism of algebraic spaces over an \
arbitrary base.  Clause (3) and the connectedness of the geometric fibres of f' in clause (1) \
are not asserted", ega "III 7.8.10" "partial"]
theorem steinFactorization_general (hf : IsProper B S hS f.hom) :
    toNormalizationInQcqs f hfqc hfqs ≫ normalizationInQcqsHom B S hS f hfqc hfqs = f ∧
      IsProper B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
      IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
      IsIntegralHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
      IsIso (pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs)) ∧
      IsRelativeNormalization B S hS f.hom
        (normalizationInQcqsHom B S hS f hfqc hfqs).hom
        (toNormalizationInQcqs f hfqc hfqs).hom :=
  ⟨toNormalizationInQcqs_comp f hfqc hfqs,
    isProper_toNormalizationInQcqs B S hS f hfqc hfqs hf,
    isSurjective_toNormalizationInQcqs B S hS f hfqc hfqs hf.universallyClosed,
    isIntegralHom_normalizationInQcqsHom f hfqc hfqs,
    isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed f hfqc hfqs
      hf.universallyClosed,
    isRelativeNormalization_normalizationInQcqs f hfqc hfqs⟩

attribute [local instance] pointTopology

/-- **Stacks 0A1C, all five clauses**, for a proper morphism `f : X ⟶ Y` of algebraic spaces over
`S` and an arbitrary base `Y`, the factorization being that of Stacks 0822:

1. `f'` is proper, and its geometric fibres are connected;
2. `π : Y' ⟶ Y` is integral;
3. the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` of Stacks 03G8 is invertible;
4. `Y' = \underline{Spec}_Y(f_* 𝒪_X)`;
5. `Y'` is the normalization of `Y` in `X`.

The conclusion also records the factorization equation, and surjectivity of `f'`.

Clauses (2), (4) and (5), the properness of `f'` and its surjectivity are proved;  they are
`AlgebraicGeometry.Space.steinFactorization_general`, which is where the tag is recorded.  The
two remaining statements are the named inputs `hconn` and `hstr`;  the module documentation says
what the source proves each from. -/
-- No `@[stacks 0A1C]` attribute here: `hconn` and `hstr` are inputs, so this statement does not
-- assert the whole of the tag.  What is proved outright is
-- `AlgebraicGeometry.Space.steinFactorization_general`.
theorem steinFactorization_general_of_connectedFibres (hf : IsProper B S hS f.hom)
    (hconn : ∀ y : GeometricPoint B S hS (normalizationInQcqs B S hS f hfqc hfqs).1,
      ConnectedPullback B S hS (toNormalizationInQcqs f hfqc hfqs).hom
        (yonedaEquiv.symm y.val.value))
    (hstr : IsIso (smallEtaleRingedToposHom B S hS
      (toNormalizationInQcqs f hfqc hfqs)).fSharp) :
    toNormalizationInQcqs f hfqc hfqs ≫ normalizationInQcqsHom B S hS f hfqc hfqs = f ∧
      IsProper B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
      IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
      (∀ y : GeometricPoint B S hS (normalizationInQcqs B S hS f hfqc hfqs).1,
        ConnectedPullback B S hS (toNormalizationInQcqs f hfqc hfqs).hom
          (yonedaEquiv.symm y.val.value)) ∧
      IsIntegralHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
      IsIso (smallEtaleRingedToposHom B S hS (toNormalizationInQcqs f hfqc hfqs)).fSharp ∧
      IsIso (pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs)) ∧
      IsRelativeNormalization B S hS f.hom
        (normalizationInQcqsHom B S hS f hfqc hfqs).hom
        (toNormalizationInQcqs f hfqc hfqs).hom :=
  have h := steinFactorization_general B S hS f hfqc hfqs hf
  ⟨h.1, h.2.1, h.2.2.1, hconn, h.2.2.2.1, hstr, h.2.2.2.2.1, h.2.2.2.2.2⟩

end AlgebraicGeometry.Space

end
