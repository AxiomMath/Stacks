module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalPair

/-!
# Canonicality of a twist pair depends only on its strict isomorphism class

Tag 01O4 normalises its representing bijections by naming the pair that the identity morphism of
relative `Proj` classifies, and `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsCanonicalTwistPair`
is the condition that a pair be that one: its invertible sheaf is the degree-one twist of
Tag 01NR and its graded map is the homogeneous-section map of the twist datum.

The pair the bijection attaches to the identity is `...ProjRepresentsF1.universalPair`, and it is
a representative chosen by `Quotient.out` from a strict isomorphism class: the normalisation
clause `...ProjRepresentsF1.pairClassifyingEquiv_symm_id` determines the class and not the
representative. This file proves that canonicality does not see that choice — it is a property of
the class — and draws the consequence for Tag 01O4's representation.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_of_strictlyEquivalent` and
  `...ProjRepresentsF1.isCanonicalTwistPair_congr`: **canonicality transports along a strict
  isomorphism of pairs**, in both directions.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_of_quot_eq`: hence it
  transports along an equality of strict isomorphism classes.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_universalPair_iff`:
  **the universal pair is canonical exactly when some canonical pair is classified by the
  identity morphism of relative `Proj`.** The right-hand side mentions no chosen representative.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_universalPair_iff_psi_eq`: the
  same with canonicality spelled out as the formula
  `...ProjRepresentsF1.isCanonicalTwistPair_iff_psi_eq` forces on the graded map.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1RepresentationOfCanonicalClassifiesId`:
  **a canonical pair classified by the identity morphism yields Tag 01O4's representation** over
  the twist datum, at the constructed pullback comparison of tensor algebras.

## Implementation notes

**The transport is the `symm` step of `strictlyEquivalent_equivalence`, composed with the
canonicality data.** A strict isomorphism of `P` with `Q` supplies `β₀ : P.L ≅ Q.L` and an
isomorphism `γ₀` of the two tensor algebras carrying `P.ψ` to `Q.ψ`; canonicality of `P` supplies
`β : P.L ≅ 𝒪(1)` and a homomorphism `γ` to the algebra of twists. The witnesses for `Q` are
`β₀.symm ≪≫ β` and `γ₀.inv ≫ γ`, and each of the four clauses is the corresponding clause for `P`
with one cancellation of `γ₀` or `β₀` in front of it.

**The proof is term-mode and the `IsIso` clause is supplied by hand.** As recorded in the
implementation notes of `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic`, `rw` does not
find these patterns, and instance search does not find `IsIso` at these spellings; the degreewise
invertibility of `γ₀.inv ≫ γ` is therefore the `hom` of an explicitly built isomorphism, through
`CategoryTheory.asIso` with explicit arguments. The two `sectionsMap` clauses go through
`congrArg`, because `SheafOfModules.sectionsMap_comp` and `sectionsMap_id` hold by `rfl`.

**What the reduction buys.** `universalPair`'s invertible sheaf is a `Quotient.out`, so no
identification of it with the degree-one twist can be read off a definition. After the transport
the identification need only be produced for *some* pair in the class, and a pair is pinned down
by its classifying morphism; `isCanonicalTwistPair_universalPair_iff` is that restatement, and
its right-hand side is Tag 01O4's normalisation clause in the tag's own words.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)

## Not done here

**No canonical twist pair is constructed, and no project tag is attached.** The right-hand side
of `isCanonicalTwistPair_universalPair_iff` is not verified: nothing in the library builds a pair
on relative `Proj` whose invertible sheaf is the degree-one twist, and two ingredients of such a
pair are absent. Surjectivity of the degree-one component of the twist datum's
homogeneous-section map — `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.degreeOneSurjective`
for that pair, equivalently `...RelativeProjQcohSheaf.Quadruple.epi_app_one` — is nowhere stated;
and the classifying morphism of such a pair is computed only chart by chart, through
`...RelativeProjQcohSheaf.Fd.eq_homDegreeOpen`, against the absolute universal family
`...ProjTripleDegreeFunctor.universalDegreeTriple`, a comparison that is also absent. See the
accompanying report.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-! ### Canonicality is a property of the strict isomorphism class -/

/-- **Canonicality of a twist pair transports along a strict isomorphism.** If `P` is the
canonical twist pair of `D` and `Q` is strictly isomorphic to `P`, then `Q` is too: the
identification of the invertible sheaf with the degree-one twist and the comparison with the
algebra of twists are composed with the inverse of the strict isomorphism. -/
public theorem isCanonicalTwistPair_of_strictlyEquivalent
    {P Q : F1Pair A TA (relativeProj A).toBase} (h : StrictlyEquivalent A TA P Q)
    (hP : IsCanonicalTwistPair A TA D P) : IsCanonicalTwistPair A TA D Q := by
  obtain ⟨β₀, γ₀, hgen₀, hone₀, hψ₀⟩ := h
  obtain ⟨β, γ, hiso, hgenc, honec, hψc⟩ := hP
  refine ⟨β₀.symm ≪≫ β, γ₀.inv ≫ γ, fun n => ?_, ?_, ?_, fun n => ?_⟩
  · exact ((gradedAlgebraIsoApp γ₀ (n : ℤ)).symm ≪≫
      @asIso _ _ _ _ (γ.app (n : ℤ)) (hiso n)).isIso_hom
  · have key : (TA (relativeProj A).scheme Q.L).tensorGenerator ≫ γ₀.inv.app 1 =
        β₀.inv ≫ (TA (relativeProj A).scheme P.L).tensorGenerator :=
      (Iso.comp_inv_eq (gradedAlgebraIsoApp γ₀ 1)).mpr
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (congrArg (β₀.inv ≫ ·) hgen₀) (β₀.inv_hom_id_assoc _))).symm
    exact Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (· ≫ γ.app 1) key)
        (Eq.trans (Category.assoc _ _ _) (congrArg (β₀.inv ≫ ·) hgenc)))
  · have hcancel : SheafOfModules.sectionsMap (γ₀.inv.app 0)
        (SheafOfModules.sectionsMap (γ₀.hom.app 0)
          (TA (relativeProj A).scheme P.L).tensor.one) =
        (TA (relativeProj A).scheme P.L).tensor.one :=
      congrArg (fun k : (TA (relativeProj A).scheme P.L).tensor.piece 0 ⟶
            (TA (relativeProj A).scheme P.L).tensor.piece 0 =>
          SheafOfModules.sectionsMap k (TA (relativeProj A).scheme P.L).tensor.one)
        (gradedAlgebraIsoApp γ₀ 0).hom_inv_id
    exact Eq.trans (congrArg (SheafOfModules.sectionsMap (γ.app 0))
      (Eq.trans (congrArg (SheafOfModules.sectionsMap (γ₀.inv.app 0)) hone₀).symm hcancel)) honec
  · have key : Q.ψ (n : ℤ) ≫
        (Scheme.Modules.pushforward (relativeProj A).toBase).map (γ₀.inv.app (n : ℤ)) =
        P.ψ (n : ℤ) :=
      (Iso.comp_inv_eq ((Scheme.Modules.pushforward (relativeProj A).toBase).mapIso
        (gradedAlgebraIsoApp γ₀ (n : ℤ)))).mpr (hψ₀ (n : ℤ)).symm
    exact Eq.trans
      (congrArg (Q.ψ (n : ℤ) ≫ ·)
        ((Scheme.Modules.pushforward (relativeProj A).toBase).map_comp
          (γ₀.inv.app (n : ℤ)) (γ.app (n : ℤ))))
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg (· ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
            (γ.app (n : ℤ))) key)
          (hψc n)))

/-- **Canonicality of a twist pair is invariant under strict isomorphism.** -/
public theorem isCanonicalTwistPair_congr
    {P Q : F1Pair A TA (relativeProj A).toBase} (h : StrictlyEquivalent A TA P Q) :
    IsCanonicalTwistPair A TA D P ↔ IsCanonicalTwistPair A TA D Q :=
  ⟨isCanonicalTwistPair_of_strictlyEquivalent A TA D h,
    isCanonicalTwistPair_of_strictlyEquivalent A TA D
      ((strictlyEquivalent_equivalence A TA).symm h)⟩

/-- **Canonicality of a twist pair depends only on its strict isomorphism class.** Two pairs with
the same class in Tag 01O4's functor are strictly isomorphic, by
`quot_mk_eq_iff_strictlyEquivalent`, so canonicality of one is canonicality of the other. -/
public theorem isCanonicalTwistPair_of_quot_eq
    {P Q : F1Pair A TA (relativeProj A).toBase}
    (h : (Quot.mk _ P : F1 A TA (relativeProj A).toBase) = Quot.mk _ Q)
    (hP : IsCanonicalTwistPair A TA D P) : IsCanonicalTwistPair A TA D Q :=
  isCanonicalTwistPair_of_strictlyEquivalent A TA D
    ((quot_mk_eq_iff_strictlyEquivalent A TA P Q).1 h) hP

/-! ### The universal pair is canonical exactly when some canonical pair classifies the
identity -/

/-- **The universal pair of Tag 01O4 is canonical as soon as some canonical pair is classified by
the identity morphism of relative `Proj`.** The classifying map is injective, so a pair the
identity classifies has the class of the universal pair, and canonicality is a property of that
class. -/
public theorem isCanonicalTwistPair_universalPair_of_classifies
    (hgen : IsGeneratedInDegreeOne A) (P : F1Pair A TA (relativeProj A).toBase)
    (hcan : IsCanonicalTwistPair A TA D P)
    (hid : pairClassifyingHom A TA (relativeProj A).toBase (relativeProj A) hgen
        (Quot.mk _ P) = ⟨𝟙 (relativeProj A).scheme, Category.id_comp _⟩) :
    IsCanonicalTwistPair A TA D (universalPair A TA (relativeProj A) hgen) :=
  isCanonicalTwistPair_of_quot_eq A TA D
    ((pairClassifyingHom_bijective A TA (relativeProj A).toBase (relativeProj A) hgen).1
      (hid.trans (pairClassifyingHom_universalPair A TA (relativeProj A) hgen).symm))
    hcan

/-- **Tag 01O4's canonicality clause mentions no chosen representative.** The universal pair — a
`Quotient.out`, hence a choice — is the canonical twist pair of `D` exactly when *some* pair on
relative `Proj` is both canonical for `D` and classified by the identity morphism.

The forward direction takes that pair to be the universal pair itself, whose classifying morphism
is the identity by `pairClassifyingHom_universalPair`. -/
public theorem isCanonicalTwistPair_universalPair_iff (hgen : IsGeneratedInDegreeOne A) :
    IsCanonicalTwistPair A TA D (universalPair A TA (relativeProj A) hgen) ↔
      ∃ P : F1Pair A TA (relativeProj A).toBase, IsCanonicalTwistPair A TA D P ∧
        pairClassifyingHom A TA (relativeProj A).toBase (relativeProj A) hgen (Quot.mk _ P) =
          ⟨𝟙 (relativeProj A).scheme, Category.id_comp _⟩ :=
  ⟨fun h => ⟨universalPair A TA (relativeProj A) hgen, h,
      pairClassifyingHom_universalPair A TA (relativeProj A) hgen⟩,
    fun ⟨P, hcan, hid⟩ =>
      isCanonicalTwistPair_universalPair_of_classifies A TA D hgen P hcan hid⟩

/-- **The same, with canonicality spelled out as a formula for the graded map.** By
`isCanonicalTwistPair_iff_psi_eq` the canonicality of a pair is an identification of its
invertible sheaf with the degree-one twist together with the formula
`ψ_n = D.ψ_n ≫ π_*(γ_n⁻¹)` for its graded map; so Tag 01O4's canonicality clause is exactly the
existence of a pair with that shape whose classifying morphism is the identity. -/
public theorem isCanonicalTwistPair_universalPair_iff_psi_eq (hgen : IsGeneratedInDegreeOne A) :
    IsCanonicalTwistPair A TA D (universalPair A TA (relativeProj A) hgen) ↔
      ∃ (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1),
        (∀ n : ℕ, P.ψ (n : ℤ) = D.ψ n ≫
            (Scheme.Modules.pushforward (relativeProj A).toBase).map
              (twistComparisonOfAppIso TA D hgen P.L β n).inv) ∧
          pairClassifyingHom A TA (relativeProj A).toBase (relativeProj A) hgen (Quot.mk _ P) =
            ⟨𝟙 (relativeProj A).scheme, Category.id_comp _⟩ :=
  (isCanonicalTwistPair_universalPair_iff A TA D hgen).trans
    ⟨fun ⟨P, hcan, hid⟩ =>
        let ⟨β, hψ⟩ := (isCanonicalTwistPair_iff_psi_eq TA D hgen P).1 hcan
        ⟨P, β, hψ, hid⟩,
      fun ⟨P, β, hψ, hid⟩ =>
        ⟨P, (isCanonicalTwistPair_iff_psi_eq TA D hgen P).2 ⟨β, hψ⟩, hid⟩⟩

/-! ### The representation of Tag 01O4 from a canonical pair classified by the identity -/

/-- **Tag 01O4's representation over a twist datum, from one canonical pair.** A pair on relative
`Proj` that is the canonical twist pair of `D` and is classified by the identity morphism upgrades
the bundle `...ProjRepresentsF1.f1Bundle` to a full representation: the bundle supplies the
representing bijections, their normalisation at the identity and their naturality, and the pair
supplies the canonicality of the bundle's universal pair. -/
public def f1RepresentationOfCanonicalClassifiesId (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (hcan : IsCanonicalTwistPair A TA D P)
    (hid : pairClassifyingHom A TA (relativeProj A).toBase (relativeProj A) hgen
        (Quot.mk _ P) = ⟨𝟙 (relativeProj A).scheme, Category.id_comp _⟩) :
    F1RepresentationCanonical A TA D where
  toF1Bundle := f1Bundle A TA hgen
  universal_isCanonical :=
    isCanonicalTwistPair_universalPair_of_classifies A TA D hgen P hcan hid

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
