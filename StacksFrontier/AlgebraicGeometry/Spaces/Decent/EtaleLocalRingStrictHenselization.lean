module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# The étale local ring as a strict henselization of the henselian local ring

The étale local ring of a decent algebraic space at a geometric point is a strict henselization
of the henselian local ring of the space at the point the geometric point lies over. The
structure map is the unique local map over the local ring of an elementary étale neighborhood,
and the identification of the residue field of the étale local ring with the chosen separable
algebraic closure is the one it carries as a strict henselization of that neighborhood stalk.

## Main results

* `AlgebraicGeometry.Space.exists_isHenselization_etaleLocalRing`: **Stacks 0EMZ**, the étale
  local ring at a geometric point is a strict henselization of the henselian local ring at the
  point it lies over.

## Implementation notes

A strict henselization is `IsLocalRing.IsHenselization R κsep Rsh` for a separably closed
extension `κsep` of the residue field of `R`, the reading of Stacks 04GQ used throughout this
library; this is why the conclusion is a henselization statement rather than a separate
predicate.

The henselian local ring and the étale local ring are both colimits indexed by a category whose
objects live one universe up, so they are rings in `Type (u + 1)` over a neighborhood stalk in
`Type u`. Both the cancellation of ind-étaleness (Stacks 08HS) and the functoriality of the
strict henselization (Stacks 04GU) are applied in the universe-independent form, so no lifting
is needed in the statement.

The algebra structures are produced rather than assumed: the structure map
`𝒪^h_{X, x} → 𝒪_{X, x̄}` is the map of Stacks 04GU attached to the residue-field homomorphism
read off from the two henselization statements, and the extension of the residue field of
`𝒪^h_{X, x}` by the separable closure is transported along the residue identification of Stacks
0EMY. The conclusion records that the structure map lies over the neighborhood stalk, which by
the uniqueness half of Stacks 04GU pins it, and that the étale local ring is itself a strict
henselization of that stalk.

That the étale local ring at x̄ is a strict henselization of the local ring of an elementary
étale neighborhood of `x` at its distinguished point is
`AlgebraicGeometry.Space.exists_algebra_isHenselization_etaleLocalRing_elementary`: the
comparison of Properties of Spaces, Lemma 04KF applied to the small étale neighborhood of x̄
that the elementary one determines, the lift of x̄ being its factorization through the
residue-field point of the distinguished point. Cofilteredness of the elementary étale
neighborhoods, which the statements of Stacks 0EMY take as a hypothesis, is not carried: it
comes from Stacks 0BGV, the category being cofiltered as soon as it is nonempty, and the given
neighborhood witnesses that.

## References

* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

/-- **Stacks 0EMZ.** The étale local ring of a decent algebraic space at a geometric point is a
strict henselization of the henselian local ring of the space at the point it lies over. -/
@[stacks 0EMZ "the étale local ring at a geometric point is a strict henselization of the
henselian local ring at the point below it, for a chosen separable closure κsep of the residue
field. The algebra structures are produced, not assumed; the structure map is pinned by lying
over the neighborhood stalk, of which the étale local ring is also a strict henselization"]
theorem exists_isHenselization_etaleLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (xbar : GeometricPoint B S hS X) (hxbar : xbar.LiesOver x)
    (κsep : Type u) [Field κsep]
    [Algebra (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u)) κsep]
    [IsSepClosure (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u)) κsep] :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    ∃ (algU : Algebra (U.scheme.left.1.presheaf.stalk U.point : Type u)
        (etaleLocalRing B S hS X xbar : Type (u + 1)))
      (alg : Algebra (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
        (etaleLocalRing B S hS X xbar : Type (u + 1)))
      (algRes : Algebra (ResidueField
        (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) κsep),
      (@algebraMap (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
            (etaleLocalRing B S hS X xbar : Type (u + 1)) _ _ alg).comp
          (stalkToHenselianLocalRing B S hS X hX x hDecent U) =
        @algebraMap (U.scheme.left.1.presheaf.stalk U.point : Type u)
          (etaleLocalRing B S hS X xbar : Type (u + 1)) _ _ algU ∧
      @IsHenselization (U.scheme.left.1.presheaf.stalk U.point : Type u) _ _ κsep _ _
        (etaleLocalRing B S hS X xbar : Type (u + 1)) _ _ algU ∧
      @IsHenselization (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) _ _
        κsep _ algRes (etaleLocalRing B S hS X xbar : Type (u + 1)) _ _ alg := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := stalkAlgebra B S hS X hX x hDecent U
  obtain ⟨algU, hSH⟩ := exists_algebra_isHenselization_etaleLocalRing_elementary
    B S hS X hX U xbar hxbar κsep
  let := algU
  let := hSH
  have hH : IsHenselization (U.scheme.left.1.presheaf.stalk U.point : Type u)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS X hX x hDecent U
  let := hH
  have hindH := IsHenselization.ind_etale
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (L := ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (Rh := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
  have hindS := IsHenselization.ind_etale
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u)) (L := κsep)
    (Rh := (etaleLocalRing B S hS X xbar : Type (u + 1)))
  have hHen := IsHenselization.henselian
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u)) (L := κsep)
    (Rh := (etaleLocalRing B S hS X xbar : Type (u + 1)))
  let := hHen
  obtain ⟨e₀, he₀⟩ := IsHenselization.exists_residueFieldEquiv
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (L := ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (Rh := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at he₀
  obtain ⟨e₁, he₁⟩ := IsHenselization.exists_residueFieldEquiv
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u)) (L := κsep)
    (Rh := (etaleLocalRing B S hS X xbar : Type (u + 1)))
  let algRes : Algebra (ResidueField
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) κsep :=
    ((algebraMap (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))
      κsep).comp e₀.symm.toRingHom).toAlgebra
  set φ : ResidueField (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) →+*
      ResidueField (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    e₁.toRingHom.comp (algebraMap (ResidueField
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) κsep)
  have hφ : φ.comp ((residue (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))).comp
        (algebraMap (U.scheme.left.1.presheaf.stalk U.point : Type u) _)) =
      (residue (etaleLocalRing B S hS X xbar : Type (u + 1))).comp
        (algebraMap (U.scheme.left.1.presheaf.stalk U.point : Type u) _) := by
    refine RingHom.ext fun r ↦ ?_
    have hr : e₀.symm (residue (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
        (algebraMap (U.scheme.left.1.presheaf.stalk U.point : Type u) _ r)) =
        residue (U.scheme.left.1.presheaf.stalk U.point : Type u) r := by
      rw [← he₀ r, e₀.symm_apply_apply]
    change e₁ (algebraMap _ κsep (e₀.symm (residue _ _))) = _
    rw [hr]
    exact he₁ r
  set f := HenselianLocalRing.indEtaleAlgHomOfResidue
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (Rsh := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
    (Ssh := (etaleLocalRing B S hS X xbar : Type (u + 1)))
    hindH φ hφ
  have hresidue := HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue
    (R := (U.scheme.left.1.presheaf.stalk U.point : Type u))
    (Rsh := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
    (Ssh := (etaleLocalRing B S hS X xbar : Type (u + 1)))
    hindH φ hφ
  let alg : Algebra (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
      (etaleLocalRing B S hS X xbar : Type (u + 1)) := (f : _ →+* _).toAlgebra
  have htower : (algebraMap (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
        (etaleLocalRing B S hS X xbar : Type (u + 1))).comp
        (stalkToHenselianLocalRing B S hS X hX x hDecent U) =
      algebraMap (U.scheme.left.1.presheaf.stalk U.point : Type u)
        (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    RingHom.ext fun r ↦ f.commutes r
  let : IsScalarTower (U.scheme.left.1.presheaf.stalk U.point : Type u)
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq' htower.symm
  refine ⟨algU, alg, algRes, htower, hSH, ?_, ?_, ⟨e₁, fun y ↦ ?_⟩⟩
  · exact hHen
  · exact StacksDraft.indEtale_of_comp hindH hindS
  · exact (RingHom.congr_fun hresidue y).symm

end AlgebraicGeometry.Space

end
