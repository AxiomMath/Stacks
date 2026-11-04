module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SurjectiveComponents
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFibreFiniteness

/-!
# The normalization of a locally Noetherian scheme of dimension one

This is [Stacks, Tag 0C45]: for `X` locally Noetherian of dimension one with normalization
`ν : X^ν → X`, the morphism `ν` is integral, surjective and a bijection on irreducible
components, it factors through the reduction `X_{red}` by the normalization of `X_{red}`, which
is birational, the stalk of `ν_* 𝒪_{X^ν}` at a closed point is the integral closure of the local
ring in the total ring of fractions of its reduction, the fibres and the residue field
extensions of `ν` are finite, and `X^ν` is a disjoint union of integral normal locally
Noetherian schemes each of whose affine opens is the spectrum of a finite product of Dedekind
domains.

## Main definitions

* `AlgebraicGeometry.Scheme.normalizationSchemeOfIsLocallyNoetherian` and
  `AlgebraicGeometry.Scheme.normalizationOfIsLocallyNoetherian`: the normalization of a locally
  Noetherian scheme, whose quasi-compact opens have finitely many irreducible components.

## Main results

* `AlgebraicGeometry.normalization_of_isLocallyNoetherian_dimension_one` is Tag 0C45, all six
  parts.
* `AlgebraicGeometry.stalkNilradicalSubschemeRingEquiv`: the stalk of the reduction is the
  reduction of the stalk.

## Implementation notes

The bijection on irreducible components in part (1) is
`AlgebraicGeometry.Scheme.bijOn_irreducibleComponents_normalization`, which holds for the
normalization of any scheme whose quasi-compact opens have finitely many irreducible
components and is part of Tag 035Q.

Part (4) is Tag 0C3B part (2), which holds at every point and not only at a closed one; the
statement here is the source's, restricted to closed points. Its parenthetical identification
`(𝒪_{X,x})_red = 𝒪_{X_red,x}` is `AlgebraicGeometry.stalkNilradicalSubschemeRingEquiv`, carried
in the statement as a second conjunct.

Part (6) needs the dimension hypothesis: the local description of the normalization over an
affine open is Krull–Akizuki, in
`AlgebraicGeometry.isFiniteProductOfDedekindDomains_sections_normalizationScheme`. The
remaining parts hold for every scheme whose quasi-compact opens have finitely many irreducible
components, except for the finiteness statements of part (5), which are again Krull–Akizuki.

## References

* [Stacks Project, Tag 0C45](https://stacks.math.columbia.edu/tag/0C45)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

/-! ### The stalk of the reduction -/

/-- **The kernel of the stalk map of the closed immersion of the reduction is the nilradical.**
That kernel is the stalk of the nilradical ideal sheaf, whose sections over an affine open are
the nilpotents there, so it consists of nilpotent germs; conversely a nilpotent germ dies in the
stalk of the reduction, which is a reduced ring. -/
theorem ker_stalkMap_subschemeι_nilradical (X : Scheme.{u}) (z : X.nilradical.subscheme) :
    RingHom.ker ((X.nilradical.subschemeι).stalkMap z).hom =
      nilradical (X.presheaf.stalk (X.nilradical.subschemeι z)) := by
  have : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  refine le_antisymm ?_ ?_
  · obtain ⟨-, ⟨U, hU, rfl⟩, hzU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (X.nilradical.subschemeι z)) isOpen_univ
    rw [← stalk_ker_eq_of_affine_target X.nilradical.subschemeι z U hU hzU,
      Scheme.IdealSheafData.ker_subschemeι]
    refine iSup_le fun V => iSup_le fun hzV => ?_
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact mem_nilradical.mpr
      ((mem_nilradical.mp hs).map (X.presheaf.germ V.1 _ hzV).hom)
  · intro a ha
    refine RingHom.mem_ker.mpr ?_
    exact ((mem_nilradical.mp ha).map
      ((X.nilradical.subschemeι).stalkMap z).hom).eq_zero

/-- **The stalk of the reduction is the reduction of the stalk**: the identification
`(𝒪_{X,x})_red = 𝒪_{X_red,x}`. The stalk map of the closed immersion of the reduction is
surjective with kernel the nilradical. -/
noncomputable def stalkNilradicalSubschemeRingEquiv (X : Scheme.{u})
    (z : X.nilradical.subscheme) :
    (X.presheaf.stalk (X.nilradical.subschemeι z) ⧸
        nilradical (X.presheaf.stalk (X.nilradical.subschemeι z))) ≃+*
      X.nilradical.subscheme.presheaf.stalk z := by
  have hsurj : Function.Surjective ((X.nilradical.subschemeι).stalkMap z).hom :=
    SurjectiveOnStalks.stalkMap_surjective X.nilradical.subschemeι z
  rw [← ker_stalkMap_subschemeι_nilradical X z]
  exact RingHom.quotientKerEquivOfSurjective hsurj

/-! ### The normalization of a locally Noetherian scheme -/

namespace Scheme

/-- The normalization of a locally Noetherian scheme: every quasi-compact open of such a scheme
has finitely many irreducible components, so the normalization is defined. -/
abbrev normalizationSchemeOfIsLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Scheme.{u} :=
  X.normalizationScheme (finite_irreducibleComponents_of_isCompact X)

/-- The normalization morphism of a locally Noetherian scheme. -/
abbrev normalizationOfIsLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    X.normalizationSchemeOfIsLocallyNoetherian ⟶ X :=
  X.normalization (finite_irreducibleComponents_of_isCompact X)

end Scheme

/-- **Stacks Project, Tag 0C45.** Let `X` be a locally Noetherian scheme of dimension `1` and
let `ν : X^ν → X` be its normalization. Then

1. `ν` is integral, surjective, and induces a bijection on irreducible components,
2. there is a factorization `X^ν → X_red → X` and the morphism `X^ν → X_red` is the
   normalization of `X_red`,
3. `X^ν → X_red` is birational,
4. for every closed point `x ∈ X` the stalk `(ν_* 𝒪_{X^ν})_x` is the integral closure of
   `𝒪_{X,x}` in the total ring of fractions of `(𝒪_{X,x})_red = 𝒪_{X_red,x}`,
5. the fibres of `ν` are finite and the residue field extensions are finite,
6. `X^ν` is a disjoint union of integral normal locally Noetherian schemes and each affine open
   is the spectrum of a finite product of Dedekind domains. -/
@[stacks 0C45, ega "IV 18.9.7.8" "more general"]
theorem normalization_of_isLocallyNoetherian_dimension_one (X : Scheme.{u})
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X = 1) :
    -- (1)
    (IsIntegralHom X.normalizationOfIsLocallyNoetherian ∧
        Surjective X.normalizationOfIsLocallyNoetherian ∧
        Set.BijOn (fun C ↦ closure (X.normalizationOfIsLocallyNoetherian.base '' C))
          (irreducibleComponents X.normalizationSchemeOfIsLocallyNoetherian)
          (irreducibleComponents X)) ∧
      -- (2) and (3)
      (∃ g : X.normalizationSchemeOfIsLocallyNoetherian ⟶ X.nilradical.subscheme,
        g ≫ X.nilradical.subschemeι = X.normalizationOfIsLocallyNoetherian ∧
          IsBirational g ∧
          ∃ e : X.normalizationSchemeOfIsLocallyNoetherian ≅
            X.nilradical.subscheme.normalizationScheme
              (X.finite_irreducibleComponents_reduction
                (finite_irreducibleComponents_of_isCompact X)),
            e.hom ≫ X.nilradical.subscheme.normalization
              (X.finite_irreducibleComponents_reduction
                (finite_irreducibleComponents_of_isCompact X)) = g) ∧
      -- (4)
      (∀ x : X, IsClosed ({x} : Set X) →
        letI := normalizationPushforwardStalkAlgebra X
          (finite_irreducibleComponents_of_isCompact X) x
        letI : Algebra (X.presheaf.stalk x)
            (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
          (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
        Nonempty (normalizationPushforwardStalk X
              (finite_irreducibleComponents_of_isCompact X) x ≃ₐ[X.presheaf.stalk x]
            integralClosure (X.presheaf.stalk x)
              (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x)))) ∧
          ∀ z : X.nilradical.subscheme, X.nilradical.subschemeι z = x →
            Nonempty ((X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x)) ≃+*
              X.nilradical.subscheme.presheaf.stalk z)) ∧
      -- (5)
      ((∀ x : X, (X.normalizationOfIsLocallyNoetherian.base ⁻¹' {x}).Finite) ∧
        ∀ y : X.normalizationSchemeOfIsLocallyNoetherian,
          (X.normalizationOfIsLocallyNoetherian.residueFieldMap y).hom.Finite) ∧
      -- (6)
      ((∃ (ι : Type u) (Y : ι → Scheme.{u}) (_ : ∀ i, IsIntegral (Y i))
          (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsLocallyNoetherian (Y i)),
          Nonempty (X.normalizationSchemeOfIsLocallyNoetherian ≅ ∐ Y)) ∧
        ∀ W : X.normalizationSchemeOfIsLocallyNoetherian.Opens, IsAffineOpen W →
          Stacks.IsFiniteProductOfDedekindDomains
            Γ(X.normalizationSchemeOfIsLocallyNoetherian, W)) := by
  have hfin := finite_irreducibleComponents_of_isCompact X
  have hdim' : topologicalKrullDim X ≤ 1 := le_of_eq hdim
  have : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  refine ⟨⟨X.isIntegralHom_normalization hfin, inferInstance,
      X.bijOn_irreducibleComponents_normalization hfin⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (2) and (3)
    obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hfin
    refine ⟨e.hom ≫ X.nilradical.subscheme.normalization
      (X.finite_irreducibleComponents_reduction hfin), by rw [Category.assoc, he], ?_, e, rfl⟩
    exact IsBirational.comp (isBirational_of_iso e)
      (Scheme.isBirational_normalization X.nilradical.subscheme _)
  · -- (4)
    refine fun x _ => ⟨⟨normalizationStalkAlgEquivIntegralClosureFractionRing X hfin x⟩,
      fun z hz => ?_⟩
    subst hz
    exact ⟨stalkNilradicalSubschemeRingEquiv X z⟩
  · -- (5), fibres
    exact fun x => finite_fibre_normalization hdim' hfin x
  · -- (5), residue fields
    exact fun y => finite_residueFieldMap_normalization hdim' hfin y
  · -- (6), the disjoint union
    obtain ⟨ι, Y, hnormal, hintegral, ⟨e⟩⟩ :=
      X.exists_iso_sigma_isIntegral_isNormal_normalizationScheme hfin
    have : IsLocallyNoetherian (X.normalizationScheme hfin) :=
      isLocallyNoetherian_normalizationScheme hdim' hfin
    exact ⟨ι, Y, hintegral, hnormal,
      fun i => isLocallyNoetherian_of_isOpenImmersion (Sigma.ι Y i ≫ e.inv), ⟨e⟩⟩
  · -- (6), the affine opens
    exact fun W hW =>
      isFiniteProductOfDedekindDomains_sections_normalizationScheme hdim' hfin W hW

end AlgebraicGeometry

end
