module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCriterion
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# The normalization of a strict normal crossings divisor

Let `D` be a strict normal crossings divisor on a locally Noetherian scheme `X`. Each irreducible
component of the closed subscheme cut out by `D` is regular, hence normal, so its own
normalization morphism is an isomorphism; since the normalization of a scheme is the disjoint
union of the normalizations of its irreducible components (Tag 0CDV), the normalization of `D` is
the disjoint union of the irreducible components of `D` themselves, each taken with its reduced
closed subscheme structure inside `X`.

## Main results

* `AlgebraicGeometry.disjoint_range_sigmaι_of_ne`: two distinct injections into a coproduct of
  schemes have disjoint ranges.
* `Stacks.Divisors.exists_sigmaIso_divisorNormalization_of_isStrictNormalCrossingsDivisor`: the
  normalization of a strict normal crossings divisor is isomorphic, compatibly with the maps to
  the ambient scheme, to the coproduct of the closed subschemes of the ambient scheme cut out by
  the irreducible components of the divisor.
* `Stacks.Divisors.exists_mem_range_sigmaι_hom_of_isStrictNormalCrossingsDivisor`: for any such
  isomorphism the composites of the coproduct injections with it, which are open immersions by
  instance search, have ranges that cover the normalization.
* `Stacks.Divisors.exists_componentCover_divisorNormalization_of_isStrictNormalCrossingsDivisor`:
  the same information packaged as a family of open immersions from those components into the
  normalization which covers it with pairwise disjoint ranges and is compatible with the maps to
  the ambient scheme.

## Implementation notes

The identification of an irreducible component of the subscheme cut out by `D`, with its reduced
induced structure, with the closed subscheme of `X` cut out by the corresponding component ideal
is non-canonical (`Stacks.Divisors.exists_iso_reducedComponent_componentIdealSubscheme` is an
existential), so the component isomorphisms are chosen with `choose` and the resulting coproduct
isomorphism is itself only asserted to exist. For the same reason the covering family is produced
by an existential statement rather than defined.

The two statements about the coproduct injections take the isomorphism as a hypothesis, so that
they apply to any isomorphism onto the normalization and not only to the chosen one; neither
needs the compatibility with the maps to the ambient scheme.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two distinct injections into a coproduct of schemes have disjoint ranges: a point of the
coproduct determines the summand it comes from. -/
public theorem disjoint_range_sigmaι_of_ne {ι : Type u} (g : ι → Scheme.{u}) {i j : ι}
    (hij : i ≠ j) :
    Disjoint (Set.range (Sigma.ι g i).base) (Set.range (Sigma.ι g j).base) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff g j i b a).mp hb)).symm

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)

/-- **Stacks Project, Tag 0CDV** for a strict normal crossings divisor. The normalization of a
strict normal crossings divisor `D` on a locally Noetherian scheme is the disjoint union of the
irreducible components of `D`, each taken with its reduced closed subscheme structure in the
ambient scheme, compatibly with the closed immersions into the ambient scheme.

The normalization of `D` is the coproduct of the normalizations of the irreducible components of
`D` by Tag 0CDV; each component is normal by
`Stacks.Divisors.isNormal_reducedComponent_of_isStrictNormalCrossingsDivisor`, so its
normalization morphism is an isomorphism by Tag 0H7D, and each component is identified with the
closed subscheme of the ambient scheme cut out by its component ideal. -/
@[ega "II 6.3.6" "special case"]
public theorem exists_sigmaIso_divisorNormalization_of_isStrictNormalCrossingsDivisor
    (h : IsStrictNormalCrossingsDivisor D) :
    ∃ e : (∐ fun C : irreducibleComponents D.subscheme ↦ (componentIdeal D C).subscheme) ≅
            divisorNormalizationScheme D,
      e.hom ≫ divisorNormalization D ≫ D.subschemeι =
        Sigma.desc fun C : irreducibleComponents D.subscheme ↦
          (componentIdeal D C).subschemeι := by
  let : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  obtain ⟨e₀, he₀⟩ := D.subscheme.exists_iso_normalizationScheme_sigma_reducedComponent
    (finite_irreducibleComponents_of_isCompact D.subscheme)
  have hex : ∀ C : irreducibleComponents D.subscheme,
      ∃ q : (componentIdeal D C).subscheme ≅
          (D.subscheme.reducedComponent C).normalizationScheme
            (D.subscheme.finite_irreducibleComponents_reducedComponent C),
        q.hom ≫ (D.subscheme.reducedComponent C).normalization
            (D.subscheme.finite_irreducibleComponents_reducedComponent C) ≫
              D.subscheme.reducedComponentι C ≫ D.subschemeι =
          (componentIdeal D C).subschemeι := by
    intro C
    obtain ⟨eC, heC⟩ := exists_iso_reducedComponent_componentIdealSubscheme D C
    have : IsNormal (D.subscheme.reducedComponent C) :=
      isNormal_reducedComponent_of_isStrictNormalCrossingsDivisor D h C
    have : IsIso ((D.subscheme.reducedComponent C).normalization
        (D.subscheme.finite_irreducibleComponents_reducedComponent C)) :=
      ((D.subscheme.reducedComponent C).isIso_normalization_iff_isNormal
        (D.subscheme.finite_irreducibleComponents_reducedComponent C)).2 inferInstance
    refine ⟨eC.symm ≪≫ (asIso ((D.subscheme.reducedComponent C).normalization
      (D.subscheme.finite_irreducibleComponents_reducedComponent C))).symm, ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← heC, Iso.inv_hom_id_assoc]
  choose q hq using hex
  have heq : e₀.hom ≫ divisorNormalization D ≫ D.subschemeι =
      (Sigma.desc fun Z : irreducibleComponents D.subscheme ↦
        (D.subscheme.reducedComponent Z).normalization
          (D.subscheme.finite_irreducibleComponents_reducedComponent Z) ≫
            D.subscheme.reducedComponentι Z) ≫ D.subschemeι := by
    rw [← Category.assoc, he₀]
  refine ⟨Sigma.mapIso q ≪≫ e₀, Sigma.hom_ext _ _ fun C ↦ ?_⟩
  rw [Iso.trans_hom, Category.assoc, Sigma.ι_mapIso_hom_assoc, heq, Sigma.ι_comp_desc_assoc,
    Sigma.ι_comp_desc, Category.assoc]
  exact hq C

/-- The coproduct injections into the normalization of a strict normal crossings divisor, read
through an isomorphism of the normalization with the coproduct of the components, cover the
normalization. -/
public theorem exists_mem_range_sigmaι_hom_of_isStrictNormalCrossingsDivisor
    (e : (∐ fun C : irreducibleComponents D.subscheme ↦ (componentIdeal D C).subscheme) ≅
          divisorNormalizationScheme D) (y : divisorNormalizationScheme D) :
    ∃ C : irreducibleComponents D.subscheme, y ∈ Set.range (Sigma.ι
      (fun C : irreducibleComponents D.subscheme ↦
        (componentIdeal D C).subscheme) C ≫ e.hom).base := by
  obtain ⟨C, z, hz⟩ := exists_sigmaι_eq
    (fun C : irreducibleComponents D.subscheme ↦ (componentIdeal D C).subscheme) (e.inv.base y)
  refine ⟨C, z, ?_⟩
  show (Sigma.ι (fun C : irreducibleComponents D.subscheme ↦
    (componentIdeal D C).subscheme) C ≫ e.hom) z = y
  rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  simp

/-- **Stacks Project, Tag 0CDV** for a strict normal crossings divisor, in covering form. The
normalization of a strict normal crossings divisor `D` on a locally Noetherian scheme is covered
by open immersions with pairwise disjoint ranges, one for each irreducible component of `D`, from
the closed subscheme of the ambient scheme cut out by that component; each of them composed with
the map to the ambient scheme is the closed immersion of that component. -/
public theorem exists_componentCover_divisorNormalization_of_isStrictNormalCrossingsDivisor
    (h : IsStrictNormalCrossingsDivisor D) :
    ∃ ε : ∀ C : irreducibleComponents D.subscheme,
            (componentIdeal D C).subscheme ⟶ divisorNormalizationScheme D,
      (∀ C, IsOpenImmersion (ε C)) ∧
      (∀ C, ε C ≫ divisorNormalization D ≫ D.subschemeι = (componentIdeal D C).subschemeι) ∧
      (∀ y : divisorNormalizationScheme D, ∃ C, y ∈ Set.range (ε C).base) ∧
      (∀ C C', C ≠ C' → Disjoint (Set.range (ε C).base) (Set.range (ε C').base)) := by
  obtain ⟨e, he⟩ := exists_sigmaIso_divisorNormalization_of_isStrictNormalCrossingsDivisor D h
  refine ⟨fun C ↦ Sigma.ι (fun C : irreducibleComponents D.subscheme ↦
    (componentIdeal D C).subscheme) C ≫ e.hom, fun C ↦ ?_, fun C ↦ ?_, fun y ↦ ?_,
    fun C C' hCC' ↦ ?_⟩
  · exact inferInstance
  · rw [Category.assoc, he, Sigma.ι_comp_desc]
  · exact exists_mem_range_sigmaι_hom_of_isStrictNormalCrossingsDivisor D e y
  · have hinj : Function.Injective ⇑e.hom.base := e.hom.isOpenEmbedding.injective
    rw [Set.disjoint_left]
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hb
    exact Set.disjoint_left.mp (disjoint_range_sigmaι_of_ne
      (fun C : irreducibleComponents D.subscheme ↦ (componentIdeal D C).subscheme) hCC')
      ⟨a, rfl⟩ ⟨b, hinj hb⟩

end Stacks.Divisors

end
