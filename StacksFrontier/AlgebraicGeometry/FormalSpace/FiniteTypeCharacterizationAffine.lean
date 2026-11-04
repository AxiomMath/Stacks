module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects

/-!
# Stacks 0ANV for a morphism of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of affine
formal algebraic spaces over `S` with `Y` countably indexed. **Stacks 0ANV** says that `f` is
locally of finite type if and only if it is of finite type, if and only if it corresponds to a
morphism of `WAdm^{count}` satisfying the equivalent conditions of Stacks 0ANU.

The formal-spectrum forms of the lemma in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationVariants` assume the source
is already a formal spectrum `Spf C`. Here `X` is an arbitrary affine formal algebraic space, as
in the source, and its countable indexing is derived: a morphism locally of finite type is
representable by algebraic spaces, hence affine by Stacks 0AKN, and Stacks 0AKP makes `X`
countably indexed; Stacks 0AN1 and Stacks 0AN0 then present `f` as the formal spectrum map of a
continuous homomorphism of `WAdm^{count}`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CorrespondsToCountablyWeaklyAdmissibleMap`: a morphism of fppf
  sheaves is the formal spectrum map of a morphism of `WAdm^{count}` with a given property.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isAffineFormalAlgebraicSpace`:
  **Stacks 0ANV**.

## References

* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANV](https://stacks.math.columbia.edu/tag/0ANV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 0ANV for a morphism of affine formal algebraic spaces -/

variable (B S hS) in
/-- A morphism `t : U ⟶ V` of fppf sheaves over `S` *corresponds to a morphism of
`WAdm^{count}` with the property `P`*: `V` and `U` are formal spectra of weakly admissible
topological `S`-algebras `A` and `R` with countable fundamental systems of neighbourhoods of
zero, and `t` is the formal spectrum map of a continuous homomorphism `A → R` with `P`. -/
abbrev CorrespondsToCountablyWeaklyAdmissibleMap
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    {U V : FppfSheaf B S hS} (t : U ⟶ V) : Prop :=
  ∃ (A R : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : IsLinearTopology R R) (hA : TopologicalRing.IsCountablyWeaklyAdmissible A)
    (_ : TopologicalRing.IsCountablyWeaklyAdmissible R)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
    (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
    t = eU.hom ≫ formalSpectrumMap hA.1 g ≫ eV.inv ∧ P g.toRingHom

/-- Being locally of finite type is unchanged by composing on both sides with isomorphisms. -/
theorem isLocallyOfFiniteType_iso_comp_comp {U U' V V' : FppfSheaf B S hS} (eU : U ≅ U')
    (eV : V' ≅ V) (t : U' ⟶ V') (ht : IsLocallyOfFiniteType B S hS t) :
    IsLocallyOfFiniteType B S hS (eU.hom ≫ t ≫ eV.hom) :=
  IsLocallyOfFiniteType.comp B S hS eU.hom (t ≫ eV.hom)
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eU.hom
      (isRepresentableEtale_of_isIso B S hS eU.hom))
    (IsLocallyOfFiniteType.comp B S hS t eV.hom ht
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eV.hom
        (isRepresentableEtale_of_isIso B S hS eV.hom)))

/-- **Stacks 0ANV.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
with `Y` countably indexed. Then `f` being locally of finite type, `f` being of finite type in
the sense of Definition 0AM4, part (2), and `f` corresponding to a morphism `B → A` of
`WAdm^{count}` satisfying the equivalent conditions of Stacks 0ANU — taken in the two forms
(a), of finite type modulo every weak ideal of definition, and (c), taut and topologically of
finite type — are all equivalent.

As in the source, the source `X` is not assumed countably indexed. If `f` is locally of finite
type it is representable by algebraic spaces, hence affine by **Stacks 0AKN**, and `X` is then
countably indexed by **Stacks 0AKP**; the two steps together are clause (1) of Stacks 0AKQ,
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentable'`. Both spaces are then
formal spectra of rings of `WAdm^{count}` by **Stacks 0AN1**,
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_of_isCountablyIndexed`, and `f` is the
formal spectrum map of a continuous homomorphism by **Stacks 0AN0**,
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`. The equivalence
for that homomorphism is **Stacks 0ANT** together with Stacks 0ANU, in the form
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible`.
Being locally of finite type upgrades to being of finite type by Stacks 0AKN,
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal`, and
Stacks 0AJJ. -/
@[stacks 0ANV "the equivalence at the source's hypotheses: `f` an arbitrary morphism of affine \
formal algebraic spaces with countably indexed target. Countable indexing of the source is \
derived from condition (1) by Stacks 0AKN and Stacks 0AKP, the presentations as formal spectra \
by Stacks 0AN1 and the presenting homomorphism by Stacks 0AN0. Condition (3) is the existence \
of such presentations of `X` and `Y` by rings of `WAdm^count` and of a continuous homomorphism \
with formal spectrum map `f` satisfying the conditions of Stacks 0ANU, in the forms (a) and (c)"]
theorem isLocallyOfFiniteType_tfae_of_isAffineFormalAlgebraicSpace {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hYc : IsCountablyIndexed B S hS Y) :
    List.TFAE
      [IsLocallyOfFiniteType B S hS f,
        IsFiniteType' B S hS f,
        CorrespondsToCountablyWeaklyAdmissibleMap B S hS
          (fun φ ↦ TopologicalRing.FiniteTypeModuloEveryWeakIdeal φ) f,
        CorrespondsToCountablyWeaklyAdmissibleMap B S hS
          TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f] := by
  tfae_have 1 → 2 := fun h ↦
    (isFiniteType_iff_isBootstrapFiniteType B S hS f).mpr
      (IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal B S hS f hX hY h)
  tfae_have 2 → 1 := fun h ↦ h.1
  tfae_have 1 → 3 := by
    intro hf
    have hXc : IsCountablyIndexed B S hS X :=
      isCountablyIndexed_of_isRepresentable' B S hS f hX hY hf.1 hYc
    obtain ⟨R, _, _, _, _, E, hR, hRc, ⟨eX⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hXc
    obtain ⟨A, _, _, _, _, D, hA, hAc, ⟨eY⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hYc
    obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
      (eX.inv ≫ f ≫ eY.hom)
    have heq : f = eX.hom ≫ formalSpectrumMap hA g ≫ eY.inv := by
      rw [hg]; simp
    have hmap : IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g) := by
      rw [hg]
      exact isLocallyOfFiniteType_iso_comp_comp eX.symm eY f hf
    have h3 := ((formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible hA hR hAc D E
      g).out 1 3).mp hmap
    exact ⟨A, R, _, _, _, _, _, _, _, _, ⟨hA, hAc⟩, ⟨hR, hRc⟩, D, E, eX, eY, g, heq, h3.2⟩
  tfae_have 3 → 4 := by
    rintro ⟨A, R, _, _, _, _, _, _, _, _, hA, hR, D, E, eX, eY, g, heq, h⟩
    have h4 := ((formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible hA.1 hR.1 hA.2 D E
      g).out 3 4).mp (And.intro hR h)
    exact ⟨A, R, _, _, _, _, _, _, _, _, hA, hR, D, E, eX, eY, g, heq, h4.2⟩
  tfae_have 4 → 1 := by
    rintro ⟨A, R, _, _, _, _, _, _, _, _, hA, hR, D, E, eX, eY, g, heq, h⟩
    have hmap := ((formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible hA.1 hR.1 hA.2 D E
      g).out 4 1).mp (And.intro hR h)
    rw [heq]
    exact isLocallyOfFiniteType_iso_comp_comp eX (eY.symm) _ hmap
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
