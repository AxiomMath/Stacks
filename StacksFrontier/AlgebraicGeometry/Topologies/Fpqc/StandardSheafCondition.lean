module

public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# The fpqc sheaf condition and standard fpqc coverings

A presheaf of sets on the category of schemes is an fpqc sheaf exactly when it is a Zariski
sheaf and satisfies the sheaf property for every *standard* fpqc covering, that is, for every
finite jointly surjective family of flat morphisms with affine sources over an affine base.
Moreover, in the presence of the Zariski condition, the standard-covering condition is
equivalent to the sheaf property for a single faithfully flat morphism of affine schemes.

## Main results

* `AlgebraicGeometry.isSheaf_fpqcTopology_iff_and_standardCovering_iff_faithfullyFlat` — Stacks
  022H in full: the fpqc sheaf condition is the conjunction of the sheaf property for Zariski
  coverings and for standard fpqc coverings, and under the first, the second is the sheaf
  property for faithfully flat morphisms of affine schemes.
* `AlgebraicGeometry.isSheaf_fpqcTopology_iff_zariski_and_standardCovering` — the fpqc sheaf
  condition as the conjunction of the Zariski condition and the standard-covering condition.
* `AlgebraicGeometry.isSheafFor_standardCovering_iff_affine_singleton` — in the presence of the
  Zariski condition, the standard-covering condition is the single-morphism condition.
* `AlgebraicGeometry.Scheme.AffineCover.ofFaithfullyFlat` — the one-member standard fpqc
  covering of `Spec R` attached to a faithfully flat ring map `R ⟶ S`.

## Implementation notes

A standard fpqc covering, Stacks 022F, is spelled as in
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement`: an
`AlgebraicGeometry.Scheme.AffineCover` for `AlgebraicGeometry.Flat` with finite index type over
an affine base. No new notion of covering is introduced.

Mathlib's `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` already gives the equivalence with
the conjunction of the Zariski condition and the *single faithfully flat morphism of affines*
condition, and supplies the whole reduction from arbitrary fpqc coverings. What is added here is
the standard-covering condition, which that equivalence does not mention: a standard fpqc
covering is an fpqc covering, which gives one implication, and a faithfully flat morphism of
affine schemes is a one-member standard fpqc covering, which gives the other. The disjoint-union
step of the source's last paragraph is therefore not needed, because Mathlib's reduction is
already stated for a single morphism rather than for a finite family.

The ascription of `AlgebraicGeometry.Flat` to a `CategoryTheory.MorphismProperty` is what lets
instance search find the `AlgebraicGeometry.IsZariskiLocalAtSource` and
`CategoryTheory.MorphismProperty.IsMultiplicative` instances that
`AlgebraicGeometry.isSheaf_type_propQCTopology_iff` asks for; without it they are not found for
the universe-polymorphic predicate. The same device is used by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FpqcTopology.SheafCriterion`.

## References

* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- Flatness of morphisms of schemes as a morphism property. The ascription is what lets
instance search see the instances whose arguments are morphism properties rather than
universe-polymorphic predicates. -/
private abbrev flatProperty : MorphismProperty Scheme.{u} := @Flat

/-- The standard fpqc covering of `Spec R` with the single member `Spec S ⟶ Spec R`, attached to
a faithfully flat ring map `R ⟶ S`. -/
public noncomputable def Scheme.AffineCover.ofFaithfullyFlat {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Flat (Spec.map f)) (hs : Surjective (Spec.map f)) :
    (Spec R).AffineCover.{w} (@Flat.{u}) where
  I₀ := PUnit.{w + 1}
  X _ := S
  f _ := Spec.map f
  idx _ := ⟨⟩
  covers x := hs.1 x
  map_prop _ := hf

/-- `AlgebraicGeometry.Scheme.AffineCover.ofFaithfullyFlat` has a single member, so finitely
many. -/
public instance Scheme.AffineCover.finite_I₀_ofFaithfullyFlat {R S : CommRingCat.{u}}
    (f : R ⟶ S) (hf : Flat (Spec.map f)) (hs : Surjective (Spec.map f)) :
    Finite (Scheme.AffineCover.ofFaithfullyFlat.{u, w} f hf hs).I₀ :=
  inferInstanceAs (Finite PUnit.{w + 1})

/-- The one-member standard fpqc covering attached to a faithfully flat ring map has the
singleton presieve of the corresponding morphism of affine schemes. -/
@[simp]
public lemma Scheme.AffineCover.presieve₀_cover_ofFaithfullyFlat {R S : CommRingCat.{u}}
    (f : R ⟶ S) (hf : Flat (Spec.map f)) (hs : Surjective (Spec.map f)) :
    (Scheme.AffineCover.ofFaithfullyFlat.{u, w} f hf hs).cover.presieve₀ =
      Presieve.singleton (Spec.map f) :=
  show Presieve.ofArrows _ (fun _ : PUnit.{w + 1} ↦ Spec.map f) = _ from
    Presieve.ofArrows_pUnit _

/-- A standard fpqc covering is a covering sieve of the fpqc topology: a finite jointly
surjective family of flat morphisms with affine sources over an affine base is an fpqc
covering. -/
public lemma sieve_generate_presieve₀_mem_fpqcTopology {T : Scheme.{u}} [IsAffine T]
    (𝒱 : T.AffineCover.{w} (@Flat.{u})) [Finite 𝒱.I₀] :
    Sieve.generate 𝒱.cover.presieve₀ ∈ Scheme.fpqcTopology.{u} T :=
  Precoverage.generate_mem_toGrothendieck
    (presieve₀_mem_fpqcPrecoverage_of_finite_affineCover 𝒱)

/-- A presheaf of sets on the category of schemes is a sheaf for the fpqc topology if and only if
it is a sheaf for the Zariski topology and satisfies the sheaf property for every standard fpqc
covering: every finite jointly surjective family of flat morphisms with affine sources over an
affine base. This is the first statement of Stacks 022H; the whole lemma is
`AlgebraicGeometry.isSheaf_fpqcTopology_iff_and_standardCovering_iff_faithfullyFlat`. -/
public theorem isSheaf_fpqcTopology_iff_zariski_and_standardCovering
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} F ↔
      Presieve.IsSheaf Scheme.zariskiTopology.{u} F ∧
        ∀ {T : Scheme.{u}} [IsAffine T] (𝒱 : T.AffineCover.{w} (@Flat.{u})), Finite 𝒱.I₀ →
          Presieve.IsSheafFor F 𝒱.cover.presieve₀ := by
  rw [Scheme.fpqcTopology_eq_propQCTopology,
    isSheaf_type_propQCTopology_iff (P := flatProperty.{u}) F]
  refine and_congr_right fun hzar ↦ ⟨fun h₂' T _ 𝒱 hfin ↦ ?_, fun h₂ R S f hf hs ↦ ?_⟩
  · -- A standard fpqc covering is an fpqc covering, so the sheaf condition applies to it.
    have hsh : Presieve.IsSheaf (Scheme.propQCTopology flatProperty.{u}) F :=
      (isSheaf_type_propQCTopology_iff (P := flatProperty.{u}) F).mpr ⟨hzar, h₂'⟩
    have : Finite 𝒱.I₀ := hfin
    exact hsh.isSheafFor _ (sieve_generate_presieve₀_mem_fpqcTopology 𝒱)
  · -- A faithfully flat morphism of affines is a one-member standard fpqc covering.
    have h := h₂ (Scheme.AffineCover.ofFaithfullyFlat.{u, w} f hf hs) inferInstance
    rwa [Scheme.AffineCover.presieve₀_cover_ofFaithfullyFlat] at h

/-- **Stacks 022H, the final sentence.** For a Zariski sheaf of sets on the category of schemes,
the sheaf property for every standard fpqc covering is equivalent to the sheaf property for a
single faithfully flat morphism of affine schemes. -/
public theorem isSheafFor_standardCovering_iff_affine_singleton (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    (hzar : Presieve.IsSheaf Scheme.zariskiTopology.{u} F) :
    (∀ {T : Scheme.{u}} [IsAffine T] (𝒱 : T.AffineCover.{w} (@Flat.{u})), Finite 𝒱.I₀ →
        Presieve.IsSheafFor F 𝒱.cover.presieve₀) ↔
      ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), Flat (Spec.map f) → Surjective (Spec.map f) →
        Presieve.IsSheafFor F (Presieve.singleton (Spec.map f)) := by
  have h := isSheaf_fpqcTopology_iff_zariski_and_standardCovering.{u, v, w} F
  rw [Scheme.fpqcTopology_eq_propQCTopology,
    isSheaf_type_propQCTopology_iff (P := flatProperty.{u}) F] at h
  exact ⟨fun h₂ ↦ (h.mpr ⟨hzar, h₂⟩).2, fun h₂' ↦ (h.mp ⟨hzar, h₂'⟩).2⟩

/-- The sheaf property for every Zariski covering, a jointly surjective family of open immersions,
is the sheaf condition for the Zariski topology. -/
public lemma isSheaf_zariskiTopology_iff_forall_zariskiPrecoverage (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.zariskiTopology.{u} F ↔
      ∀ {T : Scheme.{u}} (R : Presieve T), R ∈ Scheme.zariskiPrecoverage T →
        Presieve.IsSheafFor F R :=
  ⟨fun h _ R hR ↦ (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange F).mp h R hR,
    fun h ↦ (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange F).mpr
      fun _ R hR ↦ h R hR⟩

/-- A faithfully flat morphism of affine schemes is a one-member fpqc covering, so an fpqc sheaf
satisfies the sheaf property for it. -/
public lemma isSheafFor_singleton_of_isSheaf_fpqcTopology {F : Scheme.{u}ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf Scheme.fpqcTopology.{u} F) {V U : Scheme.{u}} [IsAffine V]
    [IsAffine U] (g : V ⟶ U) (hf : Flat g) (hs : Surjective g) :
    Presieve.IsSheafFor F (Presieve.singleton g) := by
  have := hf
  have := hs
  exact hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck g.singleton_mem_fpqcPrecoverage)

/-- **Stacks 022H.** A presheaf of sets `F` on the category of schemes satisfies the sheaf
property for the fpqc topology if and only if it satisfies
(1) the sheaf property for every Zariski covering, that is, every jointly surjective family of
open immersions, and
(2) the sheaf property for every standard fpqc covering, that is, every finite jointly surjective
family of flat morphisms with affine sources over an affine base.
Moreover, in the presence of (1), property (2) is equivalent to
(2') the sheaf property for `{V ⟶ U}` with `V` and `U` affine and `V ⟶ U` faithfully flat. -/
@[stacks 022H "both statements of the lemma: the fpqc sheaf condition is equivalent to \
(1) ∧ (2), and under (1), (2) is equivalent to (2')", sga "3 XI 3.4" "special case"]
public theorem isSheaf_fpqcTopology_iff_and_standardCovering_iff_faithfullyFlat
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    (Presieve.IsSheaf Scheme.fpqcTopology.{u} F ↔
      (∀ {T : Scheme.{u}} (R : Presieve T), R ∈ Scheme.zariskiPrecoverage T →
          Presieve.IsSheafFor F R) ∧
        ∀ {T : Scheme.{u}} [IsAffine T] (𝒱 : T.AffineCover.{w} (@Flat.{u})), Finite 𝒱.I₀ →
          Presieve.IsSheafFor F 𝒱.cover.presieve₀) ∧
    ((∀ {T : Scheme.{u}} (R : Presieve T), R ∈ Scheme.zariskiPrecoverage T →
        Presieve.IsSheafFor F R) →
      ((∀ {T : Scheme.{u}} [IsAffine T] (𝒱 : T.AffineCover.{w} (@Flat.{u})), Finite 𝒱.I₀ →
          Presieve.IsSheafFor F 𝒱.cover.presieve₀) ↔
        ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (g : V ⟶ U), Flat g → Surjective g →
          Presieve.IsSheafFor F (Presieve.singleton g))) := by
  have hZ := isSheaf_zariskiTopology_iff_forall_zariskiPrecoverage F
  have hmain := isSheaf_fpqcTopology_iff_zariski_and_standardCovering.{u, v, w} F
  refine ⟨by rw [hmain, hZ], fun hz ↦ ⟨fun hstd ↦ ?_, fun haff ↦ ?_⟩⟩
  · exact fun g hf hs ↦
      isSheafFor_singleton_of_isSheaf_fpqcTopology (hmain.mpr ⟨hZ.mpr hz, hstd⟩) g hf hs
  · -- The case `V = Spec S`, `U = Spec R` of (2') is Mathlib's single-morphism condition.
    have hsh : Presieve.IsSheaf Scheme.fpqcTopology.{u} F := by
      rw [Scheme.fpqcTopology_eq_propQCTopology,
        isSheaf_type_propQCTopology_iff (P := flatProperty.{u}) F]
      exact ⟨hZ.mpr hz, fun f hf hs ↦ haff (Spec.map f) hf hs⟩
    intro T _ 𝒱 hfin
    exact (hmain.mp hsh).2 𝒱 hfin

end AlgebraicGeometry

end
