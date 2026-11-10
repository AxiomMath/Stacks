module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.SigmaPoints

/-!
# Monomorphisms into disjoint unions of spectra of fields

A monomorphism of schemes into a disjoint union `∐ᵢ Spec kᵢ` of spectra of fields is the
inclusion of a subfamily of the components: there is a subset `J` of the index set and an
isomorphism of the source with `∐_{j ∈ J} Spec kⱼ` compatible with the two maps into the
disjoint union.

## Main results

* `AlgebraicGeometry.epi_appTop_of_mono`: a monomorphism of affine schemes induces an
  epimorphism on global sections.
* `AlgebraicGeometry.isIso_of_mono_to_spec_field`: a monomorphism from a nonempty scheme into the
  spectrum of a field is an isomorphism.
* `AlgebraicGeometry.exists_iso_coproduct_spec_of_mono`: a monomorphism into a disjoint union of
  spectra of fields is the inclusion of a subset of its components.

## Implementation notes

The identification is stated as an isomorphism whose composite with the canonical inclusion of
the selected components is the given monomorphism, so it is an isomorphism *over* the original
coproduct and not merely an abstract isomorphism of schemes.

## References

* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

/-- A monomorphism of affine schemes induces an epimorphism on global sections. -/
public theorem epi_appTop_of_mono {S T : Scheme.{u}} (g : S ⟶ T)
    [IsAffine S] [IsAffine T] [Mono g] :
    Epi (CommRingCat.ofHom g.appTop.hom) := by
  have hmono : Mono (Spec.map g.appTop) := by
    rw [show Spec.map g.appTop = S.isoSpec.inv ≫ g ≫ T.isoSpec.hom by
      rw [← Scheme.isoSpec_hom_naturality g, Iso.inv_hom_id_assoc]]
    infer_instance
  have := Scheme.Spec.mono_of_mono_map
    (show Mono (Scheme.Spec.map g.appTop.op) from hmono)
  simpa using CategoryTheory.unop_epi_of_mono g.appTop.op

/-- A monomorphism from a nonempty scheme into the spectrum of a field is an isomorphism. -/
public theorem isIso_of_mono_to_spec_field {K : Type u} [Field K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) [Mono g] [Nonempty X] : IsIso g := by
  let : Subsingleton X := g.injective.subsingleton
  let : IsAffine X := inferInstance
  let : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  let φ : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop
  let : Epi g.appTop := epi_appTop_of_mono g
  have : Epi φ := by dsimp [φ]; infer_instance
  let : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have : Algebra.IsEpi K Γ(X, ⊤) := by
    rw [← CommRingCat.epi_iff_epi]
    exact inferInstanceAs (Epi φ)
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).2
    ⟨(algebraMap K Γ(X, ⊤)).injective,
      Algebra.IsEpi.surjective_algebraMap_of_field (k := K) (S := Γ(X, ⊤))⟩
  have : IsIso g.appTop := by
    rw [show g.appTop = (Scheme.ΓSpecIso (.of K)).hom ≫ φ by simp [φ]]
    infer_instance
  have : IsIso (g ≫ (Spec (.of K)).isoSpec.hom) := by
    rw [← Scheme.isoSpec_hom_naturality g]
    infer_instance
  exact IsIso.of_isIso_comp_right g (Spec (.of K)).isoSpec.hom

/-- A monomorphism into a disjoint union of spectra of fields is an open immersion. -/
private theorem isOpenImmersion_to_coproduct_spec_of_mono
    {I : Type v} [Small.{u} I] (K : I → Type u) [∀ i, Field (K i)]
    {X : Scheme.{u}} (g : X ⟶ ∐ fun i ↦ Spec (.of (K i))) [Mono g] :
    IsOpenImmersion g := by
  let U (i : I) := (Sigma.ι (fun i ↦ Spec (.of (K i))) i).opensRange
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U
  · exact (sigmaOpenCover (fun i ↦ Spec (.of (K i)))).iSup_opensRange
  · intro i
    let g' := g ∣_ U i
    let q : (g ⁻¹ᵁ U i).toScheme ⟶ Spec (.of (K i)) :=
      g' ≫ (Sigma.ι (fun i ↦ Spec (.of (K i))) i).isoOpensRange.inv
    have : Mono g' := mono_of_mono_fac (morphismRestrict_ι g (U i))
    have : Mono q := by dsimp [q]; infer_instance
    rcases isEmpty_or_nonempty (g ⁻¹ᵁ U i).toScheme with _ | _
    · infer_instance
    · have : IsIso q := isIso_of_mono_to_spec_field q
      have : IsIso g' :=
        IsIso.of_isIso_comp_right g' (Sigma.ι (fun i ↦ Spec (.of (K i))) i).isoOpensRange.inv
      exact IsOpenImmersion.of_isIso g'

/-- A monomorphism into a disjoint union of spectra of fields is, over that disjoint union, the
inclusion of precisely a subset of its components. -/
@[stacks 03DP]
public theorem exists_iso_coproduct_spec_of_mono {ι : Type v} [Small.{u} ι] (k : ι → Type u)
    [∀ i, Field (k i)] {Y : Scheme.{u}}
    (f : Y ⟶ ∐ fun i ↦ Spec (.of (k i))) [Mono f] :
    ∃ J : Set ι, ∃ e : Y ≅ ∐ fun j : J ↦ Spec (.of (k j.1)),
      e.hom ≫ Sigma.desc (fun j : J ↦ Sigma.ι (fun i ↦ Spec (.of (k i))) j.1) = f := by
  let J : Set ι := {i | ∃ y : Y, ∃ x : Spec (.of (k i)),
    f y = Sigma.ι (fun i ↦ Spec (.of (k i))) i x}
  let g : (∐ fun j : J ↦ Spec (.of (k j.1))) ⟶ ∐ fun i ↦ Spec (.of (k i)) :=
    Sigma.desc (fun j : J ↦ Sigma.ι (fun i ↦ Spec (.of (k i))) j.1)
  have : IsOpenImmersion f := isOpenImmersion_to_coproduct_spec_of_mono k f
  have : IsOpenImmersion g := by
    dsimp [g]
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    simpa [Function.onFun_apply, disjoint_iff, TopologicalSpace.Opens.ext_iff] using
      disjoint_opensRange_sigmaι (fun i ↦ Spec (.of (k i))) i.1 j.1
        (fun h ↦ hij (Subtype.ext h))
  have hrange : Set.range f = Set.range g := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨i, x, hx'⟩ := exists_sigmaι_eq (fun i ↦ Spec (.of (k i))) (f y)
      have hi : i ∈ J := ⟨y, x, hx'.symm⟩
      refine ⟨Sigma.ι (fun j : J ↦ Spec (.of (k j.1))) ⟨i, hi⟩ x, ?_⟩
      dsimp [g]
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]; exact hx'
    · rintro ⟨z, rfl⟩
      obtain ⟨j, x, hx⟩ := exists_sigmaι_eq (fun j : J ↦ Spec (.of (k j.1))) z
      obtain ⟨y, x', hy⟩ := j.2
      refine ⟨y, ?_⟩
      rw [← hx, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      simpa only [Subsingleton.elim x x'] using hy
  exact ⟨J, IsOpenImmersion.isoOfRangeEq f g hrange,
    IsOpenImmersion.isoOfRangeEq_hom_fac f g hrange⟩

end AlgebraicGeometry
