module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.AffineGlobalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# An invertible module is trivial above a neighbourhood of any point of the target

Let `f : X ⟶ Y` be a finite morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`y ∈ Y`. Then some open neighbourhood `V ∋ y` has `L` trivial on `f^{-1}(V)` [Stacks, Tag 0BUT];
equivalently, `f` satisfies `Stacks.Divisors.HasTrivializingTargetCover` for `L`.

## The argument

Stacks reduces to the affine case. Choose an affine open `U ∋ y`; since `f` is finite, `f^{-1}U`
is an affine open of `X`, and it is presented here as the image of the open immersion
`hB.fromSpec : Spec Γ(X, f^{-1}U) ⟶ X` so that the affine scheme in play is literally a
spectrum. The fibre `f^{-1}(y)` is finite, so by clauses 2 and 3 of [Stacks, Tag 0F20] on a
spectrum
(`AlgebraicGeometry.Scheme.Modules.exists_sections_finite_subset_nonvanishingOpen_of_spec`) there
is a section `s` of `L` upstairs whose nonvanishing locus `N` contains the whole fibre. Its image
`A ⊆ X` is then an open neighbourhood of the fibre on which `L` is trivialized by `s` (Tag 01CY),
and because a finite morphism is closed the tube lemma gives an open `V ∋ y` with `f^{-1}V ⊆ A`.

## Main definitions

* `Stacks.SheafOfModules.restrictIsoUnitOfLE`: triviality of a restriction passes to a smaller
  open.
* `Stacks.SheafOfModules.restrictIsoUnitOfIsoOver`: triviality of a restriction transports along
  an isomorphism of schemes over `X`.

## Main results

* `Stacks.SheafOfModules.nonempty_restrictIsoUnit_of_le_nonvanishingOpen`: an invertible module
  is trivial on every open subscheme inside the nonvanishing locus of a global section.
* `Stacks.Divisors.hasTrivializingTargetCover_of_isFinite`: **Stacks Project, Tag 0BUT**, in the
  form the norm construction consumes.
* `Stacks.Divisors.exists_isTrivial_restrict_preimage_of_isFinite`: the same statement written
  with `Stacks.SheafOfModules.IsTrivial`, which is how Tag 0BUT itself reads.

## Implementation notes

The affine open `f^{-1}U` is *not* used through its own open subscheme `(f ⁻¹ᵁ U).toScheme`, but
through `IsAffineOpen.fromSpec`. The reason is that global generation is available on `Spec A`
and transporting it to an abstract affine scheme would mean comparing germs across
`Scheme.isoSpec`; routing the whole argument through the spectrum avoids that comparison, at the
cost of one isomorphism of *opens of `X`* at the end, which `Scheme.Hom.isoImage` supplies.

Moving the trivialization from `N`, an open of the spectrum, to `f^{-1}V`, an open of `X`, is
done by the two reusable lemmas above rather than inline: `restrictIsoUnitOfIsoOver` crosses
`Scheme.Hom.isoImage`, and `restrictIsoUnitOfLE` descends the inclusion `f^{-1}V ≤ A`. Both are
built only from Mathlib's `restrictFunctorComp`, `restrictFunctorCongr`, `restrictFunctorId` and
`restrictUnitIso`; no sections are computed.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class carrying
`@[stacks 01CS "invertible"]` and the one the Tag 01CY nonvanishing-locus API is stated in. Its
invariance under isomorphism, needed to read `Scheme.Modules.pullback` invertibility
(`Stacks.Modules.isInvertible_pullback`) as `Scheme.Modules.restrictFunctor` invertibility, is
`Stacks.SheafOfModules.isInvertible_of_iso`; the superficially similarly named
`Stacks.SheafOfModules.Invertible.isInvertible_of_iso` is about the *other* copy of the class,
`AlgebraicGeometry.SheafOfModules.IsInvertible`, and does not apply.

## References

* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

/-- Triviality of the restriction of `L` to an open subscheme passes to a smaller open. -/
noncomputable def restrictIsoUnitOfLE {X : Scheme.{u}} (L : X.Modules) {P A : X.Opens}
    (h : P ≤ A) (e : L.restrict A.ι ≅ _root_.SheafOfModules.unit A.toScheme.ringCatSheaf) :
    L.restrict P.ι ≅ _root_.SheafOfModules.unit P.toScheme.ringCatSheaf :=
  have hq : X.homOfLE h ≫ A.ι = P.ι := by simp
  ((Scheme.Modules.restrictFunctorCongr hq).app L).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) A.ι).app L ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

/-- Triviality of the restriction of `L` along an open immersion transports along an isomorphism
of schemes over `X`. -/
noncomputable def restrictIsoUnitOfIsoOver {X Z₁ Z₂ : Scheme.{u}} (L : X.Modules)
    {k₁ : Z₁ ⟶ X} {k₂ : Z₂ ⟶ X} [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (ε : Z₁ ≅ Z₂) (hε : ε.hom ≫ k₂ = k₁)
    (e : L.restrict k₁ ≅ _root_.SheafOfModules.unit Z₁.ringCatSheaf) :
    L.restrict k₂ ≅ _root_.SheafOfModules.unit Z₂.ringCatSheaf :=
  have e₁ : (L.restrict k₂).restrict ε.hom ≅ _root_.SheafOfModules.unit Z₁.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorComp ε.hom k₂).app L).symm ≪≫
      ((Scheme.Modules.restrictFunctorCongr hε).app L) ≪≫ e
  ((Scheme.Modules.restrictFunctorId).app (L.restrict k₂)).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr ε.inv_hom_id).app (L.restrict k₂)).symm ≪≫
    (Scheme.Modules.restrictFunctorComp ε.inv ε.hom).app (L.restrict k₂) ≪≫
    (Scheme.Modules.restrictFunctor ε.inv).mapIso e₁ ≪≫
    Scheme.Modules.restrictUnitIso ε.inv

/-- **Tag 01CY on an open subscheme.** An invertible module is trivial on every open subscheme
contained in the nonvanishing locus of a global section. -/
theorem nonempty_restrictIsoUnit_of_le_nonvanishingOpen (Z : Scheme.{u}) (L : Z.Modules)
    [IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property L]
    (s : L.sections) (V : Z.Opens)
    (hV : V ≤ nonvanishingOpen (X := Z.toRingedSpace) L s) :
    Nonempty (L.restrict V.ι ≅ _root_.SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  have hlocal : ∀ z : Z.toRingedSpace.carrier, IsLocalRing (ringStalk Z.toRingedSpace z) :=
    fun z => Z.isLocalRing z
  refine ⟨Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit _ L
    (isoUnitOver (X := Z.toRingedSpace) L V (s.eval (op V)) fun W hW => ?_)⟩
  exact (PresheafOfModules.sections_property s (homOfLE hW).op).symm ▸
    bijective_smul_eval_of_le_nonvanishingOpen (X := Z.toRingedSpace) L s W (hW.trans hV)

end Stacks.SheafOfModules

namespace Stacks.Divisors

open Stacks.SheafOfModules

/-- **Stacks Project, Tag 0BUT.** Let `f : X ⟶ Y` be a finite morphism of schemes and `L` an
invertible `𝒪_X`-module. Then every point of `Y` has an open neighbourhood `V` such that `L` is
trivial on `f^{-1}(V)`.

This discharges the hypothesis `Stacks.Divisors.HasTrivializingTargetCover` carried by every
result of `StacksDraft/AlgebraicGeometry/F3b/NormInvertible/`. -/
theorem hasTrivializingTargetCover_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (L : X.Modules)
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L] :
    HasTrivializingTargetCover f L := by
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hB : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hji : IsOpenImmersion hB.fromSpec := hB.isOpenImmersion_fromSpec
  have hLq : L.IsQuasicoherent := Scheme.isQuasicoherent_of_isInvertible X L
  have hL'i : IsInvertible (Spec Γ(X, f ⁻¹ᵁ U)).presheaf
      (structureSheafRing (Spec Γ(X, f ⁻¹ᵁ U)).toRingedSpace).property
      (L.restrict hB.fromSpec) := by
    have := Stacks.Modules.isInvertible_pullback hB.fromSpec L
    exact isInvertible_of_iso (Spec Γ(X, f ⁻¹ᵁ U)).presheaf
      (structureSheafRing (Spec Γ(X, f ⁻¹ᵁ U)).toRingedSpace).property
      ((Scheme.Modules.restrictFunctorIsoPullback hB.fromSpec).app L).symm
  have hE : (hB.fromSpec.base ⁻¹' (f.base ⁻¹' {y})).Finite :=
    (f.finite_preimage_singleton y).preimage hB.fromSpec.isOpenEmbedding.injective.injOn
  obtain ⟨s, hEs, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_sections_finite_subset_nonvanishingOpen_of_spec
      (L.restrict hB.fromSpec) hE ⊤ fun _ _ => trivial
  set N : (Spec Γ(X, f ⁻¹ᵁ U)).Opens :=
    nonvanishingOpen (X := (Spec Γ(X, f ⁻¹ᵁ U)).toRingedSpace) (L.restrict hB.fromSpec) s with hN
  set A : X.Opens := hB.fromSpec ''ᵁ N with hA
  have hfibA : f.base ⁻¹' {y} ⊆ (A : Set X) := by
    intro x hx
    have hxB : x ∈ (f ⁻¹ᵁ U : X.Opens) := by
      show f.base x ∈ U
      rw [show f.base x = y from hx]
      exact hyU
    obtain ⟨z, hz⟩ : ∃ z, hB.fromSpec.base z = x := by
      rw [← hB.opensRange_fromSpec] at hxB
      exact hxB
    exact ⟨z, hEs (show hB.fromSpec.base z ∈ f.base ⁻¹' {y} from hz ▸ hx), hz⟩
  obtain ⟨V, hVopen, hyV, hVA⟩ :=
    exists_isOpen_mem_preimage_subset f.isClosedMap A.isOpen hfibA
  refine ⟨⟨V, hVopen⟩, hyV, ?_⟩
  obtain ⟨eN⟩ := nonempty_restrictIsoUnit_of_le_nonvanishingOpen
    (Spec Γ(X, f ⁻¹ᵁ U)) (L.restrict hB.fromSpec) s N le_rfl
  have e₀ : L.restrict (N.ι ≫ hB.fromSpec) ≅
      _root_.SheafOfModules.unit N.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorComp N.ι hB.fromSpec).app L ≪≫ eN
  have eA : L.restrict A.ι ≅ _root_.SheafOfModules.unit A.toScheme.ringCatSheaf :=
    restrictIsoUnitOfIsoOver L (hB.fromSpec.isoImage N)
      (Scheme.Hom.isoImage_hom_ι hB.fromSpec N) e₀
  exact ⟨restrictIsoUnitOfLE L (A := A) hVA eA⟩

/-- **Stacks Project, Tag 0BUT**, written with `Stacks.SheafOfModules.IsTrivial`: for a finite
morphism `f : X ⟶ Y`, an invertible `𝒪_X`-module `L` and a point `y` of `Y`, there is an open
neighbourhood `V` of `y` over which `L` becomes trivial on the inverse image. -/
@[stacks 0BUT]
theorem exists_isTrivial_restrict_preimage_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (L : X.Modules)
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L] (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsTrivial (f ⁻¹ᵁ V).toScheme.presheaf
        (structureSheafRing (f ⁻¹ᵁ V).toScheme.toRingedSpace).property
        (L.restrict (f ⁻¹ᵁ V).ι) :=
  hasTrivializingTargetCover_of_isFinite f L y

end Stacks.Divisors

end
