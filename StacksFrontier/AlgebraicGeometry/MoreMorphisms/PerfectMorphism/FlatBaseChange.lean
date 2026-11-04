module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FlatBaseChange
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# Flat base change of a perfect morphism

A flat base change of a perfect morphism of schemes is perfect (Stacks 0688).

## Main results

* `RingHom.isPerfectRingMap_of_isPushout_of_flat`: the algebra content, that a perfect ring map
  `A → B` stays perfect after a flat base change `A → A'`, the base-changed algebra being
  presented as a pushout `B' = A' ⊗_A B`.
* `AlgebraicGeometry.perfect_of_isPullback_of_flat`: **Stacks 0688**, in a cartesian square of
  schemes whose base map is flat, the base change of a perfect morphism is perfect.
* `AlgebraicGeometry.perfect_pullback_snd`: the same in the `pullback` spelling.

## Implementation notes

Perfectness of a ring map is pseudo-coherence together with finite Tor dimension of the target as
a module over the source (Stacks 067H), and the two halves travel along a flat base change for
different reasons. Pseudo-coherence is carried by
`Algebra.PseudoCoherent.of_isPushout_of_flat`, the algebra content of Stacks 0680.
Finite Tor dimension is Stacks 066M: the base-changed module is `A' ⊗_A B`, the extension of
scalars of `B` along the flat map `A → A'`, and flat extension of scalars preserves Tor
amplitude. The bound coming out of perfectness of `A → B` is an arbitrary interval `[a, b]`
rather than one of the form `[-d, 0]`, so the interval-preserving form is derived here from the
flat-representative characterisation of Stacks 0654, exactly as
`StacksDraft.TorAmplitude.hasTorDimensionLE_extendScalars_of_flat` does for `[-d, 0]`.

Unlike pseudo-coherence, perfectness of a ring map is not packaged as a
`RingHom.PropertyIsLocal` in this library, so the geometric statement is not an instance of
`AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`. Instead the affine-local statement
Stacks 0686, `AlgebraicGeometry.perfect_iff_exists_affine_openCover`, is fed the cover of `S'` by
the affine opens lying over an affine open of `S`, and, over each of those, the cover of its
inverse image by the opens `g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'` of
`StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens`, whose sections are the tensor product
`Γ(X, U) ⊗_{Γ(S, V)} Γ(S', V')`.

The derived categories of modules come from `HasDerivedCategory.standard`, which is only ever a
local instance, so it is re-declared here.

## References

* [The Stacks Project, Lemma 37.61.2 (0688)](https://stacks.math.columbia.edu/tag/0688)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 37.60.3 (0680)](https://stacks.math.columbia.edu/tag/0680)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
* [The Stacks Project, Lemma 15.66.11 (066M)](https://stacks.math.columbia.edu/tag/066M)
* [The Stacks Project, Lemma 15.66.4 (0654)](https://stacks.math.columbia.edu/tag/0654)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StacksDraft.TorAmplitude
open scoped AlgebraicGeometry TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace RingHom

/-- Flat extension of scalars preserves Tor amplitude in an arbitrary interval: Tor amplitude in
`[a, b]` is the existence of a flat representative concentrated in `[a, b]` (Stacks 0654), a
condition that mentions no derived tensor product, and that condition is preserved by
`StacksDraft.TorAmplitude.hasFlatRepresentative_extendScalars`.

This is `StacksDraft.TorAmplitude.hasTorDimensionLE_extendScalars_of_flat`, which is Stacks 066M,
with the interval `[-d, 0]` of a Tor-dimension bound replaced by an arbitrary one; the proof is
the same. The two rings carry unrelated certified derived tensor products, since nothing
identifies them. -/
private theorem hasTorAmplitude_extendScalars_of_flat {A A' : Type u} [CommRing A] [CommRing A']
    {φ : A →+* A'} (hφ : φ.Flat) (D : CertifiedDerivedTensoring.{u, u} A)
    (D' : CertifiedDerivedTensoring.{u, u} A') (M : ModuleCat.{u} A) (a b : ℤ)
    (hM : HasTorAmplitude D.tensor D.comparison D.isLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) a b) :
    HasTorAmplitude D'.tensor D'.comparison D'.isLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).obj
        ((ModuleCat.extendScalars.{u, u, u} φ).obj M)) a b := by
  have := preservesFiniteLimits_extendScalars hφ
  have := additive_extendScalars hφ
  refine (hasTorAmplitude_of_iso
    (((ModuleCat.extendScalars.{u, u, u} φ).mapDerivedCategorySingleFunctor 0).app M) a b).mp ?_
  refine (hasTorAmplitude_iff_hasFlatRepresentative D'.comparison D'.isLeftDerived _ a b).mpr ?_
  exact hasFlatRepresentative_extendScalars hφ _ a b
    ((hasTorAmplitude_iff_hasFlatRepresentative D.comparison D.isLeftDerived _ a b).mp hM)

/-- **The algebra content of Stacks 0688.** Let `A → B` be a perfect ring map and let `A → A'` be
flat. Then the base change `A' → B'` is perfect, for any presentation of `B'` as the pushout
`A' ⊗_A B`.

Perfectness of `A → B` is quantified over the certified derived tensor products of `A`, as
Stacks 067H has it, and the conclusion is perfectness at any one certified derived tensor product
of `A'`; the canonical certificate of `A`
(`StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`) is the one used to read the Tor
amplitude of `B` over `A`. -/
theorem isPerfectRingMap_of_isPushout_of_flat
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [Algebra.IsPushout A A' B B'] [Module.Flat A A']
    (h : ∀ D : CertifiedDerivedTensoring.{u, u} A,
      IsPerfectRingMap A B D.tensor D.comparison D.isLeftDerived)
    (D' : CertifiedDerivedTensoring.{u, u} A') :
    IsPerfectRingMap A' B' D'.tensor D'.comparison D'.isLeftDerived := by
  obtain ⟨hpc, a, b, hamp⟩ := h (canonicalCertifiedDerivedTensoring A)
  refine ⟨hpc.of_isPushout_of_flat, a, b, ?_⟩
  have hφ : (algebraMap A A').Flat := flat_algebraMap_iff.mpr ‹Module.Flat A A'›
  have hext := hasTorAmplitude_extendScalars_of_flat hφ (canonicalCertifiedDerivedTensoring A) D'
    (ModuleCat.of A B) a b hamp
  let e : (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')).obj (ModuleCat.of A B) ≅
      ModuleCat.of A' B' :=
    ((FaithfullyFlat.extendScalarsCarrierEquiv A A' (ModuleCat.of A B)).trans
      (Algebra.IsPushout.equiv A A' B B').toLinearEquiv).toModuleIso
  exact (hasTorAmplitude_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).mapIso e) a b).mp hext

end RingHom

namespace AlgebraicGeometry

/-- In a cartesian square of schemes whose base map `g` is flat, with `f` perfect, the map on
sections of `f'` over a product `U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'` of affine opens lying over an affine
open `V` of `S` is a perfect ring map.

The square of section rings is a pushout square, by
`AlgebraicGeometry.algebra_isPushout_appLE_of_isPullback`, and `Γ(S, V) → Γ(S', V')` is flat, so
this is `RingHom.isPerfectRingMap_of_isPushout_of_flat`. -/
private theorem isPerfectRingMap_appLE_of_isPullback {X X' S S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [Flat g] [Perfect f]
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    {V' : S'.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)
    {U' : X'.Opens} (hU' : U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :
    ∀ D : CertifiedDerivedTensoring.{u, u} Γ(S', V'),
      letI := (f'.appLE V' U' (hU'.le.trans inf_le_right)).hom.toAlgebra
      RingHom.IsPerfectRingMap Γ(S', V') Γ(X', U') D.tensor D.comparison D.isLeftDerived := by
  intro D
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (g'.appLE U U' (hU'.le.trans inf_le_left)).hom.toAlgebra
  let : Algebra Γ(S', V') Γ(X', U') := (f'.appLE V' U' (hU'.le.trans inf_le_right)).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', U') :=
    ((g'.appLE U U' (hU'.le.trans inf_le_left)).hom.comp (f.appLE V U hUV).hom).toAlgebra
  have hcomp : (g'.appLE U U' (hU'.le.trans inf_le_left)).hom.comp (f.appLE V U hUV).hom =
      (f'.appLE V' U' (hU'.le.trans inf_le_right)).hom.comp (g.appLE V V' hV'V).hom := by
    simpa using congrArg CommRingCat.Hom.hom
      (isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V hU').w
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(X', U') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) Γ(S', V') Γ(X', U') := IsScalarTower.of_algebraMap_eq' hcomp
  have := algebra_isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V hU'
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have : Module.Flat Γ(S, V) Γ(S', V') :=
    HasRingHomProperty.appLE @Flat g ‹Flat g› ⟨V, hV⟩ ⟨V', hV'⟩ hV'V
  exact RingHom.isPerfectRingMap_of_isPushout_of_flat (Perfect.perfect_appLE f U hU V hV hUV) D

/-- **Stacks 0688.** A flat base change of a perfect morphism of schemes is perfect: if
`f : X ⟶ S` is perfect, `g : S' ⟶ S` is flat and the square with sides `g' : X' ⟶ X` and
`f' : X' ⟶ S'` is cartesian, then `f'` is perfect. -/
@[stacks 0688]
theorem perfect_of_isPullback_of_flat {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [Flat g] [Perfect f] :
    Perfect f' := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
  refine (perfect_iff_exists_affine_openCover f').mpr
    ⟨Σ V : S.affineOpens, {V' : S'.affineOpens // (V' : S'.Opens) ≤ g ⁻¹ᵁ (V : S.Opens)},
      fun j ↦ (j.2.1 : S'.Opens), ?_, fun j ↦ j.2.1.2, fun j ↦ ?_⟩
  · -- The affine opens of `S'` lying over an affine open of `S` cover `S'`.
    refine IsOpenCover.mk (top_le_iff.1 fun x _ ↦ ?_)
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens
      (show g.base x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V', hV', hxV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 S'.isBasis_affineOpens
      (show x ∈ g ⁻¹ᵁ V from hxV)
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, ⟨V', hV'⟩, hV'V⟩, hxV'⟩
  · -- Over each of them, the products with the affine opens of `X` over the same affine open of
    -- `S` cover the inverse image, are affine, and have perfect map on sections.
    refine ⟨{U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (j.1 : S.Opens)},
      fun i ↦ g' ⁻¹ᵁ (i.1 : X.Opens) ⊓ f' ⁻¹ᵁ (j.2.1 : S'.Opens), ?_,
      fun i ↦ IsAffineOpen.inf_preimage_of_isPullback sq j.1.2 i.1.2 i.2 j.2.1.2 j.2.2 rfl,
      fun i ↦ isPerfectRingMap_appLE_of_isPullback sq j.1.2 i.1.2 i.2 j.2.1.2 j.2.2 rfl⟩
    refine le_antisymm (iSup_le fun i ↦ inf_le_right) fun x hx ↦ ?_
    have hbase : g.base (f'.base x) = f.base (g'.base x) :=
      (congrArg (fun q : X' ⟶ S ↦ q.base x) sq.w).symm
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show g'.base x ∈ f ⁻¹ᵁ (j.1 : S.Opens) from by simpa [hbase] using j.2.2 hx)
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hUV⟩, hxU, hx⟩

/-- The `pullback` spelling of `AlgebraicGeometry.perfect_of_isPullback_of_flat`: the projection
to a flat base from the fibre product of a perfect morphism with it is perfect. -/
theorem perfect_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    [Perfect f] : Perfect (Limits.pullback.snd f g) :=
  perfect_of_isPullback_of_flat (IsPullback.of_hasPullback f g)

end AlgebraicGeometry

end
