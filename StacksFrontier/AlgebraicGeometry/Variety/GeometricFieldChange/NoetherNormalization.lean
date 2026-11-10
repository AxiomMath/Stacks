module

import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Basic
import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.LocalStructure
import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Cotangent
import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Numerical
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Cotangent
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.NoetherNormalization
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
import StacksFrontier.RingTheory.Unramified.Properties
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Variants of Noether normalization

A morphism locally of finite type factors, near a point of its source at which the fibre has
dimension `d`, through relative affine `d`-space over any affine open neighbourhood of the
image point, by a quasi-finite morphism. For a finite type morphism of affine schemes there is
a global factorization through relative affine `d`-space whose restriction to the chosen fibre
is finite.
If instead `r` is the dimension of the relative cotangent space at the point, the morphism
factors near that point through relative affine `(r + 1)`-space by an immersion, and through a
scheme smooth of relative dimension `r` by a closed immersion.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.exists_affineOpen_quasiFinite_affineSpace_factorization`: the local
  quasi-finite factorization near a point.
* `AlgebraicGeometry.exists_factorization_finite_fiber`: the global factorization of a finite
  type morphism of affine schemes, finite on the chosen fibre.
* `AlgebraicGeometry.exists_factorization_unramifiedAt`: for a finite type morphism of affine
  schemes, the factorization through relative affine `r`-space by a morphism unramified at a
  chosen point, where `r` is the dimension of the residue-field fibre of the relative
  differentials there.
* `AlgebraicGeometry.finiteDimensional_relativeCotangentSpace`,
  `AlgebraicGeometry.finrank_relativeCotangentSpace_eq_fiberRelativeCotangentSpace` and
  `AlgebraicGeometry.finrank_relativeCotangentSpace_eq_finrank_dottedTangentArrow`: that `r` is
  finite, and the two further descriptions of it the source gives.
* `AlgebraicGeometry.exists_affineOpen_immersion_into_affineSpace`: an affine open neighbourhood
  of the point lying over the chosen affine open of the base immerses into relative affine
  `(r + 1)`-space over that open, compatibly with the morphism.
* `AlgebraicGeometry.exists_closedImmersion_smoothFactorization`: the same neighbourhood is a
  closed subscheme of a scheme smooth of relative dimension `r` over that open, through which
  the morphism factors.

## Implementation notes

Affine `d`-space is indexed by `ULift (Fin d)`, placing the coordinate type in the universe of
the schemes. In the first result, the equality of composites into `S` together with the
containment of the chosen open in the inverse image of `V` expresses the factorization over
`V`, and quasi-finiteness is spelled out as local finite type, local quasi-finiteness and
quasi-compactness. In the second, the induced morphism of fibres is specified by its two
projections, which characterize the canonical map between the pullbacks defining them.

The integer `r` of the unramified factorization is the dimension over `κ(x)` of
`Stacks.SmoothAtJacobian.relativeCotangentSpace`, the residue-field fibre at `x` of the stalk of
the sheaf of relative differentials. Its finiteness comes from [Stacks, Tag 01V2] read at a
point, which is `Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk`: the
sheaf-level finite type statement does not give it directly, since finite type of a
quasi-coherent module is detected on affine charts and carries no stalkwise consequence on its
own, so the route to the stalk is through that point-local form and then base change to `κ(x)`.
The source's two further descriptions of `r` are the fibre computed on the scheme-theoretic
fibre through `x`, identified with the first by [Stacks, Tag 01V9], and the relative tangent
space, identified with the first by [Stacks, Tag 0B2D] together with the fact that the dimension
of a dual equals the dimension of the space.

The coordinates of the factorization are produced at the level of rings. The differentials of
the local ring at `x` over `Γ(S, ⊤)` are a localization of those of `Γ(X, ⊤)`, so they are
spanned by the differentials of global sections; `r` of those span the residue-field fibre, and
the morphism to affine `r`-space they define through
`AlgebraicGeometry.AffineSpace.homOfVector` has `Ω` relative to affine space with vanishing
fibre at `x`, hence vanishing stalk by Nakayama, hence is unramified at `x` on a principal open
by [Stacks, Tag 00UV] (6).

Tag 0CBL takes `r` to be all three of the dimensions of Tag 0CBK; the two theorems for it here
assume only the first of those equalities, the other two being
`AlgebraicGeometry.finrank_relativeCotangentSpace_eq_fiberRelativeCotangentSpace` and
`AlgebraicGeometry.finrank_relativeCotangentSpace_eq_finrank_dottedTangentArrow` above. The
proof follows the source. A local form of Tag 0CBK gives, on an affine neighbourhood of the
point lying over the chosen affine open `V` of the base, a morphism to relative affine `r`-space
over `V` unramified at the point; the dimension `r` does not change under that restriction
because it and the restricted morphism are read on the same affine chart, which is
`finrank_relativeCotangentSpace_resLE`. Tag 0CBJ then presents a smaller affine neighbourhood as
a locally closed subscheme of the affine line over affine `r`-space, and that affine line is
affine `(r + 1)`-space over `V`, which is `affineSpaceSuccIso`. The neighbourhood produced is an
open of the chart rather than of the source, and is carried back by
`AlgebraicGeometry.Scheme.Hom.isoImage`. For the second clause the target of the immersion is
shrunk by `AlgebraicGeometry.Scheme.Hom.liftCoborder`, which makes it a closed immersion into an
open subscheme; an open subscheme of a scheme smooth of relative dimension `r` over `V` is still
smooth of relative dimension `r` over `V`.

## References

* [Stacks Project, Tag 0CBH](https://stacks.math.columbia.edu/tag/0CBH)
* [Stacks Project, Tag 0CBI](https://stacks.math.columbia.edu/tag/0CBI)
* [Stacks Project, Tag 0CBJ](https://stacks.math.columbia.edu/tag/0CBJ)
* [Stacks Project, Tag 0CBK](https://stacks.math.columbia.edu/tag/0CBK)
* [Stacks Project, Tag 0CBL](https://stacks.math.columbia.edu/tag/0CBL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry


private theorem relativeDimensionAt_eq_of_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] :
    Algebra.relativeDimensionAt R q =
      _root_.relativeDimensionAt R S
        (PrimeSpectrum.comap (algebraMap R S) (⟨q, ‹_›⟩ : PrimeSpectrum S)).asIdeal
        (PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨⟨q, ‹_›⟩, rfl⟩) := by
  rw [_root_.relativeDimensionAt, krullDimAt_eq_topologicalKrullDimAt,
    ← topologicalKrullDimAt_eq_of_homeomorph, Algebra.relativeDimensionAt]

private theorem comap_fiberMap_preimageHomeomorphFiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] :
    PrimeSpectrum.comap
        (_root_.fiberMap R S
          (PrimeSpectrum.comap (algebraMap R S) (⟨q, ‹_›⟩ : PrimeSpectrum S)).asIdeal)
        (PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨⟨q, ‹_›⟩, rfl⟩) = ⟨q, ‹_›⟩ := by
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R S) (⟨q, ‹_›⟩ : PrimeSpectrum S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  let x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) := ⟨⟨q, ‹_›⟩, rfl⟩
  have key : ((e.symm (e x) : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) :
      PrimeSpectrum S) = PrimeSpectrum.comap (_root_.fiberMap R S p.asIdeal) (e x) := rfl
  rw [← key, e.symm_apply_apply]

/-- Relative Noether normalization on an affine neighbourhood of a point. -/
@[stacks 0CBH, ega "IV 13.3.1.1" "quasi-finite factoriz."]
theorem exists_affineOpen_quasiFinite_affineSpace_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (V : S.affineOpens) (hxV : f x ∈ V.1) (d : ℕ)
    (hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ (U : X.affineOpens) (_hxU : x ∈ U.1)
      (_hUV : U.1 ≤ f ⁻¹ᵁ V.1)
      (π : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.1.toScheme),
      (π ≫ (AffineSpace.over (ULift.{u} (Fin d)) V.1.toScheme).hom ≫ V.1.ι =
        U.1.ι ≫ f) ∧
      ((LocallyOfFiniteType π ∧ QuasiCompact π) ∧ LocallyQuasiFinite π) := by
  classical
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      hxV (f ⁻¹ᵁ V.1).isOpen
  let W : X.affineOpens := ⟨W₀, hW₀⟩
  let R := Γ(S, V.1)
  let A := Γ(X, W.1)
  let F := f.appLE V.1 W.1 hWV
  let : Algebra R A := F.hom.toAlgebra
  have hft : F.hom.FiniteType := f.finiteType_appLE V.2 W.2 hWV
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hft
  let q : PrimeSpectrum A := W.2.primeIdealOf ⟨x, hxW⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  let qbar : PrimeSpectrum (p.asIdeal.Fiber A) :=
    PrimeSpectrum.preimageHomeomorphFiber R A p ⟨q, rfl⟩
  let : p.asIdeal.IsPrime := p.isPrime
  have hdim_chart : Algebra.relativeDimensionAt R q.asIdeal = (d : WithBot ℕ∞) := by
    rwa [← fiberDimensionAt_eq_relativeDimensionAt_chart f V W hWV x hxW]
  have hdim : _root_.relativeDimensionAt R A p.asIdeal qbar =
      ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [← relativeDimensionAt_eq_of_fiber (R := R) (S := A) q.asIdeal, hdim_chart]
    norm_cast
  obtain ⟨g, hg, φ, hφ, hφft, hφqf⟩ :=
    quasiFinite_over_polynomial_of_relativeDimension R A q p.asIdeal qbar
      (comap_fiberMap_preimageHomeomorphFiber q.asIdeal) d hdim
  let U : X.affineOpens := ⟨X.basicOpen g, W.2.basicOpen g⟩
  have hUaff : IsAffineOpen U.1 := U.2
  have hVaff : IsAffineOpen V.1 := V.2
  have hWU : U.1 ≤ W.1 := X.basicOpen_le g
  have hUV : U.1 ≤ f ⁻¹ᵁ V.1 := hWU.trans hWV
  have hxU : x ∈ U.1 := by
    change x ∈ X.basicOpen g
    have hqx : W.2.fromSpec q = x := W.2.fromSpec_primeIdealOf ⟨x, hxW⟩
    rw [← hqx]
    change q ∈ W.2.fromSpec ⁻¹ᵁ X.basicOpen g
    rw [W.2.fromSpec_preimage_basicOpen]
    change g ∉ q.asIdeal
    exact hg
  let B := Γ(X, U.1)
  let ρ := f.appLE V.1 U.1 hUV
  let : Algebra R B := ρ.hom.toAlgebra
  have hrestring : F ≫ X.presheaf.map (homOfLE hWU).op = ρ := by
    simpa [F, ρ] using Scheme.Hom.appLE_map f hWV (homOfLE hWU).op
  let : IsLocalization.Away g B := W.2.isLocalization_basicOpen g
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    change ρ.hom r = (X.presheaf.map (homOfLE hWU).op).hom (F.hom r)
    exact congrArg (fun k : CommRingCat.Hom R B => k.hom r) hrestring.symm
  let e : Localization.Away g ≃ₐ[A] B :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) B
  let ren : MvPolynomial (ULift.{u} (Fin d)) R ≃ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  let φ' : MvPolynomial (ULift.{u} (Fin d)) R →+* Localization.Away g :=
    φ.comp ren.toRingHom
  have hφ'ft : φ'.FiniteType :=
    hφft.comp (RingHom.FiniteType.of_surjective _ ren.surjective)
  have hφ'qf : φ'.QuasiFinite :=
    hφqf.comp (RingHom.QuasiFinite.of_finite ren.toRingEquiv.finite)
  let θ : MvPolynomial (ULift.{u} (Fin d)) R →+* B := e.toRingHom.comp φ'
  have hθft : θ.FiniteType :=
    (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).comp hφ'ft
  have hθqf : θ.QuasiFinite :=
    (RingHom.QuasiFinite.of_finite e.toRingEquiv.finite).comp hφ'qf
  let : IsScalarTower R A (Localization.Away g) := inferInstance
  have hbase : θ.comp (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin d)) R) = ρ.hom := by
    ext r
    change e (φ (ren (MvPolynomial.C r))) = ρ.hom r
    have hrenC : ren (MvPolynomial.C r) = MvPolynomial.C r := by
      change ren (algebraMap R (MvPolynomial (ULift.{u} (Fin d)) R) r) = _
      exact ren.commutes r
    rw [hrenC, show φ (MvPolynomial.C r) = algebraMap R (Localization.Away g) r from
      RingHom.congr_fun hφ r]
    change e (algebraMap R (Localization.Away g) r) = algebraMap R B r
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away g), e.commutes]
    exact (IsScalarTower.algebraMap_apply R A B r).symm
  let m := Spec.map (CommRingCat.ofHom θ)
  have hmft : LocallyOfFiniteType m :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hθft
  have hmqf : LocallyQuasiFinite m :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr hθqf
  have hmqc : QuasiCompact m := by
    let : IsAffineHom m := inferInstance
    infer_instance
  let mapIso : AffineSpace (ULift.{u} (Fin d)) (Spec R) ≅
      AffineSpace (ULift.{u} (Fin d)) V.1.toScheme := {
    hom := AffineSpace.map (ULift.{u} (Fin d)) hVaff.isoSpec.inv
    inv := AffineSpace.map (ULift.{u} (Fin d)) hVaff.isoSpec.hom
    hom_inv_id := by
      rw [← AffineSpace.map_comp, hVaff.isoSpec.inv_hom_id, AffineSpace.map_id]
    inv_hom_id := by
      rw [← AffineSpace.map_comp, hVaff.isoSpec.hom_inv_id, AffineSpace.map_id]
  }
  let targetIso : Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin d)) R)) ≅
      AffineSpace (ULift.{u} (Fin d)) V.1.toScheme :=
    (AffineSpace.SpecIso (ULift.{u} (Fin d)) R).symm ≪≫ mapIso
  let π : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.1.toScheme :=
    hUaff.isoSpec.hom ≫ m ≫ targetIso.hom
  have htarget : targetIso.hom ≫
      (AffineSpace.over (ULift.{u} (Fin d)) V.1.toScheme).hom ≫ V.1.ι =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin d)) R)) ≫ hVaff.fromSpec := by
    change (AffineSpace.SpecIso (ULift.{u} (Fin d)) R).inv ≫
        (AffineSpace.map (ULift.{u} (Fin d)) hVaff.isoSpec.inv ≫
          (𝔸(ULift.{u} (Fin d); V.1.toScheme) ↘ V.1.toScheme)) ≫ V.1.ι = _
    simp only [Category.assoc, AffineSpace.map_over_assoc,
      AffineSpace.SpecIso_inv_over_assoc, hVaff.isoSpec_inv_ι]
  have hmaps : m ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin d)) R)) = Spec.map ρ := by
    dsimp [m]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hbase]
    rfl
  have hUincl : hUaff.isoSpec.hom ≫ hUaff.fromSpec = U.1.ι := by
    rw [IsAffineOpen.fromSpec, ← Category.assoc, hUaff.isoSpec.hom_inv_id,
      Category.id_comp]
  have hfactor : π ≫
      (AffineSpace.over (ULift.{u} (Fin d)) V.1.toScheme).hom ≫ V.1.ι =
      U.1.ι ≫ f := by
    simp only [π, Category.assoc, htarget]
    rw [← Category.assoc m (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin d)) R))) hVaff.fromSpec,
      hmaps, IsAffineOpen.SpecMap_appLE_fromSpec f hVaff hUaff hUV,
      ← Category.assoc, hUincl]
  exact ⟨U, hxU, hUV, π, hfactor, ⟨⟨by dsimp [π]; infer_instance,
    by dsimp [π]; infer_instance⟩, by dsimp [π]; infer_instance⟩⟩




private lemma lift_mem_integer_adjoin_range {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) {s : Set A} {x : B} (hx : x ∈ Algebra.adjoin ℤ (g '' s)) :
    ∃ a, g a = x := by
  let R : Subalgebra ℤ B := g.toIntAlgHom.range
  have hs : g '' s ⊆ R := by
    rintro _ ⟨a, ha, rfl⟩
    exact g.toIntAlgHom.mem_range.mpr ⟨a, rfl⟩
  exact g.toIntAlgHom.mem_range.mp (Algebra.adjoin_le hs hx)

private lemma finite_normalization_coordinates {k B T : Type*} [Field k] [CommRing B]
    [CommRing T] [Algebra k T] (g : B →+* T) (s : Set B) (hs : s.Finite)
    (hgen : Algebra.adjoin k (g '' s) = ⊤) [Nontrivial T] (d : ℕ)
    (hdim : ringKrullDim T = d) :
    ∃ z : Fin d → B,
      (MvPolynomial.aeval (g ∘ z) : MvPolynomial (Fin d) k →ₐ[k] T).Finite := by
  obtain ⟨r, y, hy, hinj, hfin, hr⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top k (hs.image g) hgen
  have hrd : r = d := by
    exact_mod_cast hr.symm.trans hdim
  subst d
  let z : Fin r → B := fun i => Classical.choose
    (lift_mem_integer_adjoin_range g (hy i))
  refine ⟨z, ?_⟩
  convert hfin using 1
  congr 1
  funext i
  exact Classical.choose_spec (lift_mem_integer_adjoin_range g (hy i))

private lemma finite_generators_after_tensor {A k B : Type*} [CommRing A] [CommRing k]
    [CommRing B] [Algebra A k] [Algebra A B] [Algebra.FiniteType A B] :
    ∃ s : Set B, s.Finite ∧ Algebra.adjoin k
      ((Algebra.TensorProduct.includeRight (A := k) : B →ₐ[A] (TensorProduct A k B)) '' s) = ⊤ := by
  have hfg : (⊤ : Subalgebra A B).FG := Algebra.FiniteType.out
  obtain ⟨s, hs, hgen⟩ := Subalgebra.fg_def.mp hfg
  refine ⟨s, hs, ?_⟩
  change Algebra.adjoin k ((fun x : B => (1 : k) ⊗ₜ[A] x) '' s) = ⊤
  exact Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (R := A) (A := k) s hgen

private lemma affine_ring_noether_normalization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (p : PrimeSpectrum A) (d : ℕ)
    (hdim : ringKrullDim (p.asIdeal.Fiber B) = d) :
    ∃ y : Fin d → B,
      (MvPolynomial.aeval
        (fun i => Algebra.TensorProduct.includeRight (A := p.asIdeal.ResidueField) (y i)) :
        MvPolynomial (Fin d) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
          p.asIdeal.Fiber B).Finite := by
  let k := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber B
  let : Algebra A k := inferInstance
  let : Algebra k T := inferInstance
  have hsub : ¬ Subsingleton T := by
    intro h
    have hb : ringKrullDim T = ⊥ := ringKrullDim_eq_bot_of_subsingleton
    rw [hdim] at hb
    exact (by simp : (d : WithBot ℕ∞) ≠ ⊥) hb
  let : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsub
  obtain ⟨s, hs, hgen⟩ :=
    finite_generators_after_tensor (A := A) (k := k) (B := B)
  let g : B →+* T := (Algebra.TensorProduct.includeRight (A := k) : B →ₐ[A] T).toRingHom
  exact finite_normalization_coordinates (k := k) g s hs hgen d hdim

private noncomputable def fiberIsoOfIsos {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (eX : X ≅ Y) (eS : S ≅ T) (g : Y ⟶ T)
    (hfac : eX.hom ≫ g = f ≫ eS.hom) (s : S) :
    f.fiber s ≅ g.fiber (eS.hom s) := by
  let eκ := eS.hom.residueFieldMap s
  letI : IsIso eX.hom := eX.isIso_hom
  letI : IsIso eS.hom := eS.isIso_hom
  letI : IsOpenImmersion eS.hom := IsOpenImmersion.of_isIso eS.hom
  letI : IsIso eκ := inferInstance
  letI : IsIso (Spec.map eκ) := by infer_instance
  let m := pullback.map f (S.fromSpecResidueField s) g
    (T.fromSpecResidueField (eS.hom s)) eX.hom (Spec.map eκ) eS.hom
    hfac.symm (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField eS.hom s).symm
  exact @asIso _ _ _ _ m (pullback.map_isIso _ _ _ _ _ _ _ _ _)

private noncomputable def affineFiberRingIso {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] (s : S)
    [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom)
    [hp : (S.isoSpec.hom s).asIdeal.IsPrime] :
    f.fiber s ≅ Spec (.of ((S.isoSpec.hom s).asIdeal.Fiber Γ(X, ⊤))) := by
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let p : PrimeSpectrum A := S.isoSpec.hom s
  letI : p.asIdeal.IsPrime := p.2
  let hf := CommRingCat.ofHom (algebraMap A B)
  have hφ : f.appTop = hf := by ext b; exact congrArg (fun m : A →+* B => m b) halg.symm
  let eBase := fiberIsoOfIsos f X.isoSpec S.isoSpec (Spec.map hf)
    (by simpa only [← hφ] using Scheme.isoSpec_hom_naturality f) s
  exact eBase.trans (asIso (Spec.fiberToSpecResidueFieldIso A B p).hom.left)

private lemma fiber_dimension_eq_ring_dimension {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] (s : S)
    [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom)
    [hp : (S.isoSpec.hom s).asIdeal.IsPrime] :
    ringKrullDim ((S.isoSpec.hom s).asIdeal.Fiber Γ(X, ⊤)) =
      topologicalKrullDim (f.fiber s) := by
  let e := Scheme.homeoOfIso (affineFiberRingIso f s halg)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

/-- A morphism locally of finite type between affine schemes makes `Γ(X, ⊤)` a finite type
algebra over `Γ(S, ⊤)`. -/
private theorem finiteType_algebra_appTop {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X]
    [IsAffine S] [LocallyOfFiniteType f] :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance)

/-- Noether normalization for a finite-type map of affine schemes at a chosen fibre. -/
@[stacks 0CBI]
theorem exists_factorization_finite_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] [QuasiCompact f]
    (s : S) (d : ℕ) (hd : topologicalKrullDim (f.fiber s) = d) :
    ∃ π : X ⟶ 𝔸(ULift (Fin d); S),
      (π ≫ 𝔸(ULift (Fin d); S) ↘ S = f) ∧
      ∃ πs : f.fiber s ⟶ (𝔸(ULift (Fin d); S) ↘ S).fiber s,
        (πs ≫ (𝔸(ULift (Fin d); S) ↘ S).fiberι s = f.fiberι s ≫ π) ∧
        (πs ≫ (𝔸(ULift (Fin d); S) ↘ S).fiberToSpecResidueField s =
          f.fiberToSpecResidueField s) ∧
        IsFinite πs := by
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  let : Algebra.FiniteType A B := finiteType_algebra_appTop f
  let p : PrimeSpectrum A := S.isoSpec.hom s
  let : p.asIdeal.IsPrime := p.2
  have hdRing : ringKrullDim (p.asIdeal.Fiber B) = d :=
    (fiber_dimension_eq_ring_dimension f s rfl).trans hd
  obtain ⟨y, hfin⟩ := affine_ring_noether_normalization p d hdRing
  let ψFin : MvPolynomial (Fin d) A →ₐ[A] B := MvPolynomial.aeval y
  let e : ULift (Fin d) ≃ Fin d := Equiv.ulift
  let z : ULift (Fin d) → B := fun i => y (e i)
  let ψ : MvPolynomial (ULift (Fin d)) A →ₐ[A] B := MvPolynomial.aeval z
  let k := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber B
  let θFin : MvPolynomial (Fin d) k →ₐ[k] T := MvPolynomial.aeval
    (fun i => Algebra.TensorProduct.includeRight (A := k) (ψFin (.X i)))
  let θULift : MvPolynomial (ULift (Fin d)) k →ₐ[k] T := MvPolynomial.aeval
    (fun i => Algebra.TensorProduct.includeRight (A := k) (ψ (.X i)))
  let rename := MvPolynomial.renameEquiv k (Equiv.ulift : ULift (Fin d) ≃ Fin d)
  have hθ : θFin.comp rename.toAlgHom = θULift := by
    ext i
    simp only [AlgHom.comp_apply, θFin, θULift, rename, MvPolynomial.aeval_X]
    simp [ψFin, ψ, z, e]
  have hθfinite : θULift.Finite := by
    rw [← hθ]
    have hfinθ : θFin.Finite := by simpa only [θFin, ψFin, MvPolynomial.aeval_X] using hfin
    exact RingHom.Finite.comp hfinθ (RingHom.Finite.of_surjective _ rename.surjective)
  let π : X ⟶ 𝔸(ULift (Fin d); S) :=
    AffineSpace.homOfVector f
      (fun i => X.isoSpec.hom.appTop
        ((Scheme.ΓSpecIso (.of B)).inv (ψ (.X i))))
  have hfactor : π ≫ 𝔸(ULift (Fin d); S) ↘ S = f := by
    simp [π, AffineSpace.homOfVector_over]
  let πs : f.fiber s ⟶ (𝔸(ULift (Fin d); S) ↘ S).fiber s :=
    pullback.lift (f.fiberι s ≫ π) (f.fiberToSpecResidueField s) (by
      rw [Category.assoc, hfactor]
      exact f.fiber_fac s)
  refine ⟨π, hfactor, πs, ?_, ?_, ?_⟩
  · change pullback.lift (f.fiberι s ≫ π) (f.fiberToSpecResidueField s) _ ≫
      pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  · change pullback.lift (f.fiberι s ≫ π) (f.fiberToSpecResidueField s) _ ≫
      pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  · let hf : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (algebraMap A B)
    have hφ : f.appTop = hf := by
      ext b
      simp [hf, RingHom.algebraMap_toAlgebra]
    let eSourceBase := fiberIsoOfIsos f X.isoSpec S.isoSpec (Spec.map hf)
      (by
        calc
          X.isoSpec.hom ≫ Spec.map hf = X.isoSpec.hom ≫ Spec.map (f.appTop) := by
            congr 1
          _ = f ≫ S.isoSpec.hom := Scheme.isoSpec_hom_naturality f) s
    let eSourceSpecArrow := Spec.fiberToSpecResidueFieldIso A B p
    have : IsIso eSourceSpecArrow.hom := eSourceSpecArrow.isIso_hom
    let eSpecFiber := (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberToSpecResidueField p
    let eSourceSpec := eSourceSpecArrow.hom.left
    have : IsIso eSourceSpec := Arrow.isIso_left eSourceSpecArrow.hom
    have hsourceArrow' : eSourceSpec ≫
        Spec.map (CommRingCat.ofHom (algebraMap k T)) =
        eSpecFiber ≫ eSourceSpecArrow.hom.right := eSourceSpecArrow.hom.w
    let eSource := eSourceBase.trans
      (@asIso _ _ _ _ eSourceSpec (Arrow.isIso_left eSourceSpecArrow.hom))
    let incl := (Algebra.TensorProduct.includeRight (A := k) : B →ₐ[A] T).toRingHom
    have hSourceBase : eSourceBase.hom ≫ eSpecFiber =
        f.fiberToSpecResidueField s ≫
          Spec.map (Scheme.Hom.residueFieldMap S.isoSpec.hom s) := by
      dsimp only [eSourceBase, fiberIsoOfIsos, eSpecFiber,
        Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField, asIso_hom, pullback.map]
      exact pullback.lift_snd _ _ _
    have hSourceB : eSourceSpec ≫
        Spec.map (CommRingCat.ofHom incl) =
        pullback.fst (Spec.map hf) ((Spec A).fromSpecResidueField p) := by
      let fB := Spec.map (CommRingCat.ofHom (algebraMap A B))
      let fK := Spec.map (CommRingCat.ofHom (algebraMap A k))
      let fIso := Spec.map (Scheme.Spec.residueFieldIso A p).inv
      let g := (Spec A).fromSpecResidueField p
      have hbase : fIso ≫ fK = g := by
        simpa only [fIso, fK, g] using
          Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField A p
      let eC : pullback g fB ≅ pullback (fIso ≫ fK) fB :=
        pullback.congrHom hbase.symm rfl
      let m : pullback (fIso ≫ fK) fB ≅ pullback fK fB := asIso
        (pullback.map (fIso ≫ fK) fB fK fB fIso (𝟙 _) (𝟙 _) (by simp) (by simp))
      let eL := pullbackSymmetry fB g ≪≫ (eC ≪≫ m) ≪≫ pullbackSpecIso A k B
      change eL.hom ≫ _ = _
      simp [eL, eC, m, fB, fK, fIso, g, hf, incl, pullback.map, Category.assoc]
    have hSourceFst : eSourceBase.hom ≫
        pullback.fst (Spec.map hf) ((Spec A).fromSpecResidueField p) =
        f.fiberι s ≫ X.isoSpec.hom := by
      dsimp only [eSourceBase, fiberIsoOfIsos, pullback.map]
      exact pullback.lift_fst _ _ _
    have hSourceComp : eSource.hom ≫ Spec.map (CommRingCat.ofHom incl) =
        f.fiberι s ≫ X.isoSpec.hom := by
      simpa only [eSource, Iso.trans_hom, asIso_hom, Category.assoc] using
        congrArg (fun m => eSourceBase.hom ≫ m) hSourceB |>.trans hSourceFst
    have hSourceCoord (i : ULift (Fin d)) :
        eSource.hom.appTop ((Scheme.ΓSpecIso
          (.of (TensorProduct A k B))).inv
          (CommRingCat.ofHom incl (ψ (.X i)))) =
        (f.fiberι s ≫ π).appTop (AffineSpace.coord S i) := by
      have h := congrArg (fun m => m.appTop ((Scheme.ΓSpecIso (.of B)).inv (ψ (.X i))))
        hSourceComp
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      have hnat : (Spec.map (CommRingCat.ofHom incl)).appTop
          ((Scheme.ΓSpecIso (.of B)).inv (ψ (.X i))) =
          (Scheme.ΓSpecIso (.of (TensorProduct A k B))).inv
            (CommRingCat.ofHom incl (ψ (.X i))) := by
        simpa only [CommRingCat.comp_apply] using
          (congrArg (fun m => m (ψ (.X i)))
            (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom incl))).symm
      change eSource.hom.appTop ((Spec.map (CommRingCat.ofHom incl)).appTop
        ((Scheme.ΓSpecIso (.of B)).inv (ψ (.X i)))) = _ at h
      rw [hnat, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simpa [π, AffineSpace.homOfVector_appTop_coord, ConcreteCategory.comp_apply] using h
    have hπsFst : πs ≫ pullback.fst
        (𝔸(ULift (Fin d); S) ↘ S) (S.fromSpecResidueField s) =
        f.fiberι s ≫ π := by
      dsimp only [πs, Scheme.Hom.fiber, Scheme.Hom.fiberι]
      exact pullback.lift_fst _ _ _
    let g : 𝔸(ULift (Fin d); S) ⟶ S := 𝔸(ULift (Fin d); S) ↘ S
    let eTargetBase : g.fiber s ≅ 𝔸(ULift (Fin d); Spec (S.residueField s)) :=
      (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).isoIsPullback
      _ _ (AffineSpace.isPullback_map (n := ULift (Fin d)) (S.fromSpecResidueField s))
    let eκ := Scheme.Hom.residueFieldMap S.isoSpec.hom s
    have : IsIso eκ := inferInstance
    let eκRingEquiv :=
      ((Scheme.Spec.residueFieldIso A p).symm.trans (asIso eκ)).commRingCatIsoToRingEquiv
    let ePoly := MvPolynomial.mapEquiv (ULift (Fin d)) eκRingEquiv
    have hPolySymm : ePoly.symm = MvPolynomial.mapEquiv (ULift (Fin d)) eκRingEquiv.symm := by
      ext x
      simp [ePoly]
    let eTargetPoly :=
      (AffineSpace.SpecIso (ULift (Fin d)) (CommRingCat.of (S.residueField s))).trans
        (Scheme.Spec.mapIso ePoly.toCommRingCatIso.op)
    have hTargetPolyCoord (i : ULift (Fin d)) :
        eTargetPoly.inv.appTop
          (AffineSpace.coord (Spec (CommRingCat.of (S.residueField s))) i) =
        (Scheme.ΓSpecIso (.of (MvPolynomial (ULift (Fin d)) k))).inv (.X i) := by
      change (Spec.map (CommRingCat.ofHom ePoly.symm.toRingHom)).appTop
          ((AffineSpace.SpecIso (ULift (Fin d))
            (CommRingCat.of (S.residueField s))).inv.appTop
              (AffineSpace.coord (Spec (CommRingCat.of (S.residueField s))) i)) = _
      rw [AffineSpace.SpecIso_inv_appTop_coord]
      have he : ePoly.symm (.X i) = (.X i) := by simp [ePoly]
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      congr 1
    let specθ := Spec.map (CommRingCat.ofHom θULift.toRingHom)
    have hcoeffRing :
        CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
            MvPolynomial (ULift (Fin d)) ↑(S.residueField s)) ≫
          CommRingCat.ofHom ePoly.symm.toRingHom ≫
          CommRingCat.ofHom θULift.toRingHom =
        CommRingCat.ofHom ((algebraMap k T).comp eκRingEquiv.symm.toRingHom) := by
      apply CommRingCat.hom_ext
      ext x
      change θULift.toRingHom (ePoly.symm (MvPolynomial.C x)) =
        algebraMap k T (eκRingEquiv.symm x)
      rw [show ePoly.symm (MvPolynomial.C x) =
          algebraMap k (MvPolynomial (ULift (Fin d)) k) (eκRingEquiv.symm x) by
        simp [ePoly]]
      exact θULift.commutes _
    have hcoeff :
        Spec.map (CommRingCat.ofHom θULift.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ePoly.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
            MvPolynomial (ULift (Fin d)) ↑(S.residueField s))) =
        Spec.map (CommRingCat.ofHom ((algebraMap k T).comp eκRingEquiv.symm.toRingHom)) := by
      rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
      change Spec.map ((CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
          MvPolynomial (ULift (Fin d)) ↑(S.residueField s)) ≫
        CommRingCat.ofHom ePoly.symm.toRingHom) ≫
        CommRingCat.ofHom θULift.toRingHom) = _
      exact congrArg Spec.map hcoeffRing
    rw [hPolySymm] at hcoeff
    have hSourcePoly :
        Arrow.Hom.left eSourceSpecArrow.hom ≫
          Spec.map (CommRingCat.ofHom θULift.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ePoly.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
            MvPolynomial (ULift (Fin d)) ↑(S.residueField s))) =
        eSpecFiber ≫
          eSourceSpecArrow.hom.right ≫
          Spec.map (CommRingCat.ofHom eκRingEquiv.symm.toRingHom) := by
      calc
        _ = eSourceSpec ≫ Spec.map
            (CommRingCat.ofHom ((algebraMap k T).comp eκRingEquiv.symm.toRingHom)) := by
              change eSourceSpec ≫ (Spec.map (CommRingCat.ofHom θULift.toRingHom) ≫
                Spec.map (CommRingCat.ofHom ePoly.symm.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
                  MvPolynomial (ULift (Fin d)) ↑(S.residueField s)))) = _
              exact congrArg (fun m => eSourceSpec ≫ m) hcoeff
        _ = eSourceSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) ≫
            Spec.map (CommRingCat.ofHom eκRingEquiv.symm.toRingHom) :=
          congrArg (fun m => eSourceSpec ≫ m)
                (AlgebraicGeometry.Spec.map_comp
                  (CommRingCat.ofHom eκRingEquiv.symm.toRingHom)
                  (CommRingCat.ofHom (algebraMap k T)))
        _ = _ := by
          change (eSourceSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap k T))) ≫
            Spec.map (CommRingCat.ofHom eκRingEquiv.symm.toRingHom) = _
          rw [hsourceArrow']
          exact Category.assoc _ _ _
    let eTarget : g.fiber s ≅
        Scheme.Spec.obj (Opposite.op (CommRingCat.of (MvPolynomial (ULift (Fin d)) k))) :=
      eTargetBase.trans eTargetPoly
    have hcomm : eSource.hom ≫ specθ = πs ≫ eTarget.hom := by
      apply (cancel_mono eTargetPoly.inv).1
      dsimp only [eTarget, Iso.trans_hom]
      simp only [Scheme.Spec_obj, CategoryTheory.Arrow.mk_left, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
      apply AffineSpace.hom_ext
      · have hTargetBase : eTargetBase.hom ≫
            (𝔸(ULift (Fin d); Spec (S.residueField s)) ↘ Spec (S.residueField s)) =
              g.fiberToSpecResidueField s := by
          simp [eTargetBase, Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField]
        simp only [Category.assoc]
        change (eSource.hom ≫ specθ) ≫ eTargetPoly.inv ≫
            (𝔸(ULift (Fin d); Spec (S.residueField s)) ↘ Spec (S.residueField s)) =
          πs ≫ eTargetBase.hom ≫
            (𝔸(ULift (Fin d); Spec (S.residueField s)) ↘ Spec (S.residueField s))
        rw [hTargetBase]
        have hTargetPolyBase : eTargetPoly.inv ≫
            (𝔸(ULift (Fin d); Spec (S.residueField s)) ↘ Spec (S.residueField s)) =
            Spec.map (CommRingCat.ofHom
              ((MvPolynomial.mapEquiv (ULift (Fin d)) eκRingEquiv.symm).toRingHom)) ≫
              Spec.map (CommRingCat.ofHom (MvPolynomial.C : ↑(S.residueField s) →+*
                MvPolynomial (ULift (Fin d)) ↑(S.residueField s))) := by
          simp only [eTargetPoly, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
            Scheme.Spec_map, Quiver.Hom.unop_op,
            RingEquiv.toCommRingCatIso_inv, Category.assoc]
          change Spec.map (CommRingCat.ofHom ePoly.symm.toRingHom) ≫
              (AffineSpace.SpecIso (ULift (Fin d))
                (CommRingCat.of (S.residueField s))).inv ≫
              (𝔸(ULift (Fin d); Spec (CommRingCat.of (S.residueField s))) ↘
                Spec (CommRingCat.of (S.residueField s))) = _
          rw [AffineSpace.SpecIso_inv_over (n := ULift (Fin d))
            (CommRingCat.of (S.residueField s)), hPolySymm]
        rw [Category.assoc, hTargetPolyBase]
        simp only [eSource, Iso.trans_hom, asIso_hom, specθ, Category.assoc]
        have hpoly := congrArg (fun m => eSourceBase.hom ≫ m) hSourcePoly
        rw [hPolySymm] at hpoly
        have hleft : Arrow.Hom.left eSourceSpecArrow.hom = eSourceSpec := rfl
        rw [hleft] at hpoly
        rw [hpoly, ← Category.assoc, hSourceBase]
        have hright : Arrow.Hom.right eSourceSpecArrow.hom =
            Spec.map (Scheme.Spec.residueFieldIso A p).inv := by
          dsimp [eSourceSpecArrow, Spec.fiberToSpecResidueFieldIso]
          rfl
        have hring : CommRingCat.ofHom eκRingEquiv.symm.toRingHom ≫
            (Scheme.Spec.residueFieldIso A p).inv ≫ eκ = 𝟙 _ := by
          apply CommRingCat.hom_ext
          ext x
          change eκRingEquiv (eκRingEquiv.symm x) = x
          exact eκRingEquiv.apply_symm_apply x
        have hcancel : Spec.map eκ ≫ Arrow.Hom.right eSourceSpecArrow.hom ≫
            Spec.map (CommRingCat.ofHom eκRingEquiv.symm.toRingHom) = 𝟙 _ := by
          rw [hright, ← Spec.map_comp, ← Spec.map_comp]
          simpa only [CommRingCat.of_carrier, Spec.map_id, Category.assoc] using
            congrArg Spec.map hring
        rw [Category.assoc, hcancel, Category.comp_id]
        dsimp only [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber, πs]
        exact (pullback.lift_snd _ _ _).symm
      · intro i
        have hTargetFst : eTargetBase.hom ≫ AffineSpace.map (ULift (Fin d))
            (S.fromSpecResidueField s) = pullback.fst g (S.fromSpecResidueField s) :=
          (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).isoIsPullback_hom_fst
            _ _ (AffineSpace.isPullback_map (n := ULift (Fin d)) (S.fromSpecResidueField s))
        have hTargetCoord' : eTargetBase.hom.appTop
            (AffineSpace.coord (Spec (CommRingCat.of ↑(S.residueField s))) i) =
            (pullback.fst g (S.fromSpecResidueField s)).appTop (AffineSpace.coord S i) := by
          have h := congrArg (fun m => m.appTop (AffineSpace.coord S i)) hTargetFst
          rwa [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            AffineSpace.map_appTop_coord] at h
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        rw [hTargetCoord', hTargetPolyCoord]
        have hθCoord : specθ.appTop
            ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift (Fin d)) k))).inv (.X i)) =
            (Scheme.ΓSpecIso (.of T)).inv (θULift (.X i)) := by
          change (Spec.map (CommRingCat.ofHom θULift.toRingHom)).appTop
              ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift (Fin d)) k))).inv (.X i)) = _
          rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
            CommRingCat.comp_apply]
          congr 1
        rw [hθCoord]
        have hθX : θULift (.X i) = incl (ψ (.X i)) := by
          simp [θULift, incl]
        have hSourceCoord' : eSource.hom.appTop
            ((Scheme.ΓSpecIso (.of T)).inv (θULift (.X i))) =
            (Scheme.Hom.fiberι f s ≫ π).appTop (AffineSpace.coord S i) := by
          rw [hθX]
          change (ConcreteCategory.hom (Scheme.Hom.appTop eSource.hom))
              ((ConcreteCategory.hom (Scheme.ΓSpecIso
                (CommRingCat.of (TensorProduct A k B))).inv)
                (incl (ψ (MvPolynomial.X i)))) = _
          exact hSourceCoord i
        rw [hSourceCoord']
        exact (congrArg (fun m => m.appTop (AffineSpace.coord S i)) hπsFst).symm
    have : IsFinite specθ := (IsFinite.SpecMap_iff _).2 hθfinite
    let : IsIso eSource.hom := eSource.isIso_hom
    have : IsIso eTarget.inv := eTarget.symm.isIso_hom
    have : IsFinite eSource.hom := inferInstance
    have : IsFinite eTarget.inv := inferInstance
    have hEq : eSource.hom ≫ specθ ≫ eTarget.inv = πs := by
      simpa [Category.assoc] using
        congrArg (fun m => m ≫ eTarget.inv) hcomm
    rw [← hEq]
    infer_instance

/-! ### Factoring through affine space by a morphism unramified at a point -/

section UnramifiedFactorization

open scoped TensorProduct
open Stacks.SmoothAtJacobian (relativeCotangentSpace fiberRelativeCotangentSpace
  relativeDifferentialStalk)
open Stacks.RelativeDifferentialStalkMap (algebraStalkMap
  relativeDifferentialsStalkKaehlerEquiv)

/-- `κ(x)` as an algebra over the local ring at `x`, through the residue map. This is the
action over which `Stacks.SmoothAtJacobian.relativeCotangentSpace` is formed. -/
private noncomputable abbrev residueMapAlgebra {X : Scheme.{u}} (x : X) :
    Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

attribute [local instance] residueMapAlgebra residueSMulComm residueSMulComm'
attribute [local instance] Stacks.SmoothAtJacobian.relativeDifferentialStalkModule

/-- Scalars from the local ring at `x` act on `κ(x)` through `κ(x)` itself. -/
private noncomputable abbrev residueMapTower {X : Scheme.{u}} (x : X) :
    IsScalarTower (X.presheaf.stalk x) (X.residueField x) (X.residueField x) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] residueMapTower

/-- **Stacks Project, Tag 0CBK, finiteness of `r`.** For a morphism locally of finite type the
residue-field fibre at `x` of the stalk of the sheaf of relative differentials is a
finite-dimensional `κ(x)`-vector space, so the integer `r` of the tag is defined. -/
@[stacks 0CBK "finiteness of r"]
theorem finiteDimensional_relativeCotangentSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    FiniteDimensional (X.residueField x) (relativeCotangentSpace f x) := by
  have := Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk f x
  exact Module.Finite.base_change (X.presheaf.stalk x) (X.residueField x)
    (relativeDifferentialStalk f x)

/-- **Stacks Project, Tag 0CBK, first equality defining `r`.** The residue-field fibre of the
stalk of `Ω_{X/S}` at `x` and the corresponding fibre computed on the scheme-theoretic fibre
through `x` have the same dimension over `κ(x)`:
`dim_{κ(x)} Ω_{X/S,x} ⊗ κ(x) = dim_{κ(x)} Ω_{X_s/s,x} ⊗ κ(x)`. -/
@[stacks 0CBK "first equality"]
theorem finrank_relativeCotangentSpace_eq_fiberRelativeCotangentSpace
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module.finrank (X.residueField x) (relativeCotangentSpace f x) =
      Module.finrank (X.residueField x) (fiberRelativeCotangentSpace f x) :=
  ((Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification
    f x).equiv.toLinearEquiv).finrank_eq

/-- **Stacks Project, Tag 0CBK, second equality defining `r`.** The residue-field fibre of the
stalk of `Ω_{X/S}` at `x` and the relative tangent space at `x` have the same dimension over
`κ(x)`: `dim_{κ(x)} Ω_{X/S,x} ⊗ κ(x) = dim_{κ(x)} T_{X/S,x}`. The tangent space is the
`𝒪_{X,x}`-linear dual of the stalk, which is the `κ(x)`-linear dual of the fibre. -/
@[stacks 0CBK "second equality"]
theorem finrank_relativeCotangentSpace_eq_finrank_dottedTangentArrow
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module.finrank (X.residueField x) (relativeCotangentSpace f x) =
      Module.finrank (X.residueField x) (DottedTangentArrow f x) := by
  rw [(tangentSpaceEquivCotangentSpace f x).finrank_eq]
  exact (((LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x)
      (M := relativeDifferentialStalk f x)
      (N := X.residueField x)).finrank_eq).trans
    (Subspace.dual_finrank_eq (K := X.residueField x)
      (V := relativeCotangentSpace f x))).symm

/-- A spanning family of a finite-dimensional vector space of dimension `r` contains a
subfamily indexed by `Fin r` which still spans. -/
private theorem exists_fin_spanning_subfamily {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {ι : Type*} (w : ι → W)
    (hw : Submodule.span K (Set.range w) = ⊤) (r : ℕ) (hr : Module.finrank K W = r) :
    ∃ u : Fin r → ι, Submodule.span K (Set.range (w ∘ u)) = ⊤ := by
  classical
  obtain ⟨t, hts, hspant, hindep⟩ := exists_linearIndependent K (Set.range w)
  rw [hw] at hspant
  let b : Module.Basis t K W :=
    Module.Basis.mk hindep (by rw [Subtype.range_coe]; exact hspant.ge)
  have : Finite t := Module.Finite.finite_basis b
  have hcard : Nat.card t = r := by
    rw [← hr, Module.finrank_eq_nat_card_basis b]
  let e : t ≃ Fin r := Finite.equivFinOfCardEq hcard
  choose u hu using fun i : Fin r => hts (e.symm i).2
  refine ⟨u, ?_⟩
  have hrange : Set.range (w ∘ u) = t := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      change w (u i) ∈ t
      rw [hu i]
      exact (e.symm i).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by rw [Function.comp_apply, hu (e ⟨y, hy⟩), e.symm_apply_apply]⟩
  rwa [hrange]

/-- **The ring-level content of the tag.** Let `A → B` be of finite type, let `q` be a prime of
`B` with local ring `B₀`, and let `A → P → B` be a factorization. If each `v i` comes from `P`
and the classes of the `d (v i)` span the residue-field fibre of `Ω_{B₀⁄A}`, then `P → B` is
unramified at `q`: some `B_g` with `g ∉ q` is unramified over `P`.

The differentials of `B₀` over `P` are a quotient of those over `A` by a submodule containing
every `d (v i)`, so their residue-field fibre vanishes; Nakayama makes the module itself vanish,
and [Stacks, Tag 00UV] (6) converts that into unramifiedness on a principal open. -/
private theorem exists_unramified_away_of_span_residueFibre
    {A P B B₀ : Type u} [CommRing A] [CommRing P] [CommRing B] [CommRing B₀]
    (q : Ideal B) [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    [Algebra.FiniteType A B] [q.IsPrime]
    [Algebra B B₀] [IsLocalization.AtPrime B₀ q] [IsLocalRing B₀]
    [Algebra A B₀] [IsScalarTower A B B₀]
    {ι : Type*} (v : ι → B) (hv : ∀ i, v i ∈ Set.range (algebraMap P B))
    (hspan : Submodule.span (IsLocalRing.ResidueField B₀)
        (Set.range fun i => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
          KaehlerDifferential.D A B₀ (algebraMap B B₀ (v i))) = ⊤) :
    ∃ g ∉ q, Algebra.Unramified P (Localization.Away g) := by
  classical
  let : Algebra P B₀ := ((algebraMap B B₀).comp (algebraMap P B)).toAlgebra
  have : IsScalarTower P B B₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A P B₀ := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A B₀ a = algebraMap B B₀ (algebraMap P B (algebraMap A P a))
    rw [← IsScalarTower.algebraMap_apply A P B, ← IsScalarTower.algebraMap_apply A B B₀]
  have : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType A P B
  have hφsurj : Function.Surjective (KaehlerDifferential.map A P B₀ B₀) :=
    KaehlerDifferential.map_surjective A P B₀
  have : Algebra.EssFiniteType B B₀ :=
    Algebra.EssFiniteType.of_isLocalization (R := B) (S := B₀) q.primeCompl
  have : Algebra.EssFiniteType P B := Algebra.EssFiniteType.of_finiteType P B
  have : Algebra.EssFiniteType P B₀ := Algebra.EssFiniteType.comp P B B₀
  -- the residue-field fibre of `Ω[B₀⁄P]` vanishes
  have hsub : Subsingleton (IsLocalRing.ResidueField B₀ ⊗[B₀] Ω[B₀⁄P]) := by
    set κ := IsLocalRing.ResidueField B₀ with hκ
    set Φ : κ ⊗[B₀] Ω[B₀⁄A] →ₗ[κ] κ ⊗[B₀] Ω[B₀⁄P] :=
      TensorProduct.AlgebraTensorModule.map LinearMap.id
        (KaehlerDifferential.map A P B₀ B₀) with hΦdef
    have hΦtop : LinearMap.range Φ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul c ω =>
        obtain ⟨ω', rfl⟩ := hφsurj ω
        exact ⟨c ⊗ₜ[B₀] ω', rfl⟩
      | add z w hz hw =>
        obtain ⟨a, ha⟩ := hz
        obtain ⟨b, hb⟩ := hw
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    have hzero : ∀ i, Φ ((1 : κ) ⊗ₜ[B₀]
        KaehlerDifferential.D A B₀ (algebraMap B B₀ (v i))) = 0 := by
      intro i
      obtain ⟨p, hp⟩ := hv i
      have ht : algebraMap B B₀ (v i) = algebraMap P B₀ p := by
        rw [← hp, IsScalarTower.algebraMap_apply P B B₀]
      rw [hΦdef, TensorProduct.AlgebraTensorModule.map_tmul, KaehlerDifferential.map_D,
        Algebra.algebraMap_self_apply, ht, Derivation.map_algebraMap]
      exact TensorProduct.tmul_zero _ _
    have hbot : LinearMap.range Φ = ⊥ := by
      rw [← Submodule.map_top, ← hspan, Submodule.map_span, Submodule.span_eq_bot]
      rintro y ⟨w, ⟨i, rfl⟩, rfl⟩
      exact hzero i
    have htb : (⊤ : Submodule κ (κ ⊗[B₀] Ω[B₀⁄P])) = ⊥ := hΦtop ▸ hbot
    refine subsingleton_of_forall_eq 0 fun z => ?_
    have hz : z ∈ (⊥ : Submodule κ (κ ⊗[B₀] Ω[B₀⁄P])) := htb ▸ Submodule.mem_top
    simpa using hz
  -- Nakayama upgrades that to the vanishing of `Ω[B₀⁄P]` itself
  have hzeroStalk : Subsingleton Ω[B₀⁄P] := by
    have hgen : Stacks.SmoothAtJacobian.GeneratedByAtMost (IsLocalRing.ResidueField B₀)
        (IsLocalRing.ResidueField B₀ ⊗[B₀] Ω[B₀⁄P]) 0 := by
      refine ⟨∅, ?_, by simp⟩
      refine top_unique fun z _ => ?_
      rw [hsub.elim z 0]
      exact Submodule.zero_mem _
    obtain ⟨s, hs, hcard⟩ :=
      Stacks.RelativeDifferentialStalkMap.generatedByAtMost_of_tensor_residueField
        (B := B₀) (M := Ω[B₀⁄P]) hgen
    have hsempty : s = ∅ := by
      rw [← Finset.card_eq_zero]
      exact le_antisymm (by exact_mod_cast hcard) (Nat.zero_le _)
    refine subsingleton_of_forall_eq 0 fun z => ?_
    have hz : z ∈ (⊤ : Submodule B₀ Ω[B₀⁄P]) := Submodule.mem_top
    rw [← hs, hsempty] at hz
    simpa using hz
  -- hence the localization of `Ω[B⁄P]` at `q` vanishes
  have hloc : IsLocalizedModule q.primeCompl (KaehlerDifferential.map P P B B₀) :=
    omega_localization_total P B q.primeCompl B₀
  have : Subsingleton (LocalizedModule q.primeCompl Ω[B⁄P]) :=
    (IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl Ω[B⁄P])
      (KaehlerDifferential.map P P B B₀)).toEquiv.subsingleton_congr.mpr hzeroStalk
  exact Algebra.exists_unramified_away_of_subsingleton_localizedModule q this

/-- **The choice of the `r` coordinates.** If the residue-field fibre of `Ω[B₀⁄A]` has dimension
`r` over the residue field, then `r` global elements of `B` have differentials whose classes
span it. The differentials of the local ring are a localization of those of `B`, hence spanned
by the `d b` with `b ∈ B`, and a spanning family of an `r`-dimensional space has a spanning
subfamily of `r` members. -/
private theorem exists_coordinates_span_residueFibre
    {A B B₀ : Type u} [CommRing A] [CommRing B] [CommRing B₀]
    (q : Ideal B) [Algebra A B] [Algebra.FiniteType A B] [q.IsPrime]
    [Algebra B B₀] [IsLocalization.AtPrime B₀ q] [IsLocalRing B₀]
    [Algebra A B₀] [IsScalarTower A B B₀] (r : ℕ)
    (hr : Module.finrank (IsLocalRing.ResidueField B₀)
        (IsLocalRing.ResidueField B₀ ⊗[B₀] Ω[B₀⁄A]) = r) :
    ∃ u : ULift.{u} (Fin r) → B, Submodule.span (IsLocalRing.ResidueField B₀)
      (Set.range fun i => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
        KaehlerDifferential.D A B₀ (algebraMap B B₀ (u i))) = ⊤ := by
  classical
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_finiteType A B
  have : Algebra.EssFiniteType B B₀ :=
    Algebra.EssFiniteType.of_isLocalization (R := B) (S := B₀) q.primeCompl
  have : Algebra.EssFiniteType A B₀ := Algebra.EssFiniteType.comp A B B₀
  have hfin : Module.Finite B₀ Ω[B₀⁄A] := KaehlerDifferential.finite A B₀
  have : FiniteDimensional (IsLocalRing.ResidueField B₀)
      (IsLocalRing.ResidueField B₀ ⊗[B₀] Ω[B₀⁄A]) :=
    Module.Finite.base_change B₀ (IsLocalRing.ResidueField B₀) Ω[B₀⁄A]
  -- the differentials of the local ring are spanned by the `d b` for `b` a global element
  have hspanB₀ : Submodule.span B₀
      (Set.range fun b : B => KaehlerDifferential.D A B₀ (algebraMap B B₀ b)) = ⊤ := by
    have himg := span_eq_top_of_isLocalizedModule (R := B) B₀
      q.primeCompl (KaehlerDifferential.map A A B B₀)
      (v := Set.range (KaehlerDifferential.D A B))
      (KaehlerDifferential.span_range_derivation A B)
    rwa [← Set.range_comp, show (KaehlerDifferential.map A A B B₀) ∘
      (KaehlerDifferential.D A B) = fun b : B =>
        KaehlerDifferential.D A B₀ (algebraMap B B₀ b) from
      funext fun b => KaehlerDifferential.map_D A A B B₀ b] at himg
  -- hence the residue-field fibre is spanned by their classes
  have hspanκ : Submodule.span (IsLocalRing.ResidueField B₀)
      (Set.range fun b : B => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
        KaehlerDifferential.D A B₀ (algebraMap B B₀ b)) = ⊤ := by
    have h1 := (IsLocalRing.map_tensorProduct_mk_eq_top (R := B₀)
      (M := Ω[B₀⁄A]) (N := Submodule.span B₀
        (Set.range fun b : B => KaehlerDifferential.D A B₀ (algebraMap B B₀ b)))).mpr hspanB₀
    rw [Submodule.map_span, ← Set.range_comp] at h1
    rwa [← Submodule.restrictScalars_eq_top_iff (S := B₀),
      Submodule.restrictScalars_span B₀ (IsLocalRing.ResidueField B₀)
        IsLocalRing.residue_surjective]
  obtain ⟨u, hu⟩ := exists_fin_spanning_subfamily
    (K := IsLocalRing.ResidueField B₀)
    (fun b : B => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
      KaehlerDifferential.D A B₀ (algebraMap B B₀ b)) hspanκ r hr
  have hdown : Function.Surjective (ULift.down : ULift.{u} (Fin r) → Fin r) :=
    fun j => ⟨ULift.up j, rfl⟩
  refine ⟨u ∘ ULift.down, ?_⟩
  rwa [show (fun i : ULift.{u} (Fin r) => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
      KaehlerDifferential.D A B₀ (algebraMap B B₀ ((u ∘ ULift.down) i))) =
      ((fun b : B => (1 : IsLocalRing.ResidueField B₀) ⊗ₜ[B₀]
        KaehlerDifferential.D A B₀ (algebraMap B B₀ b)) ∘ u) ∘ ULift.down from rfl,
    hdown.range_comp _]

/-- **Stacks Project, Tag 0CBK.** Let `f : X ⟶ S` be a finite type morphism of affine schemes
and let `x` be a point of `X`. If `r` is the dimension over `κ(x)` of the residue-field fibre at
`x` of the stalk of the sheaf of relative differentials, then `f` factors as `X ⟶ 𝐀^r_S ⟶ S`
with the first morphism unramified at `x`.

The coordinates of the factorization are `r` global sections of `X` whose differentials span
that fibre. -/
@[stacks 0CBK]
theorem exists_factorization_unramifiedAt {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : X) (r : ℕ)
    (hr : Module.finrank (X.residueField x) (relativeCotangentSpace f x) = r) :
    ∃ π : X ⟶ 𝔸(ULift.{u} (Fin r); S),
      (π ≫ 𝔸(ULift.{u} (Fin r); S) ↘ S = f) ∧ UnramifiedAt π x := by
  classical
  let A := ToType Γ(S, ⊤)
  let B := ToType Γ(X, ⊤)
  let A₀ := ToType (S.presheaf.stalk (f.base x))
  let B₀ := ToType (X.presheaf.stalk x)
  let : Algebra A B := f.appTop.hom.toAlgebra
  let : Algebra A A₀ := (S.presheaf.germ ⊤ (f.base x) trivial).hom.toAlgebra
  let : Algebra B B₀ := (X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : Algebra A₀ B₀ := algebraStalkMap f x
  let : Algebra A B₀ := ((algebraMap B B₀).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType A B := finiteType_algebra_appTop f
  let p : PrimeSpectrum A := (isAffineOpen_top S).primeIdealOf ⟨f.base x, trivial⟩
  let q : PrimeSpectrum B := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  have : IsLocalization.AtPrime A₀ p.asIdeal :=
    (isAffineOpen_top S).isLocalization_stalk ⟨f.base x, trivial⟩
  have : IsLocalization.AtPrime B₀ q.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  -- the two towers through the stalks agree
  have hcompat : f.appTop ≫ X.presheaf.germ ⊤ x trivial =
      S.presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x :=
    (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm
  have : IsScalarTower A A₀ B₀ := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change (algebraMap B B₀) (algebraMap A B a) = (f.stalkMap x).hom _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) a
  -- read the stalk of relative differentials as the differentials of `B₀` over `A`
  let e2 : Ω[B₀⁄A] ≃ₗ[B₀] Ω[B₀⁄A₀] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map A A₀ B₀ B₀)
      (omega_localization_base A B₀ p.asIdeal.primeCompl A₀)
  let ψ : relativeDifferentialStalk f x →ₗ[B₀] Ω[B₀⁄A] :=
    e2.symm.toLinearMap ∘ₗ (relativeDifferentialsStalkKaehlerEquiv f x).toLinearMap
  have hψ : Function.Bijective ψ :=
    e2.symm.bijective.comp (relativeDifferentialsStalkKaehlerEquiv f x).bijective
  let eΩ : relativeDifferentialStalk f x ≃ₗ[B₀] Ω[B₀⁄A] := LinearEquiv.ofBijective ψ hψ
  let eW : (X.residueField x) ⊗[B₀] relativeDifferentialStalk f x
      ≃ₗ[X.residueField x] (X.residueField x) ⊗[B₀] Ω[B₀⁄A] :=
    LinearEquiv.baseChange B₀ (X.residueField x) _ _ eΩ
  have hrW : Module.finrank (X.residueField x)
      ((X.residueField x) ⊗[B₀] Ω[B₀⁄A]) = r :=
    eW.finrank_eq.symm.trans hr
  -- choose the `r` coordinates and form the morphism to affine `r`-space
  obtain ⟨v, hv⟩ :=
    exists_coordinates_span_residueFibre (A := A) (B := B) (B₀ := B₀) q.asIdeal r hrW
  refine ⟨AffineSpace.homOfVector f v, AffineSpace.homOfVector_over _ _, ?_⟩
  have hfac : AffineSpace.homOfVector f v ≫ 𝔸(ULift.{u} (Fin r); S) ↘ S = f :=
    AffineSpace.homOfVector_over _ _
  set π := AffineSpace.homOfVector f v with hπ
  let P := ToType Γ(𝔸(ULift.{u} (Fin r); S), ⊤)
  let : Algebra P B := π.appTop.hom.toAlgebra
  let : Algebra A P := (𝔸(ULift.{u} (Fin r); S) ↘ S).appTop.hom.toAlgebra
  have : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.appTop).hom a =
      (π.appTop).hom (((𝔸(ULift.{u} (Fin r); S) ↘ S).appTop).hom a)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hfac]
  -- the coordinates are the images of the coordinate functions of affine space
  have hvP : ∀ i, v i ∈ Set.range (algebraMap P B) :=
    fun i => ⟨AffineSpace.coord S i, AffineSpace.homOfVector_appTop_coord f v i⟩
  obtain ⟨g, hgq, hunram⟩ :=
    exists_unramified_away_of_span_residueFibre
      (A := A) (P := P) (B := B) (B₀ := B₀) q.asIdeal v hvP hv
  -- the basic open of `g` is an affine neighbourhood of `x` on which `π` is unramified
  have hxg : x ∈ X.basicOpen g := by
    have hxm : (isAffineOpen_top X).fromSpec q ∈ X.basicOpen g := by
      rw [← (isAffineOpen_top X).fromSpec_image_basicOpen g]
      exact Set.mem_image_of_mem _ ((PrimeSpectrum.mem_basicOpen g q).2 hgq)
    simpa [q, IsAffineOpen.fromSpec_primeIdealOf] using hxm
  refine ⟨X.basicOpen g, (isAffineOpen_top X).basicOpen g, hxg, ⊤,
    isAffineOpen_top _, le_top, ?_⟩
  let : Algebra B (ToType Γ(X, X.basicOpen g)) :=
    (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ π ⁻¹ᵁ ⊤)).op).hom.toAlgebra
  let : Algebra P (ToType Γ(X, X.basicOpen g)) :=
    (π.appLE ⊤ (X.basicOpen g) le_top).hom.toAlgebra
  have : IsLocalization.Away g (ToType Γ(X, X.basicOpen g)) :=
    (isAffineOpen_top X).isLocalization_basicOpen g
  have : IsScalarTower P B (ToType Γ(X, X.basicOpen g)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eLoc : ToType Γ(X, X.basicOpen g) ≃ₐ[B] Localization.Away g :=
    IsLocalization.algEquiv (Submonoid.powers g) _ _
  exact Algebra.Unramified.of_equiv (eLoc.symm.restrictScalars P)

end UnramifiedFactorization

section ImmersionIntoAffineSpace

open Stacks.SmoothAtJacobian (relativeCotangentSpace)
open scoped TensorProduct

/-- The dimension of the residue-field fibre of the Kähler differentials is unchanged by an
isomorphism of the pair `(base ring, ring)`. -/
private theorem finrank_tensor_kaehler_congr
    {R A R' A' K K' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Field K] [Field K'] [Algebra R A] [Algebra R' A'] [Algebra A K] [Algebra A' K']
    (eR : R →+* R') (eA : A →+* A') (φ : K →+* K')
    (hR : Function.Surjective eR) (hA : Function.Bijective eA)
    (h1 : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (h2 : ∀ a, φ (algebraMap A K a) = algebraMap A' K' (eA a)) :
    Module.finrank K (K ⊗[A] Ω[A⁄R]) = Module.finrank K' (K' ⊗[A'] Ω[A'⁄R']) := by
  let _ : Algebra A A' := eA.toAlgebra
  let _ : Algebra R R' := eR.toAlgebra
  let _ : Algebra K K' := φ.toAlgebra
  let _ : Algebra R A' := (eA.comp (algebraMap R A)).toAlgebra
  let _ : Algebra A K' := ((algebraMap A' K').comp eA).toAlgebra
  have _ : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq fun r => h1 r
  have _ : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun a => (h2 a).symm
  have _ : Algebra.FormallyEtale A A' :=
    Algebra.FormallyEtale.of_equiv (R := A)
      (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective eA hA) fun _ => rfl)
  let e : K' ⊗[A] Ω[A⁄R] ≃ₗ[K'] K' ⊗[A'] Ω[A'⁄R'] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' K' K' Ω[A⁄R]).symm.trans
      (((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A A').trans
        (Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective R R' A'
          hR)).baseChange A' K' _ _)
  exact (Stacks.Tag01V9NumericalCriterion.finrank_tensor_residueField_eq A K K'
    Ω[A⁄R]).trans e.finrank_eq

/-- The inclusion of an open subscheme induces on global sections the restriction map
`Γ(X, U) ⟶ Γ(U, ⊤)`. -/
private theorem appLE_ι_top_eq_topIso_inv {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  simp
  congr 1

/-- Restricting a morphism to open subschemes induces on global sections the map it induces on
the sections over those opens. -/
private theorem appLE_resLE_top {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    f.appLE V U hUV ≫ U.topIso.inv =
      V.topIso.inv ≫ (f.resLE V U hUV).appLE ⊤ ⊤ le_top := by
  have hg : (f.resLE V U hUV).appLE ⊤ ⊤ le_top = (f.resLE V U hUV).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [hg, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]

/-- The prime of `Γ(X, U)` at `x` is the contraction of the prime of `Γ(U, ⊤)` at `x`. -/
private theorem asIdeal_primeIdealOf_eq_comap {X : Scheme.{u}} (U : X.affineOpens) (x : X)
    (hxU : x ∈ U.1) (htU : IsAffineOpen (⊤ : U.1.toScheme.Opens)) :
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal =
      (htU.primeIdealOf ⟨⟨x, hxU⟩, trivial⟩).asIdeal.comap (U.1.topIso.inv).hom := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := U.1.ι) (x := (⟨x, hxU⟩ : U.1))
    U.1 U.2 ⊤ htU U.1.ι_preimage_self.ge trivial
  rw [appLE_ι_top_eq_topIso_inv] at h
  exact (congrArg PrimeSpectrum.asIdeal h).symm

/-- **The relative cotangent space is local on the source and target.** Restricting `f` to
affine opens `U ≤ f⁻¹ V` does not change the dimension of the relative cotangent space at a
point of `U`. -/
private theorem finrank_relativeCotangentSpace_resLE {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Module.finrank (U.1.toScheme.residueField ⟨x, hxU⟩)
        (relativeCotangentSpace (f.resLE V.1 U.1 hUV) ⟨x, hxU⟩) =
      Module.finrank (X.residueField x)
        (relativeCotangentSpace f x) := by
  have _ : IsAffine U.1.toScheme := U.2
  have _ : IsAffine V.1.toScheme := V.2
  have htU : IsAffineOpen (⊤ : U.1.toScheme.Opens) := isAffineOpen_top _
  have htV : IsAffineOpen (⊤ : V.1.toScheme.Opens) := isAffineOpen_top _
  let _ : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let _ : Algebra Γ(V.1.toScheme, ⊤) Γ(U.1.toScheme, ⊤) :=
    ((f.resLE V.1 U.1 hUV).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have hf := Stacks.Tag01V9NumericalCriterion.finrank_relativeCotangentSpace_eq_chart
    f x U V hxU hUV
  have hg := Stacks.Tag01V9NumericalCriterion.finrank_relativeCotangentSpace_eq_chart
    (f.resLE V.1 U.1 hUV) ⟨x, hxU⟩ ⟨⊤, htU⟩ ⟨⊤, htV⟩ trivial le_top
  rw [hf, hg]
  refine (finrank_tensor_kaehler_congr (V.1.topIso.inv).hom (U.1.topIso.inv).hom
    (Ideal.ResidueField.map _ _ (U.1.topIso.inv).hom
      (asIdeal_primeIdealOf_eq_comap U x hxU htU))
    (ConcreteCategory.bijective_of_isIso V.1.topIso.inv).surjective
    (ConcreteCategory.bijective_of_isIso U.1.topIso.inv)
    (fun r => ?_) (fun a => Ideal.ResidueField.map_algebraMap _ _ _ _ a)).symm
  exact congrArg (fun m => (CommRingCat.Hom.hom m) r) (appLE_resLE_top f U.1 V.1 hUV)

/-- The reindexing bijection `ULift (Fin (r + 1)) ≃ Option (ULift (Fin r))`. -/
private def uliftFinSuccEquiv (r : ℕ) :
    ULift.{u} (Fin (r + 1)) ≃ Option (ULift.{u} (Fin r)) :=
  Equiv.ulift.trans ((finSuccEquiv r).trans (Equiv.optionCongr Equiv.ulift.symm))

/-- Splitting off one variable: `B[x_0, …, x_r] ≃ₐ[B] B[x_0, …, x_{r-1}][X]`. -/
private noncomputable def mvPolySuccAlgEquiv (B : Type u) [CommRing B] (r : ℕ) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) B ≃ₐ[B]
      Polynomial (MvPolynomial (ULift.{u} (Fin r)) B) :=
  (MvPolynomial.renameEquiv B (uliftFinSuccEquiv r)).trans
    (MvPolynomial.optionEquivLeft B (ULift.{u} (Fin r)))

/-- `mvPolySuccAlgEquiv` carries constants to constants. -/
private lemma mvPolySuccAlgEquiv_C (B : Type u) [CommRing B] (r : ℕ) (b : B) :
    mvPolySuccAlgEquiv B r (MvPolynomial.C b) = Polynomial.C (MvPolynomial.C b) := by
  rw [mvPolySuccAlgEquiv]
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C,
    MvPolynomial.optionEquivLeft_C]

/-- The isomorphism of spectra induced by a ring isomorphism. -/
private noncomputable def specMapIso {R T : Type u} [CommRing R] [CommRing T] (e : R ≃+* T) :
    Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (e : R →+* T))
  inv := Spec.map (CommRingCat.ofHom (e.symm : T →+* R))
  hom_inv_id := by
    have h : ((e : R →+* T).comp (e.symm : T →+* R)) = RingHom.id T :=
      RingHom.ext fun x => e.apply_symm_apply x
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h, CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    have h : (((e.symm : T →+* R)).comp (e : R →+* T)) = RingHom.id R :=
      RingHom.ext fun x => e.symm_apply_apply x
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h, CommRingCat.ofHom_id, Spec.map_id]

private lemma specMapIso_hom {R T : Type u} [CommRing R] [CommRing T] (e : R ≃+* T) :
    (specMapIso e).hom = Spec.map (CommRingCat.ofHom (e : R →+* T)) := rfl

/-- The global sections of an isomorphism of schemes. -/
private def gammaMapIso {X Y : Scheme.{u}} (e : X ≅ Y) : Γ(Y, ⊤) ≅ Γ(X, ⊤) :=
  Scheme.Γ.mapIso e.op

private lemma gammaMapIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (gammaMapIso e).hom = e.hom.appTop := rfl

/-- Evaluation of `Γ(S, ⊤)[x_0, …, x_{r-1}]` at the standard coordinates of `𝔸^r_S`. -/
private noncomputable def coordEvalHom (S : Scheme.{u}) (r : ℕ) :
    MvPolynomial (ULift.{u} (Fin r)) ↥Γ(S, ⊤) →+* ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤) :=
  MvPolynomial.eval₂Hom ((𝔸(ULift.{u} (Fin r); S) ↘ S).appTop).hom (AffineSpace.coord S)

/-- `coordEvalHom` is an isomorphism when the base is affine. -/
private noncomputable def coordEvalIso (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) ↥Γ(S, ⊤)) ≅
      Γ(𝔸(ULift.{u} (Fin r); S), ⊤) :=
  (Scheme.ΓSpecIso _).symm ≪≫ gammaMapIso (AffineSpace.isoOfIsAffine (ULift.{u} (Fin r)) S)

private lemma coordEvalIso_hom (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    (coordEvalIso S r).hom = CommRingCat.ofHom (coordEvalHom S r) := by
  rw [coordEvalIso, Iso.trans_hom, Iso.symm_hom, gammaMapIso_hom,
    AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
  rfl

private lemma coordEvalIso_ringEquiv_apply (S : Scheme.{u}) [IsAffine S] (r : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin r)) ↥Γ(S, ⊤)) :
    (coordEvalIso S r).commRingCatIsoToRingEquiv p = coordEvalHom S r p := by
  change (coordEvalIso S r).hom.hom p = _
  rw [coordEvalIso_hom, CommRingCat.hom_ofHom]

/-- The ring isomorphism `Γ(S, ⊤)[x_0, …, x_r] ≃+* Γ(𝔸^r_S, ⊤)[X]`. -/
private noncomputable def polySuccRingEquiv (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) ↥Γ(S, ⊤) ≃+*
      Polynomial ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤) :=
  (mvPolySuccAlgEquiv (↥Γ(S, ⊤)) r).toRingEquiv.trans
    (Polynomial.mapEquiv (coordEvalIso S r).commRingCatIsoToRingEquiv)

/-- `polySuccRingEquiv` carries the constant `b` to the constant polynomial whose value is the
constant function `b` on `𝔸^r_S`. -/
private lemma polySuccRingEquiv_C (S : Scheme.{u}) [IsAffine S] (r : ℕ) (b : ↥Γ(S, ⊤)) :
    polySuccRingEquiv S r (MvPolynomial.C b) =
      Polynomial.C (coordEvalHom S r (MvPolynomial.C b)) := by
  rw [polySuccRingEquiv]
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, mvPolySuccAlgEquiv_C,
    Polynomial.mapEquiv_apply, Polynomial.map_C]
  exact congrArg (fun z => Polynomial.C z) (coordEvalIso_ringEquiv_apply S r _)

/-- `Scheme.isoSpec` of `𝔸^r_S` factors `AffineSpace.isoOfIsAffine` through `coordEvalHom`. -/
private lemma isoSpec_inv_affineSpace (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    (𝔸(ULift.{u} (Fin r); S)).isoSpec.inv =
      Spec.map (CommRingCat.ofHom (coordEvalHom S r)) ≫
        (AffineSpace.isoOfIsAffine (ULift.{u} (Fin r)) S).inv := by
  rw [Iso.eq_comp_inv, AffineSpace.isoOfIsAffine_hom, ← Scheme.isoSpec_hom, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- The affine line over affine `r`-space is affine `(r+1)`-space. -/
private noncomputable def affineSpaceSuccIso (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    Spec (CommRingCat.of (Polynomial ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤))) ≅
      𝔸(ULift.{u} (Fin (r + 1)); S) :=
  specMapIso (polySuccRingEquiv S r) ≪≫
    (AffineSpace.isoOfIsAffine (ULift.{u} (Fin (r + 1))) S).symm

/-- The identification of `AlgebraicGeometry.affineSpaceSuccIso` is compatible with the structure
morphisms down to `S`: the inclusion of the constants `Γ(𝔸^r_S, ⊤) → Γ(𝔸^r_S, ⊤)[X]` becomes the
projection `𝔸^{r+1}_S ⟶ 𝔸^r_S`. -/
private theorem affineSpaceSuccIso_hom_over (S : Scheme.{u}) [IsAffine S] (r : ℕ) :
    (affineSpaceSuccIso S r).hom ≫ 𝔸(ULift.{u} (Fin (r + 1)); S) ↘ S =
      Spec.map (CommRingCat.ofHom (Polynomial.C :
          ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤) →+*
            Polynomial ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤))) ≫
        (𝔸(ULift.{u} (Fin r); S)).isoSpec.inv ≫ 𝔸(ULift.{u} (Fin r); S) ↘ S := by
  have key : CommRingCat.ofHom (MvPolynomial.C :
        ↥Γ(S, ⊤) →+* MvPolynomial (ULift.{u} (Fin (r + 1))) ↥Γ(S, ⊤)) ≫
      CommRingCat.ofHom ((polySuccRingEquiv S r : _ →+* _)) =
      CommRingCat.ofHom (MvPolynomial.C :
          ↥Γ(S, ⊤) →+* MvPolynomial (ULift.{u} (Fin r)) ↥Γ(S, ⊤)) ≫
        CommRingCat.ofHom (coordEvalHom S r) ≫
          CommRingCat.ofHom (Polynomial.C :
            ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤) →+*
              Polynomial ↥Γ(𝔸(ULift.{u} (Fin r); S), ⊤)) :=
    CommRingCat.hom_ext <| RingHom.ext fun b => polySuccRingEquiv_C S r b
  rw [affineSpaceSuccIso, isoSpec_inv_affineSpace]
  simp only [Iso.trans_hom, Iso.symm_hom, specMapIso_hom, Category.assoc,
    AffineSpace.isoOfIsAffine_inv_over, ← Spec.map_comp_assoc]
  exact congrArg (fun z => Spec.map z ≫ S.isoSpec.inv) key

/-- Precomposing with a morphism smooth of relative dimension `0` preserves relative dimension. -/
private theorem smoothOfRelativeDimension_zero_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) [SmoothOfRelativeDimension 0 f] [SmoothOfRelativeDimension n g] :
    SmoothOfRelativeDimension n (f ≫ g) := by
  have h := (inferInstance : SmoothOfRelativeDimension (0 + n) (f ≫ g))
  rwa [Nat.zero_add] at h

/-- Postcomposing with a morphism smooth of relative dimension `0` preserves relative dimension. -/
private theorem smoothOfRelativeDimension_comp_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension n (f ≫ g) := by
  have h := (inferInstance : SmoothOfRelativeDimension (n + 0) (f ≫ g))
  rwa [Nat.add_zero] at h

/-- Affine `n`-space over an affine base is smooth of relative dimension `n`. -/
private theorem smoothOfRelativeDimension_affineSpace_over (S : Scheme.{u}) [IsAffine S]
    (n : ℕ) : SmoothOfRelativeDimension n (𝔸(ULift.{u} (Fin n); S) ↘ S) := by
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n ↥Γ(S, ⊤)
      (MvPolynomial (ULift.{u} (Fin n)) ↥Γ(S, ⊤)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n
      (MvPolynomial.renameEquiv ↥Γ(S, ⊤) (Equiv.ulift.{u, 0} (α := Fin n)).symm)
  have hC : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        ↥Γ(S, ⊤) →+* MvPolynomial (ULift.{u} (Fin n)) ↥Γ(S, ⊤)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    change (algebraMap ↥Γ(S, ⊤)
      (MvPolynomial (ULift.{u} (Fin n)) ↥Γ(S, ⊤))).IsStandardSmoothOfRelativeDimension n
    rwa [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have h1 := smoothOfRelativeDimension_comp_zero (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : ↥Γ(S, ⊤) →+* MvPolynomial (ULift.{u} (Fin n)) ↥Γ(S, ⊤)))) S.isoSpec.inv n
  have heq : 𝔸(ULift.{u} (Fin n); S) ↘ S =
      (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) S).hom ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C :
          ↥Γ(S, ⊤) →+* MvPolynomial (ULift.{u} (Fin n)) ↥Γ(S, ⊤))) ≫ S.isoSpec.inv) := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := ULift.{u} (Fin n)) (S := S),
      Iso.hom_inv_id_assoc]
  rw [heq]
  exact smoothOfRelativeDimension_zero_comp _ _ n

/-- **Tag 0CBK on an affine neighbourhood.** A morphism locally of finite type factors, on an
affine open neighbourhood of `x` lying over a prescribed affine open `V` of the target, through
relative affine `r`-space over `V` by a morphism unramified at `x`. -/
private theorem exists_affineOpen_unramifiedAt_affineSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (V : S.affineOpens) (hxV : f x ∈ V.1) (r : ℕ)
    (hr : Module.finrank (X.residueField x) (relativeCotangentSpace f x) = r) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
      (π : U.1.toScheme ⟶ 𝔸(ULift.{u} (Fin r); V.1.toScheme)),
      π ≫ 𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme = f.resLE V.1 U.1 hUV ∧
        UnramifiedAt π ⟨x, hxU⟩ := by
  obtain ⟨W, hW, hxW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V.1) hxV
  have hWV : W ≤ f ⁻¹ᵁ V.1 := hWsub
  let _ : IsAffine W.toScheme := hW
  let _ : IsAffine V.1.toScheme := V.2
  have hfin : Module.finrank (W.toScheme.residueField ⟨x, hxW⟩)
      (relativeCotangentSpace (f.resLE V.1 W hWV) ⟨x, hxW⟩) = r :=
    (finrank_relativeCotangentSpace_resLE f ⟨W, hW⟩ V x hxW hWV).trans hr
  obtain ⟨π, hπ, hunram⟩ :=
    exists_factorization_unramifiedAt (f.resLE V.1 W hWV) ⟨x, hxW⟩ r hfin
  exact ⟨⟨W, hW⟩, hxW, hWV, π, hπ, hunram⟩

/-- **Tag 0CBJ over an affine target.** A morphism unramified at `x` with affine target `A`
restricts, on an affine open neighbourhood of `x`, to an immersion into a scheme étale over `A`
which is itself immersed in the affine line over `A`. -/
private theorem exists_immersion_over_affineLine {Y A : Scheme.{u}} [IsAffine A]
    (π : Y ⟶ A) (z : Y) (hz : UnramifiedAt π z) :
    ∃ (W : Y.Opens) (_ : IsAffineOpen W) (_ : z ∈ W) (D : Scheme.{u})
      (j : W.toScheme ⟶ D) (i : D ⟶ Spec (CommRingCat.of (Polynomial ↥Γ(A, ⊤)))),
      IsImmersion j ∧ IsImmersion i ∧
        SmoothOfRelativeDimension 0 (i ≫ Spec.map (CommRingCat.ofHom
          (Polynomial.C : ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤))) ≫ A.isoSpec.inv) ∧
        j ≫ i ≫ Spec.map (CommRingCat.ofHom
            (Polynomial.C : ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤))) ≫ A.isoSpec.inv =
          W.ι ≫ π := by
  obtain ⟨W, hW, hzW, hWT, P, -, j, hj, heq⟩ :=
    exists_isImmersion_specMap_derivativePair_of_unramifiedAt π z
      (⊤ : A.Opens) (isAffineOpen_top A) trivial hz
  refine ⟨W, hW, hzW, Spec (CommRingCat.of P.Ring), j,
    Spec.map (CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom), hj,
    P.isImmersion_specMap_aeval_X, ?_, ?_⟩
  · have hring : CommRingCat.ofHom (Polynomial.C : ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤)) ≫
        CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom =
          CommRingCat.ofHom (algebraMap ↥Γ(A, ⊤) P.Ring) := by
      ext a
      simp
    have hcomp : Spec.map (CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤))) =
          Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(A, ⊤) P.Ring)) := by
      rw [← Spec.map_comp, hring]
    have hstd0 : Algebra.IsStandardSmoothOfRelativeDimension 0 ↥Γ(A, ⊤) P.Ring :=
      Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
    have hsm0 : SmoothOfRelativeDimension 0
        (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(A, ⊤) P.Ring))) := by
      rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 0)]
      refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
      rwa [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [← Category.assoc, hcomp]
    infer_instance
  · have h1 : A.isoSpec.inv = (isAffineOpen_top A).isoSpec.inv ≫ (⊤ : A.Opens).ι := by
      rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top]
    calc j ≫ Spec.map (CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C :
            ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤))) ≫ A.isoSpec.inv
        = (j ≫ Spec.map (CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (Polynomial.C :
              ↥Γ(A, ⊤) →+* Polynomial ↥Γ(A, ⊤)))) ≫ A.isoSpec.inv := by
          simp only [Category.assoc]
      _ = (π.resLE ⊤ W hWT ≫ (isAffineOpen_top A).isoSpec.hom) ≫ A.isoSpec.inv := by
          rw [heq]
      _ = W.ι ≫ π := by
          rw [h1, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

/-- **The diagram of Tag 0CBL.** On an affine open neighbourhood `U` of `x` over `V` the
restriction of `f` factors through a scheme `D` smooth of relative dimension `r` over `V` by an
immersion, and `D` is itself immersed in relative affine `(r+1)`-space over `V`. -/
private theorem exists_immersion_smooth_diagram {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (V : S.affineOpens) (hxV : f x ∈ V.1) (r : ℕ)
    (hr : Module.finrank (X.residueField x) (relativeCotangentSpace f x) = r) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (D : Scheme.{u})
      (j : U.1.toScheme ⟶ D) (dV : D ⟶ V.1.toScheme)
      (j' : D ⟶ 𝔸(ULift.{u} (Fin (r + 1)); V.1.toScheme)),
      IsImmersion j ∧ IsImmersion j' ∧ SmoothOfRelativeDimension r dV ∧
        j ≫ dV = f.resLE V.1 U.1 hUV ∧
        j' ≫ 𝔸(ULift.{u} (Fin (r + 1)); V.1.toScheme) ↘ V.1.toScheme = dV := by
  classical
  let _ : IsAffine V.1.toScheme := V.2
  obtain ⟨U₀, hxU₀, hU₀V, π, hπ, hunram⟩ :=
    exists_affineOpen_unramifiedAt_affineSpace f x V hxV r hr
  obtain ⟨W, hW, hxW, D, j, i, hj, hi, hsm, hfac⟩ :=
    exists_immersion_over_affineLine π ⟨x, hxU₀⟩ hunram
  set q : D ⟶ 𝔸(ULift.{u} (Fin r); V.1.toScheme) :=
    i ≫ Spec.map (CommRingCat.ofHom (Polynomial.C :
        ↥Γ(𝔸(ULift.{u} (Fin r); V.1.toScheme), ⊤) →+*
          Polynomial ↥Γ(𝔸(ULift.{u} (Fin r); V.1.toScheme), ⊤))) ≫
      (𝔸(ULift.{u} (Fin r); V.1.toScheme)).isoSpec.inv with hqdef
  let Z : X.Opens := U₀.1.ι ''ᵁ W
  have hZ : IsAffineOpen Z := hW.image_of_isOpenImmersion U₀.1.ι
  have hxZ : x ∈ Z := ⟨⟨x, hxU₀⟩, hxW, rfl⟩
  have hZV : Z ≤ f ⁻¹ᵁ V.1 := le_trans (Scheme.Opens.ι_image_le (U := U₀.1) W) hU₀V
  let e : W.toScheme ≅ Z.toScheme := U₀.1.ι.isoImage W
  refine ⟨⟨Z, hZ⟩, hxZ, hZV, D, e.inv ≫ j,
    q ≫ 𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme,
    i ≫ (affineSpaceSuccIso V.1.toScheme r).hom, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · have hAr : SmoothOfRelativeDimension r
        (𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme) :=
      smoothOfRelativeDimension_affineSpace_over V.1.toScheme r
    exact smoothOfRelativeDimension_zero_comp _ _ r
  · rw [← cancel_mono V.1.ι]
    calc ((e.inv ≫ j) ≫ q ≫ 𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme) ≫ V.1.ι
        = e.inv ≫ (j ≫ q) ≫
            (𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme) ≫ V.1.ι := by
          simp only [Category.assoc]
      _ = e.inv ≫ (W.ι ≫ π) ≫
            (𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme) ≫ V.1.ι := by rw [hfac]
      _ = e.inv ≫ W.ι ≫ (π ≫ 𝔸(ULift.{u} (Fin r); V.1.toScheme) ↘ V.1.toScheme) ≫
            V.1.ι := by simp only [Category.assoc]
      _ = e.inv ≫ W.ι ≫ f.resLE V.1 U₀.1 hU₀V ≫ V.1.ι := by rw [hπ]
      _ = e.inv ≫ (e.hom ≫ Z.ι) ≫ f := by
          rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoImage_hom_ι, Category.assoc]
      _ = f.resLE V.1 Z hZV ≫ V.1.ι := by
          rw [Scheme.Hom.resLE_comp_ι]
          simp
  · have hΦ := affineSpaceSuccIso_hom_over V.1.toScheme r
    rw [hqdef, Category.assoc, hΦ]
    simp only [Category.assoc]

/-- **Stacks Project, Tag 0CBL, first clause.** Let `f : X ⟶ S` be locally of finite type, let
`x` be a point of `X` and let `V` be an affine open neighbourhood of its image. If `r` is the
dimension over `κ(x)` of the residue-field fibre at `x` of the stalk of the sheaf of relative
differentials, then `f` restricted to some affine open `U ∋ x` lying over `V` factors as an
immersion into relative affine `(r+1)`-space over `V` followed by the projection. -/
@[stacks 0CBL "clause (1): the immersion into affine (r+1)-space"]
theorem exists_affineOpen_immersion_into_affineSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (V : S.affineOpens) (hxV : f x ∈ V.1) (r : ℕ)
    (hr : Module.finrank (X.residueField x) (relativeCotangentSpace f x) = r) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
      (j : U.1.toScheme ⟶ 𝔸(ULift.{u} (Fin (r + 1)); V.1.toScheme)),
      IsImmersion j ∧
        j ≫ 𝔸(ULift.{u} (Fin (r + 1)); V.1.toScheme) ↘ V.1.toScheme =
          f.resLE V.1 U.1 hUV := by
  obtain ⟨U, hxU, hUV, D, j, dV, j', hj, hj', -, hjd, hj'd⟩ :=
    exists_immersion_smooth_diagram f x V hxV r hr
  refine ⟨U, hxU, hUV, j ≫ j', inferInstance, ?_⟩
  rw [Category.assoc, hj'd, hjd]

/-- **Stacks Project, Tag 0CBL, second clause.** In the situation of
`AlgebraicGeometry.exists_affineOpen_immersion_into_affineSpace`, the affine open `U` may instead
be taken to be a closed subscheme of a scheme smooth of relative dimension `r` over `V`, through
which the restriction of `f` factors. -/
@[stacks 0CBL "clause (2): the closed immersion into a smooth scheme"]
theorem exists_closedImmersion_smoothFactorization {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (V : S.affineOpens) (hxV : f x ∈ V.1) (r : ℕ)
    (hr : Module.finrank (X.residueField x) (relativeCotangentSpace f x) = r) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (D : Scheme.{u})
      (j : U.1.toScheme ⟶ D) (g : D ⟶ V.1.toScheme),
      IsClosedImmersion j ∧ SmoothOfRelativeDimension r g ∧
        j ≫ g = f.resLE V.1 U.1 hUV := by
  obtain ⟨U, hxU, hUV, D, j, dV, j', hj, -, hsm, hjd, -⟩ :=
    exists_immersion_smooth_diagram f x V hxV r hr
  refine ⟨U, hxU, hUV, j.coborderRange.toScheme, j.liftCoborder,
    j.coborderRange.ι ≫ dV, inferInstance, ?_, ?_⟩
  · exact smoothOfRelativeDimension_zero_comp _ _ r
  · rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, hjd]

end ImmersionIntoAffineSpace


end AlgebraicGeometry

end
