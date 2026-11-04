module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndomorphismProjection
public import StacksFrontier.AlgebraicGeometry.ProjMapComposition.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Local
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange

/-!
# The universal family of projective transformations attached to an endomorphism

Let `V` be a finite-dimensional vector space, `E = End(V)` and `A = Sym(Eᵛ)`. The canonical
linear map

`V → Eᵛ ⊗ V = Hom(E, V)`,  `v ↦ (g ↦ g v)`,

extends to an `A`-linear endomorphism `ψ` of `V ⊗ A` whose matrix entries are the coordinates on
the parameter space of endomorphisms: it is the *universal* endomorphism of `V`. Applying `Sym`
and `Proj` to it gives the universal family of projective transformations

`𝐏(V ⊗ 𝒪_S) ⊇ U(ψ) --r_ψ--> 𝐏(V ⊗ 𝒪_S)`,  `S = Spec A`,

over the affine space `S = 𝔸(E)` of endomorphisms of `V`, whose fibre over a point `g` of `S` is
the projective transformation `r_g : 𝐏(V) ⊇ U(g) → 𝐏(V)` of
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/EndomorphismProjection.lean`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamRing`: the coordinate ring `A = Sym(Eᵛ)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndCoeff`: the canonical map
  `V → Eᵛ ⊗ V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEnd`: the universal endomorphism `ψ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndDomain`: the open `U(ψ)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndProjection`: the morphism `r_ψ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamPoint` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamFibreHom`: the point of the parameter space
  attached to an endomorphism `g`, and the specialization of the homogeneous coordinate ring of
  the family at that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamFibreInclusion`: the inclusion
  `𝐏(V) → 𝐏(V ⊗ 𝒪_S)` of the fibre of the family over that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.fibreSquareIso`: the canonical identification of the
  two domains of the fibre square below.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalFamilySpaceIso`: the identification of the
  total space `𝐏(V ⊗ 𝒪_S)` of the family with the product `𝔸(E) × 𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamFibre_universalEnd`: **the fibre of the
  universal endomorphism at the point `g` is `g`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamFibreHom_symAlgMap`: the same statement one
  step up, on symmetric algebras: specializing `Sym ψ` at the point `g` gives `Sym g`, the graded
  homomorphism out of which `r_g` is built.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_universalEndDomain_iff`: **`U(g)` is the fibre
  of `U(ψ)` over the parameter point of `g`**, which is the use the source makes of the family.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.notMem_universalEndDomain_iff`: a point lies outside
  `U(ψ)` exactly when every degree-one form in the image of `ψ` vanishes at it, the relative form
  of `AlgebraicGeometry.ProjectiveSpaceOfModule.notMem_endDomain_iff`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndProjection_comp_toSpec`: **`r_ψ` is a
  morphism over the parameter space**, so it is a family of projective transformations
  parametrized by `S` and not merely a morphism of schemes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endParamFibreInclusion_comp_toSpec`: the fibre
  inclusion is a morphism over the point of `S` attached to `g`, so it really is the inclusion of
  the fibre over that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.fibreSquareIso_hom_comp_morphismRestrict`: **`r_g` is
  the fibre of `r_ψ` over the parameter point of `g`, as a square of scheme morphisms**:
  `r_ψ ∘ ι_g = ι_g ∘ r_g`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_universalFamilySpace`: **the total space
  of the family is the product `𝔸(E) × 𝐏(V)`**, the shape in which the source writes `0B2W`
  (there with `𝐏` in place of its cone `𝔸(E)`).

## Implementation notes

The relative projective space `𝐏(V ⊗ 𝒪_S)` over the affine base `S = Spec A` is Mathlib's `Proj`
of the graded ring `Sym_A(V ⊗ A)`, whose degree-zero part is `A`; the construction of `U(ψ)` and
`r_ψ` out of the graded ring homomorphism `Sym ψ` is then the same
`Stacks.AlgebraicGeometry.ProjShared.mapDomain` and
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` that produce the fibrewise `U(g)` and `r_g`,
applied over `A` instead of over `k`.

The source states the family over the *projective* parameter space `𝐏 = 𝐏(Eᵛ)`, as the relative
Proj morphism attached to the map of sheaves `ψ : V ⊗ 𝒪_𝐏 → V ⊗ 𝒪_𝐏(1)`, using the
identifications `𝐏(V ⊗ 𝒪_𝐏) = 𝐏(V ⊗ 𝒪_𝐏(1)) = 𝐏 × 𝐏(V)`. What is constructed here is its
pullback to the affine cone `𝔸(E) = Spec Sym(Eᵛ)` over `𝐏`, where `𝒪(1)` is trivial and the map
of sheaves becomes the honest endomorphism `universalEnd` of `V ⊗ 𝒪_{𝔸(E)}`; the fibre over the
point `g` of `𝔸(E)` is the fibre of the source's family over `[g] ∈ 𝐏`, for every nonzero `g`.
The family over `𝐏` is not obtained from this one by descent along `𝔸(E) ∖ {0} → 𝐏`: no such
descent is constructed anywhere. It is built directly from the source's own `ψ` in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyOverProjectiveSpace.lean`,
as `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafDomain` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection`.

The source's sentence that `U(g)` is the fibre `U(ψ)_{[g]}` and `r_g` the fibre of `r_ψ` over
`[g]` is here in full: the first half is `mem_universalEndDomain_iff`, and the second is
`fibreSquareIso_hom_comp_morphismRestrict`, the square of *scheme* morphisms
`r_ψ ∘ ι_g = ι_g ∘ r_g`. That square is the composition law
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp` applied to the two factorizations of the
one graded homomorphism that `endParamFibreHom_symAlgMap` provides; the generic form of that
argument, with the identification of the two domains the law carries, is
`Stacks.AlgebraicGeometry.ProjTwistChain.factorizationIso_hom_comp`. Both sides are morphisms
over the parameter space, by `universalEndProjection_comp_toSpec` and
`endParamFibreInclusion_comp_toSpec`.

The source's shape `𝐏 × 𝐏(V)` for the total space is here over the cone:
`isPullback_universalFamilySpace` is the cartesian square
`𝐏(V ⊗ 𝒪_S) = 𝔸(E) ×_{Spec k} 𝐏(V)`, and `universalFamilySpaceIso` the resulting isomorphism.
Both are the specialization to `k → Sym(Eᵛ)` of
`Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec`, which is Tag 01N2's
square `Stacks.ProjBaseChange.isPullback_map_Spec` transported along the base-change comparison
`SymPow.symAlgBaseChangeEquiv` of symmetric algebras read as an isomorphism of graded rings.

The family over `𝐏` itself is not in this file, and what used to be the obstruction to it is
*not* the partially defined relative Proj morphism. For a homomorphism of quasi-coherent graded
`𝒪_S`-algebras over an arbitrary base, with no surjectivity assumed, Tag 07ZG's open is
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain` and its
morphism is `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom`, both glued from the
absolute `mapDomain` and `mapHom` over the affine charts of the base. That machinery is now
pointed at an arbitrary base and an arbitrary morphism of quasi-coherent modules: the general
construction the source invokes for its `ψ` is
`Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleRationalMap`,

`𝐏(E₂) ⊇ U(u) --r_u--> 𝐏(E₁)` over `X`,

built from `Stacks.SymGraded.schemeSheafGradedAlgebraHom`, the functoriality of the sheafified
symmetric algebra. **That instantiation is now carried out**, in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyOverProjectiveSpace.lean`:
the morphism `ψ : V ⊗ 𝒪_𝐏 ⟶ V ⊗ 𝒪_𝐏(1)` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafMap`, and the family it gives over
the projective parameter space is
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafDomain` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection`. The two modules it runs
between are `Stacks.AlgebraicGeometry.BaseModuleOnScheme.tensorStructureSheaf`, quasi-coherent by
Tag 01BG, and `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` of it,
quasi-coherent by Tag 0GQM; `ψ` itself is written through the universal property
`Stacks.AlgebraicGeometry.BaseModuleOnScheme.homEquiv`,

`Hom_{𝒪_X}(V ⊗ 𝒪_X, M) ≃ Hom_k(V, Γ(X, M))`,

whose input, the `k`-linear map `V → Γ(𝐏, V ⊗ 𝒪_𝐏(1))`, is assembled from `universalEndCoeff`
and the canonical `k`-linear `Eᵛ → Γ(𝐏, 𝒪_𝐏(1))`. The latter is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.degreeSectionLinear`, which is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` once the `𝒮 0`-action of
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections` is identified with
the `k`-action that `AlgebraicGeometry.moduleSpecΓFunctor` puts on the global sections through
`AlgebraicGeometry.projectiveSpaceOfModuleToSpec`; that identification is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq`. Monoidality of
`V ↦ V ⊗ 𝒪_X` — which would have assembled `ψ` without ever naming a global section — is still
not available: neither `AlgebraicGeometry.tilde.functor` nor
`AlgebraicGeometry.Scheme.Modules.pullback` is recorded as monoidal for
`Stacks.AlgebraicGeometry.schemeMonoidalCategory`.

What remains absent over `𝐏` is only the *shape* of the source's display:

* **The invariance of a relative `Proj` under twisting the module by an invertible one**, which is
  what turns `𝐏(V ⊗ 𝒪_𝐏(1))` into the `𝐏 × 𝐏(V)` of the displayed equation. Only the absolute
  graded-ring form exists, `Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral` over
  a commutative ring; `relativeProj (twist 𝒜 ℒ) ≅ relativeProj 𝒜` over a base scheme is not
  stated anywhere. In consequence the fibre of the family over `𝐏` at a point `[g]` is not
  compared with `r_g`; that comparison is the one made here over the affine cone.

  The *product* half of the identification is no longer missing over `𝐏`. It is
  `Stacks.AlgebraicGeometry.ConstantModuleBundle.exists_isPullback_tensorStructureSheafBundle` of
  `StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyProductSpace.lean`,
  which is `isPullback_universalFamilySpace` with the affine base replaced by an arbitrary scheme
  over `Spec k`, and its instance at `𝐏` identifies the *target* `𝐏(V ⊗ 𝒪_𝐏)` of the family with
  `𝐏 × 𝐏(V)`. What `isPullback_universalFamilySpace` and
  `Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec` do not reach, being
  base change along a ring map, is exactly that non-affine instance.

Finite-dimensionality of `V` is needed and not merely convenient: the source's canonical map
lands in `Eᵛ ⊗ V ⊆ Hom(E, V)`, and `v ↦ (g ↦ g v)` has rank `dim V`, so it is a finite-rank
operator, hence in the image of `Eᵛ ⊗ V`, exactly when `V` is finite-dimensional.

## References

* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u w w'

section Generic

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The homogeneous prime of the image of a point under `r_ψ`.** A positive-degree homogeneous
element lies in it exactly when its image under `ψ` lies in the homogeneous prime of the point.
This is the generic form of
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_endProjection_iff`. -/
private theorem mem_mapHom_iff (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) {d : ℕ}
    (hd : 0 < d) {x : A} (hx : x ∈ 𝒜 d) :
    x ∈ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal ↔ ψ x ∈ (y.val : Proj ℬ).asHomogeneousIdeal := by
  have h := congrArg (y ∈ ·) (mapHom_preimage_basicOpen 𝒜 ℬ ψ x d hx hd)
  simp only [Scheme.Hom.mem_preimage, Proj.mem_basicOpen, eq_iff_iff] at h
  exact not_iff_not.mp h

/-- A surjective homomorphism of graded rings is surjective in each degree. -/
private theorem exists_mem_eq_of_surjective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ)
    {e : ℕ} {h : B} (hh : h ∈ ℬ e) : ∃ f : A, f ∈ 𝒜 e ∧ ψ f = h := by
  obtain ⟨a, rfl⟩ := hψ h
  refine ⟨GradedRing.proj 𝒜 e a, by rw [GradedRing.proj_apply]; exact SetLike.coe_mem _, ?_⟩
  rw [GradedRing.proj_apply, ψ.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hh]

/-- The morphism induced by a graded ring homomorphism is compatible with the maps to the spectrum
of a ring `R` mapping into the degree-zero parts, whenever the maps agree in degree zero. -/
private theorem mapHom_comp_toSpec_map {R : Type u} [CommRing R] (ψ : 𝒜 →+*ᵍ ℬ)
    (a : R →+* 𝒜 0) (b : R →+* ℬ 0)
    (h : (Stacks.AlgebraicGeometry.RelativeProj.zeroHom 𝒜 ℬ ψ).comp a = b) :
    mapHom 𝒜 ℬ ψ ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom a) =
      (mapDomain 𝒜 ℬ ψ).ι ≫ Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom b) := by
  rw [← Category.assoc, Stacks.AlgebraicGeometry.RelativeProj.mapHom_toSpecZero]
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

end Generic

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The homogeneous coordinate ring `A = Sym((End V)ᵛ)` of the parameter space `𝐏 = 𝐏((End V)ᵛ)`
of a projective transformation. Its spectrum is the affine space of endomorphisms of `V`. -/
public abbrev endParamRing : Type u := SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V))

/-- **The canonical map `V → (End V)ᵛ ⊗ V = Hom(End V, V)`** of the source, sending `v` to the
evaluation `g ↦ g v`. -/
@[stacks 0B2W "the canonical map V → V ⊗ Eᵛ = Hom(E, V), v ↦ (g ↦ g v)"]
public def universalEndCoeff : V →ₗ[k] Module.Dual k (V →ₗ[k] V) ⊗[k] V :=
  (dualTensorHomEquiv k (V →ₗ[k] V) V).symm.toLinearMap ∘ₗ
    (LinearMap.applyₗ (R := k) (M := V) (M₂ := V))

/-- **The universal endomorphism `ψ` of `V ⊗ 𝒪` over the affine parameter space**: the `A`-linear
extension of the canonical map `V → (End V)ᵛ ⊗ V ⊆ A ⊗ V`. On the fibre over an endomorphism `g`
it is `g`. -/
@[stacks 0B2W "ψ over the affine parameter space Spec Sym(Eᵛ), the cone over 𝐏: the universal \
endomorphism of V ⊗ 𝒪, in place of the map of sheaves V ⊗ 𝒪_𝐏 → V ⊗ 𝒪_𝐏(1) over 𝐏"]
public def universalEnd :
    endParamRing k V ⊗[k] V →ₗ[endParamRing k V] endParamRing k V ⊗[k] V :=
  LinearMap.liftBaseChange _
    (TensorProduct.map (SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))) LinearMap.id ∘ₗ
      universalEndCoeff k V)

/-- **The open `U(ψ)` of the universal family**: the domain of definition of the morphism of
relative projective spaces induced by `Sym ψ` over the affine parameter space. -/
@[stacks 0B2W "U(ψ) ⊆ 𝐏(V ⊗ 𝒪_S) for S = Spec Sym(Eᵛ) the affine parameter space, the cone \
over 𝐏; the open over 𝐏 itself is \
AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafDomain, built there from the \
source's own ψ : V ⊗ 𝒪_𝐏 → V ⊗ 𝒪_𝐏(1) and not from this one by descent along 𝔸(E) ∖ {0} → 𝐏, \
which is constructed nowhere; what is not identified with 𝐏 × 𝐏(V) is its ambient 𝐏(V ⊗ \
𝒪_𝐏(1))"]
public abbrev universalEndDomain :
    (projectiveSpaceOfModule (endParamRing k V) (endParamRing k V ⊗[k] V)).Opens :=
  mapDomain _ _ (SymPow.gradedSymAlgMap (universalEnd k V))

/-- **The universal family `r_ψ` of projective transformations**, `𝐏(V ⊗ 𝒪_S) ⊇ U(ψ) → 𝐏(V ⊗ 𝒪_S)`
over the affine space `S` of endomorphisms of `V`: the morphism of relative projective spaces
induced by `Sym ψ` on its domain of definition. -/
@[stacks 0B2W "r_ψ : U(ψ) → 𝐏(V ⊗ 𝒪_S) for S = Spec Sym(Eᵛ) the affine parameter space, the \
cone over 𝐏; the morphism over 𝐏 itself is \
AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection, built there from the \
source's own ψ and not from this one by descent along 𝔸(E) ∖ {0} → 𝐏, which is constructed \
nowhere; what is not identified with 𝐏 × 𝐏(V) are its total spaces"]
public def universalEndProjection :
    (universalEndDomain k V).toScheme ⟶
      projectiveSpaceOfModule (endParamRing k V) (endParamRing k V ⊗[k] V) :=
  mapHom _ _ (SymPow.gradedSymAlgMap (universalEnd k V))

/-- The point of the affine parameter space attached to an endomorphism `g` of `V`: the
`k`-algebra homomorphism `Sym((End V)ᵛ) → k` evaluating a functional at `g`. -/
public def endParamPoint (g : V →ₗ[k] V) : endParamRing k V →ₐ[k] k :=
  SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g)

/-- Specialization of `V ⊗ A` at the parameter point attached to `g`, giving `V`. -/
public def endParamFibre (g : V →ₗ[k] V) : endParamRing k V ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap ∘ₗ LinearMap.rTensor V (endParamPoint k V g).toLinearMap

omit [Module.Finite k V] in
private theorem endParamFibre_tmul (g : V →ₗ[k] V) (a : endParamRing k V) (v : V) :
    endParamFibre k V g (a ⊗ₜ[k] v) = endParamPoint k V g a • v := rfl

omit [Module.Finite k V] in
private theorem endParamFibre_smul (g : V →ₗ[k] V) (a : endParamRing k V)
    (y : endParamRing k V ⊗[k] V) :
    endParamFibre k V g (a • y) = endParamPoint k V g a • endParamFibre k V g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [smul_tmul', endParamFibre_tmul, endParamFibre_tmul, smul_eq_mul,
      _root_.map_mul, mul_smul]
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]

omit [Module.Finite k V] in
/-- Specializing the canonical map `V → (End V)ᵛ ⊗ V` at `g` evaluates it at `g`. -/
private theorem endParamFibre_map_ι (g : V →ₗ[k] V)
    (z : Module.Dual k (V →ₗ[k] V) ⊗[k] V) :
    endParamFibre k V g
        (TensorProduct.map (SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))) LinearMap.id z) =
      dualTensorHom k (V →ₗ[k] V) V z g := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v => simp [endParamFibre_tmul, endParamPoint, dualTensorHom_apply]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, LinearMap.add_apply]

/-- **The fibre of the universal endomorphism over the parameter point of `g` is `g`.** This is
what makes `universalEnd` universal: the family it defines has `r_g` as its fibre over `g`. -/
@[stacks 0B2W "the fibre of ψ over the parameter point of g is g"]
public theorem endParamFibre_universalEnd (g : V →ₗ[k] V) (x : endParamRing k V ⊗[k] V) :
    endParamFibre k V g (universalEnd k V x) = g (endParamFibre k V g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [universalEnd, LinearMap.liftBaseChange_tmul, endParamFibre_smul, LinearMap.comp_apply,
      endParamFibre_map_ι, endParamFibre_tmul, map_smul]
    congr 1
    show dualTensorHom k (V →ₗ[k] V) V
      ((dualTensorHomEquiv k (V →ₗ[k] V) V).symm (LinearMap.applyₗ (R := k) (M₂ := V) v)) g = g v
    exact congrFun (congrArg DFunLike.coe
      ((dualTensorHomEquiv k (V →ₗ[k] V) V).apply_symm_apply
        (LinearMap.applyₗ (R := k) (M₂ := V) v))) g
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Reduction of coefficients at the parameter point of `g`, `A ⊗ Sym_k(V) → Sym_k(V)`. -/
public def endParamFibreCoeff (g : V →ₗ[k] V) :
    endParamRing k V ⊗[k] SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId k (SymmetricAlgebra k V)).comp (endParamPoint k V g))
    (AlgHom.id k (SymmetricAlgebra k V)) fun _ _ => Commute.all _ _

omit [Module.Finite k V] in
private theorem endParamFibreCoeff_tmul (g : V →ₗ[k] V) (a : endParamRing k V)
    (x : SymmetricAlgebra k V) :
    endParamFibreCoeff k V g (a ⊗ₜ[k] x) = endParamPoint k V g a • x := by
  simp only [endParamFibreCoeff, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, Algebra.ofId_apply, AlgHom.id_apply, Algebra.smul_def]

/-- Specialization of the homogeneous coordinate ring of the universal family at the parameter
point of `g`: the ring homomorphism `Sym_A(V ⊗ A) → Sym_k(V)` reducing the coefficients along
`endParamPoint`, through the base-change comparison of symmetric algebras. -/
public def endParamFibreHom (g : V →ₗ[k] V) :
    SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V) →+* SymmetricAlgebra k V :=
  (endParamFibreCoeff k V g).toRingHom.comp
    (SymPow.symAlgBaseChangeInv (endParamRing k V) V).toRingHom

omit [Module.Finite k V] in
private theorem endParamFibreHom_ι (g : V →ₗ[k] V) (x : endParamRing k V ⊗[k] V) :
    endParamFibreHom k V g
        (SymmetricAlgebra.ι (endParamRing k V) (endParamRing k V ⊗[k] V) x) =
      SymmetricAlgebra.ι k V (endParamFibre k V g x) := by
  show endParamFibreCoeff k V g (SymPow.symAlgBaseChangeInv (endParamRing k V) V
    (SymmetricAlgebra.ι (endParamRing k V) (endParamRing k V ⊗[k] V) x)) = _
  rw [SymPow.symAlgBaseChangeInv_ι]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, endParamFibreCoeff_tmul, endParamFibre_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Module.Finite k V] in
private theorem endParamFibreHom_algebraMap (g : V →ₗ[k] V) (a : endParamRing k V) :
    endParamFibreHom k V g
        (algebraMap (endParamRing k V)
          (SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V)) a) =
      algebraMap k (SymmetricAlgebra k V) (endParamPoint k V g a) := by
  show endParamFibreCoeff k V g (SymPow.symAlgBaseChangeInv (endParamRing k V) V
    (algebraMap _ _ a)) = _
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, endParamFibreCoeff_tmul,
    Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]

/-- **`Sym g` is the fibre of `Sym ψ` over the parameter point of `g`.** Reducing the universal
graded endomorphism of `Sym_A(V ⊗ A)` along the point of the parameter space attached to an
endomorphism `g` of `V` gives the graded endomorphism `Sym g` of `Sym_k(V)` out of which `U(g)`
and `r_g` are built. -/
@[stacks 0B2W "the fibre of r_ψ over the parameter point of g is r_g, on the homogeneous \
coordinate rings: Sym ψ reduces to Sym g"]
public theorem endParamFibreHom_symAlgMap (g : V →ₗ[k] V)
    (x : SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V)) :
    endParamFibreHom k V g (SymPow.symAlgMap (universalEnd k V) x) =
      SymPow.symAlgMap g (endParamFibreHom k V g x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap a =>
    rw [AlgHom.commutes, endParamFibreHom_algebraMap]
    exact (AlgHom.commutes _ _).symm
  | ι x =>
    rw [SymPow.symAlgMap_ι, endParamFibreHom_ι, endParamFibreHom_ι, SymPow.symAlgMap_ι,
      endParamFibre_universalEnd]
  | mul a b ha hb => simp only [_root_.map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The coefficient reduction carries the degree-`n` symmetric power of `V ⊗ A` over `A` into
the degree-`n` symmetric power of `V` over `k`. -/
public theorem endParamFibreHom_mem (g : V →ₗ[k] V) {n : ℕ}
    {x : SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V)}
    (hx : x ∈ SymPow.symmetricPower n (endParamRing k V) (endParamRing k V ⊗[k] V)) :
    endParamFibreHom k V g x ∈ SymPow.symmetricPower n k V := by
  rw [SymPow.symmetricPower] at hx ⊢
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [endParamFibreHom_algebraMap, pow_zero]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [_root_.map_mul, endParamFibreHom_ι, pow_succ']
    exact Submodule.mul_mem_mul ⟨_, rfl⟩ ih

/-- **The specialization at the parameter point of `g`, as a homomorphism of graded rings**
`Sym_A(V ⊗ A) → Sym_k(V)`. -/
public def endParamFibreGradedHom (g : V →ₗ[k] V) :
    (fun n => SymPow.symmetricPower n (endParamRing k V) (endParamRing k V ⊗[k] V)) →+*ᵍ
      (fun n => SymPow.symmetricPower n k V) where
  __ := endParamFibreHom k V g
  map_mem := fun {_} {_} hx => endParamFibreHom_mem k V g hx

private theorem endParamFibreGradedHom_apply (g : V →ₗ[k] V)
    (x : SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V)) :
    endParamFibreGradedHom k V g x = endParamFibreHom k V g x := rfl

omit [Module.Finite k V] in
/-- The specialization at a parameter point is surjective: the fibre of the universal family is
cut out by the whole homogeneous coordinate ring of `𝐏(V)`. -/
public theorem endParamFibreHom_surjective (g : V →ₗ[k] V) :
    Function.Surjective (endParamFibreHom k V g) := by
  intro y
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    refine ⟨algebraMap (endParamRing k V) _ (algebraMap k (endParamRing k V) r), ?_⟩
    rw [endParamFibreHom_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply]
  | ι v =>
    refine ⟨SymmetricAlgebra.ι (endParamRing k V) _ ((1 : endParamRing k V) ⊗ₜ[k] v), ?_⟩
    rw [endParamFibreHom_ι, endParamFibre_tmul, _root_.map_one, one_smul]
  | mul a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨z, rfl⟩ := hb
    exact ⟨x * z, _root_.map_mul _ _ _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨z, rfl⟩ := hb
    exact ⟨x + z, map_add _ _ _⟩

/-- The specialization at a parameter point is surjective as a homomorphism of graded rings. -/
public theorem endParamFibreGradedHom_surjective (g : V →ₗ[k] V) :
    Function.Surjective (endParamFibreGradedHom k V g) := fun y => by
  obtain ⟨x, hx⟩ := endParamFibreHom_surjective k V g y
  exact ⟨x, (endParamFibreGradedHom_apply k V g x).trans hx⟩

/-- The grading of the homogeneous coordinate ring of the universal family. -/
private abbrev famGrading :
    ℕ → Submodule (endParamRing k V)
      (SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V)) :=
  fun n => SymPow.symmetricPower n (endParamRing k V) (endParamRing k V ⊗[k] V)

/-- The domain of definition of the specialization at a parameter point, which is all of
`𝐏(V)`. -/
public abbrev endParamFibreInclusionDomain (g : V →ₗ[k] V) :
    (projectiveSpaceOfModule k V).Opens :=
  mapDomain _ _ (endParamFibreGradedHom k V g)

public theorem endParamFibreInclusionDomain_eq_top (g : V →ₗ[k] V) :
    endParamFibreInclusionDomain k V g = ⊤ :=
  mapDomain_eq_top_of_surjective _ _ _ (endParamFibreHom_surjective k V g)

/-- **The fibre of the universal family over the parameter point of `g`**: the morphism
`𝐏(V) → 𝐏(V ⊗ 𝒪_S)` induced by the specialization of the homogeneous coordinate ring, defined on
all of `𝐏(V)` by `endParamFibreInclusionDomain_eq_top`. -/
@[stacks 0B2W "the inclusion of the fibre of 𝐏(V ⊗ 𝒪_S) over the parameter point of g"]
public def endParamFibreInclusion (g : V →ₗ[k] V) :
    (endParamFibreInclusionDomain k V g).toScheme ⟶
      projectiveSpaceOfModule (endParamRing k V) (endParamRing k V ⊗[k] V) :=
  mapHom _ _ (endParamFibreGradedHom k V g)

/-- **`U(g)` is the fibre `U(ψ)` over the parameter point of `g`.** A point of `𝐏(V)`, included
as a point of the fibre of the relative projective space over the parameter point of `g`, lies in
the domain of the universal family exactly when it lies in `U(g)`, the domain of `r_g`. -/
@[stacks 0B2W "U(g) is the fibre U(ψ) over the parameter point of g"]
public theorem mem_universalEndDomain_iff (g : V →ₗ[k] V)
    (y : (endParamFibreInclusionDomain k V g).toScheme) :
    (endParamFibreInclusion k V g).base y ∈ universalEndDomain k V ↔
      (y.val : projectiveSpaceOfModule k V) ∈ endDomain k V g := by
  rw [mem_mapDomain_iff, mem_mapDomain_iff]
  have key : ∀ d : ℕ, 0 < d →
      ∀ x : SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V),
        x ∈ famGrading k V d →
        (SymPow.symAlgMap (universalEnd k V) x ∈
            ((endParamFibreInclusion k V g).base y).asHomogeneousIdeal ↔
          SymPow.symAlgMap g (endParamFibreHom k V g x) ∈
            (y.val : projectiveSpaceOfModule k V).asHomogeneousIdeal) := by
    intro d hd x hx
    rw [← (endParamFibreGradedHom_apply k V g _).trans (endParamFibreHom_symAlgMap k V g x)]
    exact mem_mapHom_iff (famGrading k V) (symmetricGrading k V) (endParamFibreGradedHom k V g) y hd
      (SymPow.symAlgMap_mapsTo d (universalEnd k V) x hx)
  constructor
  · rintro ⟨d, f, hd, hf, hfy⟩
    exact ⟨d, endParamFibreHom k V g f, hd, endParamFibreHom_mem k V g hf,
      fun hmem => hfy ((key d hd f hf).mpr hmem)⟩
  · rintro ⟨e, h, he, hh, hhy⟩
    have hex : ∃ f : SymmetricAlgebra (endParamRing k V) (endParamRing k V ⊗[k] V),
        f ∈ famGrading k V e ∧ endParamFibreGradedHom k V g f = h :=
      exists_mem_eq_of_surjective (famGrading k V) (symmetricGrading k V)
        (endParamFibreGradedHom k V g) (endParamFibreGradedHom_surjective k V g) hh
    obtain ⟨f, hf, hfh⟩ := hex
    refine ⟨e, f, he, hf, fun hmem => hhy ?_⟩
    rw [← hfh, endParamFibreGradedHom_apply]
    exact (key e he f hf).mp hmem

/-- The image under `Sym f` of a positive-degree symmetric power lands in the homogeneous prime
of any point at which every degree-one form in the image of `f` vanishes. -/
private theorem symAlgMap_mem_of_forall_ι_mem {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] (f : M →ₗ[R] M) (q : projectiveSpaceOfModule R M)
    (h : ∀ v : M, SymmetricAlgebra.ι R M (f v) ∈ q.asHomogeneousIdeal)
    (d : ℕ) (hd : 0 < d) (x : SymmetricAlgebra R M) (hx : x ∈ SymPow.symmetricPower d R M) :
    SymPow.symAlgMap f x ∈ q.asHomogeneousIdeal.toIdeal := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [SymPow.symmetricPower, pow_succ'] at hx
  refine Submodule.mul_induction_on hx ?_ fun a b ha hb => by rw [map_add]; exact add_mem ha hb
  rintro a ⟨v, rfl⟩ b _
  rw [_root_.map_mul, SymPow.symAlgMap_ι]
  exact q.asHomogeneousIdeal.toIdeal.mul_mem_right _ (h v)

/-- **The domain of the universal family.** A point lies outside `U(ψ)` exactly when every
degree-one form in the image of the universal endomorphism vanishes at it: the relative form of
the description of the complement of `U(g)` as the image of `𝐏(Coker g) → 𝐏(V)`. -/
@[stacks 0B2W "the complement of U(ψ) is the relative 𝐏(Coker ψ), as the vanishing of the \
degree-one forms in the image of ψ"]
public theorem notMem_universalEndDomain_iff
    (q : projectiveSpaceOfModule (endParamRing k V) (endParamRing k V ⊗[k] V)) :
    q ∉ universalEndDomain k V ↔
      ∀ x : endParamRing k V ⊗[k] V,
        SymmetricAlgebra.ι (endParamRing k V) (endParamRing k V ⊗[k] V) (universalEnd k V x) ∈
          q.asHomogeneousIdeal := by
  constructor
  · intro h x
    by_contra hmem
    refine h ((mem_mapDomain_iff _ _ _ q).mpr
      ⟨1, SymmetricAlgebra.ι (endParamRing k V) (endParamRing k V ⊗[k] V) x, Nat.one_pos,
        by simp, ?_⟩)
    simpa [SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι] using hmem
  · intro h hq
    obtain ⟨d, x, hd, hx, hxq⟩ := (mem_mapDomain_iff _ _ _ q).mp hq
    exact hxq (symAlgMap_mem_of_forall_ι_mem (universalEnd k V) q h d hd x hx)

/-! ### The family over the parameter space -/

/-- The degree-zero part of the universal graded endomorphism is the identity on the coordinate
ring of the parameter space: `Sym ψ` is an `A`-algebra homomorphism. -/
public theorem zeroHom_universalEnd_comp_algebraMap :
    (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _
          (SymPow.gradedSymAlgMap (universalEnd k V))).comp
        (algebraMap (endParamRing k V)
          ↥(SymPow.symmetricPower 0 (endParamRing k V) (endParamRing k V ⊗[k] V))) =
      algebraMap (endParamRing k V)
        ↥(SymPow.symmetricPower 0 (endParamRing k V) (endParamRing k V ⊗[k] V)) :=
  RingHom.ext fun r => Subtype.ext
    ((Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply _ _
        (SymPow.gradedSymAlgMap (universalEnd k V)) _).trans
      ((SymPow.symAlgMap (universalEnd k V)).commutes r))

/-- **The universal family is a family over the parameter space.** The morphism `r_ψ` commutes
with the two structure morphisms of the relative projective space `𝐏(V ⊗ 𝒪_S)` to
`S = Spec Sym((End V)ᵛ)`, so it is a family of projective transformations parametrized by `S`
and its fibres are morphisms of the fibres. -/
@[stacks 0B2W "r_ψ is a morphism over the parameter space S = Spec Sym(Eᵛ), the cone over 𝐏"]
public theorem universalEndProjection_comp_toSpec :
    universalEndProjection k V ≫
        projectiveSpaceOfModuleToSpec (endParamRing k V) (endParamRing k V ⊗[k] V) =
      (universalEndDomain k V).ι ≫
        projectiveSpaceOfModuleToSpec (endParamRing k V) (endParamRing k V ⊗[k] V) := by
  exact mapHom_comp_toSpec_map _ _ (SymPow.gradedSymAlgMap (universalEnd k V))
    (algebraMap (endParamRing k V) _) _ (zeroHom_universalEnd_comp_algebraMap k V)

/-- The degree-zero part of the specialization at the parameter point of `g` is that point: on
the coordinate ring of the parameter space the specialization is `endParamPoint`. -/
public theorem zeroHom_endParamFibreGradedHom_comp_algebraMap (g : V →ₗ[k] V) :
    (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _ (endParamFibreGradedHom k V g)).comp
        (algebraMap (endParamRing k V)
          ↥(SymPow.symmetricPower 0 (endParamRing k V) (endParamRing k V ⊗[k] V))) =
      (algebraMap k ↥(SymPow.symmetricPower 0 k V)).comp (endParamPoint k V g).toRingHom :=
  RingHom.ext fun r => Subtype.ext
    ((Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply _ _
        (endParamFibreGradedHom k V g) _).trans (endParamFibreHom_algebraMap k V g r))

/-- **The fibre of the relative projective space over the parameter point of `g` is where `𝐏(V)`
goes.** The inclusion `ι_g : 𝐏(V) → 𝐏(V ⊗ 𝒪_S)` is a morphism over the point of `S` attached to
`g`, which is what makes it the inclusion of a fibre rather than merely a morphism. -/
@[stacks 0B2W "the fibre inclusion is a morphism over the parameter point of g"]
public theorem endParamFibreInclusion_comp_toSpec (g : V →ₗ[k] V) :
    endParamFibreInclusion k V g ≫
        projectiveSpaceOfModuleToSpec (endParamRing k V) (endParamRing k V ⊗[k] V) =
      (endParamFibreInclusionDomain k V g).ι ≫ projectiveSpaceOfModuleToSpec k V ≫
        Spec.map (CommRingCat.ofHom (endParamPoint k V g).toRingHom) := by
  refine (mapHom_comp_toSpec_map _ _ (endParamFibreGradedHom k V g)
    (algebraMap (endParamRing k V) _) _
    (zeroHom_endParamFibreGradedHom_comp_algebraMap k V g)).trans ?_
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  rfl

/-! ### The square of scheme morphisms over a parameter point -/

/-- **The two factorizations of one graded homomorphism.** Specializing `Sym ψ` at the parameter
point of `g` and then nothing, or specializing first and then applying `Sym g`, give the same
graded ring homomorphism `Sym_A(V ⊗ A) → Sym_k(V)`. This is
`endParamFibreHom_symAlgMap` read as an equality of graded ring homomorphisms, which is the form
the composition law for the induced morphisms of projective spectra consumes. -/
public theorem endParamFibreGradedHom_comp_gradedSymAlgMap (g : V →ₗ[k] V) :
    (endParamFibreGradedHom k V g).comp (SymPow.gradedSymAlgMap (universalEnd k V)) =
      (SymPow.gradedSymAlgMap g).comp (endParamFibreGradedHom k V g) :=
  GradedRingHom.ext fun x =>
    (endParamFibreGradedHom_apply k V g _).trans (endParamFibreHom_symAlgMap k V g x)

/-- The part of `U(g)` that `r_g` carries into the fibre of the relative projective space over
the parameter point of `g`. It is all of `U(g)`, since that fibre is the whole of `𝐏(V)`. -/
public abbrev fibreSquareSource (g : V →ₗ[k] V) : (endDomain k V g).toScheme.Opens :=
  endProjection k V g ⁻¹ᵁ endParamFibreInclusionDomain k V g

/-- The part of the fibre over the parameter point of `g` that the fibre inclusion carries into
`U(ψ)`. By `mem_universalEndDomain_iff` it is `U(g)`. -/
public abbrev fibreSquareTarget (g : V →ₗ[k] V) :
    (endParamFibreInclusionDomain k V g).toScheme.Opens :=
  endParamFibreInclusion k V g ⁻¹ᵁ universalEndDomain k V

/-- **The canonical identification of the two domains of the fibre square.** Both the part of
`U(g)` that `r_g` carries into the fibre and the part of the fibre that `ι_g` carries into `U(ψ)`
are, by Tag 01MZ's description of the domain of a composite, canonically isomorphic to the domain
of definition of the composite graded homomorphism — and that composite is one and the same
homomorphism read the two ways, by `endParamFibreGradedHom_comp_gradedSymAlgMap`. -/
public def fibreSquareIso (g : V →ₗ[k] V) :
    (fibreSquareSource k V g).toScheme ≅ (fibreSquareTarget k V g).toScheme :=
  factorizationIso _ _ _ _ (endParamFibreGradedHom k V g) (SymPow.gradedSymAlgMap g)
    (SymPow.gradedSymAlgMap (universalEnd k V)) (endParamFibreGradedHom k V g)
    (endParamFibreGradedHom_comp_gradedSymAlgMap k V g).symm

/-- **`r_g` is the fibre of `r_ψ` over the parameter point of `g`, as a square of scheme
morphisms.** Including the fibre `𝐏(V)` into the relative projective space and then applying the
universal family `r_ψ` is the same as applying `r_g` and then including the fibre: the square

`U(g) --r_g--> 𝐏(V) --ι_g--> 𝐏(V ⊗ 𝒪_S)`,  `U(g) --ι_g--> U(ψ) --r_ψ--> 𝐏(V ⊗ 𝒪_S)`

commutes, after the canonical identification `fibreSquareIso` of the two domains.

This is the composition law of Tag 01MZ applied to the two factorizations
`endParamFibreGradedHom_comp_gradedSymAlgMap` of a single graded ring homomorphism. -/
@[stacks 0B2W "the fibre of r_ψ over the parameter point of g is r_g, as scheme morphisms"]
public theorem fibreSquareIso_hom_comp_morphismRestrict (g : V →ₗ[k] V) :
    (fibreSquareIso k V g).hom ≫
        (endParamFibreInclusion k V g ∣_ universalEndDomain k V) ≫ universalEndProjection k V =
      (endProjection k V g ∣_ endParamFibreInclusionDomain k V g) ≫
        endParamFibreInclusion k V g :=
  factorizationIso_hom_comp _ _ _ _ (endParamFibreGradedHom k V g) (SymPow.gradedSymAlgMap g)
    (SymPow.gradedSymAlgMap (universalEnd k V)) (endParamFibreGradedHom k V g)
    (endParamFibreGradedHom_comp_gradedSymAlgMap k V g).symm

/-! ### The total space of the family is a product -/

omit [Module.Finite k V] in
/-- **The relative projective space of the family is a product.** The square formed by the
projection `𝐏(V ⊗ 𝒪_S) ⟶ 𝐏(V)` and the two structure morphisms is cartesian, so
`𝐏(V ⊗ 𝒪_S) = S ×_{Spec k} 𝐏(V)` with `S = Spec Sym((End V)ᵛ)` the affine space of
endomorphisms. This is `Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec`
for the base change of `V` along `k → Sym((End V)ᵛ)`. -/
@[stacks 0B2W "the total space of the family is the product 𝔸(E) × 𝐏(V), for 𝔸(E) = Spec \
Sym(Eᵛ) the cone over 𝐏; the source writes the displayed family on 𝐏 × 𝐏(V)"]
public theorem isPullback_universalFamilySpace :
    IsPullback (Stacks.ProjectiveSpaceBaseChange.map k (endParamRing k V) V)
      (projectiveSpaceOfModuleToSpec (endParamRing k V) (endParamRing k V ⊗[k] V))
      (projectiveSpaceOfModuleToSpec k V)
      (Spec.map (CommRingCat.ofHom (algebraMap k (endParamRing k V)))) :=
  Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec k
    (endParamRing k V) V

/-- **The total space of the family, as the product `𝔸(E) × 𝐏(V)`.** The identification of
`𝐏(V ⊗ 𝒪_S)` with the fibre product of `𝐏(V)` and the affine space of endomorphisms over
`Spec k`, carried by `isPullback_universalFamilySpace`. -/
@[stacks 0B2W "the identification 𝐏(V ⊗ 𝒪_S) = 𝔸(E) × 𝐏(V) over the cone 𝔸(E) = Spec Sym(Eᵛ)"]
public def universalFamilySpaceIso :
    projectiveSpaceOfModule (endParamRing k V) (endParamRing k V ⊗[k] V) ≅
      Limits.pullback (projectiveSpaceOfModuleToSpec k V)
        (Spec.map (CommRingCat.ofHom (algebraMap k (endParamRing k V)))) :=
  Stacks.ProjectiveSpaceBaseChange.isoPullback k (endParamRing k V) V

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
