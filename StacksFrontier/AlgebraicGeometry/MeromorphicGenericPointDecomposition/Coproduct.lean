module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Quasicoherent

/-!
# The direct sum decomposition of the sheaf of meromorphic functions

Let `X` be a scheme whose weakly associated points are generic points of irreducible components
and whose quasi-compact opens have finitely many irreducible components. The sheaf of
meromorphic functions on `X` is then not only the *product* over the generic points `η` of the
irreducible components of the contributions `j_{η, *} 𝒪_{Spec 𝒪_{X, η}}`, but also their *direct
sum*.

This is the first sentence of the source's proof: a locally finite direct sum of sheaves of
modules agrees with the product. The family of generic-point contributions is locally finite
because on a quasi-compact open only the finitely many generic points lying in it contribute any
sections at all, the remaining contributions restricting to zero objects.

## Main definitions

* `CategoryTheory.Limits.toPiSingle`: the morphism from one factor into a product which is the
  identity in that coordinate and zero in the others.
* `CategoryTheory.Limits.sigmaPiComparison`: the canonical morphism from a coproduct to the
  product of the same family.

## Main results

* `CategoryTheory.Limits.isIso_sigmaPiComparison_of_isZero`: a family all but finitely many of
  whose members are zero objects has coproduct the product.
* `CategoryTheory.Limits.isIso_map_sigmaPiComparison`: a functor preserving zero morphisms and
  products and coproducts of the given shape carries the comparison morphism to the comparison
  morphism.
* `AlgebraicGeometry.isIso_sigmaPiComparison_of_locallyFinite`: a family of modules on a scheme
  which is finite modulo zero objects on each member of an open covering has coproduct the
  product.
* `AlgebraicGeometry.meromorphicFunctions_iso_coproduct_genericPointStalks`: the direct sum
  decomposition of the sheaf of meromorphic functions, Tag 0EMF; and
  `meromorphicFunctions_iso_coproduct_genericPointStalks_of_isReduced`, its reduced case, which
  is Tag 02OW.

## Implementation notes

The comparison morphism is used, rather than an isomorphism produced locally and then glued,
because isomorphisms do not glue: the point of
`AlgebraicGeometry.isIso_sigmaPiComparison_of_locallyFinite` is that one fixed morphism is
tested on each member of the covering. Locality is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, and the identification of
the restriction of the comparison morphism with the comparison morphism of the restrictions is
`CategoryTheory.Limits.isIso_map_sigmaPiComparison`, applied to the restriction functor: it
preserves coproducts because it is a left adjoint, and products because its product comparison
morphism was already shown invertible in
`StacksDraft.AlgebraicGeometry.F3b.GenericPointDecomposition.Quasicoherent`.

Over a finite index the comparison morphism is inverted explicitly by the sum of the
`π_i ≫ ι_i` over the surviving indices, which avoids setting up a bicone and matching its
canonical maps against the comparison morphism.

The decidability of equality on the index type that the comparison morphism needs is supplied
classically inside the proofs, so that it appears in no statement about schemes.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace CategoryTheory.Limits

/-! ### The comparison morphism from a coproduct to a product -/

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} [DecidableEq ι]

/-- The morphism from one factor of a family into its product which is the identity in that
coordinate and zero in every other. -/
noncomputable def toPiSingle (M : ι → C) [HasProduct M] (i : ι) : M i ⟶ ∏ᶜ M :=
  Pi.lift fun j ↦ if h : i = j then eqToHom (congrArg M h) else 0

/-- The `j`-th coordinate of `toPiSingle M i` is the identity when `i = j` and zero otherwise. -/
@[reassoc (attr := simp)]
lemma toPiSingle_comp_π (M : ι → C) [HasProduct M] (i j : ι) :
    toPiSingle M i ≫ Pi.π M j = if h : i = j then eqToHom (congrArg M h) else 0 :=
  Pi.lift_π _ _

/-- The canonical morphism from the coproduct of a family to its product. -/
noncomputable def sigmaPiComparison (M : ι → C) [HasProduct M] [HasCoproduct M] :
    ∐ M ⟶ ∏ᶜ M :=
  Sigma.desc (toPiSingle M)

/-- On the `i`-th summand, the comparison morphism from the coproduct to the product is
`toPiSingle M i`. -/
@[reassoc (attr := simp)]
lemma ι_comp_sigmaPiComparison (M : ι → C) [HasProduct M] [HasCoproduct M] (i : ι) :
    Sigma.ι M i ≫ sigmaPiComparison M = toPiSingle M i :=
  Sigma.ι_desc _ _

/-- The entry of the comparison morphism from the `i`-th summand of the coproduct to the `j`-th
factor of the product is the identity when `i = j` and zero otherwise. -/
lemma ι_comp_sigmaPiComparison_comp_π (M : ι → C) [HasProduct M] [HasCoproduct M] (i j : ι) :
    Sigma.ι M i ≫ sigmaPiComparison M ≫ Pi.π M j =
      if h : i = j then eqToHom (congrArg M h) else 0 := by
  rw [ι_comp_sigmaPiComparison_assoc, toPiSingle_comp_π]

/-- A family of objects all but finitely many of which are zero has its coproduct equal to its
product: the comparison morphism is inverted by the sum, over the surviving indices, of the
projection followed by the inclusion. -/
lemma isIso_sigmaPiComparison_of_isZero (M : ι → C) [HasProduct M] [HasCoproduct M]
    (p : ι → Prop) [Finite {i // p i}] (hz : ∀ i, ¬ p i → IsZero (M i)) :
    IsIso (sigmaPiComparison M) := by
  cases nonempty_fintype {i // p i}
  have key : ∀ (i : ι) {A B : C} (f : {k // p k} → (A ⟶ B)) (g : A ⟶ B),
      (∀ s : {k // p k}, (s : ι) ≠ i → f s = 0) → (∀ h : p i, f ⟨i, h⟩ = g) → (¬ p i → g = 0) →
      ∑ s, f s = g := by
    intro i A B f g h0 h1 h2
    by_cases hi : p i
    · exact (Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)
        fun s _ hs ↦ h0 s fun h ↦ hs (Subtype.ext h)).trans (h1 hi)
    · refine (Finset.sum_eq_zero fun s _ ↦ h0 s fun h ↦ hi (h ▸ s.2)).trans (h2 hi).symm
  refine ⟨∑ s : {i // p i}, Pi.π M s.1 ≫ Sigma.ι M s.1, ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Category.comp_id, ← Category.assoc, Preadditive.comp_sum]
    refine key i _ _ (fun s hs ↦ ?_) (fun _ ↦ ?_) fun hi ↦ (hz i hi).eq_zero_of_src _
    · simp [Ne.symm hs]
    · simp
  · refine Pi.hom_ext _ _ fun j ↦ ?_
    rw [Category.id_comp, Category.assoc, Preadditive.sum_comp]
    refine key j _ _ (fun s hs ↦ ?_) (fun _ ↦ ?_) fun hj ↦ (hz j hj).eq_zero_of_tgt _
    · simp [hs]
    · simp

variable {D : Type*} [Category D] [Preadditive D] (G : C ⥤ D) [G.PreservesZeroMorphisms]

/-- A functor preserving zero morphisms takes the comparison morphism from a coproduct to a
product to the comparison morphism of the images, read through the coproduct and product
comparison morphisms of the functor. -/
lemma sigmaComparison_comp_map_sigmaPiComparison (M : ι → C) [HasProduct M] [HasCoproduct M]
    [HasProduct fun i ↦ G.obj (M i)] [HasCoproduct fun i ↦ G.obj (M i)] :
    sigmaComparison G M ≫ G.map (sigmaPiComparison M) ≫ piComparison G M =
      sigmaPiComparison fun i ↦ G.obj (M i) := by
  refine Sigma.hom_ext _ _ fun i ↦ Pi.hom_ext _ _ fun j ↦ ?_
  simp only [Category.assoc, ι_comp_sigmaPiComparison_comp_π, ι_comp_sigmaComparison_assoc,
    piComparison_comp_π, ← Functor.map_comp]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- A functor preserving zero morphisms and products and coproducts of the given shape carries
an invertible comparison morphism of the images to an invertible image of the comparison
morphism. -/
lemma isIso_map_sigmaPiComparison (M : ι → C) [HasProduct M] [HasCoproduct M]
    [HasProduct fun i ↦ G.obj (M i)] [HasCoproduct fun i ↦ G.obj (M i)]
    [PreservesLimit (Discrete.functor M) G] [PreservesColimit (Discrete.functor M) G]
    (h : IsIso (sigmaPiComparison fun i ↦ G.obj (M i))) :
    IsIso (G.map (sigmaPiComparison M)) := by
  have key : G.map (sigmaPiComparison M) = inv (sigmaComparison G M) ≫
      (sigmaPiComparison fun i ↦ G.obj (M i)) ≫ inv (piComparison G M) := by
    rw [← sigmaComparison_comp_map_sigmaPiComparison G M]
    simp
  rw [key]
  have := h
  exact IsIso.comp_isIso

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Locally finite families of modules on a scheme -/

/-- A module all of whose modules of sections are trivial is a zero object. -/
lemma isZero_of_subsingleton_sections {Y : Scheme.{u}} {M : Y.Modules}
    (h : ∀ U : Y.Opens, Subsingleton (ToType Γ(M, U))) : IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero]
  exact Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun _x ↦ (h U).elim _ _

/-- Restriction along an open immersion preserves products of any fixed shape: its product
comparison morphism is invertible. -/
lemma preservesLimitsOfShape_restrictFunctor {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (ι : Type u) : PreservesLimitsOfShape (Discrete ι) (Scheme.Modules.restrictFunctor f) := by
  constructor
  intro K
  let _ : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk))
      (Scheme.Modules.restrictFunctor f) :=
    have : IsIso (piComparison (Scheme.Modules.restrictFunctor f) (K.obj ∘ Discrete.mk)) :=
      isIso_restrictPiComparison f _
    PreservesProduct.of_iso_comparison _ _
  exact preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm

/-- The coproduct of a family of modules on a scheme is its product, as soon as on each member
of an open covering all but finitely many of the restricted modules are zero. -/
theorem isIso_sigmaPiComparison_of_locallyFinite {ι : Type u} [DecidableEq ι]
    (M : ι → X.Modules) {κ : Type*} (V : κ → X.Opens) (hV : IsOpenCover V)
    (p : κ → ι → Prop) (hfin : ∀ k, Finite {i // p k i})
    (hz : ∀ (k : κ) (i : ι), ¬ p k i →
      IsZero ((Scheme.Modules.restrictFunctor (V k).ι).obj (M i))) :
    IsIso (sigmaPiComparison M) := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV fun k ↦ ?_
  have := hfin k
  have := preservesLimitsOfShape_restrictFunctor (V k).ι ι
  exact isIso_map_sigmaPiComparison _ M (isIso_sigmaPiComparison_of_isZero _ (p k) (hz k))

/-! ### The generic-point contributions form a locally finite family -/

/-- The generic-point contribution at a generic point outside an open set restricts to a zero
module on that open set, having no sections there at all. -/
lemma isZero_restrict_genericPointStalkModule {V : X.Opens} (η : genericPoints X)
    (hη : (η : X) ∉ V) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (genericPointStalkModule X η)) := by
  refine isZero_of_subsingleton_sections fun U ↦ ?_
  have : Subsingleton Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ (V.ι ''ᵁ U)) := by
    rw [fromSpecStalk_preimage_eq_bot η.2 fun hmem ↦ hη (V.ι_image_le U hmem)]
    infer_instance
  exact this

/-- The coproduct of the generic-point contributions is their product, when every quasi-compact
open has finitely many irreducible components: on an affine open only the finitely many generic
points lying in it contribute, the others restricting to zero objects. -/
theorem nonempty_sigmaIsoPi_genericPointStalkModule (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty ((∐ fun η : genericPoints X ↦ genericPointStalkModule X η) ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η) := by
  classical
  have : IsIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModule X η) :=
    isIso_sigmaPiComparison_of_locallyFinite _ (fun V : X.affineOpens ↦ (V : X.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V η ↦ (η : X) ∈ (V : X.Opens))
      (fun V ↦ finite_genericPoints_mem_of_isCompact X _ V.2.isCompact hfinite)
      (fun _ η hη ↦ isZero_restrict_genericPointStalkModule η hη)
  exact ⟨asIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModule X η)⟩

/-! ### The direct sum decomposition -/

/-- **Stacks 0EMF, displayed direct-sum decomposition.** For a scheme whose weakly associated
points are generic points of irreducible components and whose quasi-compact opens have finitely
many irreducible components, the `𝒪_X`-module of meromorphic functions is the direct sum over
the generic points of the irreducible components of the pushed-forward structure sheaves of the
spectra of the local rings there. -/
@[stacks 0EMF "generic_point_decomposition"]
theorem meromorphicFunctions_iso_coproduct_genericPointStalks (X : Scheme.{u})
    (hassoc : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty (meromorphicFunctions X ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨(meromorphicFunctions_iso_product_genericPointStalks X hassoc hfinite).some ≪≫
    (nonempty_sigmaIsoPi_genericPointStalkModule X hfinite).some.symm⟩

/-- **Stacks 02OW, displayed direct-sum decomposition.** On a reduced scheme whose quasi-compact
opens have finitely many irreducible components, the `𝒪_X`-module of meromorphic functions is the
direct sum of the generic-point contributions. -/
@[stacks 02OW "generic-point direct sum"]
theorem meromorphicFunctions_iso_coproduct_genericPointStalks_of_isReduced (X : Scheme.{u})
    [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty (meromorphicFunctions X ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  meromorphicFunctions_iso_coproduct_genericPointStalks X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite

end AlgebraicGeometry
