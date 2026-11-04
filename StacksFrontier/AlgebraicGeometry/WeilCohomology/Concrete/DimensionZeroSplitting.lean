module

public import StacksFrontier.AlgebraicGeometry.NodalContraction.CentreFibre
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.RingTheory.Etale.GaloisSplitting
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The decomposition `X ×_k Spec(L) = ∐_{σ} Spec(L)` of a zero-dimensional scheme

Let `X` be a smooth projective scheme of dimension zero over a field `k`, so that `X = Spec(A)`
for the finite étale `k`-algebra `A = Γ(X, 𝒪_X)`, and let `L/k` be a finite separable extension
in which every minimal polynomial over `k` of an element of `A` splits (for instance a finite
Galois extension containing every factor of `A`). With `Σ = Hom_k(A, L)` the proof of Stacks
0FHQ uses

`X ×_k Spec(L) = Spec(A ⊗_k L) = Spec(∏_{σ ∈ Σ} L) = ∐_{σ ∈ Σ} Spec(L)`,

the `σ`-th coprojection being `(Spec(σ), id) : Spec(L) ⟶ X ×_k Spec(L)`. This file constructs
these coprojections in the category of smooth projective schemes over `k` and proves that they
exhibit `X ×_k Spec(L)` as a coproduct there.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.splitInj`: the coprojection
  `ι_σ : Spec(L) ⟶ X × Spec(L)` with `pr₁ ∘ ι_σ = Spec(σ)` and `pr₂ ∘ ι_σ = id`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.splitCofan`: the cofan of the `ι_σ`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.isColimitSplitCofan`: it is a colimit cofan.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isNonemptyEquidimensional_of_dimension_zero`:
  a smooth projective scheme of dimension zero is nonempty and equidimensional of dimension `0`.

## References

* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-! ### Colimit cofans of smooth projective schemes -/

/-- **A cofan of smooth projective schemes over `k` whose underlying cofan of schemes is a
colimit is a colimit.** -/
def isColimitCofanOfIsColimitMap {ι : Type u} {f : ι → (SmoothProjectiveScheme k).FullSubcategory}
    (c : Cofan f)
    (hc : IsColimit (Cofan.mk c.pt.obj.left fun i ↦ (c.inj i).hom.left)) : IsColimit c :=
  have hfac (t : Cofan f) (i : ι) : (c.inj i).hom.left ≫
      hc.desc (Cofan.mk t.pt.obj.left fun i ↦ (t.inj i).hom.left) = (t.inj i).hom.left := by
    simpa using hc.fac (Cofan.mk t.pt.obj.left fun i ↦ (t.inj i).hom.left) ⟨i⟩
  Cofan.IsColimit.mk _
    (fun t ↦ ObjectProperty.homMk (Over.homMk
      (hc.desc (Cofan.mk t.pt.obj.left fun i ↦ (t.inj i).hom.left)) (by
        refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
        change (c.inj i).hom.left ≫ _ ≫ _ = (c.inj i).hom.left ≫ _
        rw [← Category.assoc, hfac t i]
        exact (Over.w (t.inj i).hom).trans (Over.w (c.inj i).hom).symm)))
    (fun t i ↦ hom_ext_left (hfac t i))
    (fun t m hm ↦ hom_ext_left (by
      refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
      change (c.inj i).hom.left ≫ m.hom.left =
        (c.inj i).hom.left ≫ hc.desc (Cofan.mk t.pt.obj.left fun i ↦ (t.inj i).hom.left)
      rw [hfac t i]
      exact congrArg (fun g ↦ g.hom.left) (hm i)))

/-! ### Zero-dimensional schemes are nonempty and equidimensional of dimension zero -/

section DimensionZero

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)

include hX

/-- A scheme of dimension zero is nonempty: the empty space has dimension `⊥`. -/
theorem nonempty_of_dimension_zero : Nonempty X.obj.left := by
  by_contra h
  have := (topologicalKrullDim_eq_bot_iff_isEmpty (X := X.obj.left)).mpr (not_nonempty_iff.mp h)
  rw [hX] at this
  exact WithBot.coe_ne_bot this

/-- The structure morphism of a scheme of dimension zero over `k` has relative dimension `0`:
each fibre is homeomorphic to a subspace of `X`. -/
theorem relativeDimension_zero_of_dimension_zero : RelativeDimension X.obj.hom 0 := by
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  intro x
  refine le_antisymm ?_ (topologicalKrullDimAt_nonneg _)
  refine (AlgebraicGeometry.topologicalKrullDimAt_le_topologicalKrullDim _).trans ?_
  have h := le_trans (X.obj.hom.fiberHomeo (X.obj.hom x)).isInducing.topologicalKrullDim_le
    (topologicalKrullDim_subspace_le _ _)
  rw [hX] at h
  exact h

/-- **A smooth projective scheme of dimension zero is nonempty and equidimensional of dimension
`0`.** -/
theorem isNonemptyEquidimensional_of_dimension_zero : IsNonemptyEquidimensional X 0 where
  nonempty := nonempty_of_dimension_zero hX
  relativeDimension := relativeDimension_zero_of_dimension_zero hX


end DimensionZero

/-! ### The coprojections `(Spec(σ), id)` -/

section Split

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (hX : topologicalKrullDim X.obj.left = 0)
variable (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- A finite separable field extension `L/k` is étale. -/
instance : Algebra.Etale k L :=
  have : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  have : Algebra.FinitePresentation k L := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  ⟨inferInstance, inferInstance⟩

include hX

/-- The underlying scheme of `X × Y` is the fibre product `X ×_{Spec k} Y`. -/
def prodLeftIso (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (prod X Y).obj.left ≅ Limits.pullback X.obj.hom Y.obj.hom :=
  Iso.refl _

omit hX [FiniteDimensional k L] [Algebra.IsSeparable k L] in
/-- For a `k`-algebra map `σ : Γ(X, 𝒪_X) → L`, the composite
`Spec(L) ⟶ Spec(Γ(X, 𝒪_X)) ⟶ Spec(k)` of `Spec(σ)` with the structure morphism is the structure
morphism of `Spec(L)`. -/
theorem specMap_comp_specStructure (σ : globalSections X →ₐ[k] L) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specStructure k (globalSections X) =
      specStructure k L := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

/-- The morphism of schemes `(Spec(σ), id) : Spec(L) ⟶ X ×_{Spec k} Spec(L)`. -/
def splitLift (σ : globalSections X →ₐ[k] L) :
    Spec (.of L) ⟶ Limits.pullback X.obj.hom (specStructure k L) :=
  pullback.lift (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (isoSpecLeftOfDimensionZero hX).inv)
    (𝟙 _) (by
      rw [Category.assoc, ← isoSpecLeftOfDimensionZero_inv_hom hX, Category.id_comp,
        specMap_comp_specStructure])

/-- The coprojection `ι_σ = (Spec(σ), id) : Spec(L) ⟶ X × Spec(L)` for a `k`-algebra map
`σ : Γ(X, 𝒪_X) → L`, `X` of dimension zero; `Spec(σ)` is read through
`X ≅ Spec(Γ(X, 𝒪_X))`. -/
def splitInj (σ : globalSections X →ₐ[k] L) : spec k L ⟶ prod X (spec k L) :=
  ObjectProperty.homMk (Over.homMk (U := (spec k L).obj) (V := (prod X (spec k L)).obj)
    (splitLift hX L σ ≫ (prodLeftIso X (spec k L)).inv) (by
    change (splitLift hX L σ ≫ 𝟙 _) ≫ pullback.fst _ _ ≫ X.obj.hom = _
    rw [Category.comp_id, splitLift, pullback.lift_fst_assoc, Category.assoc,
      ← isoSpecLeftOfDimensionZero_inv_hom hX, specMap_comp_specStructure]
    rfl))

/-- The underlying morphism of schemes of `splitInj` is `splitLift`, read through `prodLeftIso`. -/
theorem splitInj_hom_left (σ : globalSections X →ₐ[k] L) :
    (splitInj hX L σ).hom.left = splitLift hX L σ ≫ (prodLeftIso X (spec k L)).inv := rfl

/-- The first component of `ι_σ` is `Spec(σ)`, read through `X ≅ Spec(Γ(X, 𝒪_X))`. -/
@[reassoc (attr := simp)]
theorem splitInj_fst (σ : globalSections X →ₐ[k] L) :
    haveI := finite_globalSections hX
    haveI := etale_globalSections hX
    splitInj hX L σ ≫ fst X (spec k L) = specMap σ ≫ (isoSpecOfDimensionZero hX).inv :=
  hom_ext_left (by
    show (splitLift hX L σ ≫ 𝟙 _) ≫ pullback.fst _ _ = _
    rw [Category.comp_id, splitLift, pullback.lift_fst]
    rfl)

/-- The second component of `ι_σ` is the identity of `Spec(L)`. -/
@[reassoc (attr := simp)]
theorem splitInj_snd (σ : globalSections X →ₐ[k] L) :
    splitInj hX L σ ≫ snd X (spec k L) = 𝟙 _ :=
  hom_ext_left (by
    show (splitLift hX L σ ≫ 𝟙 _) ≫ pullback.snd _ _ = 𝟙 _
    rw [Category.comp_id, splitLift, pullback.lift_snd])

/-- The cofan of the coprojections `ι_σ`, `σ ∈ Hom_k(Γ(X, 𝒪_X), L)`. -/
def splitCofan : Cofan fun _ : globalSections X →ₐ[k] L ↦ spec k L :=
  Cofan.mk (prod X (spec k L)) (splitInj hX L)

/-- The comparison `X ×_k Spec(L) ⟶ Spec(Γ(X, 𝒪_X)) ×_k Spec(L)` induced by
`X ≅ Spec(Γ(X, 𝒪_X))`, an isomorphism. -/
def prodMapSpec :
    Limits.pullback X.obj.hom (specStructure k L) ⟶
      Limits.pullback (specStructure k (globalSections X)) (specStructure k L) :=
  pullback.map X.obj.hom (specStructure k L) (specStructure k (globalSections X))
    (specStructure k L) (isoSpecLeftOfDimensionZero hX).hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, isoSpecLeftOfDimensionZero_hom_specStructure])
    (by rw [Category.comp_id, Category.id_comp])

omit [FiniteDimensional k L] [Algebra.IsSeparable k L] in
/-- The comparison `prodMapSpec` is an isomorphism. -/
theorem isIso_prodMapSpec : IsIso (prodMapSpec hX L) := by
  unfold prodMapSpec
  infer_instance

omit [FiniteDimensional k L] [Algebra.IsSeparable k L] in
/-- Under `X ×_k Spec(L) ≅ Spec(Γ(X, 𝒪_X) ⊗_k L)`, the morphism `(Spec(σ), id)` is `Spec` of the
composite of `Γ(X, 𝒪_X) ⊗_k L → ∏_{σ} L` with the projection onto the `σ`-th factor. -/
theorem splitLift_prodMapSpec_pullbackSpecIso (σ : globalSections X →ₐ[k] L) :
    splitLift hX L σ ≫ prodMapSpec hX L ≫ (pullbackSpecIso k (globalSections X) L).hom =
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom _ σ).comp
        (Stacks.FiniteEtaleSplitting.splitHom k (globalSections X) L).toRingHom)) := by
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, prodMapSpec, pullback.lift_fst,
      splitLift, pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Spec.map_comp]
    congr 1
    ext a
    simp
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, prodMapSpec, pullback.lift_snd,
      splitLift, pullback.lift_snd_assoc, Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext b
    simp

/-- **`X ×_k Spec(L) = ∐_{σ ∈ Hom_k(Γ(X, 𝒪_X), L)} Spec(L)`**, with coprojections
`(Spec(σ), id)`, when every minimal polynomial of an element of `Γ(X, 𝒪_X)` splits in `L`. -/
def isColimitSplitCofan
    (hsplit : ∀ a : globalSections X, ((minpoly k a).map (algebraMap k L)).Splits) :
    IsColimit (splitCofan hX L) := by
  haveI := finite_globalSections hX
  haveI := etale_globalSections hX
  refine isColimitCofanOfIsColimitMap _ ?_
  let Φ := Stacks.FiniteEtaleSplitting.splitEquiv hsplit
  let R : (globalSections X →ₐ[k] L) → CommRingCat.{u} := fun _ ↦ .of L
  haveI := isIso_prodMapSpec hX L
  have hdesc : Sigma.desc (splitLift hX L) ≫ prodMapSpec hX L ≫
      (pullbackSpecIso k (globalSections X) L).hom =
        sigmaSpec R ≫ Spec.map (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    rw [Sigma.ι_desc_assoc, splitLift_prodMapSpec_pullbackSpecIso, ι_sigmaSpec_assoc,
      ← Spec.map_comp]
    congr 1
  haveI : IsIso (Sigma.desc (splitLift hX L) ≫ prodMapSpec hX L ≫
      (pullbackSpecIso k (globalSections X) L).hom) := by
    rw [hdesc]
    have : IsIso (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) :=
      (RingEquiv.toCommRingCatIso Φ.toRingEquiv).isIso_hom
    infer_instance
  haveI : IsIso (Sigma.desc (splitLift hX L)) :=
    IsIso.of_isIso_comp_right _ (prodMapSpec hX L ≫ (pullbackSpecIso k (globalSections X) L).hom)
  let c := Cofan.mk (prod X (spec k L)).obj.left fun σ ↦ (splitInj hX L σ).hom.left
  haveI : IsIso (Sigma.desc c.inj) := by
    have : Sigma.desc c.inj = Sigma.desc (splitLift hX L) ≫ (prodLeftIso X (spec k L)).inv :=
      Sigma.hom_ext _ _ fun σ ↦ by
        rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
        rfl
    rw [this]
    infer_instance
  exact Cofan.isColimitOfIsIsoSigmaDesc c

end Split

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
