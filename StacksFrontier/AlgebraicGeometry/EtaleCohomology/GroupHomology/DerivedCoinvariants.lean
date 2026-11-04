module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompletedGroupAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived coinvariants of a profinite group

Let `Λ` be a ring, not necessarily commutative, and `G` a topological group with completed group
algebra `Λ[[G]]`. The coinvariants of a `Λ[[G]]`-module `N` are `Λ ⊗_{Λ[[G]]} N = N / I N`, where
`I` is the augmentation ideal, the kernel of `Λ[[G]] → Λ`; this is a `Λ`-module. Its total left
derived functor, evaluated at `N`, is the derived coinvariants

`LH₀(G, N) = Λ ⊗^L_{Λ[[G]]} N = N ⊗^L_{Λ[[G]]} Λ`

of [Stacks, Tag 03VI] and of the abstract trace formula, Section 03VO: an object of the derived
category `D(Λ)`, computed by the coinvariants of any projective resolution of `N`.

An automorphism `c` of `G` acts on `Λ[[G]]` by the ring automorphism `σ = Λ[[c]]`, which fixes the
constants and the augmentation. A `σ`-semilinear endomorphism of `N`, that is, a morphism
`N ⟶ σ^* N` of `Λ[[G]]`-modules, induces an endomorphism of `LH₀(G, N)`: lift it to a projective
resolution `P` of `N`, apply the coinvariants and identify the coinvariants of `σ^* P` with those
of `P`. This is how an element of a group `Γ` containing `G` as a normal subgroup acts on the
derived coinvariants of a `Γ`-module.

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `augmentationSubmodule`: the submodule `I N`.
* `coinvariantsFunctor`: the functor `N ↦ Λ ⊗_{Λ[[G]]} N = N / I N` from `Λ[[G]]`-modules to
  `Λ`-modules.
* `derivedCoinvariants`: `LH₀(G, N) = N ⊗^L_{Λ[[G]]} Λ ∈ D(Λ)`.
* `derivedCoinvariantsIsoOfResolution`: the identification of `LH₀(G, N)` with the coinvariants of
  any projective resolution of `N`.
* `twistFunctor`: restriction of scalars along `Λ[[c]]`.
* `twistCoinvariantsIso`: the coinvariants of `σ^* N` are those of `N`.
* `derivedCoinvariantsTwistedMap`: the endomorphism of `LH₀(G, N)` induced by a morphism
  `N ⟶ σ^* N`.

## Main results

* `derivedCoinvariantsTwistedMap_eq`: the endomorphism is computed on **any** projective resolution
  `K` of `N` and **any** lift `K ⟶ σ^* K` of the semilinear map, the object `LH₀(G, N)` being
  identified with the coinvariants of `K` by `derivedCoinvariantsIsoOfResolution`.

## Implementation notes

`LH₀(G, N)` is the image in `D(Λ)` of the coinvariants of Mathlib's chosen projective resolution of
`N`, a chain complex in degrees `≥ 0`, reindexed by `n ↦ -n` into a cochain complex
(`ComplexShape.embeddingUpIntLE 0`). That this is the total left derived functor of the
coinvariants, i.e. the derived tensor product `- ⊗^L_{Λ[[G]]} Λ`, is the classical computation of
derived functors by projective resolutions; it is used here only through its consequence that any
projective resolution computes the same object, which is `derivedCoinvariantsIsoOfResolution`.

The ring `Λ`, the group `G` and the modules live in a single universe.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
* [Stacks Project, Tag 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type u) [Ring Λ] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Coinvariants

variable {Λ G}

/-- The submodule `I N` of a `Λ[[G]]`-module `N` spanned by the products `a n` with `a` in the
augmentation ideal. -/
public def augmentationSubmodule (Λ G) [Ring Λ] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (N : Type*) [AddCommGroup N] [Module (CompletedGroupAlgebra Λ G) N] :
    Submodule (CompletedGroupAlgebra Λ G) N :=
  Submodule.span _ {x | ∃ a : CompletedGroupAlgebra Λ G, augmentation a = 0 ∧ ∃ n : N, a • n = x}

/-- For `a` in the augmentation ideal, `a n` lies in `I N`. -/
public theorem smul_mem_augmentationSubmodule {N : Type*} [AddCommGroup N]
    [Module (CompletedGroupAlgebra Λ G) N] {a : CompletedGroupAlgebra Λ G}
    (ha : augmentation a = 0) (n : N) : a • n ∈ augmentationSubmodule Λ G N :=
  Submodule.subset_span ⟨a, ha, n, rfl⟩

/-- A semilinear map along a ring endomorphism preserving the augmentation sends `I N` into
`I N'`. -/
private theorem augmentationSubmodule_le_comap_of_semilinear {N N' : Type*} [AddCommGroup N]
    [Module (CompletedGroupAlgebra Λ G) N] [AddCommGroup N'] [Module (CompletedGroupAlgebra Λ G) N']
    {σ : CompletedGroupAlgebra Λ G →+* CompletedGroupAlgebra Λ G}
    (hσ : ∀ a, augmentation (σ a) = augmentation a) (f : N →ₛₗ[σ] N') :
    augmentationSubmodule Λ G N ≤ (augmentationSubmodule Λ G N').comap f :=
  Submodule.span_le.2 <| by
    rintro _ ⟨a, ha, n, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.map_smulₛₗ]
    exact smul_mem_augmentationSubmodule ((hσ a).trans ha) _

/-- A linear map sends `I N` into `I N'`. -/
public theorem augmentationSubmodule_le_comap {N N' : Type*} [AddCommGroup N]
    [Module (CompletedGroupAlgebra Λ G) N] [AddCommGroup N'] [Module (CompletedGroupAlgebra Λ G) N']
    (f : N →ₗ[CompletedGroupAlgebra Λ G] N') :
    augmentationSubmodule Λ G N ≤ (augmentationSubmodule Λ G N').comap f :=
  augmentationSubmodule_le_comap_of_semilinear (σ := RingHom.id _) (fun _ => rfl) f

end Coinvariants

/-- The functor `N ↦ N / I N` on `Λ[[G]]`-modules. -/
public def augmentationQuotientFunctor :
    ModuleCat.{u} (CompletedGroupAlgebra Λ G) ⥤ ModuleCat.{u} (CompletedGroupAlgebra Λ G) where
  obj N := ModuleCat.of _ (N ⧸ augmentationSubmodule Λ G N)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ f.hom (augmentationSubmodule_le_comap f.hom))
  map_id N := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The functor `N ↦ N / I N` is additive. -/
public instance : (augmentationQuotientFunctor Λ G).Additive where
  map_add {N N' f g} := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- **The coinvariants functor** `N ↦ Λ ⊗_{Λ[[G]]} N = N / I N`, from `Λ[[G]]`-modules to
`Λ`-modules. -/
public def coinvariantsFunctor :
    ModuleCat.{u} (CompletedGroupAlgebra Λ G) ⥤ ModuleCat.{u} Λ :=
  augmentationQuotientFunctor Λ G ⋙ ModuleCat.restrictScalars (const : Λ →+* _)

/-- The coinvariants functor is additive. -/
public instance : (coinvariantsFunctor Λ G).Additive := by
  dsimp [coinvariantsFunctor]; infer_instance

variable {Λ G} in
/-- The coinvariants functor on representatives. -/
public theorem coinvariantsFunctor_map_mk {N N' : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (f : N ⟶ N') (x : N) :
    ((coinvariantsFunctor Λ G).map f).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.hom x) :=
  rfl

/-- Reindex a chain complex in degrees `≥ 0` as a cochain complex in degrees `≤ 0`, degree `n`
going to degree `-n`. -/
@[ega "III 6.2.7" "special case"]
public abbrev chainToCochain : ChainComplex (ModuleCat.{u} Λ) ℕ ⥤
    CochainComplex (ModuleCat.{u} Λ) ℤ :=
  (ComplexShape.embeddingUpIntLE 0).extendFunctor _

variable {Λ G}

/-- The coinvariants of a chain complex of `Λ[[G]]`-modules, as a cochain complex of `Λ`-modules in
degrees `≤ 0`. -/
public abbrev coinvariantsComplex (K : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ) :
    CochainComplex (ModuleCat.{u} Λ) ℤ :=
  (chainToCochain Λ).obj (((coinvariantsFunctor Λ G).mapHomologicalComplex _).obj K)

/-- The map of coinvariant complexes induced by a chain map. -/
public abbrev coinvariantsComplexMap
    {K L : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ} (f : K ⟶ L) :
    coinvariantsComplex K ⟶ coinvariantsComplex L :=
  (chainToCochain Λ).map (((coinvariantsFunctor Λ G).mapHomologicalComplex _).map f)

/-- Homotopic chain maps induce the same map on the coinvariants in `D(Λ)`. -/
public theorem Q_map_coinvariantsComplexMap_eq_of_homotopy
    {K L : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    DerivedCategory.Q.map (coinvariantsComplexMap f) =
      DerivedCategory.Q.map (coinvariantsComplexMap g) :=
  DerivedCategory.Q_map_eq_of_homotopy _
    (((coinvariantsFunctor Λ G).mapHomotopy h).extend (ComplexShape.embeddingUpIntLE 0))

/-- The identity chain map induces the identity of the coinvariant complex. -/
@[simp]
public theorem coinvariantsComplexMap_id
    (K : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ) :
    coinvariantsComplexMap (𝟙 K) = 𝟙 _ := by
  simp only [coinvariantsComplexMap, CategoryTheory.Functor.map_id]

/-- The map of coinvariant complexes induced by a composite is the composite of the induced maps.
-/
public theorem coinvariantsComplexMap_comp
    {K L M : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    coinvariantsComplexMap (f ≫ g) = coinvariantsComplexMap f ≫ coinvariantsComplexMap g := by
  simp only [coinvariantsComplexMap, CategoryTheory.Functor.map_comp]

/-- A homotopy equivalence of chain complexes of `Λ[[G]]`-modules induces an isomorphism of their
coinvariants in `D(Λ)`. -/
public def coinvariantsIsoOfHomotopyEquiv
    {K L : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ} (e : HomotopyEquiv K L) :
    DerivedCategory.Q.obj (coinvariantsComplex K) ≅ DerivedCategory.Q.obj (coinvariantsComplex L)
    where
  hom := DerivedCategory.Q.map (coinvariantsComplexMap e.hom)
  inv := DerivedCategory.Q.map (coinvariantsComplexMap e.inv)
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, ← coinvariantsComplexMap_comp,
      Q_map_coinvariantsComplexMap_eq_of_homotopy e.homotopyHomInvId, coinvariantsComplexMap_id,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp, ← coinvariantsComplexMap_comp,
      Q_map_coinvariantsComplexMap_eq_of_homotopy e.homotopyInvHomId, coinvariantsComplexMap_id,
      CategoryTheory.Functor.map_id]

/-- **The derived coinvariants** `LH₀(G, N) = N ⊗^L_{Λ[[G]]} Λ`, an object of `D(Λ)`: the
coinvariants of a projective resolution of `N`. -/
public abbrev derivedCoinvariants (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  DerivedCategory.Q.obj (coinvariantsComplex (projectiveResolution N).complex)

/-- Any projective resolution computes the derived coinvariants. -/
public def derivedCoinvariantsIsoOfResolution {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (K : ProjectiveResolution N) :
    derivedCoinvariants N ≅ DerivedCategory.Q.obj (coinvariantsComplex K.complex) :=
  coinvariantsIsoOfHomotopyEquiv (ProjectiveResolution.homotopyEquiv (projectiveResolution N) K)

/-! ### Twisting by an automorphism of the group -/

section Twist

variable (Λ) (c : G ≃ₜ* G)

/-- Restriction of scalars along the ring automorphism `σ = Λ[[c]]` of `Λ[[G]]` induced by an
automorphism `c` of `G`: the module `σ^* N` is `N` with `a` acting as `σ a`. -/
public abbrev twistFunctor :
    ModuleCat.{u} (CompletedGroupAlgebra Λ G) ⥤ ModuleCat.{u} (CompletedGroupAlgebra Λ G) :=
  ModuleCat.restrictScalars (mapRingEquiv (Λ := Λ) c).toRingHom

variable {Λ} {c}

/-- The identity of `N`, as a `σ`-semilinear map `σ^* N → N`. -/
public def twistToSelf (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    (twistFunctor Λ c).obj N →ₛₗ[(mapRingEquiv (Λ := Λ) c).toRingHom] N where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity of `N`, as a `σ⁻¹`-semilinear map `N → σ^* N`. -/
public def selfToTwist (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    N →ₛₗ[(mapRingEquiv (Λ := Λ) c).symm.toRingHom] (twistFunctor Λ c).obj N where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • x = (mapRingEquiv c) ((mapRingEquiv c).symm a) • x
    rw [RingEquiv.apply_symm_apply]

/-- `σ` preserves the augmentation. -/
public theorem augmentation_mapRingEquiv (x : CompletedGroupAlgebra Λ G) :
    augmentation (mapRingEquiv c x) = augmentation x :=
  augmentation_map _ _ x

/-- `σ⁻¹` preserves the augmentation. -/
public theorem augmentation_mapRingEquiv_symm (x : CompletedGroupAlgebra Λ G) :
    augmentation ((mapRingEquiv c).symm x) = augmentation x := by
  rw [← augmentation_mapRingEquiv (c := c), RingEquiv.apply_symm_apply]

/-- The identity `σ^* N → N` sends `I (σ^* N)` into `I N`. -/
public theorem augmentationSubmodule_twist_le (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    augmentationSubmodule Λ G ((twistFunctor Λ c).obj N) ≤
      (augmentationSubmodule Λ G N).comap (twistToSelf N) :=
  augmentationSubmodule_le_comap_of_semilinear (σ := (mapRingEquiv (Λ := Λ) c).toRingHom)
    augmentation_mapRingEquiv (twistToSelf N)

/-- The identity `N → σ^* N` sends `I N` into `I (σ^* N)`. -/
public theorem augmentationSubmodule_le_twist (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    augmentationSubmodule Λ G N ≤
      (augmentationSubmodule Λ G ((twistFunctor Λ c).obj N)).comap (selfToTwist N) :=
  augmentationSubmodule_le_comap_of_semilinear (σ := (mapRingEquiv (Λ := Λ) c).symm.toRingHom)
    augmentation_mapRingEquiv_symm (selfToTwist N)

/-- The coinvariants of `σ^* N` are the coinvariants of `N`: the `Λ`-linear isomorphism induced by
the identity of `N`. -/
public def twistCoinvariantsLinearEquiv (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :
    (coinvariantsFunctor Λ G).obj ((twistFunctor Λ c).obj N) ≃ₗ[Λ]
      (coinvariantsFunctor Λ G).obj N where
  toFun := Submodule.mapQ _ _ (twistToSelf N) (augmentationSubmodule_twist_le N)
  invFun := Submodule.mapQ _ _ (selfToTwist N) (augmentationSubmodule_le_twist N)
  map_add' x y := map_add _ x y
  map_smul' a x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.mapQ _ _ (twistToSelf N) (augmentationSubmodule_twist_le N)
        (Submodule.Quotient.mk ((const a : CompletedGroupAlgebra Λ G) • y)) =
      Submodule.Quotient.mk ((const a : CompletedGroupAlgebra Λ G) • twistToSelf N y)
    rw [Submodule.mapQ_apply, LinearMap.map_smulₛₗ]
    have h : (mapRingEquiv (Λ := Λ) c).toRingHom (const a) = const a := map_const _ _ a
    simp only [h]
  left_inv x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  right_inv x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

variable (Λ c)

/-- **The coinvariants of `σ^* N` are those of `N`**, naturally in `N`. -/
public def twistCoinvariantsIso :
    twistFunctor Λ c ⋙ coinvariantsFunctor Λ G ≅ coinvariantsFunctor Λ G :=
  NatIso.ofComponents (fun N => (twistCoinvariantsLinearEquiv (c := c) N).toModuleIso)
    fun {N N'} f => by
      ext x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl

variable {Λ c} in
/-- The identification of the coinvariants of `σ^* N` with those of `N` on representatives. -/
public theorem twistCoinvariantsIso_hom_app_mk (N : ModuleCat.{u} (CompletedGroupAlgebra Λ G))
    (x : (twistFunctor Λ c).obj N) :
    ((twistCoinvariantsIso Λ c).hom.app N).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (twistToSelf N x) :=
  rfl

/-- The coinvariants of `σ^* K` are those of `K`, for a chain complex `K`. -/
public def twistCoinvariantsComplexIso
    (K : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ) :
    coinvariantsComplex (((twistFunctor Λ c).mapHomologicalComplex _).obj K) ≅
      coinvariantsComplex K :=
  (chainToCochain Λ).mapIso
    ((Functor.mapHomologicalComplexCompIso (twistCoinvariantsIso Λ c) _).app K)

/-- The identification of the coinvariants of `σ^* K` with those of `K` is natural in `K`. -/
public theorem twistCoinvariantsComplexIso_hom_naturality
    {K L : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ} (f : K ⟶ L) :
    coinvariantsComplexMap (((twistFunctor Λ c).mapHomologicalComplex _).map f) ≫
        (twistCoinvariantsComplexIso Λ c L).hom =
      (twistCoinvariantsComplexIso Λ c K).hom ≫ coinvariantsComplexMap f := by
  simp only [twistCoinvariantsComplexIso, coinvariantsComplexMap, Functor.mapIso_hom,
    Iso.app_hom, ← Functor.map_comp]
  congr 1
  exact ((Functor.mapHomologicalComplexCompIso (twistCoinvariantsIso Λ c) _).hom.naturality f)

variable {Λ c}

/-- The projective resolution `σ^* P` of `σ^* N` obtained from a projective resolution `P` of `N`.
-/
public abbrev twistResolution {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (P : ProjectiveResolution N) : ProjectiveResolution ((twistFunctor Λ c).obj N) where
  complex := ((twistFunctor Λ c).mapHomologicalComplex _).obj P.complex
  projective n := ((twistFunctor Λ c).mapProjectiveResolution P).projective n
  π := ((twistFunctor Λ c).mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := ((twistFunctor Λ c).mapProjectiveResolution P).quasiIso

/-- **The endomorphism of `LH₀(G, N)` induced by a semilinear endomorphism** `φ : N ⟶ σ^* N`: lift
`φ` to the chosen projective resolution `P` of `N`, take coinvariants and identify the coinvariants
of `σ^* P` with those of `P`. -/
public def derivedCoinvariantsTwistedMap {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (φ : N ⟶ (twistFunctor Λ c).obj N) : derivedCoinvariants N ⟶ derivedCoinvariants N :=
  DerivedCategory.Q.map
    (coinvariantsComplexMap (ProjectiveResolution.lift φ (projectiveResolution N)
        (twistResolution (projectiveResolution N))) ≫
      (twistCoinvariantsComplexIso Λ c (projectiveResolution N).complex).hom)

/-- **The twisted endomorphism is computed on any projective resolution and any lift.** For a
projective resolution `K` of `N` and a chain map `κ : K ⟶ σ^* K` lifting `φ`, the endomorphism of
`LH₀(G, N)` corresponds, under `derivedCoinvariantsIsoOfResolution K`, to the endomorphism of the
coinvariants of `K` induced by `κ`. -/
public theorem derivedCoinvariantsTwistedMap_eq {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (φ : N ⟶ (twistFunctor Λ c).obj N) (K : ProjectiveResolution N)
    (κ : K.complex ⟶ ((twistFunctor Λ c).mapHomologicalComplex _).obj K.complex)
    (hκ : κ ≫ (twistResolution (c := c) K).π = K.π ≫ (ChainComplex.single₀ _).map φ) :
    (derivedCoinvariantsIsoOfResolution K).inv ≫ derivedCoinvariantsTwistedMap φ ≫
        (derivedCoinvariantsIsoOfResolution K).hom =
      DerivedCategory.Q.map (coinvariantsComplexMap κ) ≫
        DerivedCategory.Q.map (twistCoinvariantsComplexIso Λ c K.complex).hom := by
  set P := projectiveResolution N
  set α := ProjectiveResolution.homotopyEquiv P K
  set L := ProjectiveResolution.lift φ P (twistResolution (c := c) P)
  set ψ : K.complex ⟶ ((twistFunctor Λ c).mapHomologicalComplex _).obj K.complex :=
    α.inv ≫ L ≫ ((twistFunctor Λ c).mapHomologicalComplex _).map α.hom
  have h₁ : α.inv ≫ P.π = K.π := ProjectiveResolution.homotopyEquiv_inv_π P K
  have h₂ : L ≫ (twistResolution (c := c) P).π = P.π ≫ (ChainComplex.single₀ _).map φ :=
    ProjectiveResolution.lift_commutes φ P (twistResolution P)
  have h₃ : α.hom ≫ K.π = P.π := ProjectiveResolution.homotopyEquiv_hom_π P K
  have h₃' : ((twistFunctor Λ c).mapHomologicalComplex _).map α.hom ≫
      (twistResolution (c := c) K).π = (twistResolution (c := c) P).π := by
    simp only [← Category.assoc, ← Functor.map_comp, h₃]
  have hψ : ψ ≫ (twistResolution (c := c) K).π = K.π ≫ (ChainComplex.single₀ _).map φ := by
    simp only [ψ, Category.assoc, h₃']
    rw [h₂, ← Category.assoc, h₁]
  have hhom := ProjectiveResolution.liftHomotopy φ (P := K) (Q := twistResolution (c := c) K)
    ψ κ hψ hκ
  rw [← Q_map_coinvariantsComplexMap_eq_of_homotopy hhom]
  simp only [derivedCoinvariantsIsoOfResolution, coinvariantsIsoOfHomotopyEquiv,
    derivedCoinvariantsTwistedMap, ← Functor.map_comp]
  congr 1
  simp only [ψ, coinvariantsComplexMap_comp, Category.assoc]
  rw [twistCoinvariantsComplexIso_hom_naturality]

end Twist

end Stacks.GroupHomology

end
