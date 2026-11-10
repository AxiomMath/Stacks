module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import StacksFrontier.Algebra.Homology.DerivedCategory.ChainCompFactorisation
public import StacksFrontier.Cotangent.QuillenTorVanishing
public import StacksFrontier.RingTheory.AugmentationIdealPowTorFirstVariable

/-!
# The local claim in the proof of [Stacks, Tag 08RF]

Let `A` be a commutative ring, let `E` be a type and let `S = A[E] = MvPolynomial E A` with
`𝔪 = (X_e ; e ∈ E)` the ideal of variables.  Let `M` be an `S`-module killed by `𝔪` and fix a
projective resolution `Q_•` of `M`.  The **local complexes** of the second claim in the proof of
[Stacks, Tag 08RF] are

`W_m = Q_• ⊗_S 𝔪ᵐ`,

a complex of `A`-modules, read here as a cochain complex over `ℤ` concentrated in degrees `≤ 0`
by reindexing along `ComplexShape.embeddingUpIntLE 0`.  This file proves the claim: for every
additive functor `F` out of `A`-modules and all `n k : ℕ`, the transition map `W_{n+k} ⟶ W_n`
induced by `𝔪^{n+k} ⊆ 𝔪ⁿ` induces the zero map on `Hⁱ(F(-))` for every `i > -k`.

## The shape of the argument

Everything is fed into `Stacks.homologyMap_map_chainComp_eq_zero`, the form of [Stacks, Tag 08Q2]
that applies to an arbitrary additive functor, taking for the chain `K j = W_{n+k-j}` and for
`f j` the transition map of one step.  Its three hypotheses are discharged as follows.

* **`K 0` is K-projective.**  The terms of `W_m` are `Q_p ⊗_S 𝔪ᵐ`, restricted to `A`.  A
  projective `S`-module `Q_p` is a direct summand of a free one, `S^{(ι)}`, and
  `S^{(ι)} ⊗_S 𝔪ᵐ ≅ (𝔪ᵐ)^{(ι)}` is a free `A`-module because `𝔪ᵐ` is one
  (`MvPolynomial.free_variableIdeal_pow`); so each term is `A`-projective, and the complex is
  concentrated in degrees `≤ 0`, whence K-projective by
  `CochainComplex.isKProjective_of_projective`.
* **No cohomology in positive degrees.**  The reindexed complex *is* zero in positive degrees.
* **The transition maps are zero on `H^{-j}`, in every degree `j`.**  This is [Stacks, Tag 08RE].
  By `CategoryTheory.ProjectiveResolution.leftDerived_app_eq`, the map `H_j` of the transition
  chain map over `S` is a component of `NatTrans.leftDerived` of `(-) ⊗ 𝔪ᵐ`, that is of
  `CategoryTheory.Tor'`; and `MvPolynomial.tor_map_variableIdeal_pow_succ_eq_zero` together with
  the balancing of `Tor`
  (`StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero`) says that component is
  zero.  Restriction of scalars along `A → S` is exact, hence commutes with homology, which
  carries the vanishing from `S`-modules to `A`-modules; and
  `HomologicalComplex.extendHomologyIso_hom_naturality` carries it from `H_j` of the chain
  complex to `H^{-j}` of the reindexed cochain complex.

## Main definitions

* `StacksDraft.PolynomialLocalComplex.tensorRestrict`: the functor `N ↦ N ⊗_S 𝔪ᵐ` from
  `S`-modules to `A`-modules.
* `StacksDraft.PolynomialLocalComplex.localComplex`: the complex `W_m`.
* `StacksDraft.PolynomialLocalComplex.localComplexMap`: the transition map `W_b ⟶ W_a`
  attached to `a ≤ b`.

## Main results

* `StacksDraft.PolynomialLocalComplex.homologyMap_localComplexMap_eq_zero`: [Stacks, Tag 08RE]
  for the local complexes — the transition map `W_b ⟶ W_a` is zero on `H^{-j}` for every `j`,
  as soon as `a < b`.
* `StacksDraft.PolynomialLocalComplex.homologyMap_map_localComplexMap_eq_zero`: **the local
  claim.** For every additive functor `F` into an abelian category, the transition map
  `W_{n+k} ⟶ W_n` induces the zero map on `Hⁱ(F(-))` for every `i > -k`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w u v

namespace StacksDraft.PolynomialLocalComplex

/-! ### Two generalities -/

/-- A morphism which becomes zero after composing with an isomorphism is zero. -/
lemma eq_zero_of_comp_iso {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {X Y Y' : C}
    (e : Y ≅ Y') {f : X ⟶ Y} (h : f ≫ e.hom = 0) : f = 0 := by
  have h' := h =≫ e.inv
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] at h'

/-- A morphism sandwiched between two isomorphisms is zero as soon as the sandwich is. -/
lemma eq_zero_of_iso_comp_comp_iso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {X X' Y Y' : C} (e₁ : X' ≅ X) (e₂ : Y' ≅ Y) {f : X ⟶ Y}
    (h : e₁.hom ≫ f ≫ e₂.inv = 0) : f = 0 := by
  refine eq_zero_of_comp_iso e₂.symm ?_
  have h' := e₁.inv ≫= h
  rwa [Iso.inv_hom_id_assoc, comp_zero] at h'

/-- **Restriction of scalars preserves freeness over the base.** If an `R`-module `N` is free
over a subring `R₀` for a scalar-tower structure, then the restriction of scalars of `N` along
`R₀ → R` — which carries the same action, `a • x = algebraMap a • x` — is free over `R₀`. -/
lemma free_restrictScalars {R₀ : Type*} [CommRing R₀] {R : Type*} [CommRing R] [Algebra R₀ R]
    {N : Type w} [AddCommGroup N] [Module R N] [Module R₀ N] [IsScalarTower R₀ R N]
    [Module.Free R₀ N] :
    Module.Free R₀ ((ModuleCat.restrictScalars (algebraMap R₀ R)).obj (ModuleCat.of R N)) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R₀ N).map
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl,
      map_smul' := fun a x => (IsScalarTower.algebraMap_smul R a x).symm })

section PreservesHomology

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (j : ι)

/-- **A functor which preserves homology commutes with the degree-`j` homology of a complex**:
applying it degreewise and then taking homology is taking homology and then applying it. -/
def mapHomologicalComplexHomologyFunctorIso :
    G.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c j ≅
      HomologicalComplex.homologyFunctor C c j ⋙ G :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c j)
    (ShortComplex.homologyFunctorIso G)

/-- **Vanishing of a homology map is carried along a functor which preserves homology.** -/
lemma homologyMap_map_eq_zero {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (hφ : HomologicalComplex.homologyMap φ j = 0) :
    HomologicalComplex.homologyMap ((G.mapHomologicalComplex c).map φ) j = 0 := by
  have hz : (HomologicalComplex.homologyFunctor C c j ⋙ G).map φ = 0 := by
    change G.map (HomologicalComplex.homologyMap φ j) = 0
    rw [hφ, G.map_zero]
  refine eq_zero_of_comp_iso ((mapHomologicalComplexHomologyFunctorIso G c j).app L) ?_
  change (G.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c j).map φ ≫
    (mapHomologicalComplexHomologyFunctorIso G c j).hom.app L = 0
  rw [(mapHomologicalComplexHomologyFunctorIso G c j).hom.naturality φ, hz, comp_zero]

end PreservesHomology

/-! ### Tensoring with a power of the ideal of variables -/

section TensorRestrict

variable (A : Type u) [CommRing A] (E : Type v)

/-- **Tensoring over `A[E]` with the `m`-th power of the ideal of variables, read over `A`.**
This is the functor `N ↦ N ⊗_{A[E]} 𝔪ᵐ` from `A[E]`-modules to `A`-modules, where
`𝔪 = (X_e ; e ∈ E)`. -/
def tensorRestrict (m : ℕ) :
    ModuleCat.{max u v} (MvPolynomial E A) ⥤ ModuleCat.{max u v} A :=
  (tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).obj
      (ModuleCat.of (MvPolynomial E A)
        ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m)) ⋙
    ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A))

/-- The functor `StacksDraft.PolynomialLocalComplex.tensorRestrict` is additive. -/
instance (m : ℕ) : (tensorRestrict A E m).Additive := by
  dsimp only [tensorRestrict]; infer_instance

/-- **The natural transformation of `StacksDraft.PolynomialLocalComplex.tensorRestrict` induced
by `𝔪ᵇ ⊆ 𝔪ᵃ`**, for `a ≤ b`. -/
def tensorRestrictMap {a b : ℕ} (h : a ≤ b) : tensorRestrict A E b ⟶ tensorRestrict A E a :=
  Functor.whiskerRight
    ((tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).map
      (ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right h :
        (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ b :
            Ideal (MvPolynomial E A)) ≤
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ a))))
    (ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A)))

/-- The inclusion of a submodule into itself, as a morphism of module categories, is the
identity. -/
private lemma ofHom_inclusion_self {R : Type*} [Ring R] {N : Type*} [AddCommGroup N] [Module R N]
    (p : Submodule R N) (h : p ≤ p) :
    ModuleCat.ofHom (Submodule.inclusion h) = 𝟙 (ModuleCat.of R p) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- Inclusions of submodules compose, as morphisms of module categories. -/
private lemma ofHom_inclusion_comp {R : Type*} [Ring R] {N : Type*} [AddCommGroup N] [Module R N]
    {p q r : Submodule R N} (h₁ : p ≤ q) (h₂ : q ≤ r) :
    ModuleCat.ofHom (Submodule.inclusion h₁) ≫ ModuleCat.ofHom (Submodule.inclusion h₂) =
      ModuleCat.ofHom (Submodule.inclusion (h₁.trans h₂)) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The transition map of `StacksDraft.PolynomialLocalComplex.tensorRestrict` for `a ≤ a` is the
identity. -/
lemma tensorRestrictMap_rfl (a : ℕ) :
    tensorRestrictMap A E (le_refl a) = 𝟙 (tensorRestrict A E a) := by
  dsimp only [tensorRestrictMap, tensorRestrict]
  rw [ofHom_inclusion_self, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.whiskerRight_id']

/-- The transition maps of `StacksDraft.PolynomialLocalComplex.tensorRestrict` compose: for
`a ≤ b ≤ c`, the map for `b ≤ c` followed by the map for `a ≤ b` is the map for `a ≤ c`. -/
lemma tensorRestrictMap_comp {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    tensorRestrictMap A E h₂ ≫ tensorRestrictMap A E h₁ = tensorRestrictMap A E (h₁.trans h₂) := by
  dsimp only [tensorRestrictMap, tensorRestrict]
  rw [← CategoryTheory.Functor.whiskerRight_comp, ← CategoryTheory.Functor.map_comp,
    ofHom_inclusion_comp]

/-- **The terms of the local complexes are projective `A`-modules.** If `P` is a projective
`A[E]`-module then `P ⊗_{A[E]} 𝔪ᵐ` is a projective `A`-module: `P` is a direct summand of a free
`A[E]`-module `A[E]^{(ι)}`, and `A[E]^{(ι)} ⊗_{A[E]} 𝔪ᵐ ≅ (𝔪ᵐ)^{(ι)}` is a free `A`-module
because `𝔪ᵐ` is one (`MvPolynomial.free_variableIdeal_pow`). -/
lemma projective_tensorRestrict_obj (m : ℕ) (P : ModuleCat.{max u v} (MvPolynomial E A))
    [CategoryTheory.Projective P] :
    CategoryTheory.Projective ((tensorRestrict A E m).obj P) := by
  classical
  have : Module.Free A
      ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m) :=
    MvPolynomial.free_variableIdeal_pow A E m
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective (MvPolynomial E A) P).out
  have e : ((tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).obj
        (ModuleCat.of (MvPolynomial E A)
          ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m))).obj
        (ModuleCat.of (MvPolynomial E A) (↥P →₀ MvPolynomial E A)) ≅
      ModuleCat.of (MvPolynomial E A)
        (↥P →₀ ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m)) :=
    (TensorProduct.finsuppScalarLeft (MvPolynomial E A)
      ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m) ↥P).toModuleIso
  have : Module.Free A ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A))).obj
      (ModuleCat.of (MvPolynomial E A)
        (↥P →₀ ↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m)))) :=
    free_restrictScalars
  have : CategoryTheory.Projective
      ((tensorRestrict A E m).obj (ModuleCat.of (MvPolynomial E A) (↥P →₀ MvPolynomial E A))) :=
    CategoryTheory.Projective.of_iso
      ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A))).mapIso e).symm inferInstance
  have : Module.Projective A
      ((tensorRestrict A E m).obj (ModuleCat.of (MvPolynomial E A) (↥P →₀ MvPolynomial E A))) :=
    inferInstance
  have : Module.Projective A ((tensorRestrict A E m).obj P) := by
    have hid : (tensorRestrict A E m).map (ModuleCat.ofHom s) ≫
        (tensorRestrict A E m).map (ModuleCat.ofHom
          (Finsupp.linearCombination (MvPolynomial E A) id)) = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp]
      convert (tensorRestrict A E m).map_id P using 2
      exact ModuleCat.hom_ext (LinearMap.ext hs)
    exact Module.Projective.of_split
      ((tensorRestrict A E m).map (ModuleCat.ofHom s)).hom
      ((tensorRestrict A E m).map (ModuleCat.ofHom
        (Finsupp.linearCombination (MvPolynomial E A) id))).hom
      (by simpa using ModuleCat.hom_ext_iff.mp hid)
  infer_instance

end TensorRestrict

/-! ### The local complexes -/

section LocalComplex

variable {A : Type u} [CommRing A] {E : Type v}
  {M : ModuleCat.{max u v} (MvPolynomial E A)} (Q : ProjectiveResolution M)

/-- **The local complex `W_m = Q_• ⊗_{A[E]} 𝔪ᵐ` of [Stacks, Tag 08RF]**, for a projective
resolution `Q_•` of an `A[E]`-module, read as a cochain complex of `A`-modules over `ℤ`: the
homological degree `p` sits in cohomological degree `-p`, by reindexing along
`ComplexShape.embeddingUpIntLE 0`. -/
def localComplex (m : ℕ) : CochainComplex (ModuleCat.{max u v} A) ℤ :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{max u v} A)).obj
    (((tensorRestrict A E m).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)

/-- **The transition map `W_b ⟶ W_a` of the local complexes**, for `a ≤ b`: the map induced by
the inclusion `𝔪ᵇ ⊆ 𝔪ᵃ`. -/
def localComplexMap {a b : ℕ} (h : a ≤ b) : localComplex Q b ⟶ localComplex Q a :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{max u v} A)).map
    ((NatTrans.mapHomologicalComplex (tensorRestrictMap A E h)
      (ComplexShape.down ℕ)).app Q.complex)

/-- The transition map `W_a ⟶ W_a` of the local complexes is the identity. -/
lemma localComplexMap_rfl (a : ℕ) : localComplexMap Q (le_refl a) = 𝟙 (localComplex Q a) := by
  dsimp only [localComplexMap, localComplex]
  rw [tensorRestrictMap_rfl, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]

/-- The transition maps of the local complexes compose: for `a ≤ b ≤ c`, the map `W_c ⟶ W_b`
followed by `W_b ⟶ W_a` is the map `W_c ⟶ W_a`. -/
lemma localComplexMap_comp {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    localComplexMap Q h₂ ≫ localComplexMap Q h₁ = localComplexMap Q (h₁.trans h₂) := by
  dsimp only [localComplexMap, localComplex]
  rw [← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, tensorRestrictMap_comp]

/-- The chain of one-step transition maps of `StacksDraft.PolynomialLocalComplex.localComplex`
composes to the transition map of the whole chain. -/
lemma chainComp_localComplexMap (N : ℕ) (t : ℕ) :
    chainComp (fun j => localComplex Q (N - j))
        (fun j => localComplexMap Q (Nat.sub_le_sub_left (Nat.le_succ j) N)) t =
      localComplexMap Q (Nat.sub_le N t) := by
  induction t with
  | zero => exact (localComplexMap_rfl Q (N - 0)).symm
  | succ t ih =>
    have hstep : chainComp (fun j => localComplex Q (N - j))
        (fun j => localComplexMap Q (Nat.sub_le_sub_left (Nat.le_succ j) N)) (t + 1) =
      chainComp (fun j => localComplex Q (N - j))
          (fun j => localComplexMap Q (Nat.sub_le_sub_left (Nat.le_succ j) N)) t ≫
        localComplexMap Q (Nat.sub_le_sub_left (Nat.le_succ t) N) := rfl
    rw [hstep, ih, localComplexMap_comp]

/-- The local complexes vanish in positive cohomological degrees. -/
lemma isZero_localComplex_X (m : ℕ) (i : ℤ) (hi : 0 < i) : IsZero ((localComplex Q m).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).2 hi)

/-- The local complexes have no cohomology in positive degrees: they are zero there. -/
lemma isZero_localComplex_homology (m : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((localComplex Q m).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_localComplex_X Q m i hi)

/-- **The local complexes are K-projective**: they are concentrated in degrees `≤ 0` and their
terms are projective `A`-modules
(`StacksDraft.PolynomialLocalComplex.projective_tensorRestrict_obj`). -/
instance isKProjective_localComplex (m : ℕ) : (localComplex Q m).IsKProjective := by
  have : ∀ p : ℕ, CategoryTheory.Projective
      ((((tensorRestrict A E m).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).X p) :=
    fun p => projective_tensorRestrict_obj A E m (Q.complex.X p)
  dsimp only [localComplex, ComplexShape.Embedding.extendFunctor]
  exact CochainComplex.isKProjective_of_projective _ 0

/-! ### [Stacks, Tag 08RE] for the local complexes -/

/-- **[Stacks, Tag 08RE], with the first variable resolved and at the point `0`.** For an
`A[E]`-module `M` killed by the ideal of variables `𝔪`, the inclusion `𝔪ᵇ ⊆ 𝔪ᵃ` induces the
zero map on `Tor'_j^{A[E]}(M, -)` in every degree, whenever `a < b`.

The inclusion factors through `𝔪^{a+1}`, so this follows from the single-step case
`MvPolynomial.tor_map_variableIdeal_pow_succ_eq_zero` read through the balancing of `Tor`. -/
lemma tor'_map_variableIdeal_pow_eq_zero_of_lt (j : ℕ) {a b : ℕ} (hab : a < b)
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0) :
    ((Tor' (ModuleCat.{max u v} (MvPolynomial E A)) j).obj M).map
      (ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right hab.le :
        (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ b :
            Ideal (MvPolynomial E A)) ≤
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ a))) = 0 := by
  rw [← ofHom_inclusion_comp (Ideal.pow_le_pow_right hab) (Ideal.pow_le_pow_right a.le_succ),
    CategoryTheory.Functor.map_comp,
    StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero j M _
      (MvPolynomial.tor_map_variableIdeal_pow_succ_eq_zero A E j a M hM),
    comp_zero]

/-- **[Stacks, Tag 08RE] for the transition chain map over `A[E]`.** The chain map
`Q_• ⊗ 𝔪ᵇ ⟶ Q_• ⊗ 𝔪ᵃ` is zero on `H_j` in every degree, as soon as `a < b`.

By `CategoryTheory.ProjectiveResolution.leftDerived_app_eq` this homology map is, up to the two
isomorphisms identifying `H_j(Q_• ⊗ 𝔪ᵐ)` with `Tor'_j(M, 𝔪ᵐ)`, the component at `M` of
`NatTrans.leftDerived` of `(-) ⊗ 𝔪ᵇ ⟶ (-) ⊗ 𝔪ᵃ`, which is the `Tor'` map of
`StacksDraft.PolynomialLocalComplex.tor'_map_variableIdeal_pow_eq_zero_of_lt`. -/
lemma homologyMap_tensoringRight_mapHomologicalComplex_app_eq_zero (j : ℕ) {a b : ℕ} (hab : a < b)
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).map
          (ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right hab.le :
            (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ b :
                Ideal (MvPolynomial E A)) ≤
              Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ a))))
        (ComplexShape.down ℕ)).app Q.complex) j = 0 := by
  have hTor : (NatTrans.leftDerived
      ((tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).map
        (ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right hab.le :
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ b :
              Ideal (MvPolynomial E A)) ≤
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ a)))) j).app M = 0 :=
    tor'_map_variableIdeal_pow_eq_zero_of_lt j hab hM
  rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq _ Q j] at hTor
  exact eq_zero_of_iso_comp_comp_iso _ _ hTor

/-- **[Stacks, Tag 08RE] for the local complexes.** For an `A[E]`-module `M` killed by the ideal
of variables, the transition map `W_b ⟶ W_a` induces the zero map on `H^{-j}` in **every**
degree `j`, as soon as `a < b`.

Restriction of scalars along `A → A[E]` is exact, so it commutes with homology and carries the
vanishing over `A[E]` to a vanishing over `A`; the reindexing isomorphism
`HomologicalComplex.extendHomologyIso` then identifies `H^{-j}` of the reindexed complex with
`H_j` of the chain complex, naturally in the chain map. -/
lemma homologyMap_localComplexMap_eq_zero (j : ℕ) {a b : ℕ} (hab : a < b)
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0) :
    HomologicalComplex.homologyMap (localComplexMap Q hab.le) (-(j : ℤ)) = 0 := by
  have hA : HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (tensorRestrictMap A E hab.le)
        (ComplexShape.down ℕ)).app Q.complex) j = 0 := by
    have hid : (NatTrans.mapHomologicalComplex (tensorRestrictMap A E hab.le)
          (ComplexShape.down ℕ)).app Q.complex =
        ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A))).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
          ((NatTrans.mapHomologicalComplex
            ((tensoringRight (ModuleCat.{max u v} (MvPolynomial E A))).map
              (ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right hab.le :
                (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ b :
                    Ideal (MvPolynomial E A)) ≤
                  Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ a))))
            (ComplexShape.down ℕ)).app Q.complex) := rfl
    rw [hid]
    exact homologyMap_map_eq_zero _ _ _ _
      (homologyMap_tensoringRight_mapHomologicalComplex_app_eq_zero Q j hab hM)
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := (NatTrans.mapHomologicalComplex (tensorRestrictMap A E hab.le)
      (ComplexShape.down ℕ)).app Q.complex)
    (e := ComplexShape.embeddingUpIntLE (0 : ℤ))
    (hj' := (by simp : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f j = -(j : ℤ)))
  rw [hA, comp_zero] at hnat
  exact eq_zero_of_comp_iso _ hnat

/-! ### The local claim -/

/-- **The local claim in the proof of [Stacks, Tag 08RF].** Let `A` be a commutative ring, let
`S = A[E]`, let `𝔪 = (X_e ; e ∈ E)` and let `M` be an `S`-module killed by `𝔪`, with projective
resolution `Q_•`.  For every additive functor `F` from `A`-modules to an abelian category, every
`n k : ℕ` and every `i > -k`, the transition map `W_{n+k} ⟶ W_n` of the local complexes
`W_m = Q_• ⊗_S 𝔪ᵐ` induces the zero map on `Hⁱ(F(-))`.

This is `Stacks.homologyMap_map_chainComp_eq_zero` — the form of [Stacks, Tag 08Q2] which asks
nothing of `F` beyond additivity — applied to the chain `W_{n+k} ⟶ W_{n+k-1} ⟶ ⋯ ⟶ W_n` of
one-step transitions.  Its hypotheses are
`StacksDraft.PolynomialLocalComplex.isKProjective_localComplex`,
`StacksDraft.PolynomialLocalComplex.isZero_localComplex_homology` and
`StacksDraft.PolynomialLocalComplex.homologyMap_localComplexMap_eq_zero`, the last of which is
[Stacks, Tag 08RE] and holds in every degree, not only below the bound. -/
theorem homologyMap_map_localComplexMap_eq_zero
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0)
    {D : Type*} [Category D] [Abelian D] (F : ModuleCat.{max u v} A ⥤ D) [F.Additive]
    (n k : ℕ) (i : ℤ) (hi : -(k : ℤ) < i) :
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (localComplexMap Q (Nat.le_add_right n k))) i = 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{max u v} A)
  suffices H : ∀ m : ℕ, m = n + k - k → ∀ hle : m ≤ n + k,
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (localComplexMap Q hle)) i = 0 by
    exact H n (by omega) (Nat.le_add_right n k)
  rintro m rfl hle
  have h0 := Stacks.homologyMap_map_chainComp_eq_zero F k
    (fun j => localComplex Q (n + k - j))
    (fun j => localComplexMap Q (Nat.sub_le_sub_left (Nat.le_succ j) (n + k)))
    (fun i hi => isZero_localComplex_homology Q (n + k - 0) i hi)
    (fun j hj => homologyMap_localComplexMap_eq_zero Q j (by omega) hM) i hi
  rwa [chainComp_localComplexMap Q (n + k) k] at h0

end LocalComplex

end StacksDraft.PolynomialLocalComplex

end
