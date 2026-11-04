module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTwistFibreModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheafBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierTwistNoInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InvertibleTwistNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.OrthogonalSimpleQuotientsFinite
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible

/-!
# Finitely many `σ` give a constant simple quotient on the model fibre

Let `k` be a finite field with `q` elements, `K` a field over `k` of cardinality below the cutoff,
`V ⊆ 𝔸¹_k` a nonempty open, `M` a sheaf on `V` locally constant with finite values, and on the
model `Y = Spec Γ(𝔸¹_K ×_{𝔸¹_k} V)` of the fibres `C_{s_σ}`
(`Stacks.EtaleCohomology.exists_ne_zero_fourierTwistModel`) let `L_σ` be the inverse image of
`L_ψ` along `x ↦ σ x`. For a simple `Λ`-module `E`, only finitely many `σ ∈ K` have a nonzero
morphism `p⁻¹ M ⊗ L_σ ⟶ E̲` (`Stacks.EtaleCohomology.finite_setOf_ne_zero_fourierTwistModel`):

* twisting by `L_{-σ}` (`L_σ ⊗ L_{-σ} ≅ 𝟙`) turns it into a nonzero `p⁻¹ M ⟶ E̲ ⊗ L_{-σ}`;
* the sheaves `E̲ ⊗ L_{-σ}`, `σ ≠ 0`, have simple monodromy (they are constant with value `E` on
  the Artin–Schreier cover of `-σ x`) and are pairwise orthogonal: a nonzero
  `E̲ ⊗ L_{-σ} ⟶ E̲ ⊗ L_{-τ}` would twist to a nonzero `E̲ ⟶ E̲ ⊗ L_{σ - τ}`, impossible for
  `σ ≠ τ` since the Artin–Schreier cover of `(σ - τ) x` over `Y`, an open of the cover of `𝔸¹_K`,
  which is an affine line, is connected (`∑ ψ = 0`, `q ∈ Λˣ`);
* a locally constant sheaf on the irreducible normal `Y` has only finitely many pairwise
  orthogonal simple quotients (`AlgebraicGeometry.finite_of_ne_zero_hom_of_orthogonal`).

This is the finiteness, for one field, in the Artin–Schreier half of the generic coinvariant
vanishing in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isLocallyConstantWith_etaleModuleConstantSheaf`.
* `Stacks.EtaleCohomology.schemeSizeBelow_of_locallyOfFiniteType`.
* `Stacks.EtaleCohomology.nonempty_fourierTwistModel`.
* `Stacks.EtaleCohomology.finite_setOf_ne_zero_fourierTwistModel`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier
  Stacks.Blowup Polynomial

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

/-- **A constant sheaf is locally constant**, with its value as local value on the trivial
covering of every étale `X`-scheme. -/
theorem isLocallyConstantWith_etaleModuleConstantSheaf (Λ : Type) [CommRing Λ] {X : Scheme.{u}}
    (Q : ModuleCat.{u + 1} Λ → Prop) (E : ModuleCat.{u + 1} Λ) (hE : Q E) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q
      (etaleModuleConstantSheaf Λ E X) := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ⟨E, hE,
    ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso _ _ U).app E⟩⟩⟩
  refine X.smallEtaleTopology.superset_covering ?_ (X.smallEtaleTopology.top_mem U)
  intro W f _
  exact ⟨U, f, 𝟙 U, Presieve.ofArrows.mk PUnit.unit, Category.comp_id f⟩

/-- **An affine scheme locally of finite type over an object of a big étale site is in the
site.** -/
theorem schemeSizeBelow_of_locallyOfFiniteType (B : BigEtaleSite.{u}) {T S : Scheme.{u}}
    [IsAffine T] (f : T ⟶ S) [LocallyOfFiniteType f] (hS : schemeSizeBelow B.cutoff S) :
    schemeSizeBelow B.cutoff T := by
  have hcov : (⨆ _ : ULift.{u} Unit, (⟨⊤, isAffineOpen_top T⟩ : T.affineOpens).1) = ⊤ := by
    ext x
    simp
  have hI : Cardinal.mk (ULift.{u} Unit) ≤ S.size ^ Cardinal.aleph0 :=
    calc
      Cardinal.mk (ULift.{u} Unit) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ S.size := Scheme.aleph0_le_size _
      _ ≤ S.size ^ Cardinal.aleph0 := Cardinal.self_le_power _ (by simp)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit f (fun _ => ⟨⊤, isAffineOpen_top T⟩) hcov hI hS

/-- **`𝔸¹_K ⟶ Spec K` is smooth.** -/
theorem smooth_specMap_algebraMap_polynomial (K : Type u) [Field K] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K K[X]))) :=
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial K
  SmoothOfRelativeDimension.smooth 1 _

/-- **`E̲ ⊗ L` is finite type locally constant** for a finite `Λ`-module `E` and a locally free
`L`. -/
theorem ftlcProperty_etaleModuleConstantSheaf_tensor (Λ : Type) [CommRing Λ] {X : Scheme.{u}}
    (E : ModuleCat.{u + 1} Λ) [Module.Finite Λ E] (L : EtaleModules.{u, 0} Λ X)
    (hL : IsLocallyFreeEtaleModule Λ L) :
    ftlcProperty X Λ (etaleModuleConstantSheaf Λ E X ⊗ L) :=
  isLocallyConstantWith_of_imp Λ (by
    rintro E' ⟨E₁, E₂, h₁, h₂, rfl⟩
    have := h₁
    have := h₂.2
    exact (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))))
    (isLocallyConstantWith_tensor Λ _ _
      (isLocallyConstantWith_etaleModuleConstantSheaf Λ (fun E' => Module.Finite Λ E') E
        inferInstance) hL)

variable (k : Type u) [Field k] [Fintype k]

local notation "𝔸f" => affineLineStructureMap k

section Model

variable (K : Type u) [Field K] [Algebra k K] {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X]))
  [IsOpenImmersion jV]

/-- **The model `𝔸¹_K ×_{𝔸¹_k} V` is nonempty**: `𝔸¹_K ⟶ 𝔸¹_k` is onto. -/
theorem nonempty_fourierTwistModel [Nonempty V] :
    Nonempty ↥(pullback (fourierTwistModelMap k K) jV : Scheme.{u}) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ => ⟨(default : Spec (.of K)), Subsingleton.elim _ _⟩⟩
  have hw : Surjective (fourierTwistModelMap k K) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_fourierTwistModel k K).flip
      inferInstance
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨z, hz⟩ := hw.surj (jV v)
  obtain ⟨c, -⟩ : z ∈ Set.range (pullback.fst (fourierTwistModelMap k K) jV).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨v, hz.symm⟩
  exact ⟨c⟩

/-- `Spec Γ(Y) ⟶ 𝔸¹_K` is an open immersion. -/
theorem isOpenImmersion_specMap_fourierTwistModelRingHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (fourierTwistModelRingHom k K jV))) := by
  have := isAffine_fourierTwistModel k K jV
  rw [specMap_fourierTwistModelRingHom]
  infer_instance

/-- **A nonempty open of `𝔸¹_K` is geometrically unibranch**: it is smooth over `K`, hence
normal. -/
theorem isGeometricallyUnibranch_spec_of_isOpenImmersion {A : Type u} [CommRing A]
    (Φ : K[X] →+* A) [IsOpenImmersion (Spec.map (CommRingCat.ofHom Φ))] :
    IsGeometricallyUnibranch (Spec (.of A)) := by
  have := smooth_specMap_algebraMap_polynomial K
  have : IsNormal (Spec (.of A)) := isNormal_of_smooth_over_field
    (Spec.map (CommRingCat.ofHom Φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap K K[X])))
  exact isGeometricallyUnibranch_of_isNormal

/-- **The Artin–Schreier cover of `c x`, `c ≠ 0`, over an open of `𝔸¹_K` is connected.** -/
theorem connectedSpace_cover_aeval_C_mul_X_of_isOpenImmersion {A : Type u} [CommRing A]
    [Algebra k A] [Nontrivial A] (Φ : K[X] →ₐ[k] A)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom Φ.toRingHom))] {c : K} (hc : c ≠ 0) :
    ConnectedSpace (cover k A ((Φ.comp (aeval (C c * Polynomial.X))) Polynomial.X)).left := by
  rw [AlgHom.comp_apply, aeval_X]
  have : IsDomain (Ring k (C c * Polynomial.X : K[X])) :=
    isDomain_ring_scaledAffineLine k (Units.mk0 c hc)
  have : IrreducibleSpace (cover k K[X] (C c * Polynomial.X)).left :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (Ring k (C c * Polynomial.X : K[X])))))
  exact connectedSpace_cover_of_isOpenImmersion k (C c * Polynomial.X) Φ

variable (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`L_ψ(σ x)` on the model** `Spec Γ(𝔸¹_K ×_{𝔸¹_k} V)`: the inverse image of `L_ψ` along
`x ↦ σ x`. -/
abbrev fourierTwistModelSheaf (σ : K) :
    EtaleModules.{u, 0} Λ (Spec Γ(pullback (fourierTwistModelMap k K) jV, ⊤)) :=
  (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
    ((fourierTwistModelRingHom k K jV).comp (aeval (C σ * Polynomial.X : K[X])).toRingHom)))).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)

/-- **`L_ψ(a x) ⊗ L_ψ(b x) ≅ L_ψ((a + b) x)`** on a connected `Spec A` over `𝔸¹_K`. -/
theorem nonempty_inverseImage_aeval_C_mul_X_tensor_iso {A : Type u} [CommRing A] [Algebra k A]
    [ConnectedSpace (Spec (.of A))] (Φ : K[X] →ₐ[k] A)
    (hA : schemeSizeBelow B.cutoff (Spec (.of A))) (a b : K) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        (Φ.comp (aeval (C a * Polynomial.X))).toRingHom))).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀) ⊗
      (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        (Φ.comp (aeval (C b * Polynomial.X))).toRingHom))).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀) ≅
      (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        (Φ.comp (aeval (C (a + b) * Polynomial.X))).toRingHom))).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀)) :=
  nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint
    (k := k) (A := k[X]) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (hX' := hA) (e := 𝟙 _) (Φ.comp (aeval (C a * Polynomial.X)))
    (Φ.comp (aeval (C b * Polynomial.X))) (Φ.comp (aeval (C (a + b) * Polynomial.X)))
    (by simp only [AlgHom.comp_apply, aeval_X, ← map_add, ← add_mul, ← C_add])
    (Category.id_comp _).symm (Category.id_comp _).symm (Category.id_comp _).symm p₀ p₀ p₀

/-- **`L_ψ(0 x)` is the unit** on a connected `Spec A` over `𝔸¹_K`. -/
theorem nonempty_inverseImage_aeval_zero_iso_unit {A : Type u} [CommRing A] [Algebra k A]
    [ConnectedSpace (Spec (.of A))] (Φ : K[X] →ₐ[k] A)
    (hA : schemeSizeBelow B.cutoff (Spec (.of A))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        (Φ.comp (aeval (C (0 : K) * Polynomial.X))).toRingHom))).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀) ≅
      𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of A)))) := by
  obtain ⟨c⟩ :=
    nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf_of_basePoint
    (k := k) (A := k[X]) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (φ := Φ.comp (aeval (C (0 : K) * Polynomial.X))) (hX' := hA) (e := 𝟙 _) (c := 0) (by simp)
    (Category.id_comp _).symm p₀
  exact ⟨c ≪≫ (etaleModuleTensorUnitIso Λ _).symm⟩

/-- **`E̲ ⊗ (Spec φ)⁻¹ L_ψ` has simple monodromy** when the Artin–Schreier cover of `φ x` is
connected: it becomes constant with value `E` on that cover. -/
theorem isSimpleModule_monodromyAction_constantSheaf_tensor_inverseImage {A : Type u}
    [CommRing A] [Algebra k A] [IrreducibleSpace (Spec (.of A))] [Nonempty (Spec (.of A))]
    (hU : IsGeometricallyUnibranch (Spec (.of A))) (hA : schemeSizeBelow B.cutoff (Spec (.of A)))
    (φ : k[X] →ₐ[k] A) [ConnectedSpace (cover k A (φ Polynomial.X)).left]
    (x₀ : GeometricPoint (Spec (.of A))) (E : ModuleCat.{u + 1} Λ) [IsSimpleModule Λ E]
    [Finite E] :
    IsSimpleModule Λ ((monodromyAction x₀).obj (etaleModuleConstantSheaf Λ E (Spec (.of A)) ⊗
      (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀)).obj).V := by
  have : Module.Finite Λ E := Module.Finite.of_finite
  let g := φ Polynomial.X
  let W : (Spec (.of A)).Etale := Scheme.Etale.mk (Stacks.ArtinSchreier.coverHom k A g)
  have : ConnectedSpace (Spec (.of (Ring k g))) := ‹ConnectedSpace (cover k A g).left›
  have : Nonempty W.left := ‹ConnectedSpace (Spec (.of (Ring k g)))›.toNonempty
  let φ' : k[X] →ₐ[k] Ring k g := (IsScalarTower.toAlgHom k A (Ring k g)).comp φ
  obtain ⟨c₂⟩ :=
    nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf_of_basePoint
    (k := k) (A := k[X]) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (φ := φ') (hX' := schemeSizeBelow_of_locallyOfFiniteType B
      (Stacks.ArtinSchreier.coverHom k A g) hA) (e := 𝟙 _)
    (c := AdjoinRoot.root (poly k g))
    (h := Stacks.ArtinSchreier.coverHom k A g ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (by
      show algebraMap A (Ring k g) g = _
      rw [root_pow_card]
      ring)
    (by
      rw [Category.id_comp, ← Spec.map_comp]
      rfl) p₀
  let c₁ := ((etaleModuleInverseImageCompIso Λ (Stacks.ArtinSchreier.coverHom k A g)
    (Spec.map (CommRingCat.ofHom φ.toRingHom))).app (affineLineArtinSchreierSheaf k Λ ψ B p₀)).symm
  let eW : (etaleModuleInverseImage.{u, 0} Λ W.hom).obj (etaleModuleConstantSheaf Λ E
      (Spec (.of A)) ⊗ (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        φ.toRingHom))).obj (affineLineArtinSchreierSheaf k Λ ψ B p₀)) ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E :=
    (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ W.hom) _ _).symm ≪≫
      ((etaleModuleInverseImageConstantIso Λ W.hom).app E ⊗ᵢ (c₁ ≪≫ c₂ ≪≫
        (etaleModuleTensorUnitIso Λ _).symm)) ≪≫ ρ_ _
  exact isSimpleModule_monodromyAction_of_inverseImage_iso hU x₀ _
    (ftlcProperty_etaleModuleConstantSheaf_tensor Λ E _ (isLocallyFreeEtaleModule_inverseImage Λ _
      (isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf k Λ ψ B p₀))) W eW

/-- **`E̲ ⟶ E̲ ⊗ (Spec φ)⁻¹ L_ψ` vanishes** when the Artin–Schreier cover of `φ x` is
connected. -/
theorem eq_zero_of_hom_constantSheaf_tensor_inverseImage (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) {A : Type u} [CommRing A] [Algebra k A]
    [ConnectedSpace (Spec (.of A))] (hA : schemeSizeBelow B.cutoff (Spec (.of A)))
    (φ : k[X] →ₐ[k] A) [ConnectedSpace (cover k A (φ Polynomial.X)).left]
    (x₀ : GeometricPoint (Spec (.of A))) (E : ModuleCat.{u + 1} Λ) [IsSimpleModule Λ E]
    [Finite E] (f : etaleModuleConstantSheaf Λ E (Spec (.of A)) ⟶
      etaleModuleConstantSheaf Λ E (Spec (.of A)) ⊗
        (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀)) :
    f = 0 := by
  obtain ⟨p'⟩ := nonempty_finiteEtaleFiber_cover k (φ Polynomial.X) x₀
  obtain ⟨b⟩ := nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint
    (k := k) (A := k[X]) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (φ := φ) (hX' := hA) p₀ x₀ p'
  refine (cancel_mono (whiskerLeftIso (etaleModuleConstantSheaf Λ E (Spec (.of A))) b).hom).1 ?_
  rw [Limits.zero_comp]
  exact eq_zero_of_hom_constantSheaf_tensor_artinSchreierLevelSheaf (k := k) (A := A)
    (g := φ Polynomial.X) (Λ := Λ) (ψ := ψ) (B := B) (hX := hA) hψ hq x₀ p' E _

/-- **Finitely many `σ` give a constant simple quotient of `N ⊗ L_ψ(σ x)` on an open of `𝔸¹_K`.**
Let `Spec A ⟶ 𝔸¹_K` be an open immersion `Spec Φ`, `Spec A` nonempty and below the cutoff, `N` a
finite type locally constant sheaf on `Spec A` and `E` a finite simple `Λ`-module. Only finitely
many `σ ∈ K` have a nonzero morphism `N ⊗ L_ψ(σ x) ⟶ E̲`: twisted by `L_ψ(-σ x)` these morphisms
land in the sheaves `E̲ ⊗ L_ψ(-σ x)`, `σ ≠ 0`, which have simple monodromy and are pairwise
orthogonal, and `Spec A` is irreducible and normal. -/
theorem finite_setOf_ne_zero_of_isOpenImmersion (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) {A : Type u} [CommRing A] (Φ : K[X] →+* A)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom Φ))] [Nonempty (Spec (.of A))]
    (hA : schemeSizeBelow B.cutoff (Spec (.of A))) (N : EtaleModules.{u, 0} Λ (Spec (.of A)))
    (hN : ftlcProperty (Spec (.of A)) Λ N) (E : ModuleCat.{u + 1} Λ) [IsSimpleModule Λ E]
    [Finite E] :
    {σ : K | ∃ φ : N ⊗ (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
          (Φ.comp (aeval (C σ * Polynomial.X : K[X])).toRingHom)))).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀) ⟶
          etaleModuleConstantSheaf Λ E (Spec (.of A)), φ ≠ 0}.Finite := by
  let : Algebra k A := (Φ.comp (algebraMap k K[X])).toAlgebra
  let Φk : K[X] →ₐ[k] A := { toRingHom := Φ, commutes' := fun _ => rfl }
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom Φk.toRingHom)) := ‹_›
  have : IrreducibleSpace (Spec (.of A)) :=
    (Spec.map (CommRingCat.ofHom Φ)).isOpenEmbedding.irreducibleSpace
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ‹Nonempty (Spec (.of A))›
  have hU := isGeometricallyUnibranch_spec_of_isOpenImmersion K Φ
  let φ : K → (k[X] →ₐ[k] A) := fun σ => Φk.comp (aeval (C σ * Polynomial.X))
  let L : K → EtaleModules.{u, 0} Λ (Spec (.of A)) := fun σ =>
    (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom (φ σ).toRingHom))).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have htens : ∀ a b, Nonempty (L a ⊗ L b ≅ L (a + b)) :=
    nonempty_inverseImage_aeval_C_mul_X_tensor_iso k K Λ ψ B p₀ Φk hA
  have hzero : Nonempty (L 0 ≅ 𝟙_ _) := nonempty_inverseImage_aeval_zero_iso_unit k K Λ ψ B p₀ Φk hA
  let e : ∀ a b, a + b = 0 → (L a ⊗ L b ≅ 𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of A)))) :=
    fun a b h => (htens a b).some ≪≫ eqToIso (congrArg L h) ≪≫ hzero.some
  let e₁ := fun σ => e σ (-σ) (add_neg_cancel σ)
  let e₂ := fun σ => e (-σ) σ (neg_add_cancel σ)
  have hLfree : ∀ σ, IsLocallyFreeEtaleModule Λ (L σ) := fun σ =>
    isLocallyFreeEtaleModule_inverseImage Λ _
      (isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have hconn : ∀ c : K, c ≠ 0 → ConnectedSpace (cover k A (φ c Polynomial.X)).left :=
    fun _ hc => connectedSpace_cover_aeval_C_mul_X_of_isOpenImmersion k K Φk hc
  have : Module.Finite Λ E := Module.Finite.of_finite
  let Ec := etaleModuleConstantSheaf Λ E (Spec (.of A))
  let F : K → EtaleModules.{u, 0} Λ (Spec (.of A)) := fun σ => Ec ⊗ L (-σ)
  let x₀ : GeometricPoint (Spec (.of A)) :=
    GeometricPoint.ofPoint (Spec (.of A)) (Classical.arbitrary _)
  have hsimple : ∀ σ : K, σ ≠ 0 → IsSimpleModule Λ ((monodromyAction x₀).obj (F σ).obj).V :=
    fun σ hσ => by
      have := hconn (-σ) (neg_ne_zero.2 hσ)
      exact isSimpleModule_monodromyAction_constantSheaf_tensor_inverseImage k Λ ψ B p₀ hU hA
        (φ (-σ)) x₀ E
  let ι := {σ : K // σ ≠ 0 ∧ ∃ φ : N ⊗ L σ ⟶ Ec, φ ≠ 0}
  have horth : ∀ i j : ι, i ≠ j → ∀ g : F i.1 ⟶ F j.1, g = 0 := fun i j hij g => by
    by_contra hg
    have := hconn (-j.1 + i.1) fun h => hij (Subtype.ext (neg_add_eq_zero.1 h).symm)
    refine invertibleTwist_ne_zero Λ (hLfree (-i.1)) (e₂ i.1) (e₁ i.1) hg
      ((cancel_mono (α_ _ _ _ ≪≫ whiskerLeftIso Ec (htens (-j.1) i.1).some).hom).1 ?_)
    rw [Limits.zero_comp]
    exact eq_zero_of_hom_constantSheaf_tensor_inverseImage k Λ ψ B p₀ hψ hq hA (φ (-j.1 + i.1))
      x₀ E _
  have : Finite ι := finite_of_ne_zero_hom_of_orthogonal hU x₀ N hN (fun i : ι => F i.1)
    (fun i => ftlcProperty_etaleModuleConstantSheaf_tensor Λ E _ (hLfree (-i.1)))
    (fun i => hsimple i.1 i.2.1) (fun i => invertibleTwist Λ (e₁ i.1) i.2.2.choose)
    (fun i => invertibleTwist_ne_zero Λ (hLfree i.1) (e₁ i.1) (e₂ i.1) i.2.2.choose_spec) horth
  refine ((Set.finite_range (fun i : ι => i.1)).insert 0).subset fun σ hσ => ?_
  by_cases h0 : σ = 0
  · exact Or.inl h0
  · exact Or.inr ⟨⟨σ, h0, hσ⟩, rfl⟩

/-- **Finitely many `σ` give a constant simple quotient of `p⁻¹ M ⊗ L_ψ(σ x)` on the model**
`Spec Γ(𝔸¹_K ×_{𝔸¹_k} V)`, for a field `K` over `k` below the cutoff, a sheaf `M` on the nonempty
open `V ⊆ 𝔸¹_k` locally constant with finite values and a finite simple `Λ`-module `E`
(`Stacks.EtaleCohomology.finite_setOf_ne_zero_of_isOpenImmersion`, the model being an open of
`𝔸¹_K`). -/
theorem finite_setOf_ne_zero_fourierTwistModel (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (hK : schemeSizeBelow B.cutoff (Spec (.of K)))
    [Nonempty V] (M : EtaleModules.{u, 0} Λ V)
    (hM : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) M)
    (E : ModuleCat.{u + 1} Λ) [IsSimpleModule Λ E] [Finite E] :
    haveI := isAffine_fourierTwistModel k K jV
    {σ : K | ∃ φ : (etaleModuleInverseImage.{u, 0} Λ
          ((pullback (fourierTwistModelMap k K) jV).isoSpec.inv ≫
            pullback.snd (fourierTwistModelMap k K) jV)).obj M ⊗
          fourierTwistModelSheaf k K jV Λ ψ B p₀ σ ⟶
          etaleModuleConstantSheaf Λ E (Spec Γ(pullback (fourierTwistModelMap k K) jV, ⊤)),
        φ ≠ 0}.Finite := by
  have := isAffine_fourierTwistModel k K jV
  have := isOpenImmersion_specMap_fourierTwistModelRingHom k K jV
  let Y := pullback (fourierTwistModelMap k K) jV
  have : Nonempty Y := nonempty_fourierTwistModel k K jV
  have : Nonempty (Spec Γ(Y, ⊤)) := ⟨Y.isoSpec.hom (Classical.arbitrary Y)⟩
  let π : Spec Γ(Y, ⊤) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (fourierTwistModelRingHom k K jV)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K[X]))
  have := smooth_specMap_algebraMap_polynomial K
  have hA : schemeSizeBelow B.cutoff (Spec Γ(Y, ⊤)) :=
    schemeSizeBelow_of_locallyOfFiniteType B π hK
  have hN := isLocallyConstantWith_of_imp Λ (fun E hE => (ModuleCat.isFG_iff E).2 hE)
    (isLocallyConstantWith_inverseImage Λ _ (Y.isoSpec.inv ≫ pullback.snd _ jV) hM)
  exact finite_setOf_ne_zero_of_isOpenImmersion (k := k) (K := K) (Λ := Λ) (ψ := ψ) (B := B)
    (p₀ := p₀) hψ hq (fourierTwistModelRingHom k K jV) hA _ hN E

end Model

end Stacks.EtaleCohomology

end
