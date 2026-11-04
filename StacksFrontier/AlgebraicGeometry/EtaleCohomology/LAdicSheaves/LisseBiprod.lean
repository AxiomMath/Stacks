module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorProduct
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Biproducts of lisse ℓ-adic sheaves

The biproduct of two locally constant sheaves of modules on a site is locally constant: on a
common refinement of two trivializing coverings both restrictions are constant, and restriction
to an object of the site and the constant sheaf functor are additive, so they carry biproducts to
biproducts. Hence the biproduct `F ⊞ G` of two lisse ℓ-adic sheaves is lisse. On rational
stalks the inclusions and projections of `F ⊞ G` split `(F ⊞ G)_x̄ ⊗ ℚ_ℓ` into
`F_x̄ ⊗ ℚ_ℓ ⊕ G_x̄ ⊗ ℚ_ℓ` compatibly with every endomorphism of the geometric point, so the
trace of the geometric Frobenius (and of its powers) on `F ⊞ G` is the sum of the traces on `F`
and on `G`, and its characteristic polynomial is the product.

These are the witnesses' constructions in the trace form of `ι`-realizability
(`Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable`): a sum of traces is the trace on a
biproduct.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstant_biprod`: the biproduct of two locally constant sheaves
  of modules is locally constant.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.IsLisse.biprod`: `F ⊞ G` is lisse.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkEnd_biprod`,
  `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkEnd_biprod`,
  `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe v u

namespace Stacks.ConstantSheaf

section Biprod

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type*) [CommRing Λ]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v} Λ)]

omit [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v} Λ)] in
/-- **The biproduct of two constant sheaves of modules is constant**, with the biproduct of the
two values as its value: the constant sheaf functor is additive. -/
theorem isConstant_biprod [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
    (F G : Sheaf J (ModuleCat.{max u v} Λ))
    [Sheaf.IsConstant J F] [Sheaf.IsConstant J G] : Sheaf.IsConstant J (F ⊞ G) := by
  obtain ⟨M, ⟨eF⟩⟩ := F.mem_essImage_of_isConstant
  obtain ⟨N, ⟨eG⟩⟩ := G.mem_essImage_of_isConstant
  have : (presheafToSheaf J (ModuleCat.{max u v} Λ)).IsLeftAdjoint :=
    (sheafificationAdjunction J _).isLeftAdjoint
  have : PreservesBinaryBiproduct M N (Functor.const Cᵒᵖ : ModuleCat.{max u v} Λ ⥤ _) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  have : PreservesBinaryBiproduct ((Functor.const Cᵒᵖ).obj M) ((Functor.const Cᵒᵖ).obj N)
      (presheafToSheaf J (ModuleCat.{max u v} Λ)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  exact ⟨M ⊞ N, ⟨(presheafToSheaf J _).mapIso ((Functor.const Cᵒᵖ).mapBiprod M N) ≪≫
    (presheafToSheaf J _).mapBiprod _ _ ≪≫ biprod.mapIso eF eG⟩⟩

/-- Restriction along a morphism of the slice sites preserves constant sheaves. -/
theorem isConstant_overPullback_of_hom [HasWeakSheafify J (ModuleCat.{max u v} Λ)] {X Y : C}
    (f : X ⟶ Y)
    [∀ P : (Over X)ᵒᵖ ⥤ ModuleCat.{max u v} Λ, (Over.map f).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J (ModuleCat.{max u v} Λ))
    [Sheaf.IsConstant (J.over Y) ((J.overPullback (ModuleCat.{max u v} Λ) Y).obj F)] :
    Sheaf.IsConstant (J.over X) ((J.overPullback (ModuleCat.{max u v} Λ) X).obj F) := by
  obtain ⟨E, ⟨e⟩⟩ := ((J.overPullback (ModuleCat.{max u v} Λ) Y).obj F).mem_essImage_of_isConstant
  have : Sheaf.IsConstant (J.over X)
      ((J.overMapPullback (ModuleCat.{max u v} Λ) f).obj
        ((J.overPullback (ModuleCat.{max u v} Λ) Y).obj F)) :=
    ⟨E, ⟨constantSheafOverMapIso J (ModuleCat.{max u v} Λ) f E ≪≫
      (J.overMapPullback (ModuleCat.{max u v} Λ) f).mapIso e⟩⟩
  exact Sheaf.isConstant_congr _ (F.pushforwardOverMapIso f)

/-- **The biproduct of two locally constant sheaves of `Λ`-modules is locally constant**: on a
common refinement of trivializing coverings of the two, both restrictions are constant, and
restriction to an object of the site is additive. -/
theorem isLocallyConstant_biprod [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
    [∀ (X Y : C) (f : X ⟶ Y) (P : (Over X)ᵒᵖ ⥤ ModuleCat.{max u v} Λ),
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) [IsLocallyConstant J F] [IsLocallyConstant J G] :
    IsLocallyConstant J (F ⊞ G) where
  exists_cover U := by
    obtain ⟨I, X, f, hf, hF⟩ := IsLocallyConstant.exists_cover (J := J) (F := F) U
    obtain ⟨I', Y, g, hg, hG⟩ := IsLocallyConstant.exists_cover (J := J) (F := G) U
    obtain ⟨K, Z, p, hp⟩ :=
      (Sieve.ofArrows X f ⊓ Sieve.ofArrows Y g).exists_eq_ofArrows
    refine ⟨K, Z, p, hp ▸ J.intersection_covering hf hg, fun k => ?_⟩
    have hk : (Sieve.ofArrows X f ⊓ Sieve.ofArrows Y g) (p k) := by
      rw [hp]; exact Sieve.ofArrows_mk Z p k
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff X f (p k)).mp hk.1
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff Y g (p k)).mp hk.2
    have := hF i
    have := hG j
    have := isConstant_overPullback_of_hom J Λ a F
    have := isConstant_overPullback_of_hom J Λ b G
    have := isConstant_biprod (J.over (Z k)) Λ
      ((J.overPullback (ModuleCat.{max u v} Λ) (Z k)).obj F)
      ((J.overPullback (ModuleCat.{max u v} Λ) (Z k)).obj G)
    have : PreservesBinaryBiproduct F G (J.overPullback (ModuleCat.{max u v} Λ) (Z k)) :=
      preservesBinaryBiproduct_of_preservesBinaryProduct _
    exact Sheaf.isConstant_congr _
      ((J.overPullback (ModuleCat.{max u v} Λ) (Z k)).mapBiprod F G).symm

end Biprod

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.SmallEtale.LAdicSheaf

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- An ℓ-adic sheaf isomorphic to a lisse one is lisse: the isomorphism is one at every level. -/
theorem IsLisse.of_iso {F G : LAdicSheaf.{u, u + 1} B X ℓ} (e : F ≅ G) (hF : F.IsLisse) :
    G.IsLisse := fun n => by
  have := hF n
  exact Stacks.ConstantSheaf.isLocallyConstant_congr _
    (⟨e.hom.app n, e.inv.app n,
      congrArg (fun φ : F ⟶ F => φ.app n) e.hom_inv_id,
      congrArg (fun φ : G ⟶ G => φ.app n) e.inv_hom_id⟩ : F.level n ≅ G.level n)

/-- **The levelwise biproduct of two lisse ℓ-adic sheaves is lisse.** -/
theorem IsLisse.biprodSystem {F G : LAdicSheaf.{u, u + 1} B X ℓ} (hF : F.IsLisse)
    (hG : G.IsLisse) : (Stacks.EtaleCohomology.LAdicSheaf.biprodSystem F G).IsLisse := fun n => by
  have := hF n
  have := hG n
  exact Stacks.ConstantSheaf.isLocallyConstant_biprod _ _ (F.level n) (G.level n)

/-- **The biproduct of two lisse ℓ-adic sheaves is lisse.** -/
theorem IsLisse.biprod {F G : LAdicSheaf.{u, u + 1} B X ℓ} (hF : F.IsLisse) (hG : G.IsLisse) :
    (F ⊞ G).IsLisse :=
  (hF.biprodSystem hG).of_iso
    ((BinaryFan.IsLimit.mk (BinaryFan.mk (Stacks.EtaleCohomology.LAdicSheaf.biprodFst F G)
        (Stacks.EtaleCohomology.LAdicSheaf.biprodSnd F G))
      (fun f g => Stacks.EtaleCohomology.LAdicSheaf.biprodLift f g)
      (fun f g => Stacks.EtaleCohomology.LAdicSheaf.biprodLift_fst f g)
      (fun f g => Stacks.EtaleCohomology.LAdicSheaf.biprodLift_snd f g)
      (fun f g h hf hg =>
        Stacks.EtaleCohomology.LAdicSheaf.biprodLift_unique f g h hf hg)).conePointUniqueUpToIso
      (BinaryBiproduct.isLimit F G))

end AlgebraicGeometry.SmallEtale.LAdicSheaf

namespace Stacks.EtaleCohomology

section LinearAlgebra

variable {K : Type*} [Field K] {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

/-- An endomorphism commuting with a splitting `V = V₁ ⊕ V₂`, given by inclusions `i₁, i₂` and
projections `p₁, p₂`, is conjugate to the product of its two restrictions. -/
theorem conj_eq_prodMap_of_splitting (f : Module.End K V) (f₁ : Module.End K V₁)
    (f₂ : Module.End K V₂) (i₁ : V₁ →ₗ[K] V) (i₂ : V₂ →ₗ[K] V) (p₁ : V →ₗ[K] V₁)
    (p₂ : V →ₗ[K] V₂) (h₁₁ : p₁ ∘ₗ i₁ = LinearMap.id) (h₂₂ : p₂ ∘ₗ i₂ = LinearMap.id)
    (h₁₂ : p₁ ∘ₗ i₂ = 0) (h₂₁ : p₂ ∘ₗ i₁ = 0) (hsum : i₁ ∘ₗ p₁ + i₂ ∘ₗ p₂ = LinearMap.id)
    (hf₁ : f ∘ₗ i₁ = i₁ ∘ₗ f₁) (hf₂ : f ∘ₗ i₂ = i₂ ∘ₗ f₂) :
    ∃ e : V ≃ₗ[K] V₁ × V₂, e.conj f = f₁.prodMap f₂ := by
  refine ⟨LinearEquiv.ofLinear (p₁.prod p₂) (i₁.coprod i₂) ?_ ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨a, b⟩
    have ha := LinearMap.congr_fun h₁₁ a
    have hb := LinearMap.congr_fun h₂₂ b
    have hab := LinearMap.congr_fun h₁₂ b
    have hba := LinearMap.congr_fun h₂₁ a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at ha hb hab hba
    simp [ha, hb, hab, hba]
  · apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun hsum v
    simpa using this
  · apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply]
    obtain ⟨a, b⟩ := v
    have ha := LinearMap.congr_fun hf₁ a
    have hb := LinearMap.congr_fun hf₂ b
    have h11 := LinearMap.congr_fun h₁₁ (f₁ a)
    have h22 := LinearMap.congr_fun h₂₂ (f₂ b)
    have h12 := LinearMap.congr_fun h₁₂ (f₂ b)
    have h21 := LinearMap.congr_fun h₂₁ (f₁ a)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply]
      at ha hb h11 h22 h12 h21
    show (p₁.prod p₂) (f ((i₁.coprod i₂) (a, b))) = (f₁ a, f₂ b)
    simp only [LinearMap.coprod_apply, map_add, ha, hb, LinearMap.prod_apply]
    ext <;> simp [Function.prod, h11, h22, h12, h21]

variable [FiniteDimensional K V] [FiniteDimensional K V₁] [FiniteDimensional K V₂]

omit [FiniteDimensional K V] in
/-- The trace of an endomorphism commuting with a splitting is the sum of the traces of its
restrictions. -/
theorem trace_eq_add_of_splitting (f : Module.End K V) (f₁ : Module.End K V₁)
    (f₂ : Module.End K V₂) (i₁ : V₁ →ₗ[K] V) (i₂ : V₂ →ₗ[K] V) (p₁ : V →ₗ[K] V₁)
    (p₂ : V →ₗ[K] V₂) (h₁₁ : p₁ ∘ₗ i₁ = LinearMap.id) (h₂₂ : p₂ ∘ₗ i₂ = LinearMap.id)
    (h₁₂ : p₁ ∘ₗ i₂ = 0) (h₂₁ : p₂ ∘ₗ i₁ = 0) (hsum : i₁ ∘ₗ p₁ + i₂ ∘ₗ p₂ = LinearMap.id)
    (hf₁ : f ∘ₗ i₁ = i₁ ∘ₗ f₁) (hf₂ : f ∘ₗ i₂ = i₂ ∘ₗ f₂) :
    LinearMap.trace K V f = LinearMap.trace K V₁ f₁ + LinearMap.trace K V₂ f₂ := by
  obtain ⟨e, he⟩ := conj_eq_prodMap_of_splitting f f₁ f₂ i₁ i₂ p₁ p₂ h₁₁ h₂₂ h₁₂ h₂₁ hsum hf₁ hf₂
  rw [← LinearMap.trace_conj' f e, he, LinearMap.trace_prodMap']

/-- The characteristic polynomial of an endomorphism commuting with a splitting is the product
of those of its restrictions. -/
theorem charpoly_eq_mul_of_splitting (f : Module.End K V) (f₁ : Module.End K V₁)
    (f₂ : Module.End K V₂) (i₁ : V₁ →ₗ[K] V) (i₂ : V₂ →ₗ[K] V) (p₁ : V →ₗ[K] V₁)
    (p₂ : V →ₗ[K] V₂) (h₁₁ : p₁ ∘ₗ i₁ = LinearMap.id) (h₂₂ : p₂ ∘ₗ i₂ = LinearMap.id)
    (h₁₂ : p₁ ∘ₗ i₂ = 0) (h₂₁ : p₂ ∘ₗ i₁ = 0) (hsum : i₁ ∘ₗ p₁ + i₂ ∘ₗ p₂ = LinearMap.id)
    (hf₁ : f ∘ₗ i₁ = i₁ ∘ₗ f₁) (hf₂ : f ∘ₗ i₂ = i₂ ∘ₗ f₂) :
    f.charpoly = f₁.charpoly * f₂.charpoly := by
  obtain ⟨e, he⟩ := conj_eq_prodMap_of_splitting f f₁ f₂ i₁ i₂ p₁ p₂ h₁₁ h₂₂ h₁₂ h₂₁ hsum hf₁ hf₂
  rw [← LinearEquiv.charpoly_conj e f, he, LinearMap.charpoly_prodMap]

end LinearAlgebra

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The map of rational stalks of a composite is the composite of the maps. -/
theorem LAdicSheaf.rationalStalkMap_comp {F G H : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G)
    (ψ : G ⟶ H) (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (φ ≫ ψ) s =
      LAdicSheaf.rationalStalkMap ψ s ∘ₗ LAdicSheaf.rationalStalkMap φ s := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_comp, LinearMap.baseChange_comp]

/-- The map of rational stalks of the identity is the identity. -/
theorem LAdicSheaf.rationalStalkMap_id (F : LAdicSheaf.{u, u + 1} B X ℓ) (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (𝟙 F) s = LinearMap.id := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_id, LinearMap.baseChange_id]

/-- The map of rational stalks of a sum is the sum of the maps. -/
theorem LAdicSheaf.rationalStalkMap_add {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ ψ : F ⟶ G)
    (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (φ + ψ) s =
      LAdicSheaf.rationalStalkMap φ s + LAdicSheaf.rationalStalkMap ψ s := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_add, LinearMap.baseChange_add]

/-- The map of rational stalks of the zero morphism is zero. -/
theorem LAdicSheaf.rationalStalkMap_zero (F G : LAdicSheaf.{u, u + 1} B X ℓ)
    (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (0 : F ⟶ G) s = 0 := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_zero, LinearMap.baseChange_zero]

/-- The inclusions and projections of a biproduct split its rational stalk. -/
private theorem rationalStalkMap_biprod_splitting (F G : LAdicSheaf.{u, u + 1} B X ℓ)
    (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (biprod.fst : F ⊞ G ⟶ F) s ∘ₗ
        LAdicSheaf.rationalStalkMap (biprod.inl : F ⟶ F ⊞ G) s = LinearMap.id ∧
      LAdicSheaf.rationalStalkMap (biprod.snd : F ⊞ G ⟶ G) s ∘ₗ
        LAdicSheaf.rationalStalkMap (biprod.inr : G ⟶ F ⊞ G) s = LinearMap.id ∧
      LAdicSheaf.rationalStalkMap (biprod.fst : F ⊞ G ⟶ F) s ∘ₗ
        LAdicSheaf.rationalStalkMap (biprod.inr : G ⟶ F ⊞ G) s = 0 ∧
      LAdicSheaf.rationalStalkMap (biprod.snd : F ⊞ G ⟶ G) s ∘ₗ
        LAdicSheaf.rationalStalkMap (biprod.inl : F ⟶ F ⊞ G) s = 0 ∧
      LAdicSheaf.rationalStalkMap (biprod.inl : F ⟶ F ⊞ G) s ∘ₗ
          LAdicSheaf.rationalStalkMap (biprod.fst : F ⊞ G ⟶ F) s +
        LAdicSheaf.rationalStalkMap (biprod.inr : G ⟶ F ⊞ G) s ∘ₗ
          LAdicSheaf.rationalStalkMap (biprod.snd : F ⊞ G ⟶ G) s = LinearMap.id := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← LAdicSheaf.rationalStalkMap_comp, biprod.inl_fst, LAdicSheaf.rationalStalkMap_id]
  · rw [← LAdicSheaf.rationalStalkMap_comp, biprod.inr_snd, LAdicSheaf.rationalStalkMap_id]
  · rw [← LAdicSheaf.rationalStalkMap_comp, biprod.inr_fst, LAdicSheaf.rationalStalkMap_zero]
  · rw [← LAdicSheaf.rationalStalkMap_comp, biprod.inl_snd, LAdicSheaf.rationalStalkMap_zero]
  · rw [← LAdicSheaf.rationalStalkMap_comp, ← LAdicSheaf.rationalStalkMap_comp,
      ← LAdicSheaf.rationalStalkMap_add, biprod.total, LAdicSheaf.rationalStalkMap_id]

/-- **The trace on the rational stalk of a biproduct is the sum of the traces**, for the action
of every endomorphism of the geometric point. -/
theorem LAdicSheaf.trace_rationalStalkEnd_biprod (F G : LAdicSheaf.{u, u + 1} B X ℓ)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ (F ⊞ G) a) =
      LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F a) +
        LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ G a) := by
  obtain ⟨h₁₁, h₂₂, h₁₂, h₂₁, hsum⟩ := rationalStalkMap_biprod_splitting F G s
  exact trace_eq_add_of_splitting _ _ _ _ _ _ _ h₁₁ h₂₂ h₁₂ h₂₁ hsum
    (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap _ a)
    (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap _ a)

/-- **The characteristic polynomial on the rational stalk of a biproduct is the product**, for
the action of every endomorphism of the geometric point. -/
theorem LAdicSheaf.charpoly_rationalStalkEnd_biprod (F G : LAdicSheaf.{u, u + 1} B X ℓ)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    (LAdicSheaf.rationalStalkEnd B X ℓ (F ⊞ G) a).charpoly =
      (LAdicSheaf.rationalStalkEnd B X ℓ F a).charpoly *
        (LAdicSheaf.rationalStalkEnd B X ℓ G a).charpoly := by
  obtain ⟨h₁₁, h₂₂, h₁₂, h₂₁, hsum⟩ := rationalStalkMap_biprod_splitting F G s
  exact charpoly_eq_mul_of_splitting _ _ _ _ _ _ _ h₁₁ h₂₂ h₁₂ h₂₁ hsum
    (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap _ a)
    (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap _ a)

/-- **The trace of a power of the geometric Frobenius on a biproduct is the sum of the traces**:
`Tr(π_x ^ m | (F ⊞ G)_x̄ ⊗ ℚ_ℓ) = Tr(π_x ^ m | F_x̄ ⊗ ℚ_ℓ) + Tr(π_x ^ m | G_x̄ ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow (F G : LAdicSheaf.{u, u + 1} B X ℓ)
    (x : X.1) (hx : Finite (X.1.residueField x)) (m : ℕ) :
    LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkFrobenius B X ℓ (F ⊞ G) x hx ^ m) =
      LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F x hx ^ m) +
        LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkFrobenius B X ℓ G x hx ^ m) := by
  have := hx
  have hpow : ∀ {H H' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : H ⟶ H'),
      (LAdicSheaf.rationalStalkFrobenius B X ℓ H' x hx ^ m) ∘ₗ
          LAdicSheaf.rationalStalkMap φ (geometricPointAt X.1 x) =
        LAdicSheaf.rationalStalkMap φ (geometricPointAt X.1 x) ∘ₗ
          (LAdicSheaf.rationalStalkFrobenius B X ℓ H x hx ^ m) := by
    intro H H' φ
    have hc : LAdicSheaf.rationalStalkFrobenius B X ℓ H' x hx ∘ₗ
          LAdicSheaf.rationalStalkMap φ (geometricPointAt X.1 x) =
        LAdicSheaf.rationalStalkMap φ (geometricPointAt X.1 x) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B X ℓ H x hx :=
      LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap φ (frobeniusPointHom X.1 x)
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.comp_assoc, hc, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  obtain ⟨h₁₁, h₂₂, h₁₂, h₂₁, hsum⟩ :=
    rationalStalkMap_biprod_splitting F G (geometricPointAt X.1 x)
  exact trace_eq_add_of_splitting _ _ _ _ _ _ _ h₁₁ h₂₂ h₁₂ h₂₁ hsum (hpow _) (hpow _)

end Stacks.EtaleCohomology

end
