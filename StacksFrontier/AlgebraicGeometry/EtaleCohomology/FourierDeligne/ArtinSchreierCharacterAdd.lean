module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.GaloisCharacter
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Etale.Basic

/-!
# The Artin–Schreier character of a sum

For `g₁, g₂ ∈ A`, the Artin–Schreier character of `g₁ + g₂` is the product of those of `g₁` and
`g₂`: `ψ(-χ_{g₁+g₂}) = ψ(-χ_{g₁}) ψ(-χ_{g₂})`. The covers are compared through the fibre product
`C' = Spec(A[T₁]/(T₁^q - T₁ - g₁) ⊗_A A[T₂]/(T₂^q - T₂ - g₂))`, which maps to the two covers by the
projections and to the cover of `g₁ + g₂` by `T ↦ T₁ + T₂` (the `q`-th power map being additive).
If `σ ∈ π₁` moves the two projections of a point of `C'` by `a` and `b`, it moves its image in the
cover of `g₁ + g₂` by `a + b`, as one reads off the value at the root `T`. This is the
multiplicativity `L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₁ + g₂)` at the level of characters, by which the kernel
`L_ψ(x t) ⊗ L_ψ(t u)` of the composite of two Fourier transforms is `L_ψ(t (x + u))`.

## Main results

* `Stacks.ArtinSchreier.toAdd_character_add`: `χ_{g₁+g₂} = χ_{g₁} + χ_{g₂}`.
* `Stacks.ArtinSchreier.artinSchreierCharacter_add`: `ψ(-χ_{g₁+g₂}) = ψ(-χ_{g₁}) ψ(-χ_{g₂})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

open scoped TensorProduct

universe u

namespace Stacks.ArtinSchreier

variable {k : Type u} [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A]

/-- All points of all Artin–Schreier covers induce on `A` the ring homomorphism of the geometric
point. -/
theorem fiberRingHom_algebraMap_eq {g : A} {s : GeometricPoint (Spec (.of A))}
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) (c : A) :
    (fiberRingHom p).hom (algebraMap A (Ring k g) c) = (Spec.preimage s.hom).hom c := by
  have h : CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ fiberRingHom p = Spec.preimage s.hom := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_map_fiberRingHom, Spec.map_preimage]
    exact p.2
  exact congrArg (fun f => f.hom c) h

variable (k) (g₁ g₂ : A)

/-- The algebra `A[T₁]/(T₁^q - T₁ - g₁) ⊗_A A[T₂]/(T₂^q - T₂ - g₂)` of the fibre product of two
Artin–Schreier covers. -/
abbrev TensorRing := Ring k g₁ ⊗[A] Ring k g₂

/-- The element `T₁ + T₂` of the fibre product. -/
abbrev sumRoot : TensorRing k g₁ g₂ :=
  AdjoinRoot.root (poly k g₁) ⊗ₜ[A] (1 : Ring k g₂) +
    (1 : Ring k g₁) ⊗ₜ[A] AdjoinRoot.root (poly k g₂)

/-- `T₁ + T₂` is a root of `T^q - T - (g₁ + g₂)`. -/
theorem sumRoot_pow_card :
    sumRoot k g₁ g₂ ^ Fintype.card k =
      sumRoot k g₁ g₂ + algebraMap A (TensorRing k g₁ g₂) (g₁ + g₂) := by
  rw [sumRoot, add_pow_card k, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    one_pow, one_pow, root_pow_card, root_pow_card, TensorProduct.add_tmul,
    TensorProduct.tmul_add, map_add]
  have e₁ : algebraMap A (Ring k g₁) g₁ ⊗ₜ[A] (1 : Ring k g₂) =
      algebraMap A (TensorRing k g₁ g₂) g₁ := rfl
  have e₂ : (1 : Ring k g₁) ⊗ₜ[A] algebraMap A (Ring k g₂) g₂ =
      algebraMap A (TensorRing k g₁ g₂) g₂ := by
    rw [Algebra.TensorProduct.algebraMap_apply', ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [e₁, e₂]
  abel

/-- `T₁ + T₂` is a root of the Artin–Schreier polynomial of `g₁ + g₂`. -/
theorem eval₂_sumRoot :
    (poly k (g₁ + g₂)).eval₂ (algebraMap A (TensorRing k g₁ g₂)) (sumRoot k g₁ g₂) = 0 := by
  show Polynomial.eval₂ _ _ ((Polynomial.X ^ Fintype.card k -
    (Polynomial.X + Polynomial.C (g₁ + g₂)) : Polynomial A)) = 0
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C, sumRoot_pow_card, sub_self]

/-- `T ↦ T₁ + T₂`, from the Artin–Schreier algebra of `g₁ + g₂` to the fibre product. -/
def sumAlgHom : Ring k (g₁ + g₂) →ₐ[A] TensorRing k g₁ g₂ :=
  AdjoinRoot.liftAlgHom (poly k (g₁ + g₂)) (Algebra.ofId A (TensorRing k g₁ g₂))
    (sumRoot k g₁ g₂) (eval₂_sumRoot k g₁ g₂)

/-- `sumAlgHom` sends the root `T` to `T₁ + T₂`. -/
theorem sumAlgHom_root :
    sumAlgHom k g₁ g₂ (AdjoinRoot.root (poly k (g₁ + g₂))) = sumRoot k g₁ g₂ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The structure morphism of the fibre product of two Artin–Schreier covers. -/
abbrev productCoverHom : Spec (.of (TensorRing k g₁ g₂)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (TensorRing k g₁ g₂)))

/-- The fibre product of two Artin–Schreier covers is finite over `Spec A`. -/
instance isFinite_productCoverHom : IsFinite (productCoverHom k g₁ g₂) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.2 inferInstance

/-- The fibre product of two Artin–Schreier algebras is étale over `A`. -/
instance etale_tensorRing : Algebra.Etale A (TensorRing k g₁ g₂) :=
  Algebra.Etale.comp A (Ring k g₁) (TensorRing k g₁ g₂)

/-- The fibre product of two Artin–Schreier covers is étale over `Spec A`. -/
instance etale_productCoverHom : Etale (productCoverHom k g₁ g₂) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.2 inferInstance

/-- **The fibre product of the Artin–Schreier covers of `g₁` and `g₂`**, a finite étale cover. -/
def fiberProductCover : FiniteEtaleOver (Spec (.of A)) :=
  MorphismProperty.Over.mk ⊤ (productCoverHom k g₁ g₂) ⟨inferInstance, inferInstance⟩

/-- The first projection of the fibre product. -/
def fiberProductCoverFst : fiberProductCover k g₁ g₂ ⟶ cover k A g₁ :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      Ring k g₁ →+* TensorRing k g₁ g₂))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)

/-- The second projection of the fibre product. -/
def fiberProductCoverSnd : fiberProductCover k g₁ g₂ ⟶ cover k A g₂ :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Ring k g₂ →ₐ[A] TensorRing k g₁ g₂).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (Algebra.TensorProduct.includeRight : Ring k g₂ →ₐ[A] TensorRing k g₁ g₂).commutes a)

/-- `T ↦ T₁ + T₂`, from the fibre product to the cover of `g₁ + g₂`. -/
def fiberProductCoverSum : fiberProductCover k g₁ g₂ ⟶ cover k A (g₁ + g₂) :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (sumAlgHom k g₁ g₂).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (sumAlgHom k g₁ g₂).commutes a)

variable {k g₁ g₂}

/-- The ring homomorphism of a point of a geometric fibre of the fibre product. -/
def fiberProductRingHom {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    CommRingCat.of (TensorRing k g₁ g₂) ⟶ .of s.residueField :=
  Spec.preimage z.1

/-- The ring homomorphism of the image of a point of the fibre product under a morphism of covers
given by `Spec.map h` is its ring homomorphism composed with `h`. -/
private theorem fiberRingHom_map_of_left_eq {g : A} {s : GeometricPoint (Spec (.of A))}
    (f : fiberProductCover k g₁ g₂ ⟶ cover k A g) (h : CommRingCat.of (Ring k g) ⟶ .of _)
    (hf : f.left = Spec.map h) (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    fiberRingHom ((finiteEtaleFiberFunctor s).map f z) = h ≫ fiberProductRingHom z := by
  apply Spec.map_injective
  rw [spec_map_fiberRingHom, Spec.map_comp, fiberProductRingHom]
  exact (congrArg (fun t => t ≫ _) (Spec.map_preimage z.1)).symm.trans (by rw [← hf]; rfl)

/-- The ring homomorphism of the first projection of a point of the fibre product is the
restriction of its ring homomorphism to the first factor. -/
theorem fiberRingHom_map_fiberProductCoverFst {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    fiberRingHom ((finiteEtaleFiberFunctor s).map (fiberProductCoverFst k g₁ g₂) z) =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ fiberProductRingHom z := by
  exact fiberRingHom_map_of_left_eq _ _ rfl z

/-- The ring homomorphism of the second projection of a point of the fibre product is the
restriction of its ring homomorphism to the second factor. -/
theorem fiberRingHom_map_fiberProductCoverSnd {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    fiberRingHom ((finiteEtaleFiberFunctor s).map (fiberProductCoverSnd k g₁ g₂) z) =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Ring k g₂ →ₐ[A] TensorRing k g₁ g₂).toRingHom ≫ fiberProductRingHom z := by
  exact fiberRingHom_map_of_left_eq _ _ rfl z

/-- The ring homomorphism of the image of a point of the fibre product in the cover of `g₁ + g₂`
is its ring homomorphism composed with `sumAlgHom`. -/
theorem fiberRingHom_map_fiberProductCoverSum {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    fiberRingHom ((finiteEtaleFiberFunctor s).map (fiberProductCoverSum k g₁ g₂) z) =
      CommRingCat.ofHom (sumAlgHom k g₁ g₂).toRingHom ≫ fiberProductRingHom z := by
  exact fiberRingHom_map_of_left_eq _ _ rfl z

/-- The morphism `s̄ ⟶ C₁ ×_{Spec A} C₂` with given projections. -/
def fiberProductLift {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    s.source ⟶ Spec (.of (TensorRing k g₁ g₂)) :=
  pullback.lift (f := coverHom k A g₁) (g := coverHom k A g₂)
      (p₁.1 : s.source ⟶ Spec (.of (Ring k g₁))) (p₂.1 : s.source ⟶ Spec (.of (Ring k g₂)))
      (p₁.2.trans p₂.2.symm) ≫
    (pullbackSpecIso A (Ring k g₁) (Ring k g₂)).hom

/-- The first projection of `fiberProductLift p₁ p₂` is `p₁`. -/
theorem fiberProductLift_fst {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    fiberProductLift p₁ p₂ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      Ring k g₁ →+* TensorRing k g₁ g₂)) = p₁.1 := by
  rw [fiberProductLift, Category.assoc]
  exact (congrArg (fun t => _ ≫ t) (pullbackSpecIso_hom_fst A (Ring k g₁) (Ring k g₂))).trans
    (pullback.lift_fst _ _ _)

/-- The second projection of `fiberProductLift p₁ p₂` is `p₂`. -/
theorem fiberProductLift_snd {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    fiberProductLift p₁ p₂ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Ring k g₂ →ₐ[A] TensorRing k g₁ g₂).toRingHom) = p₂.1 := by
  rw [fiberProductLift, Category.assoc]
  exact (congrArg (fun t => _ ≫ t) (pullbackSpecIso_hom_snd A (Ring k g₁) (Ring k g₂))).trans
    (pullback.lift_snd _ _ _)

/-- The point of the fibre product with given projections. -/
def fiberProductPoint {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂) :=
  ⟨fiberProductLift p₁ p₂, by
    have h : productCoverHom k g₁ g₂ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Ring k g₁ →+* TensorRing k g₁ g₂)) ≫ coverHom k A g₁ := by
      rw [← Spec.map_comp]
      rfl
    change fiberProductLift p₁ p₂ ≫ productCoverHom k g₁ g₂ = s.hom
    rw [h, ← Category.assoc, fiberProductLift_fst]
    exact p₁.2⟩

/-- The first projection of `fiberProductPoint p₁ p₂` is `p₁`. -/
theorem map_fiberProductCoverFst_fiberProductPoint {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    (finiteEtaleFiberFunctor s).map (fiberProductCoverFst k g₁ g₂) (fiberProductPoint p₁ p₂) =
      p₁ :=
  Subtype.ext (fiberProductLift_fst p₁ p₂)

/-- The second projection of `fiberProductPoint p₁ p₂` is `p₂`. -/
theorem map_fiberProductCoverSnd_fiberProductPoint {s : GeometricPoint (Spec (.of A))}
    (p₁ : (finiteEtaleFiberFunctor s).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor s).obj (cover k A g₂)) :
    (finiteEtaleFiberFunctor s).map (fiberProductCoverSnd k g₁ g₂) (fiberProductPoint p₁ p₂) =
      p₂ :=
  Subtype.ext (fiberProductLift_snd p₁ p₂)

/-- The value at `T₁ + T₂` of a point of the fibre product is the sum of the values of its
projections. -/
theorem fiberProductRingHom_sumRoot {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    (fiberProductRingHom z).hom (sumRoot k g₁ g₂) =
      fiberRoot ((finiteEtaleFiberFunctor s).map (fiberProductCoverFst k g₁ g₂) z) +
        fiberRoot ((finiteEtaleFiberFunctor s).map (fiberProductCoverSnd k g₁ g₂) z) := by
  rw [fiberRoot, fiberRoot, fiberRingHom_map_fiberProductCoverFst,
    fiberRingHom_map_fiberProductCoverSnd, sumRoot, map_add]
  rfl

/-- The value at `T` of the image of a point of the fibre product in the cover of `g₁ + g₂`. -/
theorem fiberRoot_map_fiberProductCoverSum {s : GeometricPoint (Spec (.of A))}
    (z : (finiteEtaleFiberFunctor s).obj (fiberProductCover k g₁ g₂)) :
    fiberRoot ((finiteEtaleFiberFunctor s).map (fiberProductCoverSum k g₁ g₂) z) =
      fiberRoot ((finiteEtaleFiberFunctor s).map (fiberProductCoverFst k g₁ g₂) z) +
        fiberRoot ((finiteEtaleFiberFunctor s).map (fiberProductCoverSnd k g₁ g₂) z) := by
  rw [fiberRoot, fiberRingHom_map_fiberProductCoverSum, ← fiberProductRingHom_sumRoot,
    ← sumAlgHom_root]
  rfl

variable [ConnectedSpace (Spec (.of A))]

/-- **The torsor character of the Artin–Schreier cover of `g₁ + g₂` is the sum of those of `g₁`
and `g₂`**, read at any points of the three fibres. -/
theorem toAdd_character_add (x : GeometricPoint (Spec (.of A)))
    (p₁ : (finiteEtaleFiberFunctor x).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor x).obj (cover k A g₂))
    (p₁₂ : (finiteEtaleFiberFunctor x).obj (cover k A (g₁ + g₂)))
    (σ : EtaleFundamentalGroup (Spec (.of A)) x) :
    Multiplicative.toAdd ((torsorCover k A (g₁ + g₂)).character x p₁₂ σ) =
      Multiplicative.toAdd ((torsorCover k A g₁).character x p₁ σ) +
        Multiplicative.toAdd ((torsorCover k A g₂).character x p₂ σ) := by
  generalize ha₀ : Multiplicative.toAdd ((torsorCover k A g₁).character x p₁ σ) = a
  generalize hb₀ : Multiplicative.toAdd ((torsorCover k A g₂).character x p₂ σ) = b
  have ha : σ • p₁ = (finiteEtaleFiberFunctor x).map (coverTranslate k A g₁ a) p₁ :=
    ha₀ ▸ (torsorCover k A g₁).smul_eq_character x p₁ σ p₁
  have hb : σ • p₂ = (finiteEtaleFiberFunctor x).map (coverTranslate k A g₂ b) p₂ :=
    hb₀ ▸ (torsorCover k A g₂).smul_eq_character x p₂ σ p₂
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : (finiteEtaleFiberFunctor x).obj (fiberProductCover k g₁ g₂),
      (finiteEtaleFiberFunctor x).map (fiberProductCoverFst k g₁ g₂) q = p₁ ∧
        (finiteEtaleFiberFunctor x).map (fiberProductCoverSnd k g₁ g₂) q = p₂ :=
    ⟨fiberProductPoint p₁ p₂, map_fiberProductCoverFst_fiberProductPoint p₁ p₂,
      map_fiberProductCoverSnd_fiberProductPoint p₁ p₂⟩
  have n : ∀ {g : A} (f : fiberProductCover k g₁ g₂ ⟶ cover k A g),
      σ • (finiteEtaleFiberFunctor x).map f q = (finiteEtaleFiberFunctor x).map f (σ • q) :=
    fun f => ConcreteCategory.congr_hom (σ.hom.naturality f) q
  have n₁ := n (fiberProductCoverFst k g₁ g₂)
  have n₂ := n (fiberProductCoverSnd k g₁ g₂)
  rw [hq₁] at n₁
  rw [hq₂] at n₂
  refine (torsorCover k A (g₁ + g₂)).character_eq_of_smul x p₁₂ σ
    ((finiteEtaleFiberFunctor x).map (fiberProductCoverSum k g₁ g₂) q) (a := a + b) ?_
  refine (n (fiberProductCoverSum k g₁ g₂)).trans ?_
  show (finiteEtaleFiberFunctor x).map (fiberProductCoverSum k g₁ g₂) (σ • q) =
    (finiteEtaleFiberFunctor x).map (coverTranslate k A (g₁ + g₂) (a + b))
      ((finiteEtaleFiberFunctor x).map (fiberProductCoverSum k g₁ g₂) q)
  apply fiber_ext
  apply CommRingCat.hom_ext
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · ext c
    exact fiberRingHom_algebraMap _ _ c
  · show fiberRoot _ = fiberRoot _
    rw [fiberRoot_map_coverTranslate, fiberRoot_map_fiberProductCoverSum,
      fiberRoot_map_fiberProductCoverSum, ← n₁, ← n₂, ha, hb, fiberRoot_map_coverTranslate,
      fiberRoot_map_coverTranslate, hq₁, hq₂,
      IsScalarTower.algebraMap_apply k A (Ring k (g₁ + g₂)),
      IsScalarTower.algebraMap_apply k A (Ring k g₁),
      IsScalarTower.algebraMap_apply k A (Ring k g₂),
      fiberRingHom_algebraMap_eq, fiberRingHom_algebraMap_eq, fiberRingHom_algebraMap_eq, map_add,
      map_add]
    abel

/-- **The Artin–Schreier character of `g₁ + g₂` is the product of those of `g₁` and `g₂`**:
`ψ(-χ_{g₁+g₂}) = ψ(-χ_{g₁}) ψ(-χ_{g₂})`. -/
theorem artinSchreierCharacter_add {O : Type} [CommRing O] (ψ : AddChar k O)
    (x : GeometricPoint (Spec (.of A)))
    (p₁ : (finiteEtaleFiberFunctor x).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor x).obj (cover k A g₂))
    (p₁₂ : (finiteEtaleFiberFunctor x).obj (cover k A (g₁ + g₂))) :
    artinSchreierCharacter k A (g₁ + g₂) ψ x p₁₂ =
      artinSchreierCharacter k A g₁ ψ x p₁ * artinSchreierCharacter k A g₂ ψ x p₂ := by
  ext σ
  rw [MonoidHom.mul_apply, Units.val_mul, artinSchreierCharacter_apply,
    artinSchreierCharacter_apply, artinSchreierCharacter_apply,
    toAdd_character_add x p₁ p₂ p₁₂ σ, neg_add, AddChar.map_add_eq_mul]

end Stacks.ArtinSchreier

end
