module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ConeHomologyLadder
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvatureBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairBaseChangeConnection07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeTransitivity07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionComparisonLevelwise
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The base change map along a chain of completed `p`-th root extensions

Let `D → D₁ → ⋯ → D_n` be a chain of maps of rings with forms, each of whose base change maps of
completed de Rham complexes has a cone killed by `p` — in the application each step is the
completed `p`-th root extension `D_k → D_{k+1} = (D_k[z]⟨ξ⟩/(ξ - (z^p - λ_k)))^∧` of
[Stacks, Lemma 60.25.3, Tag 07N1].  This file proves that the cone of the base change map along
the composite `D → D_n` is killed by `p^n`, which is the row-zero input of the proof of
[Stacks, Lemma 60.26.3, Tag 07Q9].

The statement is about cones of morphisms of `ℕ`-indexed cochain complexes of abelian groups,
extended to `ℤ`-indexed ones.  Its form here is the annihilation of the cone *object* in the
derived category (`Crystalline.CompletedDeRham.ConeKilledNat07Q9`), which is stable under
composition by the octahedron axiom; it implies the annihilation of every cohomology group of the
mapping cone (`Crystalline.CompletedDeRham.ConeKilledNat07Q9.homology`).

## Main definitions

* `Crystalline.CompletedDeRham.ConeKilledNat07Q9` — `q` annihilates the cone of `c`.
* `Crystalline.CompletedDeRham.BaseChangeConeKilled07Q9` — for every integrable `(M, ∇)` over
  `D`, `q` annihilates the cone of the base change map along `D → D'`.

## Main results

* `Crystalline.CompletedDeRham.ConeKilledNat07Q9.of_arrowIso`, `...comp`, `...of_homotopy` and
  `...homology` — the formal properties.
* `Crystalline.CompletedDeRham.coneKilledNat07Q9_baseChange_trans` — transitivity: killed by
  `a` along `D → D₁` and by `b` along `D₁ → D₂` gives killed by `a * b` along `D → D₂`.
* `Crystalline.CompletedDeRham.baseChangeConeKilled07Q9_trans` — the same for the predicate
  `BaseChangeConeKilled07Q9`.
* `Crystalline.CompletedDeRham.coneKilledNat07Q9_baseChange_of_iso` — invariance under
  isomorphisms of the data.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive Pretriangulated DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

namespace CompletedDeRham

/-! ### Annihilation of cones -/

section Cone

variable {C : Type*} [Category* C] [Abelian C]

/-- **`q` annihilates the cone of `c`**: for a morphism `c` of `ℕ`-indexed cochain complexes,
`q • 𝟙` vanishes on the image in the derived category of the mapping cone of the extension of `c`
to `ℤ`-indexed complexes. -/
def ConeKilledNat07Q9 (q : ℤ) {K L : CochainComplex C ℕ} (c : K ⟶ L) : Prop :=
  letI := HasDerivedCategory.standard C
  q • 𝟙 (DerivedCategory.Q.obj (CochainComplex.mappingCone
    (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat))) = 0

namespace ConeKilledNat07Q9

variable {q : ℤ} {K L : CochainComplex C ℕ} {c : K ⟶ L}

/-- The annihilation of the cone is the annihilation of the third term of every distinguished
triangle on the image of the extension of `c`. -/
theorem iff_distinguished :
    ConeKilledNat07Q9 q c ↔
      letI := HasDerivedCategory.standard C
      ∀ (Z : DerivedCategory C)
        (v : DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat) ⟶ Z)
        (w : Z ⟶ (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧),
        Triangle.mk (DerivedCategory.Q.map
          (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)) v w ∈ distTriang _ →
          q • 𝟙 Z = 0 := by
  let := HasDerivedCategory.standard C
  have hT := DerivedCategory.mappingCone_triangle_distinguished
    (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)
  constructor
  · intro h Z v w hZ
    obtain ⟨i, -⟩ := exists_iso_of_arrow_iso _ _ hT hZ (Iso.refl _)
    exact Stacks.SplitCone.smul_id_eq_zero_of_iso (Triangle.π₃.mapIso i) h
  · intro h
    exact h _ _ _ hT

/-- **The annihilation only depends on the isomorphism class of the arrow.** -/
theorem of_arrowIso {K' L' : CochainComplex C ℕ} {c' : K' ⟶ L'} (φ : Arrow.mk c ≅ Arrow.mk c')
    (h : ConeKilledNat07Q9 q c') : ConeKilledNat07Q9 q c := by
  let := HasDerivedCategory.standard C
  refine iff_distinguished.2 fun Z v w hZ ↦ ?_
  exact Stacks.SplitCone.smul_id_eq_zero_of_arrowIso
    ((ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q).mapArrow.mapIso φ) q
    (iff_distinguished.1 h) v w hZ

/-- **Transitivity**: if `a` annihilates the cone of `c` and `b` that of `c'`, then `a * b`
annihilates the cone of `c ≫ c'` (the octahedron axiom). -/
theorem comp {M : CochainComplex C ℕ} {c' : L ⟶ M} {a b : ℤ} (h : ConeKilledNat07Q9 a c)
    (h' : ConeKilledNat07Q9 b c') : ConeKilledNat07Q9 (a * b) (c ≫ c') := by
  let := HasDerivedCategory.standard C
  refine iff_distinguished.2 fun Z v w hZ ↦ ?_
  refine Stacks.Triangulated.mul_smul_id_eq_zero_of_comp _ _ a b (iff_distinguished.1 h)
    (iff_distinguished.1 h') v w ?_
  rw [HomologicalComplex.extendMap_comp, Functor.map_comp] at hZ
  exact hZ

/-- **A morphism split up to `a`** — a morphism `e` back with `c ≫ e = a • 𝟙` and a homotopy from
`a • 𝟙` to `e ≫ c` killed by `c` — has its cone annihilated by `a`. -/
theorem of_homotopy {a : ℤ} (e : L ⟶ K) (hce : c ≫ e = a • 𝟙 K)
    (ho : _root_.Homotopy (a • 𝟙 L) (e ≫ c)) (hch : ∀ i j, c.f i ≫ ho.hom i j = 0) :
    ConeKilledNat07Q9 a c := by
  let := HasDerivedCategory.standard C
  exact (Stacks.SplitCone.Data.extendNat e hce ho hch).smul_id_Q_obj_mappingCone_eq_zero

/-- An isomorphism has its cone annihilated by `1`. -/
theorem of_isIso [IsIso c] : ConeKilledNat07Q9 1 c :=
  of_homotopy (inv c) (by simp) (_root_.Homotopy.ofEq (by simp)) (fun _ _ ↦ by simp)

/-- **The annihilation of the cohomology of the mapping cone.** -/
theorem homology (h : ConeKilledNat07Q9 q c) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)).homology j) = 0 := by
  let := HasDerivedCategory.standard C
  exact (Stacks.ConeLadder.coneHomologyKilled_Q_map_iff q _).1
    (Stacks.ConeLadder.ConeHomologyKilled.of_smul_id_eq_zero _ (iff_distinguished.1 h)) j

/-- Annihilation by `q` gives annihilation by any multiple of `q`. -/
theorem mul_left (h : ConeKilledNat07Q9 q c) (r : ℤ) : ConeKilledNat07Q9 (r * q) c := by
  unfold ConeKilledNat07Q9 at h ⊢
  rw [mul_smul, h, smul_zero]

end ConeKilledNat07Q9

end Cone

/-! ### Transitivity and invariance for the base change maps -/

section BaseChange

variable (p : ℕ) (D : Type u) [CommRing D] (D₁ : Type u) [CommRing D₁] (D₂ : Type u)
  [CommRing D₂] [Algebra D D₁] [Algebra D₁ D₂] [Algebra D D₂] [IsScalarTower D D₁ D₂]
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om₁ : ℕ → Type u) [∀ i, AddCommGroup (Om₁ i)] [∀ i, Module D₁ (Om₁ i)]
  (Om₂ : ℕ → Type u) [∀ i, AddCommGroup (Om₂ i)] [∀ i, Module D₂ (Om₂ i)]
  (psi₁ : ∀ i, Om i →ₛₗ[algebraMap D D₁] Om₁ i) (psi₂ : ∀ i, Om₁ i →ₛₗ[algebraMap D₁ D₂] Om₂ i)
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D₂] Om₂ i) (hpsi : ∀ i ω, psi i ω = psi₂ i (psi₁ i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge₁ : ∀ i, Om₁ i →ₗ[D₁] Om₁ 1 →ₗ[D₁] Om₁ (i + 1))
  (wedge₂ : ∀ i, Om₂ i →ₗ[D₂] Om₂ 1 →ₗ[D₂] Om₂ (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham₁ : ∀ i, Om₁ i →+ Om₁ (i + 1))
  (deRham₂ : ∀ i, Om₂ i →+ Om₂ (i + 1))
  (d : D → Om 1) (d₁ : D₁ → Om₁ 1) (d₂ : D₂ → Om₂ 1)
  (hd₁add : ∀ x y : D₁, d₁ (x + y) = d₁ x + d₁ y)
  (hd₁leib : ∀ x y : D₁, d₁ (x * y) = x • d₁ y + y • d₁ x)
  (hd₂add : ∀ x y : D₂, d₂ (x + y) = d₂ x + d₂ y)
  (hd₂leib : ∀ x y : D₂, d₂ (x * y) = x • d₂ y + y • d₂ x)
  (hpsi₁1 : ∀ x : D, psi₁ 1 (d x) = d₁ (algebraMap D D₁ x))
  (hpsi₂1 : ∀ x : D₁, psi₂ 1 (d₁ x) = d₂ (algebraMap D₁ D₂ x))
  (hpsi1 : ∀ x : D, psi 1 (d x) = d₂ (algebraMap D D₂ x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib₁ : IsGradedLeibniz D₁ Om₁ wedge₁ deRham₁ d₁)
  (hleib₂ : IsGradedLeibniz D₂ Om₂ wedge₂ deRham₂ d₂)
  (hpsi₁_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi₁ (i + 1) (wedge i ω η) = wedge₁ i (psi₁ i ω) (psi₁ 1 η))
  (hpsi₁_deRham : ∀ (i : ℕ) (ω : Om i), psi₁ (i + 1) (deRham i ω) = deRham₁ i (psi₁ i ω))
  (hpsi₂_wedge : ∀ (i : ℕ) (ω : Om₁ i) (η : Om₁ 1),
    psi₂ (i + 1) (wedge₁ i ω η) = wedge₂ i (psi₂ i ω) (psi₂ 1 η))
  (hpsi₂_deRham : ∀ (i : ℕ) (ω : Om₁ i), psi₂ (i + 1) (deRham₁ i ω) = deRham₂ i (psi₂ i ω))
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge₂ i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham₂ i (psi i ω))

include hpsi in
/-- **Transitivity of the annihilation of the cones**: if `a` kills the cone of the base change
map along `D → D₁` and `b` kills the cone of the base change map of the base-changed module along
`D₁ → D₂`, then `a * b` kills the cone of the base change map along `D → D₂`. -/
theorem coneKilledNat07Q9_baseChange_trans (nabla : CompletedConnection p D (Om 1) d M)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq₁ : IsSquareZero p D₁ Om₁ wedge₁ deRham₁ (CompletedConnection.baseChangeCarrier p D D₁ M)
      (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add hd₁leib
        hpsi₁1) hleib₁)
    (hsq₁₂ : IsSquareZero p D₂ Om₂ wedge₂ deRham₂ _
      (transitivityConnection07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ d₁ d₂ nabla hd₁add hd₁leib
        hd₂add hd₂leib hpsi₁1 hpsi₂1) hleib₂)
    (hsq₂ : IsSquareZero p D₂ Om₂ wedge₂ deRham₂ (CompletedConnection.baseChangeCarrier p D D₂ M)
      (CompletedConnection.baseChange p D D₂ M (Om 1) (Om₂ 1) d₂ (psi 1) nabla hd₂add hd₂leib
        hpsi1) hleib₂) {a b : ℤ}
    (h₁ : ConeKilledNat07Q9 a (baseChangeComplexHom p D D₁ M Om Om₁ psi₁ wedge wedge₁ deRham
      deRham₁ d₁ nabla hd₁add hd₁leib hpsi₁1 hleib hleib₁ hpsi₁_wedge hpsi₁_deRham hsq hsq₁))
    (h₂ : ConeKilledNat07Q9 b (baseChangeComplexHom p D₁ D₂
      (CompletedConnection.baseChangeCarrier p D D₁ M) Om₁ Om₂ psi₂ wedge₁ wedge₂ deRham₁ deRham₂
      d₂ (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add hd₁leib
        hpsi₁1) hd₂add hd₂leib hpsi₂1 hleib₁ hleib₂ hpsi₂_wedge hpsi₂_deRham hsq₁ hsq₁₂)) :
    ConeKilledNat07Q9 (a * b) (baseChangeComplexHom p D D₂ M Om Om₂ psi wedge wedge₂ deRham
      deRham₂ d₂ nabla hd₂add hd₂leib hpsi1 hleib hleib₂ hpsi_wedge hpsi_deRham hsq hsq₂) :=
  ConeKilledNat07Q9.of_arrowIso
    (baseChangeComplexHom_trans07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi hpsi wedge wedge₁ wedge₂
      deRham deRham₁ deRham₂ d₁ d₂ nabla hd₁add hd₁leib hd₂add hd₂leib hpsi₁1 hpsi₂1 hpsi1 hleib
      hleib₁ hleib₂ hpsi₁_wedge hpsi₁_deRham hpsi₂_wedge hpsi₂_deRham hpsi_wedge hpsi_deRham hsq
      hsq₁ hsq₁₂ hsq₂)
    (h₁.comp h₂)

end BaseChange

/-! ### Base change maps whose cones are all killed by `q` -/

section Predicate

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (d : D → Om 1) (d' : D' → Om' 1)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))

/-- **`q` kills the cones of the base change maps along `D → D'`**: for every module `M` over
`D` with an integrable completed connection `∇` (curvature zero), `q` annihilates the cone of the
base change map `M ⊗^∧_D Ω^* ⟶ M' ⊗^∧_{D'} Ω'^*`. -/
def BaseChangeConeKilled07Q9 (q : ℤ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module D M] (nabla : CompletedConnection p D (Om 1) d M),
    IsCurvatureZero p D Om wedge deRham M nabla hleib →
    ∀ (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
      (hsq' : IsSquareZero p D' Om' wedge' deRham'
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hleib'),
      ConeKilledNat07Q9 q (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham'
        d' nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq')

end Predicate

section PredicateTrans

variable (p : ℕ) (D : Type u) [CommRing D] (D₁ : Type u) [CommRing D₁] (D₂ : Type u)
  [CommRing D₂] [Algebra D D₁] [Algebra D₁ D₂] [Algebra D D₂] [IsScalarTower D D₁ D₂]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om₁ : ℕ → Type u) [∀ i, AddCommGroup (Om₁ i)] [∀ i, Module D₁ (Om₁ i)]
  (Om₂ : ℕ → Type u) [∀ i, AddCommGroup (Om₂ i)] [∀ i, Module D₂ (Om₂ i)]
  (psi₁ : ∀ i, Om i →ₛₗ[algebraMap D D₁] Om₁ i) (psi₂ : ∀ i, Om₁ i →ₛₗ[algebraMap D₁ D₂] Om₂ i)
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D₂] Om₂ i) (hpsi : ∀ i ω, psi i ω = psi₂ i (psi₁ i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge₁ : ∀ i, Om₁ i →ₗ[D₁] Om₁ 1 →ₗ[D₁] Om₁ (i + 1))
  (wedge₂ : ∀ i, Om₂ i →ₗ[D₂] Om₂ 1 →ₗ[D₂] Om₂ (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham₁ : ∀ i, Om₁ i →+ Om₁ (i + 1))
  (deRham₂ : ∀ i, Om₂ i →+ Om₂ (i + 1))
  (d : D → Om 1) (d₁ : D₁ → Om₁ 1) (d₂ : D₂ → Om₂ 1)
  (hd₁add : ∀ x y : D₁, d₁ (x + y) = d₁ x + d₁ y)
  (hd₁leib : ∀ x y : D₁, d₁ (x * y) = x • d₁ y + y • d₁ x)
  (hd₂add : ∀ x y : D₂, d₂ (x + y) = d₂ x + d₂ y)
  (hd₂leib : ∀ x y : D₂, d₂ (x * y) = x • d₂ y + y • d₂ x)
  (hpsi₁1 : ∀ x : D, psi₁ 1 (d x) = d₁ (algebraMap D D₁ x))
  (hpsi₂1 : ∀ x : D₁, psi₂ 1 (d₁ x) = d₂ (algebraMap D₁ D₂ x))
  (hpsi1 : ∀ x : D, psi 1 (d x) = d₂ (algebraMap D D₂ x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib₁ : IsGradedLeibniz D₁ Om₁ wedge₁ deRham₁ d₁)
  (hleib₂ : IsGradedLeibniz D₂ Om₂ wedge₂ deRham₂ d₂)
  (hpsi₁_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi₁ (i + 1) (wedge i ω η) = wedge₁ i (psi₁ i ω) (psi₁ 1 η))
  (hpsi₁_deRham : ∀ (i : ℕ) (ω : Om i), psi₁ (i + 1) (deRham i ω) = deRham₁ i (psi₁ i ω))
  (hpsi₂_wedge : ∀ (i : ℕ) (ω : Om₁ i) (η : Om₁ 1),
    psi₂ (i + 1) (wedge₁ i ω η) = wedge₂ i (psi₂ i ω) (psi₂ 1 η))
  (hpsi₂_deRham : ∀ (i : ℕ) (ω : Om₁ i), psi₂ (i + 1) (deRham₁ i ω) = deRham₂ i (psi₂ i ω))
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge₂ i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham₂ i (psi i ω))
  (hanti₁ : ∀ η ζ : Om₁ 1, wedge₁ 1 η ζ + wedge₁ 1 ζ η = 0)
  (hdd₁ : ∀ c : D₁, deRham₁ 1 (d₁ c) = 0)
  (hsqz₁ : ∀ (N : Type u) [AddCommGroup N] [Module D₁ N]
    (nablaN : CompletedConnection p D₁ (Om₁ 1) d₁ N),
    IsCurvatureZero p D₁ Om₁ wedge₁ deRham₁ N nablaN hleib₁ →
      IsSquareZero p D₁ Om₁ wedge₁ deRham₁ N nablaN hleib₁)
  (hanti₂ : ∀ η ζ : Om₂ 1, wedge₂ 1 η ζ + wedge₂ 1 ζ η = 0)
  (hdd₂ : ∀ c : D₂, deRham₂ 1 (d₂ c) = 0)
  (hsqz₂ : ∀ (N : Type u) [AddCommGroup N] [Module D₂ N]
    (nablaN : CompletedConnection p D₂ (Om₂ 1) d₂ N),
    IsCurvatureZero p D₂ Om₂ wedge₂ deRham₂ N nablaN hleib₂ →
      IsSquareZero p D₂ Om₂ wedge₂ deRham₂ N nablaN hleib₂)

include hpsi hanti₁ hdd₁ hsqz₁ hanti₂ hdd₂ hsqz₂ in
/-- **Transitivity of `BaseChangeConeKilled07Q9`**: killed by `a` along `D → D₁` and by `b` along
`D₁ → D₂` gives killed by `a * b` along `D → D₂`.  The base-changed connection on
`(D₁ ⊗_D M)^∧` is again integrable (`Crystalline.CompletedDeRham.isCurvatureZero_baseChange`),
so the second hypothesis applies to it, and the two cones compose by
`Crystalline.CompletedDeRham.coneKilledNat07Q9_baseChange_trans`. -/
theorem baseChangeConeKilled07Q9_trans {a b : ℤ}
    (h₁ : BaseChangeConeKilled07Q9 p D D₁ Om Om₁ psi₁ wedge wedge₁ deRham deRham₁ d d₁ hd₁add
      hd₁leib hpsi₁1 hleib hleib₁ hpsi₁_wedge hpsi₁_deRham a)
    (h₂ : BaseChangeConeKilled07Q9 p D₁ D₂ Om₁ Om₂ psi₂ wedge₁ wedge₂ deRham₁ deRham₂ d₁ d₂ hd₂add
      hd₂leib hpsi₂1 hleib₁ hleib₂ hpsi₂_wedge hpsi₂_deRham b) :
    BaseChangeConeKilled07Q9 p D D₂ Om Om₂ psi wedge wedge₂ deRham deRham₂ d d₂ hd₂add hd₂leib
      hpsi1 hleib hleib₂ hpsi_wedge hpsi_deRham (a * b) := by
  intro M _ _ nabla hint hsq hsq₂
  have hint₁ := isCurvatureZero_baseChange p D D₁ M Om Om₁ psi₁ wedge wedge₁ deRham deRham₁ d₁
    nabla hd₁add hd₁leib hpsi₁1 hleib hleib₁ hpsi₁_wedge hpsi₁_deRham hanti₁ hdd₁ hint
  have hsq₁ := hsqz₁ _ _ hint₁
  have hint₁₂ := isCurvatureZero_baseChange p D₁ D₂ _ Om₁ Om₂ psi₂ wedge₁ wedge₂ deRham₁ deRham₂
    d₂ _ hd₂add hd₂leib hpsi₂1 hleib₁ hleib₂ hpsi₂_wedge hpsi₂_deRham hanti₂ hdd₂ hint₁
  have hsq₁₂ := hsqz₂ _ _ hint₁₂
  exact coneKilledNat07Q9_baseChange_trans p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi hpsi wedge wedge₁
    wedge₂ deRham deRham₁ deRham₂ d d₁ d₂ hd₁add hd₁leib hd₂add hd₂leib hpsi₁1 hpsi₂1 hpsi1 hleib
    hleib₁ hleib₂ hpsi₁_wedge hpsi₁_deRham hpsi₂_wedge hpsi₂_deRham hpsi_wedge hpsi_deRham nabla
    hsq hsq₁ hsq₁₂ hsq₂ (h₁ M nabla hint hsq hsq₁) (h₂ _ _ hint₁ hsq₁ hsq₁₂)

end PredicateTrans

/-! ### Invariance under isomorphisms of the data -/

/-- A type synonym for a module, carrying the module structure transported along a ring
isomorphism. -/
def TransportModule07Q9 (M : Type u) : Type u := M

/-- The additive group structure on `TransportModule07Q9 M` is that of `M`. -/
instance (M : Type u) [AddCommGroup M] : AddCommGroup (TransportModule07Q9 M) :=
  inferInstanceAs (AddCommGroup M)

/-- The module structure on `TransportModule07Q9 M` over `D₀` transported along a ring
isomorphism `e : D ≃ D₀`. -/
abbrev transportModuleInst07Q9 {D D₀ : Type u} [CommRing D] [CommRing D₀] (e : D ≃+* D₀)
    (M : Type u) [AddCommGroup M] [Module D M] : Module D₀ (TransportModule07Q9 M) :=
  Module.compHom M (e.symm : D₀ →+* D)

section TransportModule

variable {D D₀ : Type u} [CommRing D] [CommRing D₀] (e : D ≃+* D₀) (M : Type u) [AddCommGroup M]
  [Module D M]

/-- The identity `M → TransportModule07Q9 M`, semilinear over `e`. -/
def toTransportModule07Q9 :
    letI := transportModuleInst07Q9 e M
    M →ₛₗ[(e : D →+* D₀)] TransportModule07Q9 M :=
  letI := transportModuleInst07Q9 e M
  { toFun := fun m ↦ m
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun c m ↦ by
      change c • m = e.symm (e c) • m
      rw [RingEquiv.symm_apply_apply] }

/-- The identity `TransportModule07Q9 M → M`, semilinear over `e⁻¹`. -/
def fromTransportModule07Q9 :
    letI := transportModuleInst07Q9 e M
    TransportModule07Q9 M →ₛₗ[(e.symm : D₀ →+* D)] M :=
  letI := transportModuleInst07Q9 e M
  { toFun := fun m ↦ m
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

end TransportModule

section Invariance

variable (p : ℕ) {D : Type u} [CommRing D] {D' : Type u} [CommRing D'] [Algebra D D']
  {D₀ : Type u} [CommRing D₀] {D₀' : Type u} [CommRing D₀'] [Algebra D₀ D₀']
  (e : D ≃+* D₀) (e' : D' ≃+* D₀') (he : ∀ x, e' (algebraMap D D' x) = algebraMap D₀ D₀' (e x))
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om₀ : ℕ → Type u) [∀ i, AddCommGroup (Om₀ i)] [∀ i, Module D₀ (Om₀ i)]
  (Om₀' : ℕ → Type u) [∀ i, AddCommGroup (Om₀' i)] [∀ i, Module D₀' (Om₀' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i) (psi₀ : ∀ i, Om₀ i →ₛₗ[algebraMap D₀ D₀'] Om₀' i)
  (phi : ∀ i, Om i →ₛₗ[(e : D →+* D₀)] Om₀ i) (phiInv : ∀ i, Om₀ i →ₛₗ[(e.symm : D₀ →+* D)] Om i)
  (phi' : ∀ i, Om' i →ₛₗ[(e' : D' →+* D₀')] Om₀' i)
  (phi'Inv : ∀ i, Om₀' i →ₛₗ[(e'.symm : D₀' →+* D')] Om' i)
  (hphi₁ : ∀ i ω, phiInv i (phi i ω) = ω) (hphi₂ : ∀ i ω, phi i (phiInv i ω) = ω)
  (hphi'₁ : ∀ i ω, phi'Inv i (phi' i ω) = ω) (hphi'₂ : ∀ i ω, phi' i (phi'Inv i ω) = ω)
  (hcomm : ∀ i ω, phi' i (psi i ω) = psi₀ i (phi i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (wedge₀ : ∀ i, Om₀ i →ₗ[D₀] Om₀ 1 →ₗ[D₀] Om₀ (i + 1))
  (wedge₀' : ∀ i, Om₀' i →ₗ[D₀'] Om₀' 1 →ₗ[D₀'] Om₀' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (deRham₀ : ∀ i, Om₀ i →+ Om₀ (i + 1)) (deRham₀' : ∀ i, Om₀' i →+ Om₀' (i + 1))
  (d : D → Om 1) (d' : D' → Om' 1) (d₀ : D₀ → Om₀ 1) (d₀' : D₀' → Om₀' 1)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hd₀'add : ∀ x y : D₀', d₀' (x + y) = d₀' x + d₀' y)
  (hd₀'leib : ∀ x y : D₀', d₀' (x * y) = x • d₀' y + y • d₀' x)
  (hpsi₀1 : ∀ x : D₀, psi₀ 1 (d₀ x) = d₀' (algebraMap D₀ D₀' x))
  (hphid : ∀ x : D, phi 1 (d x) = d₀ (e x))
  (hphi'd : ∀ b : D', phi' 1 (d' b) = d₀' (e' b))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hleib₀ : IsGradedLeibniz D₀ Om₀ wedge₀ deRham₀ d₀)
  (hleib₀' : IsGradedLeibniz D₀' Om₀' wedge₀' deRham₀' d₀')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hpsi₀_wedge : ∀ (i : ℕ) (ω : Om₀ i) (η : Om₀ 1),
    psi₀ (i + 1) (wedge₀ i ω η) = wedge₀' i (psi₀ i ω) (psi₀ 1 η))
  (hpsi₀_deRham : ∀ (i : ℕ) (ω : Om₀ i), psi₀ (i + 1) (deRham₀ i ω) = deRham₀' i (psi₀ i ω))
  (hphi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    phi (i + 1) (wedge i ω η) = wedge₀ i (phi i ω) (phi 1 η))
  (hphi_deRham : ∀ (i : ℕ) (ω : Om i), phi (i + 1) (deRham i ω) = deRham₀ i (phi i ω))
  (hphi'_wedge : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1),
    phi' (i + 1) (wedge' i ω η) = wedge₀' i (phi' i ω) (phi' 1 η))
  (hphi'_deRham : ∀ (i : ℕ) (ω : Om' i), phi' (i + 1) (deRham' i ω) = deRham₀' i (phi' i ω))

include he hcomm hphi'd hphi₁ hphi₂ hphi'₁ hphi'₂ hphi_wedge hphi_deRham hphi'_wedge
  hphi'_deRham in
/-- **Invariance of the annihilation of the cone of a base change map under isomorphisms of the
data**: for isomorphic data `(D → D', M)` and `(D₀ → D₀', M₀)`, if `q` kills the cone of the
base change map of the second, it kills that of the first. -/
theorem coneKilledNat07Q9_baseChange_of_iso {M : Type u} [AddCommGroup M] [Module D M]
    {M₀ : Type u} [AddCommGroup M₀] [Module D₀ M₀] (mu : M →ₛₗ[(e : D →+* D₀)] M₀)
    (muInv : M₀ →ₛₗ[(e.symm : D₀ →+* D)] M) (hmu₁ : ∀ m, muInv (mu m) = m)
    (hmu₂ : ∀ m, mu (muInv m) = m) (nabla : CompletedConnection p D (Om 1) d M)
    (nabla₀ : CompletedConnection p D₀ (Om₀ 1) d₀ M₀)
    (hnabla : ∀ m, nabla₀ (mu m) = comparisonValues p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi 1
      (nabla m))
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham'
      (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib')
    (hsq₀ : IsSquareZero p D₀ Om₀ wedge₀ deRham₀ M₀ nabla₀ hleib₀)
    (hsq₀' : IsSquareZero p D₀' Om₀' wedge₀' deRham₀'
      (CompletedConnection.baseChangeCarrier p D₀ D₀' M₀)
      (CompletedConnection.baseChange p D₀ D₀' M₀ (Om₀ 1) (Om₀' 1) d₀' (psi₀ 1) nabla₀ hd₀'add
        hd₀'leib hpsi₀1) hleib₀') {q : ℤ}
    (h : ConeKilledNat07Q9 q (baseChangeComplexHom p D₀ D₀' M₀ Om₀ Om₀' psi₀ wedge₀ wedge₀'
      deRham₀ deRham₀' d₀' nabla₀ hd₀'add hd₀'leib hpsi₀1 hleib₀ hleib₀' hpsi₀_wedge
      hpsi₀_deRham hsq₀ hsq₀')) :
    ConeKilledNat07Q9 q (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d'
      nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') :=
  ConeKilledNat07Q9.of_arrowIso
    (baseChangeArrowIsoOfIso07Q9 p e e' he mu muInv hmu₁ hmu₂ Om Om' Om₀ Om₀' psi psi₀ phi phiInv
      phi' phi'Inv hphi₁ hphi₂ hphi'₁ hphi'₂ hcomm wedge wedge' wedge₀ wedge₀' deRham deRham'
      deRham₀ deRham₀' d' d₀' nabla nabla₀ hnabla hd'add hd'leib hpsi1 hd₀'add hd₀'leib hpsi₀1
      hphi'd hleib hleib' hleib₀ hleib₀' hpsi_wedge hpsi_deRham hpsi₀_wedge hpsi₀_deRham
      hphi_wedge hphi_deRham hphi'_wedge hphi'_deRham hsq hsq' hsq₀ hsq₀') h

include he hcomm hphid hphi'd hphi₁ hphi₂ hphi'₁ hphi'₂ hphi_wedge hphi_deRham hphi'_wedge
  hphi'_deRham in
/-- **Invariance of `BaseChangeConeKilled07Q9` under isomorphisms of the data**: a module over
`D` is transported to `D₀` along `e`, with the transported connection
(`Crystalline.CompletedDeRham.transportConnection`), and the cone of its base change map is
compared by `Crystalline.CompletedDeRham.coneKilledNat07Q9_baseChange_of_iso`. -/
theorem baseChangeConeKilled07Q9_of_iso {q : ℤ}
    (h : BaseChangeConeKilled07Q9 p D₀ D₀' Om₀ Om₀' psi₀ wedge₀ wedge₀' deRham₀ deRham₀' d₀ d₀'
      hd₀'add hd₀'leib hpsi₀1 hleib₀ hleib₀' hpsi₀_wedge hpsi₀_deRham q) :
    BaseChangeConeKilled07Q9 p D D' Om Om' psi wedge wedge' deRham deRham' d d' hd'add hd'leib
      hpsi1 hleib hleib' hpsi_wedge hpsi_deRham q := by
  intro M _ _ nabla hint hsq hsq'
  let := transportModuleInst07Q9 e M
  let mu := toTransportModule07Q9 e M
  let muInv := fromTransportModule07Q9 e M
  have hmu₁ : ∀ m, muInv (mu m) = m := fun _ ↦ rfl
  have hmu₂ : ∀ m, mu (muInv m) = m := fun _ ↦ rfl
  let nabla₀ := transportConnection p e mu muInv phi d d₀ nabla hmu₂ hphid
  have hnabla : ∀ m, nabla₀ (mu m) =
      comparisonValues p D D₀ (e : D →+* D₀) M _ mu Om Om₀ phi 1 (nabla m) := fun m ↦
    transportConnection_apply p e mu muInv phi d d₀ nabla hmu₁ hmu₂ hphid m
  have hint₀ : IsCurvatureZero p D₀ Om₀ wedge₀ deRham₀ _ nabla₀ hleib₀ := by
    intro m₀
    show differential p D₀ Om₀ wedge₀ deRham₀ _ nabla₀ hleib₀ 1 (nabla₀ (mu (muInv m₀))) = 0
    rw [hnabla, differential_comparisonValues p D D₀ (e : D →+* D₀) M _ mu Om Om₀ phi wedge wedge₀
      deRham deRham₀ nabla nabla₀ hleib hleib₀ hphi_wedge hphi_deRham hnabla 1, hint, map_zero]
  have hsq₀ := isSquareZero_comparison p e mu muInv phi phiInv hmu₂ hphi₂ wedge wedge₀ deRham
    deRham₀ nabla nabla₀ hleib hleib₀ hphi_wedge hphi_deRham hnabla hsq
  have hsq₀' := isSquareZero_comparison p e' (baseChangeCarrierMap07Q9 p e e' he mu)
    (baseChangeCarrierMap07Q9 p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv) phi' phi'Inv
    (baseChangeCarrierMap07Q9_symm_apply p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv mu
      hmu₂) hphi'₂ wedge' wedge₀' deRham' deRham₀' _
    (CompletedConnection.baseChange p D₀ D₀' _ (Om₀ 1) (Om₀' 1) d₀' (psi₀ 1) nabla₀ hd₀'add
      hd₀'leib hpsi₀1) hleib' hleib₀' hphi'_wedge hphi'_deRham
    (baseChangeCarrierMap07Q9_horizontal p e e' he mu Om Om' Om₀ Om₀' psi psi₀ phi phi' hcomm d'
      d₀' nabla nabla₀ hnabla hd'add hd'leib hpsi1 hd₀'add hd₀'leib hpsi₀1 hphi'd) hsq'
  exact coneKilledNat07Q9_baseChange_of_iso p e e' he Om Om' Om₀ Om₀' psi psi₀ phi phiInv phi'
    phi'Inv hphi₁ hphi₂ hphi'₁ hphi'₂ hcomm wedge wedge' wedge₀ wedge₀' deRham deRham' deRham₀
    deRham₀' d d' d₀ d₀' hd'add hd'leib hpsi1 hd₀'add hd₀'leib hpsi₀1 hphi'd hleib hleib' hleib₀
    hleib₀' hpsi_wedge hpsi_deRham hpsi₀_wedge hpsi₀_deRham hphi_wedge hphi_deRham hphi'_wedge
    hphi'_deRham mu muInv hmu₁ hmu₂ nabla nabla₀ hnabla hsq hsq' hsq₀ hsq₀'
    (h _ nabla₀ hint₀ hsq₀ hsq₀')

end Invariance

/-! ### The base change map along the identity -/

section Identity

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D] Om i) (hpsi : ∀ i ω, psi i ω = ω)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  (d : D → Om 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hdadd : ∀ x y : D, d (x + y) = d x + d y)
  (hdleib : ∀ x y : D, d (x * y) = x • d y + y • d x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d (algebraMap D D x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham i (psi i ω))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D Om wedge deRham (CompletedConnection.baseChangeCarrier p D D M)
    (CompletedConnection.baseChange p D D M (Om 1) (Om 1) d (psi 1) nabla hdadd hdleib hpsi1)
    hleib)

include hpsi in
/-- In each degree, the base change map along the identity of `D` is the inverse of the
cancellation `((D ⊗_D M)^∧ ⊗̂_D Ω) ≅ M ⊗̂_D Ω` of
`Crystalline.completedBaseChangeCancel`. -/
theorem baseChangeTerm_self_eq07Q9 (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    baseChangeTerm p D D M Om Om psi i x =
      (completedBaseChangeCancel p D D (Om i) M).symm x := by
  have h : baseChangeTerm p D D M Om Om psi i =
      (completedBaseChangeCancel p D D (Om i) M).symm.toAddMonoidHom := by
    refine completedTensor_addMonoidHom_ext p fun m ω ↦ ?_
    rw [baseChangeTerm_of_tmul, hpsi]
    exact (completedBaseChangeCancel_symm_of_tmul p D D (Om i) M m ω).symm
  exact DFunLike.congr_fun h x

include hpsi in
/-- **The base change map along the identity of `D` is an isomorphism of complexes**, for a
comparison of forms which is the identity. -/
theorem isIso_baseChangeComplexHom_self07Q9 :
    IsIso (baseChangeComplexHom p D D M Om Om psi wedge wedge deRham deRham d nabla hdadd hdleib
      hpsi1 hleib hleib hpsi_wedge hpsi_deRham hsq hsq') := by
  suffices h : ∀ i, IsIso ((baseChangeComplexHom p D D M Om Om psi wedge wedge deRham deRham d
      nabla hdadd hdleib hpsi1 hleib hleib hpsi_wedge hpsi_deRham hsq hsq').f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  refine ⟨AddCommGrpCat.ofHom (completedBaseChangeCancel p D D (Om i) M).toAddMonoidHom, ?_, ?_⟩
  · refine AddCommGrpCat.ext fun (x : CompletedTensor p D (Om i) M) ↦ ?_
    exact (congrArg (completedBaseChangeCancel p D D (Om i) M)
      (baseChangeTerm_self_eq07Q9 p D M Om psi hpsi i x)).trans (AddEquiv.apply_symm_apply _ x)
  · refine AddCommGrpCat.ext fun (x : CompletedTensor p D (Om i)
      (CompletedConnection.baseChangeCarrier p D D M)) ↦ ?_
    exact (baseChangeTerm_self_eq07Q9 p D M Om psi hpsi i _).trans
      (AddEquiv.symm_apply_apply _ x)

include hpsi in
/-- **Along the identity of `D` the cones of the base change maps are killed by `1`.** -/
theorem baseChangeConeKilled07Q9_self :
    BaseChangeConeKilled07Q9 p D D Om Om psi wedge wedge deRham deRham d d hdadd hdleib hpsi1
      hleib hleib hpsi_wedge hpsi_deRham 1 := by
  intro M _ _ nabla _ hsq hsq'
  have := isIso_baseChangeComplexHom_self07Q9 p D M Om psi hpsi wedge deRham d nabla hdadd
    hdleib hpsi1 hleib hpsi_wedge hpsi_deRham hsq hsq'
  exact ConeKilledNat07Q9.of_isIso

end Identity

/-! ### The genuine completed divided power forms -/

section Genuine

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J)

/-- The wedge `Ω^i × Ω² → Ω^{i+2}` of the completed divided power forms, read as `B`-bilinear,
in the variance of `Crystalline.dividedPowerWedgeTwo`. -/
def completedDividedPowerWedgeTwoOnRing07Q9 (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[B]
      completedDividedPowerForms p A hJ (1 + 1) →ₗ[B]
        completedDividedPowerForms p A hJ (i + 1 + 1) :=
  LinearMap.mk₂ B (fun x y ↦ completedDividedPowerWedgeTwo p A hJ i x y)
    (fun x x' y ↦ by rw [map_add, LinearMap.add_apply])
    (fun c x y ↦ by
      rw [← algebraMap_smul (completedDividedPowerRing p (B := B)) c x, LinearMap.map_smul,
        LinearMap.smul_apply,
        algebraMap_smul (completedDividedPowerRing p (B := B)) c
          (completedDividedPowerWedgeTwo p A hJ i x y)])
    (fun x y y' ↦ map_add _ y y')
    (fun c x y ↦ by
      rw [← algebraMap_smul (completedDividedPowerRing p (B := B)) c y, LinearMap.map_smul,
        algebraMap_smul (completedDividedPowerRing p (B := B)) c
          (completedDividedPowerWedgeTwo p A hJ i x y)])

/-- **Integrability makes the completed de Rham complex over `B` a complex**, for the genuine
completed divided power forms read over the ring `B` itself. -/
theorem isSquareZero_completedDividedPowerFormsOnRing07Q9 (N : Type u) [AddCommGroup N]
    [Module B N] (nabla : CompletedConnection p B (completedDividedPowerForms p A hJ 1)
      (completedDividedPowerDifferentialOnRing p A hJ) N)
    (hint : IsCurvatureZero p B (completedDividedPowerForms p A hJ)
      (completedDividedPowerWedgeOnRing p A hJ) (completedDividedPowerDeRham p A hJ) N nabla
      (isGradedLeibniz_completedDividedPowerOnRing p A hJ)) :
    IsSquareZero p B (completedDividedPowerForms p A hJ)
      (completedDividedPowerWedgeOnRing p A hJ) (completedDividedPowerDeRham p A hJ) N nabla
      (isGradedLeibniz_completedDividedPowerOnRing p A hJ) :=
  isSquareZero_of_hasIntegrableConnection p B _ _ _ N nabla _
    (completedDividedPowerWedgeTwoOnRing07Q9 p A hJ)
    (isGradedExterior_completedDividedPower p A hJ).deRham_deRham
    (completedDividedPowerWedge_completedDividedPowerWedge p A hJ)
    (completedDividedPowerDeRham_completedDividedPowerWedge p A hJ) hint

end Genuine

/-! ### The de Rham map of a morphism of cosimplicial pairs -/

end CompletedDeRham

/-- **Integrability passes to the base change along a morphism of cosimplicial divided power
algebras, and the base-changed de Rham complex is a complex**: for `(M, ∇)` over `D̂(b)` with an
integrable connection, the base change along `g : D̂(b) → D̂'(b)`, with the comparison of forms
of `g`, has square-zero de Rham differentials. -/
theorem CosimplicialDPAlgebra.Hom.isSquareZero_baseChange07Q9 {A : Type u} [CommRing A]
    {E E' : CosimplicialDPAlgebra.{u, u} A} (g : E.Hom E') (p b : ℕ) (M : Type u)
    [AddCommGroup M] [Module (E.completedRing p b) M]
    (nabla : CompletedConnection p (E.completedRing p b) (E.forms p 1 b) (E.differential p b) M)
    (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p b)
      (fun i ↦ E.forms p i b) (E.wedge p b)
      (E.deRham p b) M nabla (E.isGradedLeibniz p b)) :
    letI := (g.completedRingMap p b).toAlgebra
    CompletedDeRham.IsSquareZero p (E'.completedRing p b) (fun i ↦ E'.forms p i b) (E'.wedge p b)
      (E'.deRham p b)
      (CompletedConnection.baseChangeCarrier p (E.completedRing p b) (E'.completedRing p b) M)
      (CompletedConnection.baseChange p (E.completedRing p b) (E'.completedRing p b) M
        (E.forms p 1 b) (E'.forms p 1 b) (E'.differential p b) (g.formsMap p b 1) nabla
        (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
        (g.formsMap_differential07Q9 p b))
      (E'.isGradedLeibniz p b) := by
  let := (g.completedRingMap p b).toAlgebra
  exact isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection p A (E'.dividedPowers b)
    _ (CompletedDeRham.isCurvatureZero_baseChange p (E.completedRing p b) (E'.completedRing p b) M
      (fun i ↦ E.forms p i b) (fun i ↦ E'.forms p i b) (fun i ↦ g.formsMap p b i) (E.wedge p b)
      (E'.wedge p b) (E.deRham p b) (E'.deRham p b) (E'.differential p b) nabla
      (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
      (g.formsMap_differential07Q9 p b) (E.isGradedLeibniz p b) (E'.isGradedLeibniz p b)
      (fun i ω η ↦ g.formsMap_wedge p b i ω η) (fun i ω ↦ g.formsMap_deRham p b i ω)
      (fun η ζ ↦ completedDividedPowerWedgeOnRing_one_add_swap p A (E'.dividedPowers b) η ζ)
      (fun c ↦ deRham_completedFormsDifferential p A (E'.dividedPowers b) c) hint)

namespace CosimplicialCompletedPair.Hom

open CompletedDeRham

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  {g : E.Hom E'} {W : CosimplicialCompletedPair.{u, u, u} E p}
  {W' : CosimplicialCompletedPair.{u, u, u} E' p} (F : Hom g W W')

/-- **The de Rham map of a cosimplicial degree is a semilinear comparison**: the morphism
`Crystalline.CosimplicialCompletedPair.Hom.degreeDeRhamMap` of a morphism of cosimplicial pairs
is `Crystalline.CompletedDeRham.comparisonComplexHom07Q9` of its component `F.app b` and of the
comparison of forms of `g`. -/
theorem degreeDeRhamMap_eq_comparisonComplexHom07Q9 (b : ℕ) :
    F.degreeDeRhamMap b =
      comparisonComplexHom07Q9 p (E.completedRing p b) (E'.completedRing p b)
        (g.completedRingMap p b) (W.carrier b) (W'.carrier b) (F.app b) (fun i ↦ E.forms p i b)
        (fun i ↦ E'.forms p i b) (fun i ↦ g.formsMap p b i) (E.wedge p b) (E'.wedge p b)
        (E.deRham p b) (E'.deRham p b) (W.nabla b) (W'.nabla b) (E.isGradedLeibniz p b)
        (E'.isGradedLeibniz p b) (W.isSquareZero b) (W'.isSquareZero b)
        (fun i ω η ↦ g.formsMap_wedge p b i ω η) (fun i ω ↦ g.formsMap_deRham p b i ω)
        (F.nabla_app b) :=
  HomologicalComplex.hom_ext _ _ fun _ ↦ rfl

/-- **The de Rham map in degree `0` of a morphism of pairs whose component `M(0) → M'(0)` is a
completed base change is the base change map**, up to isomorphism of arrows: for the algebra
structure of `D̂(0) → D̂'(0)` given by `g`, if `F.app 0` exhibits `M'(0)` as
`(D̂'(0) ⊗_{D̂(0)} M(0))^∧`, then `F.degreeDeRhamMap 0` is isomorphic to the base change map
`Crystalline.CompletedDeRham.baseChangeComplexHom` along `g` with `ψ = g.formsMap`. -/
def degreeDeRhamMapArrowIso07Q9 [IsAdicComplete (pAdicIdeal (A := E'.completedRing p 0) p)
      (W'.carrier 0)]
    (hsq' : letI := (g.completedRingMap p 0).toAlgebra
      IsSquareZero p (E'.completedRing p 0) (fun i ↦ E'.forms p i 0) (E'.wedge p 0)
        (E'.deRham p 0)
        (CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E'.completedRing p 0)
          (W.carrier 0))
        (CompletedConnection.baseChange p (E.completedRing p 0) (E'.completedRing p 0)
          (W.carrier 0) (E.forms p 1 0) (E'.forms p 1 0) (E'.differential p 0)
          (g.formsMap p 0 1) (W.nabla 0) (completedFormsDifferential_add p A _)
          (completedFormsDifferential_mul p A _) (g.formsMap_differential07Q9 p 0))
        (E'.isGradedLeibniz p 0))
    (h : letI := (g.completedRingMap p 0).toAlgebra
      IsBaseChange07Q9 p (E.completedRing p 0) (E'.completedRing p 0) (W.carrier 0)
        (W'.carrier 0) (F.app 0)) :
    letI := (g.completedRingMap p 0).toAlgebra
    Arrow.mk (baseChangeComplexHom p (E.completedRing p 0) (E'.completedRing p 0) (W.carrier 0)
        (fun i ↦ E.forms p i 0) (fun i ↦ E'.forms p i 0) (fun i ↦ g.formsMap p 0 i) (E.wedge p 0)
        (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0) (E'.differential p 0) (W.nabla 0)
        (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
        (g.formsMap_differential07Q9 p 0) (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0)
        (fun i ω η ↦ g.formsMap_wedge p 0 i ω η) (fun i ω ↦ g.formsMap_deRham p 0 i ω)
        (W.isSquareZero 0) hsq') ≅
      Arrow.mk (F.degreeDeRhamMap 0) :=
  letI := (g.completedRingMap p 0).toAlgebra
  baseChangeArrowIso07Q9 p (E.completedRing p 0) (E'.completedRing p 0) (W.carrier 0)
      (W'.carrier 0) (F.app 0) (fun i ↦ E.forms p i 0) (fun i ↦ E'.forms p i 0)
      (fun i ↦ g.formsMap p 0 i) (E.wedge p 0) (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0)
      (E'.differential p 0) (W.nabla 0) (W'.nabla 0) (completedFormsDifferential_add p A _)
      (completedFormsDifferential_mul p A _) (g.formsMap_differential07Q9 p 0) (F.nabla_app 0)
      (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0) (fun i ω η ↦ g.formsMap_wedge p 0 i ω η)
      (fun i ω ↦ g.formsMap_deRham p 0 i ω) (W.isSquareZero 0) hsq' (W'.isSquareZero 0) h ≪≫
    eqToIso (by rw [degreeDeRhamMap_eq_comparisonComplexHom07Q9]; rfl)

end CosimplicialCompletedPair.Hom

namespace CompletedDeRham


/-! ### Completed forms of a ring and of its completion -/

section Bridge

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The comparison `Ω̂^i_B → Ω̂^i_{B̂}` of the completed forms of `B` with those of its
completion `B̂`**, the comparison of completed forms along the completion map. -/
abbrev completionFormsMap07Q9 (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₛₗ[(completionDPAlgHom (A := A) (B := B) p).toRingHom]
      completedDividedPowerForms p A (completedDividedPowers J hJ p hp).1 i :=
  completedMapDifferentialForms p A hJ (completedDividedPowers J hJ p hp).1
    (completionDPAlgHom (A := A) (B := B) p) (completionDPAlgHom_isDPMorphism (A := A) _ hJ p hp) i

/-- Two additive maps out of a `p`-adic completion into a `p`-adic completion agree pointwise as
soon as they agree on the image of the module. -/
private theorem adicCompletion_addMonoidHom_apply_eq_of_of (p : ℕ) {R : Type*} [CommRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {S : Type*} [CommRing S] {Y : Type*}
    [AddCommGroup Y] [Module S Y]
    {f g : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y}
    (h : ∀ t : X, f (AdicCompletion.of _ X t) = g (AdicCompletion.of _ X t))
    (c : AdicCompletion (pAdicIdeal (A := R) p) X) : f c = g c :=
  DFunLike.congr_fun (adicCompletion_addMonoidHom_ext_of_of p h) c

/-- **The comparison of the completed forms of `B` and of `B̂` is linear over `B̂`**, the forms
of `B` being a `B̂`-module as a completion and those of `B̂` as a `B̂`-module: both sides are
additive in the scalar, and agree on the image of `B`, where this is the semilinearity of the
comparison over the completion map. -/
theorem completionFormsMap07Q9_smul (i : ℕ) (c : completedDividedPowerRing p (B := B))
    (ω : completedDividedPowerForms p A hJ i) :
    completionFormsMap07Q9 p A hJ hp i (c • ω) = c • completionFormsMap07Q9 p A hJ hp i ω := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p
    (f := (completionFormsMap07Q9 p A hJ hp i).toAddMonoidHom.comp
      (LinearMap.toSpanSingleton (completedDividedPowerRing p (B := B)) _ ω).toAddMonoidHom)
    (g := (LinearMap.toSpanSingleton (completedDividedPowerRing p (B := B)) _
      (completionFormsMap07Q9 p A hJ hp i ω)).toAddMonoidHom) (fun b ↦ ?_) c
  · show completionFormsMap07Q9 p A hJ hp i (AdicCompletion.of (pAdicIdeal (A := B) p) B b • ω) =
      AdicCompletion.of (pAdicIdeal (A := B) p) B b • completionFormsMap07Q9 p A hJ hp i ω
    have hb : AdicCompletion.of (pAdicIdeal (A := B) p) B b • ω = b • ω := by
      have h1 : AdicCompletion.of (pAdicIdeal (A := B) p) B b =
          algebraMap B (completedDividedPowerRing p (B := B)) b :=
        (AdicCompletion.algebraMap_apply (S := B) (pAdicIdeal (A := B) p) b).symm
      rw [h1, algebraMap_smul]
    rw [hb, map_smulₛₗ]
    rfl

/-- **The comparison carries the universal differential of the completion to the universal
differential of `B̂` read over `B̂` itself**: both sides are additive and agree on the image of
`B`. -/
theorem completionFormsMap07Q9_differential (c : completedDividedPowerRing p (B := B)) :
    completionFormsMap07Q9 p A hJ hp 1 (completedFormsDifferential p A hJ c) =
      completedDividedPowerDifferentialOnRing p A (completedDividedPowers J hJ p hp).1 c := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p
    (f := AddMonoidHom.mk'
      (fun c ↦ completionFormsMap07Q9 p A hJ hp 1 (completedFormsDifferential p A hJ c))
      (fun c c' ↦ by rw [completedFormsDifferential_add, map_add]))
    (g := AddMonoidHom.mk' (fun c ↦ completedDividedPowerDifferentialOnRing p A
        (completedDividedPowers J hJ p hp).1 c)
      (fun c c' ↦ completedDividedPowerDifferentialOnRing_add p A _ c c'))
    (fun b ↦ ?_) c
  exact completedMapDifferentialForms_completedFormsDifferential_of p A hJ _ _ _ b

end Bridge

/-! ### Base change along a divided power morphism, with the genuine forms -/

/-- A semilinear map read as semilinear over a ring map with the same values. -/
def semilinearCast07Q9 {R S : Type*} [CommRing R] [CommRing S] {σ τ : R →+* S}
    (h : ∀ x, σ x = τ x) {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module S Q] (f : P →ₛₗ[σ] Q) : P →ₛₗ[τ] Q where
  toFun := f
  map_add' := map_add f
  map_smul' c x := by rw [map_smulₛₗ, h]

/-- The cast of a semilinear map has the same values. -/
@[simp] theorem semilinearCast07Q9_apply {R S : Type*} [CommRing R] [CommRing S] {σ τ : R →+* S}
    (h : ∀ x, σ x = τ x) {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module S Q] (f : P →ₛₗ[σ] Q) (x : P) : semilinearCast07Q9 h f x = f x :=
  rfl

section GenuinePredicate

variable (p : ℕ) (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (B' : Type u) [CommRing B'] [Algebra A B'] {J' : Ideal B'}
  (hJ' : DividedPowers J') [Algebra B B'] (f : B →ₐ[A] B') (hf : IsDPMorphism hJ hJ' f.toRingHom)
  (hfa : ∀ x, f.toRingHom x = algebraMap B B' x)

/-- **The comparison of the genuine completed forms along a divided power morphism `f : B → B'`
which is the structure map**, semilinear over the structure map. -/
abbrev genuineFormsMap07Q9 (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₛₗ[algebraMap B B'] completedDividedPowerForms p A hJ' i :=
  semilinearCast07Q9 hfa (completedMapDifferentialForms p A hJ hJ' f hf i)

/-- The comparison of genuine forms carries `d` to `d`. -/
theorem genuineFormsMap07Q9_differential (x : B) :
    genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa 1
        (completedDividedPowerDifferentialOnRing p A hJ x) =
      completedDividedPowerDifferentialOnRing p A hJ' (algebraMap B B' x) := by
  rw [← hfa]
  exact completedMapDifferentialForms_differentialOnRing p A hJ hJ' f hf x

/-- The comparison of genuine forms respects the wedge product. -/
theorem genuineFormsMap07Q9_wedge (i : ℕ) (ω : completedDividedPowerForms p A hJ i)
    (η : completedDividedPowerForms p A hJ 1) :
    genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa (i + 1)
        (completedDividedPowerWedgeOnRing p A hJ i ω η) =
      completedDividedPowerWedgeOnRing p A hJ' i (genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa i ω)
        (genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa 1 η) :=
  completedMapDifferentialForms_wedge p A hJ hJ' f hf i ω η

/-- The comparison of genuine forms commutes with the de Rham differential. -/
theorem genuineFormsMap07Q9_deRham (i : ℕ) (ω : completedDividedPowerForms p A hJ i) :
    genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa (i + 1) (completedDividedPowerDeRham p A hJ i ω) =
      completedDividedPowerDeRham p A hJ' i (genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa i ω) :=
  completedMapDifferentialForms_deRham p A hJ hJ' f hf i ω

/-- **`q` kills the cones of the base change maps along a divided power morphism `B → B'`, for
the genuine completed forms of `B` and `B'`** (the forms of each ring itself, read over that
ring): this is `Crystalline.CompletedDeRham.BaseChangeConeKilled07Q9` for the comparison of forms
`Crystalline.CompletedDeRham.genuineFormsMap07Q9`. -/
def GenuineBaseChangeConeKilled07Q9 (q : ℤ) : Prop :=
  BaseChangeConeKilled07Q9 p B B' (completedDividedPowerForms p A hJ)
    (completedDividedPowerForms p A hJ') (genuineFormsMap07Q9 p A B hJ B' hJ' f hf hfa)
    (completedDividedPowerWedgeOnRing p A hJ) (completedDividedPowerWedgeOnRing p A hJ')
    (completedDividedPowerDeRham p A hJ) (completedDividedPowerDeRham p A hJ')
    (completedDividedPowerDifferentialOnRing p A hJ)
    (completedDividedPowerDifferentialOnRing p A hJ')
    (completedDividedPowerDifferentialOnRing_add p A hJ')
    (completedDividedPowerDifferentialOnRing_mul p A hJ')
    (genuineFormsMap07Q9_differential p A B hJ B' hJ' f hf hfa)
    (isGradedLeibniz_completedDividedPowerOnRing p A hJ)
    (isGradedLeibniz_completedDividedPowerOnRing p A hJ')
    (genuineFormsMap07Q9_wedge p A B hJ B' hJ' f hf hfa)
    (genuineFormsMap07Q9_deRham p A B hJ B' hJ' f hf hfa) q

end GenuinePredicate

section GenuineTrans

variable (p : ℕ) (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (B₁ : Type u) [CommRing B₁] [Algebra A B₁] {J₁ : Ideal B₁}
  (hJ₁ : DividedPowers J₁) (B₂ : Type u) [CommRing B₂] [Algebra A B₂] {J₂ : Ideal B₂}
  (hJ₂ : DividedPowers J₂) [Algebra B B₁] [Algebra B₁ B₂] [Algebra B B₂] [IsScalarTower B B₁ B₂]
  (f₁ : B →ₐ[A] B₁) (hf₁ : IsDPMorphism hJ hJ₁ f₁.toRingHom)
  (hfa₁ : ∀ x, f₁.toRingHom x = algebraMap B B₁ x)
  (f₂ : B₁ →ₐ[A] B₂) (hf₂ : IsDPMorphism hJ₁ hJ₂ f₂.toRingHom)
  (hfa₂ : ∀ x, f₂.toRingHom x = algebraMap B₁ B₂ x)
  (f : B →ₐ[A] B₂) (hf : IsDPMorphism hJ hJ₂ f.toRingHom)
  (hfa : ∀ x, f.toRingHom x = algebraMap B B₂ x)

include hfa₁ hfa₂ hfa in
/-- The comparisons of genuine forms compose. -/
theorem genuineFormsMap07Q9_comp (i : ℕ) (ω : completedDividedPowerForms p A hJ i) :
    genuineFormsMap07Q9 p A B hJ B₂ hJ₂ f hf hfa i ω =
      genuineFormsMap07Q9 p A B₁ hJ₁ B₂ hJ₂ f₂ hf₂ hfa₂ i
        (genuineFormsMap07Q9 p A B hJ B₁ hJ₁ f₁ hf₁ hfa₁ i ω) := by
  have hcomp : f = f₂.comp f₁ := AlgHom.ext fun x ↦ by
    rw [AlgHom.comp_apply]
    show f.toRingHom x = f₂.toRingHom (f₁.toRingHom x)
    rw [hfa, hfa₁, hfa₂, ← IsScalarTower.algebraMap_apply]
  show completedMapDifferentialForms p A hJ hJ₂ f hf i ω =
    completedMapDifferentialForms p A hJ₁ hJ₂ f₂ hf₂ i
      (completedMapDifferentialForms p A hJ hJ₁ f₁ hf₁ i ω)
  rw [completedMapDifferentialForms_congr p A hJ hJ₂ hcomp hf (IsDPMorphism.comp hJ₂ hf₂ hf₁)]
  exact completedMapDifferentialForms_comp p A hJ hJ₁ f₁ hf₁ hJ₂ f₂ hf₂ _ i ω

include hfa₁ hfa₂ hfa in
/-- **Transitivity for the genuine forms**: killed by `a` along `B → B₁` and by `b` along
`B₁ → B₂` gives killed by `a * b` along `B → B₂`. -/
theorem genuineBaseChangeConeKilled07Q9_trans {a b : ℤ}
    (h₁ : GenuineBaseChangeConeKilled07Q9 p A B hJ B₁ hJ₁ f₁ hf₁ hfa₁ a)
    (h₂ : GenuineBaseChangeConeKilled07Q9 p A B₁ hJ₁ B₂ hJ₂ f₂ hf₂ hfa₂ b) :
    GenuineBaseChangeConeKilled07Q9 p A B hJ B₂ hJ₂ f hf hfa (a * b) :=
  baseChangeConeKilled07Q9_trans (p := p) (D := B) (D₁ := B₁) (D₂ := B₂)
    (hpsi := genuineFormsMap07Q9_comp p A B hJ B₁ hJ₁ B₂ hJ₂ f₁ hf₁ hfa₁ f₂ hf₂ hfa₂ f hf hfa)
    (hanti₁ := completedDividedPowerWedgeOnRing_one_add_swap p A hJ₁)
    (hdd₁ := completedDividedPowerDeRham_one_differentialOnRing p A hJ₁)
    (hsqz₁ := fun N _ _ nabla hint ↦
      isSquareZero_completedDividedPowerFormsOnRing07Q9 p A hJ₁ N nabla hint)
    (hanti₂ := completedDividedPowerWedgeOnRing_one_add_swap p A hJ₂)
    (hdd₂ := completedDividedPowerDeRham_one_differentialOnRing p A hJ₂)
    (hsqz₂ := fun N _ _ nabla hint ↦
      isSquareZero_completedDividedPowerFormsOnRing07Q9 p A hJ₂ N nabla hint)
    (hpsi1 := genuineFormsMap07Q9_differential p A B hJ B₂ hJ₂ f hf hfa)
    (hpsi_wedge := genuineFormsMap07Q9_wedge p A B hJ B₂ hJ₂ f hf hfa)
    (hpsi_deRham := genuineFormsMap07Q9_deRham p A B hJ B₂ hJ₂ f hf hfa)
    (h₁ := h₁) (h₂ := h₂)

end GenuineTrans

section GenuineSelf

variable (p : ℕ) (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (f : B →ₐ[A] B) (hf : IsDPMorphism hJ hJ f.toRingHom)
  (hfa : ∀ x, f.toRingHom x = algebraMap B B x)

include hfa in
/-- The comparison of genuine forms along a divided power endomorphism which is the identity is
the identity. -/
theorem genuineFormsMap07Q9_self (i : ℕ) (ω : completedDividedPowerForms p A hJ i) :
    genuineFormsMap07Q9 p A B hJ B hJ f hf hfa i ω = ω := by
  have hid : f = AlgHom.id A B := AlgHom.ext fun x ↦ hfa x
  show completedMapDifferentialForms p A hJ hJ f hf i ω = ω
  subst hid
  exact completedMapDifferentialForms_id p A hJ i hf ω

include hfa in
/-- **Along the identity, the cones are killed by `1`**, for the genuine forms. -/
theorem genuineBaseChangeConeKilled07Q9_self :
    GenuineBaseChangeConeKilled07Q9 p A B hJ B hJ f hf hfa 1 :=
  baseChangeConeKilled07Q9_self p B (completedDividedPowerForms p A hJ)
    (genuineFormsMap07Q9 p A B hJ B hJ f hf hfa) (genuineFormsMap07Q9_self p A B hJ f hf hfa)
    (completedDividedPowerWedgeOnRing p A hJ) (completedDividedPowerDeRham p A hJ)
    (completedDividedPowerDifferentialOnRing p A hJ)
    (completedDividedPowerDifferentialOnRing_add p A hJ)
    (completedDividedPowerDifferentialOnRing_mul p A hJ)
    (genuineFormsMap07Q9_differential p A B hJ B hJ f hf hfa)
    (isGradedLeibniz_completedDividedPowerOnRing p A hJ)
    (genuineFormsMap07Q9_wedge p A B hJ B hJ f hf hfa)
    (genuineFormsMap07Q9_deRham p A B hJ B hJ f hf hfa)

end GenuineSelf

/-! ### Homotopies of `ℕ`-indexed cochain complexes from degreewise data -/

section Degreewise

variable {C : Type*} [Category* C] [Preadditive C] {K L : CochainComplex C ℕ}

/-- **A homotopy of `ℕ`-indexed cochain complexes from degreewise maps** `h q : K^{q+1} → L^q`:
`f = d h + g` in degree `0` and `f = h d + d h + g` in positive degrees. -/
def homotopyOfDegreewise07Q9 (f g : K ⟶ L) (h : ∀ q, K.X (q + 1) ⟶ L.X q)
    (h0 : f.f 0 = K.d 0 1 ≫ h 0 + g.f 0)
    (hs : ∀ q, f.f (q + 1) =
      K.d (q + 1) (q + 1 + 1) ≫ h (q + 1) + h q ≫ L.d q (q + 1) + g.f (q + 1)) :
    _root_.Homotopy f g where
  hom i j := if hij : i = j + 1 then eqToHom (by rw [hij]) ≫ h j else 0
  zero i j hij := by
    rw [dif_neg]
    intro h'
    exact hij (by simp [h'])
  comm i := by
    rw [Homotopy.dNext_cochainComplex, dif_pos rfl, eqToHom_refl, Category.id_comp]
    cases i with
    | zero => rw [Homotopy.prevD_zero_cochainComplex, add_zero, h0]
    | succ q =>
      rw [Homotopy.prevD_succ_cochainComplex, dif_pos rfl, eqToHom_refl, Category.id_comp, hs]

/-- The degree `q + 1 ⟶ q` component of `Crystalline.CompletedDeRham.homotopyOfDegreewise07Q9`. -/
theorem homotopyOfDegreewise07Q9_hom (f g : K ⟶ L) (h : ∀ q, K.X (q + 1) ⟶ L.X q)
    (h0 : f.f 0 = K.d 0 1 ≫ h 0 + g.f 0)
    (hs : ∀ q, f.f (q + 1) =
      K.d (q + 1) (q + 1 + 1) ≫ h (q + 1) + h q ≫ L.d q (q + 1) + g.f (q + 1))
    (q : ℕ) : (homotopyOfDegreewise07Q9 f g h h0 hs).hom (q + 1) q = h q := by
  show (if hij : q + 1 = q + 1 then eqToHom (by rw [hij]) ≫ h q else 0) = h q
  rw [dif_pos rfl, eqToHom_refl, Category.id_comp]

end Degreewise

section DegreewiseCone

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℕ}

/-- **Annihilation of the cone from degreewise splitting data**: a morphism `c : K ⟶ L` of
`ℕ`-indexed cochain complexes, with a map of complexes `e` back given degreewise, `e ∘ c = a`,
and a degreewise homotopy `h` with `h d = a - c e` in degree `0`, `d h + h d = a - c e` in
positive degrees and `h ∘ c = 0`, has its cone annihilated by `a`. -/
theorem coneKilledNat07Q9_of_degreewise {a : ℤ} (c : K ⟶ L) (e : ∀ q, L.X q ⟶ K.X q)
    (he : ∀ q, e q ≫ K.d q (q + 1) = L.d q (q + 1) ≫ e (q + 1))
    (hce : ∀ q, c.f q ≫ e q = a • 𝟙 (K.X q)) (h : ∀ q, L.X (q + 1) ⟶ L.X q)
    (h0 : L.d 0 1 ≫ h 0 = a • 𝟙 (L.X 0) - e 0 ≫ c.f 0)
    (hs : ∀ q, L.d (q + 1) (q + 1 + 1) ≫ h (q + 1) + h q ≫ L.d q (q + 1) =
      a • 𝟙 (L.X (q + 1)) - e (q + 1) ≫ c.f (q + 1))
    (hch : ∀ q, c.f (q + 1) ≫ h q = 0) : ConeKilledNat07Q9 a c := by
  let E : L ⟶ K := cochainComplexHomOfDegreewise e he
  have hE : ∀ q, E.f q = e q := fun q ↦ rfl
  refine ConeKilledNat07Q9.of_homotopy E ?_ (homotopyOfDegreewise07Q9 (a • 𝟙 L) (E ≫ c) h
    ?_ ?_) ?_
  · ext q : 1
    rw [HomologicalComplex.comp_f, hE, hce, HomologicalComplex.zsmul_f_apply,
      HomologicalComplex.id_f]
  · rw [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      hE, h0, sub_add_cancel]
  · intro q
    rw [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      hE, hs, sub_add_cancel]
  · intro i j
    by_cases hij : i = j + 1
    · subst hij
      rw [homotopyOfDegreewise07Q9_hom, hch]
    · show c.f i ≫ (if hij' : i = j + 1 then _ else 0) = 0
      rw [dif_neg hij, comp_zero]

end DegreewiseCone

section BaseChangeData

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
    psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham'
    (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
      hpsi1) hleib')

/-- **The cone of the base change map is killed by `a` as soon as there are degreewise splitting
data up to `a`**: a map `e` back commuting with the differentials, with `e ∘ c = a`, and a
homotopy `h` with `h d = a - c e` in degree `0`, `d h + h d = a - c e` in positive degrees and
`h ∘ c = 0`, `c` being `Crystalline.CompletedDeRham.baseChangeTerm`.  This is the form of the
conclusion of [Stacks, Lemma 60.25.3, Tag 07N1]. -/
theorem coneKilledNat07Q9_baseChange_of_data (a : ℕ)
    (e : ∀ q, CompletedTensor p D' (Om' q) (CompletedConnection.baseChangeCarrier p D D' M) →+
      CompletedTensor p D (Om q) M)
    (h : ∀ q, CompletedTensor p D' (Om' (q + 1))
        (CompletedConnection.baseChangeCarrier p D D' M) →+
      CompletedTensor p D' (Om' q) (CompletedConnection.baseChangeCarrier p D D' M))
    (he : ∀ q y, e (q + 1) (differential p D' Om' wedge' deRham'
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hleib' q y) =
      differential p D Om wedge deRham M nabla hleib q (e q y))
    (hec : ∀ q x, e q (baseChangeTerm p D D' M Om Om' psi q x) = a • x)
    (h0 : ∀ y, h 0 (differential p D' Om' wedge' deRham'
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hleib' 0 y) =
      a • y - baseChangeTerm p D D' M Om Om' psi 0 (e 0 y))
    (hs : ∀ q y, differential p D' Om' wedge' deRham'
          (CompletedConnection.baseChangeCarrier p D D' M)
          (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
            hpsi1) hleib' q (h q y) +
        h (q + 1) (differential p D' Om' wedge' deRham'
          (CompletedConnection.baseChangeCarrier p D D' M)
          (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
            hpsi1) hleib' (q + 1) y) =
      a • y - baseChangeTerm p D D' M Om Om' psi (q + 1) (e (q + 1) y))
    (hhc : ∀ q x, h q (baseChangeTerm p D D' M Om Om' psi (q + 1) x) = 0) :
    ConeKilledNat07Q9 (a : ℤ) (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham
      deRham' d' nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') := by
  refine coneKilledNat07Q9_of_degreewise _ (fun q ↦ AddCommGrpCat.ofHom (e q)) (fun q ↦ ?_)
    (fun q ↦ ?_) (fun q ↦ AddCommGrpCat.ofHom (h q)) ?_ (fun q ↦ ?_) (fun q ↦ ?_)
  · rw [complex_d, complex_d]
    exact AddCommGrpCat.ext fun (y : CompletedTensor p D' (Om' q)
      (CompletedConnection.baseChangeCarrier p D D' M)) ↦ (he q y).symm
  · refine AddCommGrpCat.ext fun (x : CompletedTensor p D (Om q) M) ↦ ?_
    exact (hec q x).trans (natCast_zsmul _ _).symm
  · rw [complex_d]
    refine AddCommGrpCat.ext fun (y : CompletedTensor p D' (Om' 0)
      (CompletedConnection.baseChangeCarrier p D D' M)) ↦ ?_
    exact (h0 y).trans (by rw [natCast_zsmul]; rfl)
  · rw [complex_d, complex_d]
    refine AddCommGrpCat.ext fun (y : CompletedTensor p D' (Om' (q + 1))
      (CompletedConnection.baseChangeCarrier p D D' M)) ↦ ?_
    exact ((add_comm _ _).trans (hs q y)).trans (by rw [natCast_zsmul]; rfl)
  · exact AddCommGrpCat.ext fun (x : CompletedTensor p D (Om (q + 1)) M) ↦ hhc q x

end BaseChangeData

section Congr

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)

/-- **The base change map depends on the comparison of forms only through its values.** -/
theorem coneKilledNat07Q9_baseChange_congr (psi psi' : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
    (hpsi : ∀ i ω, psi i ω = psi' i ω) (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
    (hpsi1' : ∀ x : D, psi' 1 (d x) = d' (algebraMap D D' x))
    (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
      psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
    (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
      psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
    (hpsi_wedge' : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
      psi' (i + 1) (wedge i omega eta) = wedge' i (psi' i omega) (psi' 1 eta))
    (hpsi_deRham' : ∀ (i : ℕ) (omega : Om i),
      psi' (i + 1) (deRham i omega) = deRham' i (psi' i omega))
    (hsq' : IsSquareZero p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib')
    (hsq'' : IsSquareZero p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi' 1) nabla hd'add hd'leib
        hpsi1') hleib') {q : ℤ}
    (h : ConeKilledNat07Q9 q (baseChangeComplexHom p D D' M Om Om' psi' wedge wedge' deRham
      deRham' d' nabla hd'add hd'leib hpsi1' hleib hleib' hpsi_wedge' hpsi_deRham' hsq hsq'')) :
    ConeKilledNat07Q9 q (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d'
      nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') := by
  have : psi = psi' := funext fun i ↦ LinearMap.ext (hpsi i)
  subst this
  exact h

end Congr

section ComparisonCongr

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] (σ : D →+* D')
  (M : Type u) [AddCommGroup M] [Module D M] (N : Type u) [AddCommGroup N] [Module D' N]
  (mu : M →ₛₗ[σ] N)
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[σ] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} {d' : D' → Om' 1}
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))

/-- **A comparison of complexes depends on the connections only through their values.** -/
theorem coneKilledNat07Q9_comparison_congr
    (nabla₁ nabla₂ : CompletedConnection p D (Om 1) d M)
    (nabla₁' nabla₂' : CompletedConnection p D' (Om' 1) d' N)
    (h₁ : ∀ m, nabla₁ m = nabla₂ m) (h₂ : ∀ n, nabla₁' n = nabla₂' n)
    (hsq₁ : IsSquareZero p D Om wedge deRham M nabla₁ hleib)
    (hsq₂ : IsSquareZero p D Om wedge deRham M nabla₂ hleib)
    (hsq₁' : IsSquareZero p D' Om' wedge' deRham' N nabla₁' hleib')
    (hsq₂' : IsSquareZero p D' Om' wedge' deRham' N nabla₂' hleib')
    (hnabla₁ : ∀ m : M, nabla₁' (mu m) =
      comparisonValues p D D' σ M N mu Om Om' psi 1 (nabla₁ m))
    (hnabla₂ : ∀ m : M, nabla₂' (mu m) =
      comparisonValues p D D' σ M N mu Om Om' psi 1 (nabla₂ m)) {q : ℤ}
    (h : ConeKilledNat07Q9 q (comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge'
      deRham deRham' nabla₂ nabla₂' hleib hleib' hsq₂ hsq₂' hpsi_wedge hpsi_deRham hnabla₂)) :
    ConeKilledNat07Q9 q (comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge'
      deRham deRham' nabla₁ nabla₁' hleib hleib' hsq₁ hsq₁' hpsi_wedge hpsi_deRham hnabla₁) := by
  have e₁ : nabla₁ = nabla₂ := CompletedConnection.ext h₁
  have e₂ : nabla₁' = nabla₂' := CompletedConnection.ext h₂
  subst e₁ e₂
  exact h

end ComparisonCongr

end CompletedDeRham

end Crystalline

end
