module

public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointIndivisibility
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SeparableExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Separable closed points and `H^0(Spec Γ(X, 𝒪_X))`

Let `W` be data (D0)–(D3) satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilData`), let `X` be
a smooth projective scheme over `k` and `k' = Γ(X, 𝒪_X)`, a finite étale `k`-algebra. This file
proves the half (2) ⇒ (1) of Stacks 0FI0 and the injectivity of `H^*(Spec(k')) → H^*(X)`.

* For finitely many `k`-algebra maps `φⱼ : A → Lⱼ` from a finite étale `k`-algebra to finite
  separable field extensions, jointly injective, `c ↦ (Spec(φⱼ)^* c)ⱼ` is injective on
  `H^*(Spec A)` (`Stacks.WeilCohomology.WeilData.injective_pull_specMap_family`). This is the
  argument of Stacks 0FVS: `Spec(A) × Spec(E) = ∐_σ Spec(E)` for a Galois `E/k` splitting `A`
  (axiom (B)(a) and Stacks 0FHJ, `Stacks.WeilCohomology.WeilData.splitMap_bijective`), and every
  `σ : A → E` factors through some `φⱼ` up to an automorphism of `E`.
* There are finitely many closed points `x₁, …, x_r ∈ X` with residue fields separable over `k`
  whose images in `Spec(k')` are all of the image of `X` (Stacks 056U); then
  `k' → ∏ᵢ κ(xᵢ)` is injective, `X` being reduced.
* Hence `H^*(Spec(k')) → ∏ᵢ H^*(xᵢ)` is injective, and so is `H^*(Spec(k')) → H^*(X)`; and if
  `H^0(Spec(k')) → H^0(X)` is bijective, then `H^0(X) → ∏ᵢ H^0(xᵢ)` is injective.

## Main definitions

* `Stacks.WeilCohomology.WeilData.SeparablePointsDetectH0`: condition (1) of Stacks 0FI0.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.closedPointSpecHom`: `Spec κ(x) ⟶ x` for a closed
  point `x` with separable residue field.

## Main results

* `Stacks.WeilCohomology.WeilData.injective_pull_specMap_family`.
* `Stacks.WeilCohomology.WeilData.injective_pull_toSpecGlobalSections`: `H^*(Spec(k')) → H^*(X)`
  is injective.
* `Stacks.WeilCohomology.WeilData.separablePointsDetectH0_of_bijective`: (2) ⇒ (1) of 0FI0.

## References

* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

attribute [local instance] residueFieldAlgebra

/-! ### Separable closed points over the points of `Spec Γ(X, 𝒪_X)` -/

namespace SmoothProjectiveScheme

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- A smooth projective scheme over a field is reduced. -/
theorem isReduced_left : IsReduced X.obj.left := by
  have : GeometricallyReduced X.obj.hom := geometricallyReduced_of_smooth X.obj.hom
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.obj.hom

/-- **Separable closed points over every point of the image of `X ⟶ Spec Γ(X, 𝒪_X)`**: there are
finitely many closed points `x₁, …, x_r` of `X` with residue fields separable over `k` such that
every point of `X` has the same image in `Spec Γ(X, 𝒪_X)` as one of them. The fibres of
`X ⟶ Spec Γ(X, 𝒪_X)` are open, `Γ(X, 𝒪_X)` being finite over `k`, and closed points with
separable residue field are dense in `X` (Stacks 056U). -/
theorem exists_separablePoints_toSpecΓ :
    ∃ (r : ℕ) (x : Fin r → X.obj.left) (_ : ∀ i, IsClosed ({x i} : Set X.obj.left))
      (_ : ∀ i, HasSeparableResidueField k X.obj.hom (x i)),
      ∀ y : X.obj.left, ∃ i, X.obj.left.toSpecΓ (x i) = X.obj.left.toSpecΓ y := by
  have : IsArtinianRing (globalSections X) := IsArtinianRing.of_finite k _
  have hD := dense_closedPoints_with_finite_separable_residueField_of_smooth X.obj.hom
  have hpt : ∀ s : Set.range X.obj.left.toSpecΓ, ∃ x : X.obj.left,
      IsClosed ({x} : Set X.obj.left) ∧ HasSeparableResidueField k X.obj.hom x ∧
        X.obj.left.toSpecΓ x = s := by
    intro s
    obtain ⟨y, hy⟩ := s.2
    have hopen : IsOpen (X.obj.left.toSpecΓ ⁻¹' {s.1}) :=
      (isOpen_discrete _).preimage X.obj.left.toSpecΓ.continuous
    obtain ⟨x, hxy, hxc, -, hxs⟩ := hD.inter_open_nonempty _ hopen ⟨y, hy⟩
    exact ⟨x, mem_closedPoints_iff.mp hxc, hxs, hxy⟩
  choose x hxc hxs hxy using hpt
  have : Finite (Set.range X.obj.left.toSpecΓ) := Finite.Set.subset Set.univ (Set.subset_univ _)
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range X.obj.left.toSpecΓ)
  refine ⟨r, fun i ↦ x (e.symm i), fun i ↦ hxc _, fun i ↦ hxs _, fun y ↦ ⟨e ⟨_, y, rfl⟩, ?_⟩⟩
  simp only [Equiv.symm_apply_apply]
  exact hxy _

/-- If the images of the points `xᵢ` in `Spec Γ(X, 𝒪_X)` cover the image of `X`, the evaluations
`Γ(X, 𝒪_X) → κ(xᵢ)` are jointly injective: `X` is reduced, so a global function vanishing at
every point is zero. -/
theorem injective_Γevaluation_of_toSpecΓ {r : ℕ} (x : Fin r → X.obj.left)
    (hx : ∀ y : X.obj.left, ∃ i, X.obj.left.toSpecΓ (x i) = X.obj.left.toSpecΓ y) :
    Function.Injective fun a : globalSections X ↦ fun i ↦ X.obj.left.Γevaluation (x i) a := by
  have := isReduced_left X
  intro b b' hbb
  rw [← sub_eq_zero]
  set a := b - b'
  have ha : ∀ i, X.obj.left.Γevaluation (x i) a = 0 := fun i ↦ by
    simp only [a, map_sub, congrFun hbb i, sub_self]
  rw [← basicOpen_eq_bot_iff (X := X.obj.left) (U := ⊤) a]
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  obtain ⟨i, hi⟩ := hx y
  have hy' : X.obj.left.toSpecΓ y ∈ PrimeSpectrum.basicOpen a := by
    rwa [← Scheme.toSpecΓ_preimage_basicOpen] at hy
  have hxi : x i ∈ X.obj.left.basicOpen a := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    show X.obj.left.toSpecΓ (x i) ∈ PrimeSpectrum.basicOpen a
    rw [hi]
    exact hy'
  exact ((X.obj.left.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) (x i) trivial a).mpr hxi) (ha i)

variable {X} {x : X.obj.left} (hx : IsClosed ({x} : Set X.obj.left))
  (hsep : HasSeparableResidueField k X.obj.hom x)

include hx in
/-- The residue field at a closed point of `X` is a finite extension of `k`. -/
theorem finite_residueField : Module.Finite k (X.obj.left.residueField x) :=
  residueField_finite_of_closed_point k X.obj.hom x hx

/-- The `k`-algebra map `Γ(X, 𝒪_X) → κ(x)`, evaluation at `x`. -/
def evaluationAlgHom (x : X.obj.left) : globalSections X →ₐ[k] X.obj.left.residueField x :=
  { toRingHom := (X.obj.left.Γevaluation x).hom
    commutes' := fun _ ↦ rfl }

/-- **`Spec κ(x)`** for a closed point `x` with residue field separable over `k`, as the spectrum
of a finite separable extension of `k`. -/
abbrev closedPointSpec : (SmoothProjectiveScheme k).FullSubcategory :=
  @spec k _ (X.obj.left.residueField x) _ _ (finite_residueField hx)
    (@etale_of_isSeparable k _ (X.obj.left.residueField x) _ _ (finite_residueField hx) hsep)

/-- **The closed point `x` is `Spec κ(x)`**: the identity of `Spec κ(x)`, from the spectrum of the
finite separable extension `κ(x)/k` to the smooth projective scheme `closedPointObj hx hsep`. -/
def closedPointSpecHom : closedPointSpec hx hsep ⟶ closedPointObj hx hsep :=
  ObjectProperty.homMk (Over.homMk (𝟙 _)
    ((Category.id_comp _).trans (fromSpecResidueField_comp_hom x)))

/-- `Spec κ(x) ⟶ X ⟶ Spec Γ(X, 𝒪_X)` is `Spec` of evaluation at `x`. -/
theorem closedPointSpecHom_comp_toSpecGlobalSections_left :
    (closedPointSpecHom hx hsep ≫ closedPointHom hx hsep ≫ toSpecGlobalSections X).hom.left =
      Spec.map (CommRingCat.ofHom (evaluationAlgHom x).toRingHom) := by
  show 𝟙 _ ≫ X.obj.left.fromSpecResidueField x ≫ X.obj.left.toSpecΓ =
    Spec.map (CommRingCat.ofHom (X.obj.left.Γevaluation x).hom)
  rw [Category.id_comp, CommRingCat.ofHom_hom, Scheme.fromSpecResidueField,
    Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

end SmoothProjectiveScheme

/-- If `φⱼ : A → Lⱼ` are jointly injective `k`-algebra maps from a finite `k`-algebra to fields and
`ψⱼ : Lⱼ → E` embed them in a normal extension `E/k`, then every `θ : A → E` is `τ ∘ ψⱼ ∘ φⱼ` for
some `j` and some `k`-endomorphism `τ` of `E`: the kernel of `θ` is that of some `φⱼ`. -/
theorem exists_algHom_comp_eq_of_injective {K' : Type u} [CommRing K'] [Algebra k K']
    [Module.Finite k K'] {ι : Type u} [Finite ι] {L : ι → Type u} [∀ j, Field (L j)]
    [∀ j, Algebra k (L j)] (φ : ∀ j, K' →ₐ[k] L j)
    (hφ : Function.Injective fun a ↦ fun j ↦ φ j a) {E : Type u} [Field E] [Algebra k E]
    [Normal k E] (ψ : ∀ j, L j →ₐ[k] E) (θ : K' →ₐ[k] E) :
    ∃ j, ∃ τ : E →ₐ[k] E, τ.comp ((ψ j).comp (φ j)) = θ := by
  classical
  have : IsArtinianRing K' := isArtinian_of_tower k inferInstance
  have : Fintype ι := Fintype.ofFinite ι
  have hker : Finset.univ.inf (fun j ↦ RingHom.ker (φ j).toRingHom) ≤
      RingHom.ker θ.toRingHom := by
    intro a ha
    obtain rfl : a = 0 := hφ (funext fun j ↦ by
      simpa using Finset.inf_le (f := fun j ↦ RingHom.ker (φ j).toRingHom) (Finset.mem_univ j) ha)
    exact zero_mem _
  have : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp hker
  have : (RingHom.ker (φ j).toRingHom).IsPrime := RingHom.ker_isPrime _
  have : (RingHom.ker (φ j).toRingHom).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hkereq : RingHom.ker (φ j).toRingHom = RingHom.ker θ.toRingHom :=
    Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top _) hj
  let m := RingHom.ker (φ j).toRingHom
  let : Field (K' ⧸ m) := Ideal.Quotient.field m
  let α : K' ⧸ m →ₐ[k] E := (ψ j).comp (Ideal.Quotient.liftₐ m (φ j) fun a ha ↦ ha)
  let β : K' ⧸ m →ₐ[k] E := Ideal.Quotient.liftₐ m θ fun a ha ↦ by
    show a ∈ RingHom.ker θ.toRingHom
    rwa [← hkereq]
  let : Algebra (K' ⧸ m) E := α.toRingHom.toAlgebra
  have : IsScalarTower k (K' ⧸ m) E :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (α.commutes c).symm
  refine ⟨j, β.liftNormal E, ?_⟩
  ext a
  have h1 := β.liftNormal_commutes E (Ideal.Quotient.mk m a)
  have h2 : algebraMap (K' ⧸ m) E (Ideal.Quotient.mk m a) = ψ j (φ j a) := rfl
  rwa [h2, Algebra.algebraMap_self, RingHom.id_apply] at h1

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-! ### Pullback to finitely many separable points of `Spec A` -/

/-- **Pullback to finitely many separable points is jointly injective on `H^*(Spec(A))`.** Let `A`
be a finite étale `k`-algebra and `φⱼ : A → Lⱼ` finitely many `k`-algebra maps to finite separable
field extensions of `k`, jointly injective. Then `c ↦ (Spec(φⱼ)^* c)ⱼ` is injective on
`H^*(Spec(A))`. For `A ≠ 0`, choose a finite Galois `E/k` splitting `A` into which every `Lⱼ`
embeds. Then `Spec(A) × Spec(E) = ∐_σ Spec(E)` with coprojections `(Spec(σ), id)`, so by axiom
(B)(a) and Stacks 0FHJ `c ⊗ 1 ↦ (Spec(σ)^* c)_σ` is injective; and every `σ : A → E` is
`τ ∘ ψⱼ ∘ φⱼ` for some `j` and some automorphism `τ` of `E`, the kernel of `σ` being that of some
`φⱼ`. For `A = 0`, `Spec(A)` is empty and `H^*(∅) = 0` (Stacks 0FHF). -/
theorem injective_pull_specMap_family [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {K' : Type u} [CommRing K'] [Algebra k K']
    [Module.Finite k K'] [Algebra.Etale k K'] {ι : Type u} [Finite ι] {L : ι → Type u}
    [∀ j, Field (L j)] [∀ j, Algebra k (L j)] [∀ j, FiniteDimensional k (L j)]
    [∀ j, Algebra.IsSeparable k (L j)] (φ : ∀ j, K' →ₐ[k] L j)
    (hφ : Function.Injective fun a ↦ fun j ↦ φ j a) :
    Function.Injective fun c : W.H (spec k K') ↦ fun j ↦ W.pull (specMap (φ j)) c := by
  classical
  rcases subsingleton_or_nontrivial K' with hK' | hK'
  · have : IsEmpty (spec k K').obj.left := inferInstanceAs (IsEmpty (PrimeSpectrum K'))
    have := W.subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point
      (spec k K')
    exact fun a b _ ↦ Subsingleton.elim a b
  obtain ⟨E, _, _, _, _, ψ, hE⟩ := FirstChernClassData.exists_isGalois_embeddings (k := k) L
  have hX : topologicalKrullDim (spec k K').obj.left = 0 :=
    topologicalKrullDim_spec_eq_zero (k := k) K'
  have := finite_globalSections hX
  have := etale_globalSections hX
  have hsplit : ∀ a : globalSections (spec k K'),
      ((minpoly k a).map (algebraMap k E)).Splits := fun a ↦ by
    have hinj : Function.Injective
        (FirstChernClassData.globalSectionsSpecAlgHom (k := k) (K' := K')) :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K')).hom).1
    rw [← minpoly.algHom_eq _ hinj a, ← minpoly.algHom_eq (Pi.algHom k L φ) hφ]
    exact hE _
  have hbij := W.splitMap_bijective hX E hA hB hC hsplit
  let Φ : W.H (spec k K') →ₗ[F] (∀ j, W.H (spec k (L j))) :=
    LinearMap.pi fun j ↦ (W.pull (specMap (φ j))).toLinearMap
  show Function.Injective Φ
  rw [injective_iff_map_eq_zero]
  intro c hc0
  have hσ : ∀ σ, W.splitPull hX E σ c = 0 := by
    intro σ
    obtain ⟨θ, hθ⟩ := FirstChernClassData.exists_specMap_eq
      (specMap σ ≫ (isoSpecOfDimensionZero hX).inv)
    obtain ⟨j, τ, hτ⟩ := exists_algHom_comp_eq_of_injective φ hφ ψ θ
    have hcj : W.pull (specMap (φ j)) c = 0 := by simpa [Φ] using congrFun hc0 j
    show W.pull (specMap σ ≫ (isoSpecOfDimensionZero hX).inv) c = 0
    rw [← hθ, ← hτ, specMap_comp, specMap_comp, W.pull_comp, W.pull_comp, AlgHom.comp_apply,
      AlgHom.comp_apply, hcj, map_zero, map_zero]
  have hκ : W.splitMap hX E (c ⊗ₜ 1) = 0 := by
    rw [splitMap_tmul]
    funext σ
    rw [hσ σ, zero_mul]
    rfl
  have ht : c ⊗ₜ[F] (1 : W.H (spec k E)) = 0 := hbij.1 (by rw [hκ, map_zero])
  have := nontrivial_spec (L := E) hA hB hC
  exact FirstChernClassData.injective_tmul_right_of_ne_zero (F := F) one_ne_zero
    (ht.trans (TensorProduct.zero_tmul _ _).symm)

/-! ### Condition (1) of Stacks 0FI0 and the map `H^*(Spec Γ(X, 𝒪_X)) → H^*(X)` -/

variable (W) in
/-- **Condition (1) of Stacks 0FI0** for `X`: there are finitely many closed points
`x₁, …, x_r ∈ X` whose residue fields are separable over `k` such that
`H^0(X) → H^0(x₁) ⊕ … ⊕ H^0(x_r)` is injective. Here `H^0(xᵢ)` is the degree-zero cohomology of
the smooth projective `k`-scheme `Spec κ(xᵢ)` (`Stacks.WeilCohomology.closedPointObj`) and the
map is pullback along the inclusions `Spec κ(xᵢ) ⟶ X`. -/
def SeparablePointsDetectH0 (X : (SmoothProjectiveScheme k).FullSubcategory) : Prop :=
  ∃ (r : ℕ) (x : Fin r → X.obj.left) (hx : ∀ i, IsClosed ({x i} : Set X.obj.left))
    (hs : ∀ i, HasSeparableResidueField k X.obj.hom (x i)),
    Function.Injective fun a : W.grade X 0 ↦ fun i ↦ W.pullDeg (closedPointHom (hx i) (hs i)) 0 a

/-- **`H^*(Spec(k')) → ∏ᵢ H^*(xᵢ)` is injective** for closed points `xᵢ` with separable residue
fields whose images cover the image of `X` in `Spec(k')`, `k' = Γ(X, 𝒪_X)`: the composite
`Spec κ(xᵢ) ⟶ X ⟶ Spec(k')` is `Spec` of evaluation at `xᵢ`, and these evaluations are jointly
injective (`injective_pull_specMap_family`). -/
theorem injective_pull_closedPointHom_comp_toSpecGlobalSections [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {r : ℕ} (x : Fin r → X.obj.left)
    (hx : ∀ i, IsClosed ({x i} : Set X.obj.left))
    (hs : ∀ i, HasSeparableResidueField k X.obj.hom (x i))
    (hcov : ∀ y : X.obj.left, ∃ i, X.obj.left.toSpecΓ (x i) = X.obj.left.toSpecΓ y) :
    Function.Injective fun c : W.H (specGlobalSections X) ↦
      fun i ↦ W.pull (closedPointHom (hx i) (hs i)) (W.pull (toSpecGlobalSections X) c) := by
  let L : ULift.{u} (Fin r) → Type u := fun j ↦ X.obj.left.residueField (x j.down)
  have : ∀ j, FiniteDimensional k (L j) := fun j ↦ finite_residueField (hx j.down)
  have : ∀ j, Algebra.IsSeparable k (L j) := fun j ↦ hs j.down
  have hZ := W.injective_pull_specMap_family hA hB hC (L := L)
    (fun j ↦ evaluationAlgHom (x j.down))
    (fun a b hab ↦ injective_Γevaluation_of_toSpecΓ X x hcov (funext fun i ↦ congrFun hab ⟨i⟩))
  intro c c' hcc
  apply hZ
  funext j
  have e : closedPointSpecHom (hx j.down) (hs j.down) ≫ closedPointHom (hx j.down) (hs j.down) ≫
      toSpecGlobalSections X = specMap (evaluationAlgHom (x j.down)) :=
    hom_ext_left (closedPointSpecHom_comp_toSpecGlobalSections_left (hx j.down) (hs j.down))
  dsimp only
  rw [← e, W.pull_comp, W.pull_comp, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.comp_apply]
  exact congrArg _ (congrFun hcc j.down)

/-- **`H^*(Spec(k')) → H^*(X)` is injective**, `k' = Γ(X, 𝒪_X)`. -/
theorem injective_pull_toSpecGlobalSections [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Function.Injective (W.pull (toSpecGlobalSections X)) := by
  obtain ⟨r, x, hx, hs, hcov⟩ := exists_separablePoints_toSpecΓ X
  exact fun c c' h ↦ W.injective_pull_closedPointHom_comp_toSpecGlobalSections hA hB hC x hx hs
    hcov (funext fun i ↦ by simp only [h])

/-- **(2) ⇒ (1) of Stacks 0FI0.** If `H^0(Spec(k')) → H^0(X)` is an isomorphism,
`k' = Γ(X, 𝒪_X)`, then for closed points `x₁, …, x_r` with separable residue fields lying over
all of the image of `X` in `Spec(k')` (Stacks 056U) the map `H^0(X) → ⊕ᵢ H^0(xᵢ)` is injective:
composed with the isomorphism it is the injective map
`H^0(Spec(k')) → ⊕ᵢ H^0(xᵢ)` of `injective_pull_closedPointHom_comp_toSpecGlobalSections`. -/
theorem separablePointsDetectH0_of_bijective [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (h : Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0)) :
    W.SeparablePointsDetectH0 X := by
  obtain ⟨r, x, hx, hs, hcov⟩ := exists_separablePoints_toSpecΓ X
  refine ⟨r, x, hx, hs, fun a a' haa ↦ ?_⟩
  obtain ⟨b, rfl⟩ := h.2 a
  obtain ⟨b', rfl⟩ := h.2 a'
  congr 1
  exact Subtype.ext <| W.injective_pull_closedPointHom_comp_toSpecGlobalSections hA hB hC x hx hs
    hcov <| funext fun i ↦ congrArg Subtype.val (congrFun haa i)

end WeilData

end Stacks.WeilCohomology

end
