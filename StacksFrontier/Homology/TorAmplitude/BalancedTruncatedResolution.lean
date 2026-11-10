module

public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.TotalDegeneration
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor
public import StacksFrontier.Homology.Perfect.BalancedTensorFree
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Truncated free resolutions and the balanced tensor product

Let `Λ` be a ring, not assumed commutative. Tensoring a complex `R` of right `Λ`-modules with a
complex `E` of left `Λ`-modules gives the total complex `Tot(R ⊗_Λ E)` of the balanced tensor
bifunctor `StacksDraft.Perfect.balancedTensorFunctor`, whose term in bidegree `(q, p)` is
`Rᑫ ⊗_Λ Eᵖ`. A *truncated finite free resolution of length `m`* is a complex of finite free right
modules concentrated in degrees `[-m, 0]` and exact strictly between `-m` and `0`; it resolves its
`H⁰` up to the syzygy `H^{-m}`.

This file proves two facts about such resolutions. Tensoring one with a bounded complex `C` of
projective left modules concentrated in `[a, b]` has no cohomology strictly between `b - m` and
`a`. Conversely, over a finite ring, if `H^{a-1}(Tot(R ⊗_Λ E))` vanishes for every truncated free
resolution `R` of length at least `b - a + 2`, where `E` is a complex of finite projective left
modules vanishing above `b`, then the cokernel of `d^{a-1} : E^{a-1} → E^a` is projective.

## Main definitions

* `StacksDraft.TorAmplitude.IsTruncatedFreeResolution`: a truncated finite free resolution of
  length `m`.

## Main results

* `StacksDraft.TorAmplitude.kFlat_balancedTensor_of_projective`: a bounded above complex of
  projective left modules is K-flat for the balanced tensor product.
* `StacksDraft.TorAmplitude.isZero_homology_mapBifunctor_of_projective`: for `R` a truncated free
  resolution of length `m` and `C` a complex of projective left modules in degrees `[a, b]`,
  `Hᵖ(Tot(R ⊗_Λ C)) = 0` for `b - m < p < a`.
* `StacksDraft.TorAmplitude.projective_cokernel_of_balancedTensor_exact`: over a finite ring, a
  complex `X₁ → X₂ → X₃` of finite projective left modules which stays exact in the middle after
  tensoring with every finite right module has projective cokernel `X₃ / X₂`.
* `StacksDraft.TorAmplitude.projective_cokernel_of_isZero_homology_mapBifunctor`: over a finite
  ring, the vanishing of `H^{a-1}(Tot(R ⊗_Λ E))` for all truncated free resolutions `R` of length
  at least `b - a + 2` makes `coker(d^{a-1})` projective.

## Implementation notes

Both theorems run on one long exact sequence. A short exact sequence `0 → R₁ → R₂ → R₃ → 0` of
complexes of right modules gives, after tensoring with a K-flat complex `E`, the vanishing of
`Hⁿ(Tot(R₂ ⊗ E))` from that of `Hⁿ(Tot(R₁ ⊗ E))` and `Hⁿ(Tot(R₃ ⊗ E))`
(`isZero_homology_mapBifunctor_X₂`): the mapping cone of `Tot(R₁ ⊗ E) → Tot(R₂ ⊗ E)` is
`Tot(cone ⊗ E)` by `Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR`, and the
cone is quasi-isomorphic to `R₃`, a quasi-isomorphism which K-flatness of `E` preserves
(`CochainComplex.KFlatBifunctor.quasiIso_of_kFlat`). K-flatness of a bounded above complex of
projectives is the engine `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE`, whose base case is
the exactness of `- ⊗_Λ M` for a projective `M`; that exactness is proved with the coordinates
`N ⊗_Λ M → (M →₀ N)` of a splitting of `(M →₀ Λ) → M` (`balancedTensorCoord`).

For the vanishing theorem the sequence is the canonical truncation `τ^{≤ -m}R → R → R'`, whose
third term has cohomology only in degree `0`. For the projectivity theorem a finite right module
`N` is resolved by a complex `K` of finite free modules (`exists_finiteFree_resolution_of_finite`,
from Stacks 066E over the Noetherian ring `Λᵐᵒᵖ`), the sequence is `σ^{≥ -m}K → K → K / σ^{≥ -m}K`,
and the brutal truncation `σ^{≥ -m}K` is a truncated free resolution of length `m`; so the
hypothesis gives `H^{a-1}(N ⊗_Λ E) = 0`. The cokernel is then split off by hand from that
exactness, applied to the single module `N = X^∨ / g^∨(Y^∨)`, as in the proof of Stacks 03TO.

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 03TO](https://stacks.math.columbia.edu/tag/03TO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u v

open StacksDraft.Perfect

attribute [instance] balancedTensorFunctor_additive

variable {Λ : Type} [Ring Λ]

/-! ### Coordinates on a tensor product with a projective module -/

section Coordinates

variable {X : ModuleCat.{v} Λ} (s : X →ₗ[Λ] X →₀ Λ)

/-- Two additive maps out of `N ⊗_Λ X` which agree on pure tensors are equal. -/
theorem balancedTensor_addHom_ext {N : ModuleCat.{v} Λᵐᵒᵖ} {Q : Type*} [AddCommGroup Q]
    {g g' : balancedTensorObject Λ N X →+ Q}
    (h : ∀ (n : N) (x : X), g (balancedTensorPure Λ N X n x) =
      g' (balancedTensorPure Λ N X n x)) : g = g' := by
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  have := StacksDraft.BalancedTensorProduct.hom_ext ℤ Λ N X (intLinearMapOfAddHom g)
    (intLinearMapOfAddHom g') h
  ext t
  exact LinearMap.congr_fun this t

/-- The biadditive map `(n, x) ↦ (k ↦ n · s(x)ₖ)` underlying the coordinates. -/
def balancedTensorCoordBiadd (N : ModuleCat.{v} Λᵐᵒᵖ) :
    (N : Type v) →+ (X : Type v) →+ (X →₀ N) where
  toFun n :=
    { toFun := fun x => (s x).mapRange (fun a => MulOpposite.op a • n) (by simp)
      map_zero' := by ext; simp
      map_add' := fun x x' => by ext; simp [add_smul] }
  map_zero' := by ext; simp
  map_add' n n' := by ext; simp [smul_add]

/-- The coordinates `N ⊗_Λ X → (X →₀ N)` attached to `s`, sending `n ⊗ x` to
`k ↦ n · s(x)ₖ`. -/
def balancedTensorCoord (N : ModuleCat.{v} Λᵐᵒᵖ) : balancedTensorObject Λ N X →+ (X →₀ N) :=
  letI : Module ℤ (X →₀ N) := AddCommGroup.toIntModule _
  (StacksDraft.BalancedTensorProduct.liftBiadditive (A := Λ) (balancedTensorCoordBiadd s N)
    (fun z n x => addHom_map_int_smul _
      ((AddMonoidHom.eval x).comp (balancedTensorCoordBiadd s N)) z n)
    (fun z n x => addHom_map_int_smul _ (balancedTensorCoordBiadd s N n) z x)
    (fun n a x => by ext k; simp [balancedTensorCoordBiadd, mul_smul])).toAddMonoidHom

/-- The coordinates of a pure tensor `n ⊗ x`. -/
theorem balancedTensorCoord_pure_eq (N : ModuleCat.{v} Λᵐᵒᵖ) (n : N) (x : X) :
    balancedTensorCoord s N (balancedTensorPure Λ N X n x) =
      (s x).mapRange (fun a => MulOpposite.op a • n) (by simp) :=
  rfl

/-- The `k`-th coordinate of a pure tensor `n ⊗ x` is `n · s(x)ₖ`. -/
theorem balancedTensorCoord_pure (N : ModuleCat.{v} Λᵐᵒᵖ) (n : N) (x : X) (k : X) :
    balancedTensorCoord s N (balancedTensorPure Λ N X n x) k = MulOpposite.op (s x k) • n :=
  rfl

/-- Recombining coordinates: `(k ↦ nₖ) ↦ ∑ₖ nₖ ⊗ k`. -/
def balancedTensorRecomb (N : ModuleCat.{v} Λᵐᵒᵖ) : (X →₀ N) →+ balancedTensorObject Λ N X :=
  Finsupp.liftAddHom fun k =>
    AddMonoidHom.mk' (fun n => balancedTensorPure Λ N X n k) (fun n n' => by simp)

/-- Recombination sends `k ↦ n` to the pure tensor `n ⊗ k`. -/
theorem balancedTensorRecomb_single (N : ModuleCat.{v} Λᵐᵒᵖ) (k : X) (n : N) :
    balancedTensorRecomb N (Finsupp.single k n) = balancedTensorPure Λ N X n k := by
  simp [balancedTensorRecomb]

/-- Recombining the coordinates attached to a splitting `s` of `(X →₀ Λ) → X` gives back the
tensor. -/
theorem balancedTensorRecomb_balancedTensorCoord
    (hs : Finsupp.linearCombination Λ id ∘ₗ s = .id) (N : ModuleCat.{v} Λᵐᵒᵖ)
    (t : balancedTensorObject Λ N X) :
    balancedTensorRecomb N (balancedTensorCoord s N t) = t := by
  suffices h : (balancedTensorRecomb N).comp (balancedTensorCoord s N) = AddMonoidHom.id _ from
    DFunLike.congr_fun h t
  refine balancedTensor_addHom_ext fun n x => ?_
  rw [AddMonoidHom.comp_apply, balancedTensorCoord_pure_eq, balancedTensorRecomb,
    Finsupp.liftAddHom_apply, Finsupp.sum_mapRange_index (by simp)]
  simp only [AddMonoidHom.mk'_apply, AddMonoidHom.id_apply]
  simp_rw [balancedTensorPure_balanced]
  rw [← map_finsuppSum]
  congr 1
  simpa [Finsupp.linearCombination_apply] using LinearMap.congr_fun hs x

/-- The coordinates are natural in the right module. -/
theorem balancedTensorCoord_natural {N N' : ModuleCat.{v} Λᵐᵒᵖ} (φ : N ⟶ N')
    (t : balancedTensorObject Λ N X) :
    balancedTensorCoord s N' (balancedTensorMap Λ φ (𝟙 X) t) =
      (balancedTensorCoord s N t).mapRange φ.hom (map_zero φ.hom) := by
  suffices h :
      (balancedTensorCoord s N').comp (balancedTensorMap Λ φ (𝟙 X)).hom.toAddMonoidHom =
        (Finsupp.mapRange.addMonoidHom φ.hom.toAddMonoidHom).comp (balancedTensorCoord s N) from
    DFunLike.congr_fun h t
  refine balancedTensor_addHom_ext fun n x => ?_
  ext k
  simp [balancedTensorMap_pure, balancedTensorCoord_pure]

/-- Recombination is natural in the right module. -/
theorem balancedTensorRecomb_natural {N N' : ModuleCat.{v} Λᵐᵒᵖ} (φ : N ⟶ N') (u : X →₀ N) :
    balancedTensorRecomb N' (u.mapRange φ.hom (map_zero φ.hom)) =
      balancedTensorMap Λ φ (𝟙 X) (balancedTensorRecomb N u) := by
  suffices h :
      (balancedTensorRecomb N').comp (Finsupp.mapRange.addMonoidHom φ.hom.toAddMonoidHom) =
        (balancedTensorMap Λ φ (𝟙 X)).hom.toAddMonoidHom.comp (balancedTensorRecomb N) from
    DFunLike.congr_fun h u
  refine Finsupp.addHom_ext fun k n => ?_
  simp [balancedTensorRecomb_single, balancedTensorMap_pure]

/-- The coordinates of a finite sum of pure tensors. -/
theorem balancedTensorCoord_sum_pure {ι : Type*} (I : Finset ι) (N : ModuleCat.{v} Λᵐᵒᵖ)
    (n : ι → N) (x : ι → X) (k : X) :
    balancedTensorCoord s N (∑ i ∈ I, balancedTensorPure Λ N X (n i) (x i)) k =
      ∑ i ∈ I, MulOpposite.op (s (x i) k) • n i := by
  simp [map_sum, Finsupp.finsetSum_apply, balancedTensorCoord_pure]

/-- Functoriality of the balanced tensor product on a finite sum of pure tensors. -/
theorem balancedTensorMap_sum_pure {ι : Type*} (I : Finset ι) {N N' : ModuleCat.{v} Λᵐᵒᵖ}
    (φ : N ⟶ N') {Y : ModuleCat.{v} Λ} (ψ : X ⟶ Y) (n : ι → N) (x : ι → X) :
    balancedTensorMap Λ φ ψ (∑ i ∈ I, balancedTensorPure Λ N X (n i) (x i)) =
      ∑ i ∈ I, balancedTensorPure Λ N' Y (φ (n i)) (ψ (x i)) := by
  simp [map_sum, balancedTensorMap_pure]

/-- Over a finite set of coordinates, recombination is a finite sum of pure tensors. -/
theorem balancedTensorRecomb_eq_sum [Fintype X] (N : ModuleCat.{v} Λᵐᵒᵖ) (u : X →₀ N) :
    balancedTensorRecomb N u = ∑ k, balancedTensorPure Λ N X (u k) k := by
  rw [balancedTensorRecomb, Finsupp.liftAddHom_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

end Coordinates

/-! ### Tensoring with a projective module is exact -/

/-- Tensoring with a projective left module preserves exactness in each degree. -/
theorem exactAt_rowComplex_of_projective (M : ModuleCat.{v} Λ) [Module.Projective Λ M]
    (G : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ) (p : ℤ) (hG : G.ExactAt p) :
    (CochainComplex.KFlatBifunctor.rowComplex (balancedTensorFunctor Λ) G M).ExactAt p := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective Λ M)
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hG ⊢
  intro t ht
  change balancedTensorMap Λ (G.d p (p + 1)) (𝟙 M) t = 0 at ht
  set u := balancedTensorCoord s (G.X p) t with hu
  have hu0 (k : M) : G.d p (p + 1) (u k) = 0 := by
    simpa [ht] using
      (congrArg (fun w => w k) (balancedTensorCoord_natural s (G.d p (p + 1)) t)).symm
  choose w hw using fun k => hG (u k) (hu0 k)
  classical
  let w' : M →₀ G.X (p - 1) :=
    Finsupp.onFinset u.support (fun k => if u k = 0 then 0 else w k) (fun k hk => by
      by_contra h
      exact hk (by simp [Finsupp.notMem_support_iff.1 h]))
  have hw' : w'.mapRange (G.d (p - 1) p).hom (map_zero _) = u := by
    ext k
    by_cases hk : u k = 0
    · simp [w', hk]
    · simp only [Finsupp.mapRange_apply, Finsupp.onFinset_apply, hk, w']
      exact hw k
  refine ⟨balancedTensorRecomb (G.X (p - 1)) w', ?_⟩
  change balancedTensorMap Λ (G.d (p - 1) p) (𝟙 M) (balancedTensorRecomb (G.X (p - 1)) w') = t
  rw [← balancedTensorRecomb_natural, hw', hu]
  exact balancedTensorRecomb_balancedTensorCoord s hs _ t

/-- Sequential colimits are exact in abelian groups, read as `ℤ`-modules. -/
theorem hasExactColimitsOfShape_nat_moduleCatInt :
    HasExactColimitsOfShape ℕ (ModuleCat.{v} ℤ) := by
  let : AB5OfSize.{0, 0, v, v + 1} AddCommGrpCat.{v} :=
    AB5OfSize_of_univLE.{0, 0, v, v} AddCommGrpCat.{v}
  exact HasExactColimitsOfShape.domain_of_functor ℕ (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})

/-- **A bounded above complex of projective left modules is K-flat for the balanced tensor
product**: tensoring it with an acyclic complex of right modules gives an acyclic total
complex. -/
theorem kFlat_balancedTensor_of_projective (E : CochainComplex (ModuleCat.{v} Λ) ℤ) (b : ℤ)
    [E.IsStrictlyLE b] (hE : ∀ n, Module.Projective Λ (E.X n)) :
    CochainComplex.KFlatBifunctor.KFlat (balancedTensorFunctor Λ) E := by
  have := hasExactColimitsOfShape_nat_moduleCatInt.{v}
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ E b (fun N => ?_)
    (fun D s hs hD n => (CochainComplex.KFlat.acyclic_colimit D hD n).of_iso
      ((colimit.isColimit D).coconePointUniqueUpToIso hs)) (fun q => ?_)
  · have := preservesColimits_balancedTensorFunctor_obj Λ N
    have := preservesColimitsOfSize_shrink.{0, v, 0, v} ((balancedTensorFunctor Λ).obj N)
    infer_instance
  · have := hE q
    exact CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ (E.X q) q
      (fun G hG p => exactAt_rowComplex_of_projective (E.X q) G p (hG p))

/-! ### Homological algebra of the total complex -/

section Homological

variable {D : Type*} [Category D] [Abelian D]

/-- A quasi-isomorphism preserves and reflects the vanishing of homology. -/
theorem isZero_homology_iff_of_quasiIso {K L : CochainComplex D ℤ} (f : K ⟶ L) [QuasiIso f]
    (n : ℤ) : IsZero (K.homology n) ↔ IsZero (L.homology n) := by
  have : IsIso (HomologicalComplex.homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).1 inferInstance
  exact (asIso (HomologicalComplex.homologyMap f n)).isZero_iff

/-- The middle of the long exact sequence of a mapping cone: if `Hⁿ(X)` and `Hⁿ(cone f)`
vanish, so does `Hⁿ(Y)`. -/
theorem isZero_homology_of_mappingCone {X Y : CochainComplex D ℤ} (f : X ⟶ Y) (n : ℤ)
    (h₁ : IsZero (X.homology n)) (h₃ : IsZero ((CochainComplex.mappingCone f).homology n)) :
    IsZero (Y.homology n) := by
  have ex := (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n).map_distinguished_exact _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
  have e := HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n
  have h₁' := h₁.of_iso (e.app X)
  have h₃' := h₃.of_iso (e.app (CochainComplex.mappingCone f))
  exact (ex.isZero_X₂ (h₁'.eq_of_src _ _) (h₃'.eq_of_tgt _ _)).of_iso (e.app Y).symm

end Homological

section Total

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  {D' : Type*} [Category D'] [Preadditive D'] [HasZeroObject D']
  (F : A ⥤ B ⥤ D') [F.Additive] [∀ X, (F.obj X).Additive]

omit [HasZeroObject D'] in
/-- `Tot(F(K, L))ⁿ` vanishes as soon as every term `F(Kᑫ, Lᵖ)` with `q + p = n` does. -/
theorem isZero_mapBifunctor_X (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)] (n : ℤ)
    (h : ∀ q p : ℤ, q + p = n → IsZero ((F.obj (K.X q)).obj (L.X p))) :
    IsZero ((HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)).X n) :=
  StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
      L).toGradedObject.isColimitCofanMapObj _ n) (fun ⟨⟨q, p⟩, hqp⟩ => h q p hqp)

/-- `Tot(F(K, L))` vanishes above `r + b` when `K` vanishes above `r` and `L` above `b`. -/
theorem isZero_mapBifunctor_X_of_isStrictlyLE (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)] (r b : ℤ) [K.IsStrictlyLE r]
    [L.IsStrictlyLE b] (n : ℤ) (hn : r + b < n) :
    IsZero ((HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)).X n) := by
  refine isZero_mapBifunctor_X F K L n fun q p hqp => ?_
  by_cases hq : r < q
  · exact (F.map_isZero (K.isZero_of_isStrictlyLE r q hq)).obj _
  · exact (F.obj _).map_isZero (L.isZero_of_isStrictlyLE b p (by omega))

/-- `Tot(F(K, L))` vanishes below `r + a` when `K` vanishes below `r` and `L` below `a`. -/
theorem isZero_mapBifunctor_X_of_isStrictlyGE (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)] (r a : ℤ) [K.IsStrictlyGE r]
    [L.IsStrictlyGE a] (n : ℤ) (hn : n < r + a) :
    IsZero ((HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)).X n) := by
  refine isZero_mapBifunctor_X F K L n fun q p hqp => ?_
  by_cases hq : q < r
  · exact (F.map_isZero (K.isZero_of_isStrictlyGE r q hq)).obj _
  · exact (F.obj _).map_isZero (L.isZero_of_isStrictlyGE a p (by omega))

end Total

/-- For a K-flat `E`, the total tensor product `Tot(- ⊗_Λ E)` carries a quasi-isomorphism of
complexes of right modules to a quasi-isomorphism, so it preserves and reflects the vanishing of
homology. -/
theorem isZero_homology_mapBifunctor_iff_of_quasiIso {E : CochainComplex (ModuleCat.{v} Λ) ℤ}
    (hE : CochainComplex.KFlatBifunctor.KFlat (balancedTensorFunctor Λ) E)
    {K L : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ} (f : K ⟶ L) [QuasiIso f] (n : ℤ) :
    IsZero ((HomologicalComplex.mapBifunctor K E (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology n) ↔
      IsZero ((HomologicalComplex.mapBifunctor L E (balancedTensorFunctor Λ)
        (ComplexShape.up ℤ)).homology n) := by
  have := CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (balancedTensorFunctor.{0, v} Λ) E hE f
    inferInstance
  exact isZero_homology_iff_of_quasiIso ((((balancedTensorFunctor.{0, v} Λ).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app E) n

/-- The middle of the long exact sequence obtained by tensoring a short exact sequence of
complexes of right modules with a K-flat complex `E`. -/
theorem isZero_homology_mapBifunctor_X₂ {E : CochainComplex (ModuleCat.{v} Λ) ℤ}
    (hE : CochainComplex.KFlatBifunctor.KFlat (balancedTensorFunctor Λ) E)
    (S : ShortComplex (CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ)) (hS : S.ShortExact) (n : ℤ)
    (h₁ : IsZero ((HomologicalComplex.mapBifunctor S.X₁ E (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology n))
    (h₃ : IsZero ((HomologicalComplex.mapBifunctor S.X₃ E (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology n)) :
    IsZero ((HomologicalComplex.mapBifunctor S.X₂ E (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology n) := by
  refine isZero_homology_of_mappingCone
    ((((balancedTensorFunctor.{0, v} Λ).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map S.f).app E) n h₁ ?_
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have h₃' := (isZero_homology_mapBifunctor_iff_of_quasiIso hE
    (CochainComplex.mappingCone.descShortComplex S) n).2 h₃
  exact h₃'.of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR
      (balancedTensorFunctor.{0, v} Λ) E S.f).symm)

/-! ### Tensoring with a module placed in degree zero -/

section Single

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [HasZeroObject A] (F : A ⥤ B ⥤ ModuleCat.{v} ℤ) [F.Additive] [∀ X, (F.obj X).Additive]

/-- The double complex `F(N[0], L)` is concentrated in the column `0`. -/
theorem isZero_mapBifunctor_singleLeft_X (N : A) (L : CochainComplex B ℤ) (p : ℤ)
    (hp : p ≠ 0) :
    IsZero ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L).X p) :=
  StacksDraft.TotalDegeneration.isZero_of_isZero_X fun _ => (F.map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N p hp)).obj _

/-- The double complex `F(N[0], L)`, as the column `0` placed in degree `0`. -/
def mapBifunctorSingleLeftColumnHom (N : A) (L : CochainComplex B ℤ) :
    StacksDraft.TotalComplexQuasiIso.singleColumn
        ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L).X 0) 0 ⟶
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) fun k hk =>
    (isZero_mapBifunctor_singleLeft_X F N L k (by simp at hk; omega)).eq_of_tgt _ _

/-- The comparison `mapBifunctorSingleLeftColumnHom` is an isomorphism of double complexes. -/
theorem isIso_mapBifunctorSingleLeftColumnHom (N : A) (L : CochainComplex B ℤ) :
    IsIso (mapBifunctorSingleLeftColumnHom F N L) := by
  have (p : ℤ) : IsIso ((mapBifunctorSingleLeftColumnHom F N L).f p) := by
    by_cases hp : p = 0
    · subst hp
      rw [mapBifunctorSingleLeftColumnHom, HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _
        (HomologicalComplex.isZero_single_obj_X _ _ _ p hp)
        (isZero_mapBifunctor_singleLeft_X F N L p hp)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `Tot(F(N[0], L))` is the termwise complex `F(N, L)`. -/
def mapBifunctorSingleLeftIso (N : A) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) L F (ComplexShape.up ℤ)]
    [(StacksDraft.TotalComplexQuasiIso.singleColumn
        ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L).X 0) 0).HasTotal
        (ComplexShape.up ℤ)] :
    HomologicalComplex.mapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)
        L F (ComplexShape.up ℤ) ≅
      ((F.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj L := by
  have := isIso_mapBifunctorSingleLeftColumnHom F N L
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit
    ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L).X 0) 0
  let e := asIso (mapBifunctorSingleLeftColumnHom F N L)
  let et : (StacksDraft.TotalComplexQuasiIso.singleColumn
        ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N)).obj L).X 0) 0).total
          (ComplexShape.up ℤ) ≅
        HomologicalComplex.mapBifunctor
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) L F (ComplexShape.up ℤ) :=
    { hom := HomologicalComplex₂.total.map e.hom (ComplexShape.up ℤ)
      inv := HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.hom_inv_id, HomologicalComplex₂.total.map_id]
      inv_hom_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.inv_hom_id, HomologicalComplex₂.total.map_id] }
  refine et.symm ≪≫ (asIso (StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit _ 0)).symm ≪≫
    (shiftFunctorZero' (CochainComplex (ModuleCat.{v} ℤ) ℤ) (-0 : ℤ) (by simp)).app _ ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun q => (F.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N)).app
        (L.X q))
      (fun q q' _ => ?_)
  simp only [Functor.mapIso_hom, Iso.app_hom, Functor.mapHomologicalComplex_obj_d]
  exact ((F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).naturality
    (L.d q q')).symm

end Single

/-! ### Finite free resolutions over a finite ring -/

/-- The opposite of a finite ring is Noetherian. -/
theorem isNoetherianRing_mulOpposite_of_finite [Finite Λ] : IsNoetherianRing Λᵐᵒᵖ :=
  have : Finite Λᵐᵒᵖ := Finite.of_equiv Λ MulOpposite.opEquiv
  isNoetherian_of_finite Λᵐᵒᵖ Λᵐᵒᵖ

attribute [local instance] HasDerivedCategory.standard in
/-- Over a finite ring, a finite right module has a resolution by a complex of finite free right
modules concentrated in degrees `≤ 0`. -/
theorem exists_finiteFree_resolution_of_finite [Finite Λ] (Q : Type v) [AddCommGroup Q]
    [Module Λᵐᵒᵖ Q] [Module.Finite Λᵐᵒᵖ Q] :
    ∃ (K : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ)
      (π : K ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (ModuleCat.of Λᵐᵒᵖ Q)),
      K.IsStrictlyLE 0 ∧ QuasiIso π ∧
        ∀ n, Module.Finite Λᵐᵒᵖ (K.X n) ∧ Module.Free Λᵐᵒᵖ (K.X n) := by
  have := isNoetherianRing_mulOpposite_of_finite (Λ := Λ)
  have hpc := ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((DerivedCategory.singleFunctor (ModuleCat.{v} Λᵐᵒᵖ) 0).obj (ModuleCat.of Λᵐᵒᵖ Q)) 0
    Q).2.2).2 inferInstance
  obtain ⟨Fr⟩ :=
    ((StacksDraft.PseudoCoherence.modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
      (R := Λᵐᵒᵖ) Q).2.2.2).1 hpc
  have hfree (n : ℕ) := Fr.free n
  have := Fr.hasHomology
  have := Fr.quasiIso
  let P : ProjectiveResolution (ModuleCat.of Λᵐᵒᵖ Q) :=
    { complex := Fr.complex
      projective := fun n => by
        have : Module.Free Λᵐᵒᵖ (Fr.complex.X n) := hfree n
        exact (IsProjective.iff_projective (Fr.complex.X n)).1 Module.Projective.of_free
      π := Fr.π }
  refine ⟨P.cochainComplex, P.π', inferInstance, inferInstance, fun n => ?_⟩
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    let e := (P.cochainComplexXIso (-k) k).toLinearEquiv
    have := Fr.finite k
    have := hfree k
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · have : Subsingleton (P.cochainComplex.X n) := ModuleCat.isZero_iff_subsingleton.mp
      (P.cochainComplex.isZero_of_isStrictlyLE 0 n (by omega))
    exact ⟨inferInstance, inferInstance⟩

/-! ### Splitting a map of finite projective modules -/

section Splitting

variable {X₁ X₂ : Type v} [AddCommGroup X₁] [Module Λ X₁] [AddCommGroup X₂] [Module Λ X₂]

/-- `∑ₗ θ(l) · φₗ = θ ∘ (∑ₗ φₗ(-) l)` for linear forms `φₗ` on `X₂` and `θ` on `X₁`. -/
theorem sum_op_smul_eq_comp [Fintype X₁] (φ : X₁ → (X₂ →ₗ[Λ] Λ)) (θ : X₁ →ₗ[Λ] Λ) :
    ∑ l, MulOpposite.op (θ l) • φ l = θ ∘ₗ ∑ l, (φ l).smulRight l := by
  ext v
  simp [LinearMap.sum_apply, map_sum, MulOpposite.smul_eq_mul_unop]

/-- The dual basis identity `∑ₖ s(v)ₖ k = v` attached to a splitting `s` of
`(X →₀ Λ) → X`. -/
theorem sum_smulRight_lapply [Fintype X₂] {s : X₂ →ₗ[Λ] X₂ →₀ Λ}
    (hs : Finsupp.linearCombination Λ id ∘ₗ s = .id) :
    ∑ k, ((Finsupp.lapply k) ∘ₗ s).smulRight k = LinearMap.id := by
  ext v
  have := LinearMap.congr_fun hs v
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by simp)] at this
  simpa [LinearMap.sum_apply] using this

/-- A module map `g` with `g ∘ s ∘ g = g` into a projective module has projective cokernel. -/
theorem projective_cokernel_of_comp_comp {Y Z : ModuleCat.{v} Λ} [Module.Projective Λ Z]
    (g : Y ⟶ Z) (s : Z ⟶ Y) (hgs : g ≫ s ≫ g = g) :
    Module.Projective Λ (cokernel g : ModuleCat.{v} Λ) := by
  let i : cokernel g ⟶ Z := cokernel.desc g (𝟙 Z - s ≫ g) (by
    simp only [Preadditive.comp_sub, hgs, Category.comp_id, sub_self])
  have hi : i ≫ cokernel.π g = 𝟙 _ := by
    apply (cancel_epi (cokernel.π g)).1
    simp [i, Preadditive.sub_comp]
  exact Module.Projective.of_split i.hom (cokernel.π g).hom
    (by simpa using congrArg ModuleCat.Hom.hom hi)

/-- **The splitting criterion.** Let `X₁ → X₂ → X₃` be a complex of finite projective left
modules over a finite ring. If `N ⊗_Λ X₁ → N ⊗_Λ X₂ → N ⊗_Λ X₃` is exact in the middle for every
finite right module `N`, then the cokernel of `X₂ → X₃` is projective.

Only one `N` is used: the quotient of the dual `X₂^∨` by the image of `X₃^∨`. Exactness there
produces, from the element `∑ₖ [φₖ] ⊗ k` attached to a dual basis `(φₖ, k)` of `X₂`, maps
`h : X₂ → X₁` and `s : X₃ → X₂` with `s ∘ g = 1 - f ∘ h`, so that `g ∘ s ∘ g = g`. -/
theorem projective_cokernel_of_balancedTensor_exact [Finite Λ] {X₁ X₂ X₃ : ModuleCat.{v} Λ}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0)
    [Module.Finite Λ X₁] [Module.Projective Λ X₁] [Module.Finite Λ X₂] [Module.Projective Λ X₂]
    [Module.Finite Λ X₃] [Module.Projective Λ X₃]
    (hex : ∀ (Q : Type v) [AddCommGroup Q] [Module Λᵐᵒᵖ Q] [Module.Finite Λᵐᵒᵖ Q]
      (x : balancedTensorObject Λ (ModuleCat.of Λᵐᵒᵖ Q) X₂),
      balancedTensorMap Λ (𝟙 _) g x = 0 → ∃ y, balancedTensorMap Λ (𝟙 _) f y = x) :
    Module.Projective Λ (cokernel g : ModuleCat.{v} Λ) := by
  classical
  have : Finite X₁ := Module.finite_of_finite Λ
  have : Finite X₂ := Module.finite_of_finite Λ
  have : Finite X₃ := Module.finite_of_finite Λ
  let _ : Fintype X₁ := Fintype.ofFinite _
  let _ : Fintype X₂ := Fintype.ofFinite _
  let _ : Fintype X₃ := Fintype.ofFinite _
  obtain ⟨s₁, hs₁⟩ := Module.projective_def'.1 (inferInstance : Module.Projective Λ X₁)
  obtain ⟨s₂, hs₂⟩ := Module.projective_def'.1 (inferInstance : Module.Projective Λ X₂)
  obtain ⟨s₃, hs₃⟩ := Module.projective_def'.1 (inferInstance : Module.Projective Λ X₃)
  let φ : X₂ → (X₂ →ₗ[Λ] Λ) := fun k => (Finsupp.lapply k) ∘ₗ s₂
  have hφ (w : X₂) : ∑ k, φ k w • k = w := by
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (sum_smulRight_lapply hs₂) w
  have key (θ : X₂ →ₗ[Λ] Λ) : ∑ k, MulOpposite.op (θ k) • φ k = θ := by
    rw [sum_op_smul_eq_comp, sum_smulRight_lapply hs₂, LinearMap.comp_id]
  let V := LinearMap.range (LinearMap.lcomp Λᵐᵒᵖ Λ g.hom)
  have : Finite (X₂ →ₗ[Λ] Λ) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite ((X₂ →ₗ[Λ] Λ) ⧸ V) := Finite.of_surjective _ (Submodule.mkQ_surjective V)
  have : Module.Finite Λᵐᵒᵖ ((X₂ →ₗ[Λ] Λ) ⧸ V) := Module.Finite.of_finite
  let N := ModuleCat.of Λᵐᵒᵖ ((X₂ →ₗ[Λ] Λ) ⧸ V)
  let q : (X₂ →ₗ[Λ] Λ) →ₗ[Λᵐᵒᵖ] N := V.mkQ
  have hq (ψ : X₃ →ₗ[Λ] Λ) : q (ψ ∘ₗ g.hom) = 0 :=
    (Submodule.Quotient.mk_eq_zero V).2 ⟨ψ, rfl⟩
  let x : balancedTensorObject Λ N X₂ := ∑ k, balancedTensorPure Λ N X₂ (q (φ k)) k
  have hcx (k : X₂) : balancedTensorCoord s₂ N x k = q (φ k) := by
    rw [balancedTensorCoord_sum_pure]
    conv_rhs => rw [← key (φ k), map_sum]
    simp only [map_smul]
    rfl
  have hx : balancedTensorMap Λ (𝟙 N) g x = 0 := by
    rw [← balancedTensorRecomb_balancedTensorCoord s₃ hs₃ N (balancedTensorMap Λ (𝟙 N) g x)]
    convert map_zero (balancedTensorRecomb (X := X₃) N)
    ext j
    rw [balancedTensorMap_sum_pure, balancedTensorCoord_sum_pure, Finsupp.coe_zero,
      Pi.zero_apply, ← hq (Finsupp.lapply j ∘ₗ s₃),
      ← key ((Finsupp.lapply j ∘ₗ s₃) ∘ₗ g.hom), map_sum]
    simp only [map_smul]
    rfl
  obtain ⟨y, hy⟩ := hex _ x hx
  choose φ' hφ' using fun l => Submodule.mkQ_surjective V (balancedTensorCoord s₁ N y l)
  let h : X₂ →ₗ[Λ] X₁ := ∑ l, (φ' l).smulRight l
  have hy' : y = ∑ l, balancedTensorPure Λ N X₁ (q (φ' l)) l := by
    rw [← balancedTensorRecomb_balancedTensorCoord s₁ hs₁ N y, balancedTensorRecomb_eq_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [← hφ' l]
  have hmem (k : X₂) : φ k - (φ k ∘ₗ f.hom) ∘ₗ h ∈ V := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    change q (φ k) = q ((φ k ∘ₗ f.hom) ∘ₗ h)
    rw [← hcx k, ← hy, hy', ← sum_op_smul_eq_comp, balancedTensorMap_sum_pure,
      balancedTensorCoord_sum_pure, map_sum]
    simp only [map_smul]
    rfl
  choose ψ' hψ' using hmem
  let s : X₃ →ₗ[Λ] X₂ := ∑ k, (ψ' k).smulRight k
  have hs (v : X₂) : s (g v) = v - f (h v) := by
    have hψ'' (k : X₂) : ψ' k (g v) = φ k v - φ k (f (h v)) :=
      LinearMap.congr_fun (hψ' k) v
    simp only [s, LinearMap.sum_apply, LinearMap.smulRight_apply, hψ'', sub_smul,
      Finset.sum_sub_distrib, hφ]
  refine projective_cokernel_of_comp_comp g (ModuleCat.ofHom s) ?_
  ext v
  change g (s (g v)) = g v
  rw [hs, map_sub, sub_eq_self]
  exact congrArg (fun u : X₁ ⟶ X₃ => u (h v)) hfg

end Splitting

/-! ### Truncated free resolutions -/

/-- A truncated finite free resolution of length `m`: a complex of finite free right `Λ`-modules
concentrated in degrees `[-m, 0]` which is exact in every degree strictly between `-m` and `0`. -/
def IsTruncatedFreeResolution (R : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ) (m : ℕ) : Prop :=
  R.IsStrictlyGE (-(m : ℤ)) ∧ R.IsStrictlyLE 0 ∧
    (∀ q, Module.Finite Λᵐᵒᵖ (R.X q) ∧ Module.Free Λᵐᵒᵖ (R.X q)) ∧
    ∀ q : ℤ, -(m : ℤ) < q → q < 0 → R.ExactAt q

/-- The cokernel of `τ^{≤ -m}R ⟶ R`, for a complex `R` concentrated in degrees `≤ 0` and exact
strictly between `-m` and `0`, has no cohomology in negative degrees. -/
theorem isGE_shortComplexTruncLE_X₃ (R : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ) (m : ℕ)
    (hex : ∀ q : ℤ, -(m : ℤ) < q → q < 0 → R.ExactAt q) :
    (R.shortComplexTruncLE (-(m : ℤ))).X₃.IsGE 0 := by
  refine (HomologicalComplex.isSupported_iff_of_quasiIso
    (R.shortComplexTruncLEX₃ToTruncGE (-(m : ℤ)) (-(m : ℤ) + 1))
    (ComplexShape.embeddingUpIntGE 0)).2 ?_
  rw [← CochainComplex.IsGE, CochainComplex.isGE_iff]
  intro i hi
  by_cases him : i < -(m : ℤ) + 1
  · exact (R.truncGE (-(m : ℤ) + 1)).exactAt_of_isGE (-(m : ℤ) + 1) i him
  · have := CochainComplex.quasiIsoAt_πTruncGE R (-(m : ℤ) + 1) i (by omega)
    exact (exactAt_iff_of_quasiIsoAt (R.πTruncGE (-(m : ℤ) + 1)) i).1
      (hex i (by omega) hi)

/-- **Vanishing of the total tensor product of a truncated free resolution.** Let `R` be a
truncated finite free resolution of length `m` and `C` a complex of projective left modules
concentrated in degrees `[a, b]`. Then `Hᵖ(Tot(R ⊗_Λ C)) = 0` for `b - m < p < a`. -/
theorem isZero_homology_mapBifunctor_of_projective
    {R : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ} {m : ℕ} (hR : IsTruncatedFreeResolution R m)
    (C : CochainComplex (ModuleCat.{v} Λ) ℤ) (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (hC : ∀ n, Module.Projective Λ (C.X n)) (p : ℤ) (hp₁ : b - m < p) (hp₂ : p < a) :
    IsZero ((HomologicalComplex.mapBifunctor R C (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)).homology p) := by
  obtain ⟨-, -, -, hex⟩ := hR
  have hK := kFlat_balancedTensor_of_projective C b hC
  refine isZero_homology_mapBifunctor_X₂ hK _ (R.shortComplexTruncLE_shortExact (-(m : ℤ))) p
    ?_ ?_
  · have : (R.shortComplexTruncLE (-(m : ℤ))).X₁.IsStrictlyLE (-(m : ℤ)) :=
      (inferInstance : (R.truncLE (-(m : ℤ))).IsStrictlyLE (-(m : ℤ)))
    exact StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X p
      (isZero_mapBifunctor_X_of_isStrictlyLE _ _ _ (-(m : ℤ)) b p (by omega))
  · have := isGE_shortComplexTruncLE_X₃ R m hex
    refine (isZero_homology_mapBifunctor_iff_of_quasiIso hK
      ((R.shortComplexTruncLE (-(m : ℤ))).X₃.πTruncGE 0) p).2 ?_
    exact StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X p
      (isZero_mapBifunctor_X_of_isStrictlyGE _ _ _ 0 a p (by omega))

/-- The stupid truncation `σ^{≥ -m}K` of a complex `K` of finite free right modules which is
concentrated in degrees `≤ 0` and exact in negative degrees is a truncated free resolution of
length `m`. -/
theorem isTruncatedFreeResolution_stupidTrunc (K : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ)
    [K.IsStrictlyLE 0] (hK : ∀ n, Module.Finite Λᵐᵒᵖ (K.X n) ∧ Module.Free Λᵐᵒᵖ (K.X n))
    (hex : ∀ q : ℤ, q < 0 → K.ExactAt q) (m : ℕ) :
    IsTruncatedFreeResolution (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(m : ℤ)))) m := by
  refine ⟨inferInstance, ?_, fun q => ?_, fun q hq₁ hq₂ => ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE 0 i hi).of_iso
      (StacksDraft.StupidTruncation.stupidTruncGEXIso K _ i (by omega))
  · by_cases hq : -(m : ℤ) ≤ q
    · let e := (StacksDraft.StupidTruncation.stupidTruncGEXIso K _ q hq).toLinearEquiv
      obtain ⟨_, _⟩ := hK q
      exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
    · have : Subsingleton ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(m : ℤ)))).X q) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (CochainComplex.isZero_of_isStrictlyGE _ (-(m : ℤ)) q (by omega))
      exact ⟨inferInstance, inferInstance⟩
  · have := StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE K (-(m : ℤ)) q hq₁
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hex q hq₂)).of_iso
      (asIso (HomologicalComplex.homologyMap
        (HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE (-(m : ℤ)))) q))

/-- **The key consequence of the vanishing hypothesis.** If `H^{a-1}(Tot(R ⊗_Λ E)) = 0` for every
truncated free resolution `R` of length at least `b - a + 2`, then the same vanishing holds with
`R` replaced by any finite right module placed in degree `0`. -/
theorem isZero_homology_mapBifunctor_single_of_truncated [Finite Λ]
    (E : CochainComplex (ModuleCat.{v} Λ) ℤ) (a b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ n, Module.Projective Λ (E.X n))
    (hT : ∀ (R : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ) (m : ℕ), b - a + 2 ≤ (m : ℤ) →
      IsTruncatedFreeResolution R m →
      IsZero ((HomologicalComplex.mapBifunctor R E (balancedTensorFunctor Λ)
        (ComplexShape.up ℤ)).homology (a - 1)))
    (Q : Type v) [AddCommGroup Q] [Module Λᵐᵒᵖ Q] [Module.Finite Λᵐᵒᵖ Q] :
    IsZero ((HomologicalComplex.mapBifunctor
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (ModuleCat.of Λᵐᵒᵖ Q)) E
        (balancedTensorFunctor Λ) (ComplexShape.up ℤ)).homology (a - 1)) := by
  obtain ⟨K, π, hKle, hπ, hK⟩ := exists_finiteFree_resolution_of_finite (Λ := Λ) Q
  have hKE := kFlat_balancedTensor_of_projective E b hE
  have hex (q : ℤ) (hq : q < 0) : K.ExactAt q :=
    (exactAt_iff_of_quasiIsoAt π q).2 (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))
  have hm : b - a + 2 ≤ ((b - a + 2).toNat : ℤ) := Int.self_le_toNat _
  set m := (b - a + 2).toNat
  have hRz := hT _ m hm (isTruncatedFreeResolution_stupidTrunc K hK hex m)
  have := StacksDraft.StupidTruncation.mono_ιStupidTrunc K
    (ComplexShape.embeddingUpIntGE (-(m : ℤ)))
  let S := ShortComplex.mk (HomologicalComplex.ιStupidTrunc K
    (ComplexShape.embeddingUpIntGE (-(m : ℤ)))) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hC : CochainComplex.IsStrictlyLE S.X₃ (-(m : ℤ) - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    refine (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)).isIso_f_iff.1 ?_
    change IsIso ((HomologicalComplex.ιStupidTrunc K
      (ComplexShape.embeddingUpIntGE (-(m : ℤ)))).f i)
    rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K _ i (by omega)]
    infer_instance
  have hKz := isZero_homology_mapBifunctor_X₂ hKE S hS (a - 1) hRz
    (StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X _
      (isZero_mapBifunctor_X_of_isStrictlyLE _ _ _ (-(m : ℤ) - 1) b (a - 1) (by omega)))
  exact (isZero_homology_mapBifunctor_iff_of_quasiIso hKE π (a - 1)).1 hKz

/-- **Projectivity of the cokernel at the bottom of the Tor window.** Let `Λ` be a finite ring
and `E` a complex of finite projective left `Λ`-modules which vanishes above degree `b`. If
`H^{a-1}(Tot(R ⊗_Λ E)) = 0` for every truncated finite free resolution `R` of length at least
`b - a + 2`, then the cokernel of `d^{a-1} : E^{a-1} → E^a` is projective. -/
theorem projective_cokernel_of_isZero_homology_mapBifunctor [Finite Λ]
    (E : CochainComplex (ModuleCat.{v} Λ) ℤ) (a b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ n, Module.Finite Λ (E.X n) ∧ Module.Projective Λ (E.X n))
    (hT : ∀ (R : CochainComplex (ModuleCat.{v} Λᵐᵒᵖ) ℤ) (m : ℕ), b - a + 2 ≤ (m : ℤ) →
      IsTruncatedFreeResolution R m →
      IsZero ((HomologicalComplex.mapBifunctor R E (balancedTensorFunctor Λ)
        (ComplexShape.up ℤ)).homology (a - 1))) :
    Module.Projective Λ (cokernel (E.d (a - 1) a) : ModuleCat.{v} Λ) := by
  obtain ⟨_, _⟩ := hE (a - 2)
  obtain ⟨_, _⟩ := hE (a - 1)
  obtain ⟨_, _⟩ := hE a
  refine projective_cokernel_of_balancedTensor_exact (E.d (a - 2) (a - 1)) (E.d (a - 1) a)
    (E.d_comp_d _ _ _) fun Q _ _ _ x hx => ?_
  have hz := IsZero.of_iso
    (isZero_homology_mapBifunctor_single_of_truncated E a b (fun n => (hE n).2) hT Q)
    ((HomologicalComplex.homologyFunctor _ _ (a - 1)).mapIso
      (mapBifunctorSingleLeftIso (balancedTensorFunctor Λ) (ModuleCat.of Λᵐᵒᵖ Q) E).symm)
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ (a - 1)).2 hz
  rw [HomologicalComplex.exactAt_iff' _ (a - 2) (a - 1) a (by simp; omega) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  exact hex x hx

end StacksDraft.TorAmplitude
