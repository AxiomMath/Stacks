module

public import Mathlib.Algebra.Homology.HomologySequence
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyIResolution
public import StacksFrontier.Algebra.DirectSum.ParityOperator
public import StacksFrontier.Algebra.Homology.DoubleComplexesOfModules
public import StacksCore.Tactic.StacksAttribute

/-! # The augmentation of the resolution tower is a quasi-isomorphism

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `M` be a right
differential graded `A`-module. The file `Module/PropertyIResolution.lean` builds, following the
proof of Stacks 09KU, the resolution tower

`M = M₀ ↪ I₀ ↠ M₁ ↪ I₁ ↠ M₂ ↪ ⋯`

out of Stacks 09KT, the totalization `I = ∏ᵢ Iᵢ[-i]` of the tower `I₀ → I₁ → ⋯`, and the
augmentation `M ⟶ I`. This file proves that the augmentation is a quasi-isomorphism, which is
the second of the two things Stacks 09KU asserts about it; the first, that `I` has property (I),
is the filtration of
`StacksFrontier/Algebra/DifferentialGraded/Module/ResolutionFiltration.lean` and is not done here.

The mathematics is Stacks 09J0, already formalized in this repository as
`HomologicalComplex₂.quasiIso_toProductTotal` for double complexes of abelian groups and bridged
to modules by `HomologicalComplex₂.quasiIso_of_isProductTotal`. What this file supplies is the
three inputs that bridge expects: the double complex `K^{p,q} = Iₚ^q`, the identification of the
underlying complex of abelian groups of `I` with the product total complex `Tot_π(K)`, and the
two exactness hypotheses of 09J0.

## Main definitions

* `DifferentialGradedModule.towerDouble`: the double complex `K^{p,q} = Jₚ^q` of a tower
  `J₀ → J₁ → ⋯` of differential graded modules.
* `DifferentialGradedModule.towerTotalPi`: the components of a homogeneous element of the
  totalization, as a point of `Tot_π^n(K)`.
* `DifferentialGradedModule.towerTotalProductTotalIso`: the isomorphism between the complex of
  abelian groups underlying the totalization and `Tot_π(K)`.
* `DifferentialGradedModule.resolutionAug₀`: the injection `M ⟶ I₀`, at the honest type of `M`.
* `DifferentialGradedModule.resolutionDouble`: the double complex `K^{p,q} = Iₚ^q` of the
  resolution tower.
* `DifferentialGradedModule.resolutionAugmented`: the complex of complexes
  `0 → M^• → I₀^• → I₁^• → ⋯`.

## Main results

* `DifferentialGradedModule.exists_mem_grading_eq_d`: an element in the image of the
  differential which is homogeneous of degree `n` is the differential of a homogeneous element
  of degree `n - 1`.
* `DifferentialGradedModule.Hom.exists_mem_grading_of_mem_range`: a homogeneous element in the
  image of a homomorphism is the image of a homogeneous element of the same degree.
* `DifferentialGradedModule.toProductTotal_towerTotal`: a homomorphism into the totalization
  whose zeroth component is `b` and whose higher components vanish becomes, under the
  identification above, the canonical map `M^• → Tot_π(K)` of Stacks 09J0; applied to the
  augmentation, this is the compatibility 09J0 asks for.
* `DifferentialGradedModule.acyclic_augment_resolution`: the first exactness hypothesis of
  Stacks 09J0 — the complex of complexes `0 → M^• → I₀^• → I₁^• → ⋯` is exact.
* `DifferentialGradedModule.acyclic_opcycles_augment_resolution`: the second — so are the
  complexes of cokernels of the differentials.
* `DifferentialGradedModule.quasiIso_resolutionAug`: the augmentation `M ⟶ I` is a
  quasi-isomorphism.

## Implementation notes

*The totalization is compared with `Tot_π` degreewise and by hand.* Stacks' product total
complex is indexed by the pairs `(p, q) ∈ ℕ × ℤ` with `p + q = n`, while the totalization is a
product over `ℕ` of shifted factors; the comparison is the reindexing `p ↦ (p, n - p)`, and the
map in the forward direction is `towerTotalPi`, shown bijective by
`towerTotal.eq_of_π_eq` and `towerTotal.exists_mem_grading` rather than by writing down an
inverse. The signs match on the nose: `towerTotal.π_d_zero` and `towerTotal.π_d_succ` at offset
`0` produce exactly the `(-1)^p` of `HomologicalComplex₂.productTotalDComp`.

*Several definitions are made implicitly reducible locally.* `toCochainComplex` and
`HomologicalComplex₂.productTotalX` are semireducible, so a goal mentioning a point of
`Tot_π^n(K)` is not type-correct at instance transparency once it has been rewritten, and the
rewriting tactics refuse. Likewise `resolutionModule (p + 1)` and
`Hom.cokernelObj (resolutionφ p)` are two spellings of one module which agree only by unfolding
`resolutionModule`, so a `0` elaborated at one of them is rejected at the other. Making those
definitions reducible inside this file is the scoped form of the fix; the alternative, stating
every step at the honest type, would require a bridging lemma per component.

*Every step whose statement mentions a point of a graded piece is stated with its binder at the
honest type of that piece.* The rewriting tactics refuse a goal that is not type-correct at
instance transparency, and the degree-`n` term of a cochain complex underlying a differential
graded module is such a spelling of `M.grading n`. So the component-level content sits in lemmas
quantified over `x : N.grading n` — `productTotalD_towerTotalPi`, `towerTotalPi_gradedMap`,
`resolutionDouble_d_f_apply`, `pOpcycles_eq_zero_of_resolutionAug₀` — and the plumbing proofs
discharge their goals by `exact`, which checks definitional equality at default transparency.

*The exactness hypotheses are reduced to elementwise statements about the tower.* Exactness of a
complex of complexes is degreewise exactness (`HomologicalComplex.exact_of_degreewise_exact`),
and exactness of a short complex of `R`-modules is elementwise
(`CategoryTheory.ShortComplex.moduleCat_exact_iff`), so both hypotheses become statements about
homogeneous elements of the modules `Mᵢ` and `Iᵢ`. For the complexes of cokernels the objects of
opcycles are handled through `CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_zero_iff`,
which says that the class of a homogeneous element of degree `q` vanishes exactly when it is the
differential of something; the homogeneous refinement of that `something` is
`exists_mem_grading_eq_d`, and the input which is not formal is
`DifferentialGradedModule.DualResolutionStep.exists_eq_d`, i.e. Stacks 09KT(2).

## References

* [Stacks Project, Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), the second half of
  whose proof this is, and
  [Tag 09J0](https://stacks.math.columbia.edu/tag/09J0), which it applies.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex
  DifferentialGradedModule.resolutionModule DifferentialGradedModule.resolutionI
  DifferentialGradedModule.resolutionφ DifferentialGradedModule.resolutionMap
  DifferentialGradedModule.resolutionTotal HomologicalComplex₂.productTotalX

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Homogeneous refinements

Two statements of the form "an element of a homogeneous subset is the image of a homogeneous
element", both proved by taking the relevant graded component of an arbitrary preimage. -/

/-- The degree-`q` component of `d y` is `d` of the degree-`(q - 1)` component of `y`: the
differential is a grading-preserving map into the once-shifted module, so it commutes with
taking graded components up to the shift. -/
theorem gradedProjection_d (N : DifferentialGradedModule.{u, u, u} A) (q : ℤ) (y : N.M) :
    DirectSum.gradedProjection N.grading q (N.d y)
      = N.d (DirectSum.gradedProjection N.grading (q - 1) y) := by
  induction y using DirectSum.Decomposition.inductionOn N.grading with
  | zero => simp
  | @homogeneous m y =>
      have hdy : N.d (y : N.M) ∈ N.grading (m + 1) := N.d_mem m _ y.2
      by_cases h : m = q - 1
      · subst h
        rw [DirectSum.gradedProjection_of_mem_same N.grading y.2,
          DirectSum.gradedProjection_of_mem_same N.grading
            (show N.d (y : N.M) ∈ N.grading q from by simpa using hdy)]
      · rw [DirectSum.gradedProjection_of_mem_ne N.grading y.2 h,
          DirectSum.gradedProjection_of_mem_ne N.grading hdy (by omega), map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **A homogeneous element in the image of the differential is the differential of a
homogeneous element**, of degree one less. -/
theorem exists_mem_grading_eq_d (N : DifferentialGradedModule.{u, u, u} A) {q : ℤ} {x : N.M}
    (hx : x ∈ N.grading q) {y : N.M} (hy : N.d y = x) :
    ∃ y' ∈ N.grading (q - 1), N.d y' = x := by
  refine ⟨DirectSum.gradedProjection N.grading (q - 1) y,
    DirectSum.gradedProjection_mem _ _ _, ?_⟩
  rw [← gradedProjection_d, hy, DirectSum.gradedProjection_of_mem_same N.grading hx]

/-- **A homogeneous element in the image of a homomorphism is the image of a homogeneous
element** of the same degree. -/
theorem Hom.exists_mem_grading_of_mem_range {M N : DifferentialGradedModule.{u, u, u} A} (f : Hom M
  N)
    {n : ℤ} {y : N.M} (hy : y ∈ N.grading n) (hyr : ∃ x, f.toFun x = y) :
    ∃ x ∈ M.grading n, f.toFun x = y := by
  obtain ⟨x, rfl⟩ := hyr
  refine ⟨(DirectSum.decompose M.grading x n : M.M), SetLike.coe_mem _, ?_⟩
  rw [← DirectSum.coe_decompose_apply_map M.grading N.grading f.toFun
    (fun i z hz => f.map_grading i z hz) x n,
    DirectSum.decompose_of_mem_same N.grading hy]

/-- **The projection onto a cokernel is surjective in each degree**: a homogeneous element of
degree `n` of `Coker f` is the class of a homogeneous element of degree `n`, by the definition of
the grading of the cokernel. -/
theorem Hom.exists_mem_grading_cokernelπ {M N : DifferentialGradedModule.{u, u, u} A} (f : Hom M N)
    {n : ℤ} {z : (Hom.cokernelObj f).M} (hz : z ∈ (Hom.cokernelObj f).grading n) :
    ∃ y ∈ N.grading n, (Hom.cokernelπ f).toFun y = z := by
  obtain ⟨y, hyN, rfl⟩ := hz
  exact ⟨y, hyN, rfl⟩

/-! ### The double complex of a tower -/

section Tower

variable (J : ℕ → DifferentialGradedModule.{u, u, u} A) (g : ∀ i, J i ⟶ J (i + 1))
  (hg : ∀ (i : ℕ) (x : (J i).M), (g (i + 1)).toFun ((g i).toFun x) = 0)

/-- **The double complex of a tower** `J₀ → J₁ → ⋯` of differential graded `A`-modules with
`g_{i+1} ∘ gᵢ = 0`: the complex of cochain complexes `p ↦ Jₚ^•`, i.e. the double complex
`K^{p,q} = Jₚ^q` of Stacks 09J0 whose product total complex is the totalization of the tower. -/
@[implicit_reducible]
def towerDouble :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  CochainComplex.of (fun p => (forgetToCochainComplex A).obj (J p))
    (fun p => (forgetToCochainComplex A).map (g p))
    (fun p => by
      rw [← (forgetToCochainComplex A).map_comp,
        show g p ≫ g (p + 1) = 0 from by
          apply Hom.ext; apply LinearMap.ext; intro x; exact hg p x,
        Functor.map_zero])

/-- The `p`-th differential of the double complex of a tower is the cochain map underlying
`gₚ`. -/
theorem towerDouble_d (p : ℕ) : (towerDouble J g hg).d p (p + 1) = (g p).toCochainMap :=
  CochainComplex.of_d (fun p => (forgetToCochainComplex A).obj (J p))
    (fun p => (forgetToCochainComplex A).map (g p)) p

/-- The underlying double complex of abelian groups of the double complex of a tower, which is
the one Stacks 09J0 is stated for. -/
abbrev towerDoubleAb : HomologicalComplex₂ AddCommGrpCat.{u}
    (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  (HomologicalComplex₂.forget₂AddCommGrpCat.{u} R).obj (towerDouble J g hg)

/-- The vertical differential of the double complex of a tower is the differential of `Jₚ`. -/
theorem towerDoubleAb_X_d_apply (p : ℕ) (q : ℤ) (y : (J p).grading q) :
    ((towerDoubleAb J g hg).X p).d q (q + 1) y = (J p).gradedDifferential q y := by
  have hd : ((towerDoubleAb J g hg).X p).d q (q + 1)
      = (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          (ModuleCat.ofHom ((J p).gradedDifferential q)) := by
    rw [show ((towerDoubleAb J g hg).X p).d q (q + 1)
        = (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
            ((J p).toCochainComplex.d q (q + 1)) from rfl, toCochainComplex_d]
  rw [hd]
  rfl

/-- The horizontal differential of the double complex of a tower is `gₚ`. -/
theorem towerDoubleAb_d_f_apply (p : ℕ) (q : ℤ) (y : (J p).grading q) :
    ((towerDoubleAb J g hg).d p (p + 1)).f q y = (g p).gradedMap q y := by
  have hd : (towerDoubleAb J g hg).d p (p + 1)
      = (CochainComplex.forget₂AddCommGrpCat.{u} R).map (g p).toCochainMap := by
    rw [show (towerDoubleAb J g hg).d p (p + 1)
        = (CochainComplex.forget₂AddCommGrpCat.{u} R).map ((towerDouble J g hg).d p (p + 1))
          from rfl, towerDouble_d]
  rw [hd]
  rfl

/-! ### The totalization as the product total complex -/

/-- **The components of a homogeneous element of the totalization**, read as a point of
`Tot_π^n(K) = ∏_{p + q = n} Jₚ^q`: the `(p, q)`-component is the `p`-th component of the
element, which is homogeneous of degree `q = n - p`. -/
def towerTotalPi (n : ℤ) (x : (towerTotal J 0 g hg).grading n) :
    ∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, (J i.1.1).grading i.1.2 :=
  fun i => ⟨towerTotal.π J 0 g hg i.1.1 x.val, by
    have h := (towerTotal.mem_grading_iff J 0 g hg x.val).1 x.property i.1.1
    have hi := i.2
    rwa [show n - (0 + (i.1.1 : ℤ)) = i.1.2 from by omega] at h⟩

/-- The `(p, q)`-component of `towerTotalPi` is the `p`-th component of the element. -/
@[simp] theorem towerTotalPi_val (n : ℤ) (x : (towerTotal J 0 g hg).grading n)
    (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) :
    ((towerTotalPi J g hg n x i : (J i.1.1).grading i.1.2) : (J i.1.1).M)
      = towerTotal.π J 0 g hg i.1.1 x.val := rfl

/-- `towerTotalPi` is additive. -/
def towerTotalPiHom (n : ℤ) : (towerTotal J 0 g hg).grading n →+
    (∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, (J i.1.1).grading i.1.2) where
  toFun := towerTotalPi J g hg n
  map_zero' := by funext i; exact Subtype.ext (map_zero _)
  map_add' x y := by funext i; exact Subtype.ext (map_add _ _ _)

/-- A homogeneous element of the totalization is determined by its components. -/
theorem towerTotalPi_injective (n : ℤ) : Function.Injective (towerTotalPi J g hg n) := by
  intro x y h
  refine Subtype.ext (towerTotal.eq_of_π_eq J 0 g hg fun i => ?_)
  exact congrArg Subtype.val (congrFun h ⟨(i, n - i), by omega⟩)

/-- Every point of `Tot_π^n(K)` is the family of components of a homogeneous element of degree
`n` of the totalization. -/
theorem towerTotalPi_surjective (n : ℤ) : Function.Surjective (towerTotalPi J g hg n) := by
  intro y
  obtain ⟨z, hz, hzq⟩ := towerTotal.exists_mem_grading J 0 g hg n
    (fun i => (y ⟨(i, n - i), by omega⟩).val)
    (fun i => by
      have := (y ⟨(i, n - i), by omega⟩).property
      rwa [show n - (0 + (i : ℤ)) = n - (i : ℤ) from by omega])
  refine ⟨⟨z, hz⟩, ?_⟩
  funext i
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  obtain rfl : q = n - (p : ℤ) := by omega
  exact Subtype.ext (hzq p)

/-- The degree-`n` part of the totalization is `Tot_π^n(K) = ∏_{p + q = n} Jₚ^q`. -/
def towerTotalGradingEquiv (n : ℤ) : (towerTotal J 0 g hg).grading n ≃+
    (∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, (J i.1.1).grading i.1.2) :=
  AddEquiv.ofBijective (towerTotalPiHom J g hg n)
    ⟨towerTotalPi_injective J g hg n, towerTotalPi_surjective J g hg n⟩

/-- The degree-`n` part of the totalization, as an isomorphism of abelian groups onto the
degree-`n` part of `Tot_π(K)`. -/
def towerTotalGradingIsoAb (n : ℤ) :
    ((CochainComplex.forget₂AddCommGrpCat.{u} R).obj
      ((forgetToCochainComplex A).obj (towerTotal J 0 g hg))).X n ≅
      (towerDoubleAb J g hg).productTotal.X n :=
  AddEquiv.toAddCommGrpIso (towerTotalGradingEquiv J g hg n)

/-- **The components of the twisted differential of the totalization are the components of the
differential of `Tot_π(K)`.** This is where the signs are checked: at offset `0` the `p`-th
component of the differential of the totalization is `gₚ₋₁` plus `(-1)^p d_{Jₚ}`, which is
`HomologicalComplex₂.productTotalDComp`. -/
theorem productTotalD_towerTotalPi (n : ℤ) (x : (towerTotal J 0 g hg).grading n)
    (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n + 1}) :
    (towerDoubleAb J g hg).productTotalD n (towerTotalPi J g hg n x) i
      = towerTotalPi J g hg (n + 1) ((towerTotal J 0 g hg).gradedDifferential n x) i := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  refine Subtype.ext ?_
  rcases p with _ | p
  · obtain rfl : q = n + 1 := by push_cast at h; omega
    rw [HomologicalComplex₂.productTotalD_apply_zero_left (q' := n) (hq := by omega)
      (h := h) (h' := by omega), towerDoubleAb_X_d_apply]
    simp only [towerTotalPi_val, gradedDifferential_apply]
    rw [towerTotal.π_d_zero]
    simp
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [HomologicalComplex₂.productTotalD_apply_succ (q' := q') (hq := rfl) (h := h)
      (h' := by push_cast at h ⊢; omega), towerDoubleAb_d_f_apply, towerDoubleAb_X_d_apply]
    change (((g p).gradedMap (q' + 1)
          (towerTotalPi J g hg n x ⟨(p, q' + 1), by push_cast at h ⊢; omega⟩)
        + (-1 : ℤ) ^ (p + 1) • (J (p + 1)).gradedDifferential q'
            (towerTotalPi J g hg n x ⟨(p + 1, q'), by push_cast at h ⊢; omega⟩) :
        (J (p + 1)).grading (q' + 1)) : (J (p + 1)).M) = _
    simp only [AddMemClass.coe_add, AddSubgroupClass.coe_zsmul, towerTotalPi_val,
      gradedDifferential_apply, Hom.gradedMap_apply]
    rw [towerTotal.π_d_succ, zero_add, Int.coe_negOnePow_natCast]

/-- **The complex of abelian groups underlying the totalization of a tower is the product total
complex of the double complex of the tower.** This is the identification `e` that Stacks 09J0,
in the form `HomologicalComplex₂.quasiIso_of_isProductTotal`, asks a consumer to supply. -/
def towerTotalProductTotalIso :
    (CochainComplex.forget₂AddCommGrpCat.{u} R).obj
        ((forgetToCochainComplex A).obj (towerTotal J 0 g hg)) ≅
      (towerDoubleAb J g hg).productTotal :=
  HomologicalComplex.Hom.isoOfComponents (towerTotalGradingIsoAb J g hg) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [HomologicalComplex₂.productTotal_d,
      show ((CochainComplex.forget₂AddCommGrpCat.{u} R).obj
          ((forgetToCochainComplex A).obj (towerTotal J 0 g hg))).d i (i + 1)
        = (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
            (ModuleCat.ofHom ((towerTotal J 0 g hg).gradedDifferential i)) from by
        rw [← toCochainComplex_d]; rfl]
    ext x
    funext k
    exact productTotalD_towerTotalPi J g hg i x k)

/-! ### The homomorphism into the totalization as the canonical map to `Tot_π` -/

variable (N : DifferentialGradedModule.{u, u, u} A) (a : N ⟶ towerTotal J 0 g hg) (b : N ⟶ J 0)

/-- The `(p, q)`-component of the image of a homogeneous element of `N` under a homomorphism
into the totalization whose zeroth component is `b` and whose higher components vanish: it is
`b` for `p = 0` and zero otherwise, which is exactly the `(p, q)`-component of the canonical map
`N^• → Tot_π(K)` of Stacks 09J0. -/
theorem towerTotalPi_gradedMap
    (h0 : ∀ x : N.M, towerTotal.π J 0 g hg 0 (a.toFun x) = b.toFun x)
    (hs : ∀ (i : ℕ) (x : N.M), towerTotal.π J 0 g hg (i + 1) (a.toFun x) = 0)
    (n : ℤ) (x : N.grading n) (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) :
    towerTotalPi J g hg n (a.gradedMap n x) i
      = HomologicalComplex₂.toProductTotalComp
          (K := (HomologicalComplex₂.forget₂AddCommGrpCat.{u} R).obj (towerDouble J g hg))
          ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ((forgetToCochainComplex A).map b))
          n x i.1.1 i.1.2 i.2 := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  rcases p with _ | p
  · obtain rfl : q = n := by push_cast at h; omega
    refine Subtype.ext ?_
    rw [HomologicalComplex₂.toProductTotalComp_zero_left, towerTotalPi_val]
    exact (h0 x.val).trans rfl
  · refine Subtype.ext ?_
    rw [HomologicalComplex₂.toProductTotalComp_succ, towerTotalPi_val]
    exact (hs p x.val).trans (ZeroMemClass.coe_zero _).symm

/-- **A homomorphism into the totalization whose zeroth component is `b` and whose higher
components vanish becomes, under `towerTotalProductTotalIso`, the canonical map
`N^• → Tot_π(K)`** of Stacks 09J0. This is the compatibility `he` that
`HomologicalComplex₂.quasiIso_of_isProductTotal` asks a consumer to supply. -/
theorem toProductTotal_towerTotal
    (h0 : ∀ x : N.M, towerTotal.π J 0 g hg 0 (a.toFun x) = b.toFun x)
    (hs : ∀ (i : ℕ) (x : N.M), towerTotal.π J 0 g hg (i + 1) (a.toFun x) = 0)
    (w : (forgetToCochainComplex A).map b ≫ (towerDouble J g hg).d 0 1 = 0) :
    (CochainComplex.forget₂AddCommGrpCat.{u} R).map ((forgetToCochainComplex A).map a)
        ≫ (towerTotalProductTotalIso J g hg).hom
      = HomologicalComplex₂.toProductTotal
          (K := (HomologicalComplex₂.forget₂AddCommGrpCat.{u} R).obj (towerDouble J g hg))
          ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ((forgetToCochainComplex A).map b))
          (HomologicalComplex₂.forget₂AddCommGrpCat_w _ w) := by
  ext n x
  funext i
  exact towerTotalPi_gradedMap J g hg N a b h0 hs n x i

end Tower

/-! ### Opcycles of the complex underlying a differential graded module

The object of opcycles in degree `q` of the cochain complex underlying a differential graded
module `N` is `Coker(d_N^{q-1})`, the second kind of object Stacks 09J0 asks about. The three
facts needed are that the projection onto it is surjective, that the class of a homogeneous
element vanishes exactly when the element is a differential, and that it is natural. -/

section Opcycles

/-- The projection onto the opcycles in degree `q` is surjective: it is an epimorphism of
`R`-modules. -/
theorem pOpcycles_surjective (N : DifferentialGradedModule.{u, u, u} A) (q : ℤ) :
    Function.Surjective (((forgetToCochainComplex A).obj N).pOpcycles q) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

/-- An element in the image of a differential of the underlying cochain complex is in the image
of the differential of the module. The index `m` is arbitrary: when it is not `q - 1` the
differential of the cochain complex vanishes by the shape of `ComplexShape.up ℤ` and the element
is zero. -/
theorem exists_eq_d_of_d_apply (N : DifferentialGradedModule.{u, u, u} A) (m q : ℤ)
    (v : N.grading m) (y : N.grading q)
    (h : ((forgetToCochainComplex A).obj N).d m q v = y) :
    ∃ w : N.M, N.d w = (y : N.M) := by
  by_cases hmq : m + 1 = q
  · subst hmq
    rw [show ((forgetToCochainComplex A).obj N).d m (m + 1)
      = ModuleCat.ofHom (N.gradedDifferential m) from toCochainComplex_d N m] at h
    exact ⟨(v : N.M), congrArg Subtype.val h⟩
  · rw [((forgetToCochainComplex A).obj N).shape m q hmq] at h
    refine ⟨0, ?_⟩
    have h0 : (y : N.M) = 0 := by
      have hv := congrArg Subtype.val h.symm
      simpa using hv
    rw [map_zero, h0]

/-- **A homogeneous element whose class in the opcycles vanishes is a differential.** This is
the concrete description of the opcycles as a cokernel. -/
theorem exists_eq_d_of_pOpcycles_eq_zero (N : DifferentialGradedModule.{u, u, u} A) (q : ℤ)
    (y : N.grading q)
    (h : ((forgetToCochainComplex A).obj N).pOpcycles q y = 0) :
    ∃ w : N.M, N.d w = (y : N.M) := by
  have h2 := (CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_zero_iff
    (((forgetToCochainComplex A).obj N).sc q) y).1 h
  obtain ⟨v, hv⟩ := h2
  exact exists_eq_d_of_d_apply N _ q v y hv

/-- **The class in the opcycles of a differential of a homogeneous element vanishes.** -/
theorem pOpcycles_eq_zero_of_eq_d (N : DifferentialGradedModule.{u, u, u} A) (q' q : ℤ) (hq : q' + 1
  = q)
    (y : N.grading q) (w : N.M) (hw : w ∈ N.grading q') (hwy : N.d w = (y : N.M)) :
    ((forgetToCochainComplex A).obj N).pOpcycles q y = 0 := by
  subst hq
  have hd : ((forgetToCochainComplex A).obj N).d q' (q' + 1) ⟨w, hw⟩ = y := by
    rw [show ((forgetToCochainComplex A).obj N).d q' (q' + 1)
      = ModuleCat.ofHom (N.gradedDifferential q') from toCochainComplex_d N q']
    exact Subtype.ext hwy
  rw [← hd, ← ConcreteCategory.comp_apply, HomologicalComplex.d_pOpcycles]
  rfl

/-- Naturality of the projection onto the opcycles, elementwise. -/
theorem opcyclesMap_pOpcycles {N N' : DifferentialGradedModule.{u, u, u} A} (h : N ⟶ N') (q : ℤ)
    (y : N.grading q) :
    HomologicalComplex.opcyclesMap ((forgetToCochainComplex A).map h) q
        (((forgetToCochainComplex A).obj N).pOpcycles q y)
      = ((forgetToCochainComplex A).obj N').pOpcycles q (h.gradedMap q y) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.p_opcyclesMap,
    ConcreteCategory.comp_apply]
  rfl

/-- The kernel of the projection onto a cokernel is the image. -/
theorem Hom.cokernelπ_eq_zero_iff {M N : DifferentialGradedModule.{u, u, u} A} (f : Hom M N) (y :
  N.M) :
    (Hom.cokernelπ f).toFun y = 0 ↔ ∃ x, f.toFun x = y := by
  rw [Hom.cokernelπ_toFun_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

end Opcycles

/-! ### The resolution tower of Stacks 09KU -/

section Resolution

variable (M : DifferentialGradedModule.{u, u, u} A)

/-- **The injection `M ⟶ I₀` of Stacks 09KT**, assembled at the honest type of `M` out of the
restatements of `Module/PropertyIResolution.lean`. `DifferentialGradedModule.resolutionφ M 0` is
a homomorphism out of `resolutionModule M 0`, which is `M` only by default-transparency
unfolding; this is the same homomorphism with `M` itself as its source. -/
def resolutionAug₀ : M ⟶ resolutionI M 0 where
  toFun := resolutionφ₀ M
  map_smul := resolutionφ₀_smul M
  map_grading := resolutionφ₀_grading M
  map_d := LinearMap.ext (resolutionφ₀_d M)

/-- Each injection of the resolution tower is injective, by Stacks 09KT(1). -/
theorem resolutionφ_injective (p : ℕ) : Function.Injective (resolutionφ M p).toFun :=
  (dualResolutionStep (resolutionModule M p)).injective

/-- The `p`-th transition map of the resolution tower is the projection onto the cokernel of `φₚ`
followed by the injection `φ_{p+1}`. -/
private theorem resolutionMap_toFun_apply (p : ℕ) (y : (resolutionI M p).M) :
    (resolutionMap M p).toFun y
      = (resolutionφ M (p + 1)).toFun ((Hom.cokernelπ (resolutionφ M p)).toFun y) := rfl

/-- **The kernel of the `p`-th transition map of the resolution tower is the image of the `p`-th
injection**: `fₚ = (Iₚ ↠ M_{p+1}) ∘ (M_{p+1} ↪ I_{p+1})` with the second map injective, so `fₚ`
kills exactly what the projection onto the cokernel kills. -/
theorem resolutionMap_eq_zero_iff (p : ℕ) (y : (resolutionI M p).M) :
    (resolutionMap M p).toFun y = 0 ↔ ∃ x, (resolutionφ M p).toFun x = y := by
  rw [resolutionMap_toFun_apply]
  refine ⟨fun h => ((resolutionφ M p).cokernelπ_eq_zero_iff y).1
    (resolutionφ_injective M (p + 1) (by rw [h, map_zero])), ?_⟩
  rintro ⟨x, rfl⟩
  rw [((resolutionφ M p).cokernelπ_eq_zero_iff _).2 ⟨x, rfl⟩, map_zero]

/-- Exactness of `M → I₀ → I₁` in each degree: a homogeneous element of `I₀` killed by `f₀` is
the image of a homogeneous element of `M`. -/
theorem exists_mem_grading_resolutionφ₀ (n : ℤ) (y : (resolutionI M 0).M)
    (hy : y ∈ (resolutionI M 0).grading n) (h : (resolutionMap M 0).toFun y = 0) :
    ∃ x ∈ M.grading n, resolutionφ₀ M x = y :=
  (resolutionφ M 0).exists_mem_grading_of_mem_range hy
    ((resolutionMap_eq_zero_iff M 0 y).1 h)

/-- Exactness of `Iₚ → I_{p+1} → I_{p+2}` in each degree: a homogeneous element of `I_{p+1}`
killed by `f_{p+1}` is the image of a homogeneous element of `Iₚ`, because the projection
`Iₚ ↠ M_{p+1}` is surjective in each degree. -/
theorem exists_mem_grading_resolutionMap (p : ℕ) (n : ℤ) (y : (resolutionI M (p + 1)).M)
    (hy : y ∈ (resolutionI M (p + 1)).grading n) (h : (resolutionMap M (p + 1)).toFun y = 0) :
    ∃ z ∈ (resolutionI M p).grading n, (resolutionMap M p).toFun z = y := by
  obtain ⟨x, hx, hxy⟩ := (resolutionφ M (p + 1)).exists_mem_grading_of_mem_range hy
    ((resolutionMap_eq_zero_iff M (p + 1) y).1 h)
  obtain ⟨z, hz, hzx⟩ := (resolutionφ M p).exists_mem_grading_cokernelπ (n := n) hx
  refine ⟨z, hz, ?_⟩
  rw [resolutionMap_toFun_apply, hzx, hxy]

/-- **The double complex `K^{p,q} = Iₚ^q` of the resolution tower of Stacks 09KU.** -/
@[implicit_reducible]
def resolutionDouble :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  towerDouble (resolutionI M) (resolutionMap M) (resolutionMap_resolutionMap M)

/-- The `p`-th differential of the double complex of the resolution tower is `fₚ`. -/
theorem resolutionDouble_d_eq (p : ℕ) :
    (resolutionDouble M).d p (p + 1) = (forgetToCochainComplex A).map (resolutionMap M p) :=
  towerDouble_d (resolutionI M) (resolutionMap M) (resolutionMap_resolutionMap M) p

/-- The composition `M → I₀ → I₁` is zero, so the double complex of the resolution tower can be
augmented by the injection `M ⟶ I₀`. -/
theorem resolutionAug₀_w :
    (forgetToCochainComplex A).map (resolutionAug₀ M) ≫ (resolutionDouble M).d 0 1 = 0 := by
  rw [resolutionDouble_d_eq, ← (forgetToCochainComplex A).map_comp,
    show resolutionAug₀ M ≫ resolutionMap M 0 = 0 from by
      apply Hom.ext; apply LinearMap.ext; intro x; exact resolutionMap_resolutionφ₀ M x,
    Functor.map_zero]

/-- **The augmented complex of complexes `0 → M^• → I₀^• → I₁^• → ⋯`** whose exactness, together
with that of its complexes of cokernels, is what Stacks 09J0 needs. -/
abbrev resolutionAugmented : CochainComplex (CochainComplex (ModuleCat.{u} R) ℤ) ℕ :=
  CochainComplex.augment (resolutionDouble M)
    ((forgetToCochainComplex A).map (resolutionAug₀ M)) (resolutionAug₀_w M)

/-- The `p`-th differential of the double complex of the resolution tower computes `fₚ` on a
homogeneous element. -/
theorem resolutionDouble_d_f_apply (p : ℕ) (n : ℤ) (y : (resolutionI M p).grading n) :
    ((resolutionDouble M).d p (p + 1)).f n y = (resolutionMap M p).gradedMap n y := by
  rw [resolutionDouble_d_eq]
  rfl

/-- The injection `M ⟶ I₀` is injective in each degree. -/
theorem resolutionAug₀_gradedMap_eq_zero (n : ℤ) (x : M.grading n)
    (h : (resolutionAug₀ M).gradedMap n x = 0) : x = 0 := by
  refine Subtype.ext (resolutionφ₀_injective M ?_)
  have hv := congrArg Subtype.val h
  simp only [ZeroMemClass.coe_zero] at hv
  exact hv.trans (map_zero (resolutionφ₀ M)).symm

/-- Exactness of the augmented complex at `I₀`, in each degree. -/
theorem resolutionAugmented_exact_one (n : ℤ) (y : (resolutionI M 0).grading n)
    (h : (resolutionMap M 0).gradedMap n y = 0) :
    ∃ x : M.grading n, (resolutionAug₀ M).gradedMap n x = y := by
  obtain ⟨x, hx, hxy⟩ := exists_mem_grading_resolutionφ₀ M n y.val y.property
    (by have hv := congrArg Subtype.val h; simpa using hv)
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Exactness of the augmented complex at `I_{p+1}`, in each degree. -/
theorem resolutionAugmented_exact_succ (p : ℕ) (n : ℤ) (y : (resolutionI M (p + 1)).grading n)
    (h : (resolutionMap M (p + 1)).gradedMap n y = 0) :
    ∃ z : (resolutionI M p).grading n, (resolutionMap M p).gradedMap n z = y := by
  obtain ⟨z, hz, hzy⟩ := exists_mem_grading_resolutionMap M p n y.val y.property
    (by have hv := congrArg Subtype.val h; simpa using hv)
  exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

/-- **The first exactness hypothesis of Stacks 09J0**: the complex of complexes
`0 → M^• → I₀^• → I₁^• → ⋯` is exact. Exactness in the abelian category of cochain complexes is
degreewise exactness, and degreewise it is the exactness of the resolution tower. -/
theorem acyclic_augment_resolution : (resolutionAugmented M).Acyclic := by
  intro j
  rcases j with _ | p
  · rw [HomologicalComplex.exactAt_iff' (resolutionAugmented M) 0 0 1
      CochainComplex.prev_nat_zero (ComplexShape.next_eq' _ rfl)]
    apply HomologicalComplex.exact_of_degreewise_exact
    intro n
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    refine ⟨0, ?_⟩
    rw [resolutionAug₀_gradedMap_eq_zero M n x₂ hx₂]
    exact map_zero _
  · rw [HomologicalComplex.exactAt_iff' (resolutionAugmented M) p (p + 1) (p + 2)
      (CochainComplex.prev_nat_succ p) (ComplexShape.next_eq' _ rfl)]
    apply HomologicalComplex.exact_of_degreewise_exact
    intro n
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    rcases p with _ | p
    · have hx : (resolutionMap M 0).gradedMap n x₂ = 0 :=
        (resolutionDouble_d_f_apply M 0 n x₂).symm.trans hx₂
      obtain ⟨x, hxy⟩ := resolutionAugmented_exact_one M n x₂ hx
      exact ⟨x, hxy⟩
    · have hx : (resolutionMap M (p + 1)).gradedMap n x₂ = 0 :=
        (resolutionDouble_d_f_apply M (p + 1) n x₂).symm.trans hx₂
      obtain ⟨z, hzy⟩ := resolutionAugmented_exact_succ M p n x₂ hx
      exact ⟨z, (resolutionDouble_d_f_apply M p n z).trans hzy⟩

/-! ### The complexes of cokernels -/

/-- **The core of the second exactness hypothesis of Stacks 09J0.** If the class in
`Coker(d_{I_p})` of a homogeneous element `y` of `Iₚ` is killed by `fₚ`, then that class is the
class of the image of a homogeneous element of `Mₚ`.

The chase: `fₚ(y)` is a differential in `I_{p+1}`, so by Stacks 09KT(2) the class of `y` in
`M_{p+1}` is a differential there, say of `u`; lifting `u` to `v ∈ Iₚ` of degree `q - 1` makes
`y - d v` vanish in `M_{p+1}`, hence equal to the image of some homogeneous `s ∈ Mₚ`; and
`d v` dies in the opcycles. -/
theorem exists_grading_pOpcycles_resolutionφ (p : ℕ) (q : ℤ)
    (y : (resolutionI M p).grading q)
    (h : HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionMap M p)) q
      (((forgetToCochainComplex A).obj (resolutionI M p)).pOpcycles q y) = 0) :
    ∃ s : (resolutionModule M p).grading q,
      ((forgetToCochainComplex A).obj (resolutionI M p)).pOpcycles q
          ((resolutionφ M p).gradedMap q s)
        = ((forgetToCochainComplex A).obj (resolutionI M p)).pOpcycles q y := by
  rw [opcyclesMap_pOpcycles] at h
  obtain ⟨w, hw⟩ := exists_eq_d_of_pOpcycles_eq_zero (resolutionI M (p + 1)) q _ h
  obtain ⟨u, hu⟩ := (dualResolutionStep (resolutionModule M (p + 1))).exists_eq_d
    ((Hom.cokernelπ (resolutionφ M p)).toFun (y : (resolutionI M p).M)) ⟨w, hw⟩
  have hmem : (Hom.cokernelπ (resolutionφ M p)).toFun (y : (resolutionI M p).M)
      ∈ (resolutionModule M (p + 1)).grading q :=
    (Hom.cokernelπ (resolutionφ M p)).map_grading q _ y.property
  obtain ⟨u', hu'mem, hu'⟩ := exists_mem_grading_eq_d (resolutionModule M (p + 1)) hmem hu
  obtain ⟨v, hvmem, hv⟩ := (resolutionφ M p).exists_mem_grading_cokernelπ (n := q - 1) hu'mem
  have hdv : (resolutionI M p).d v ∈ (resolutionI M p).grading q := by
    have hd := (resolutionI M p).d_mem (q - 1) v hvmem
    simpa using hd
  have hker : (Hom.cokernelπ (resolutionφ M p)).toFun
      ((y : (resolutionI M p).M) - (resolutionI M p).d v) = 0 := by
    rw [map_sub]
    have hcd : (Hom.cokernelπ (resolutionφ M p)).toFun ((resolutionI M p).d v)
        = (resolutionModule M (p + 1)).d ((Hom.cokernelπ (resolutionφ M p)).toFun v) :=
      LinearMap.congr_fun (Hom.cokernelπ (resolutionφ M p)).map_d v
    rw [hcd, hv, hu', sub_self]
  obtain ⟨s, hsmem, hs⟩ := (resolutionφ M p).exists_mem_grading_of_mem_range
    (show (y : (resolutionI M p).M) - (resolutionI M p).d v ∈ (resolutionI M p).grading q from
      Submodule.sub_mem _ y.property hdv)
    ((Hom.cokernelπ_eq_zero_iff _ _).1 hker)
  refine ⟨⟨s, hsmem⟩, ?_⟩
  have hz : ((forgetToCochainComplex A).obj (resolutionI M p)).pOpcycles q
      ⟨(resolutionI M p).d v, hdv⟩ = 0 :=
    pOpcycles_eq_zero_of_eq_d (resolutionI M p) (q - 1) q (by ring) ⟨_, hdv⟩ v hvmem rfl
  have heq : (resolutionφ M p).gradedMap q ⟨s, hsmem⟩
      = y - ⟨(resolutionI M p).d v, hdv⟩ := Subtype.ext hs
  rw [heq, map_sub, hz, sub_zero]

/-- If the class in `Coker(d_{I₀})` of the image of a homogeneous `y ∈ M` vanishes then `φ₀(y)`
is a differential, so by Stacks 09KT(2) `y` is one too and its own class vanishes. -/
theorem pOpcycles_eq_zero_of_resolutionAug₀ (q : ℤ) (y : M.grading q)
    (h : HomologicalComplex.opcyclesMap ((forgetToCochainComplex A).map (resolutionAug₀ M)) q
      (((forgetToCochainComplex A).obj M).pOpcycles q y) = 0) :
    ((forgetToCochainComplex A).obj M).pOpcycles q y = 0 := by
  rw [opcyclesMap_pOpcycles] at h
  obtain ⟨w, hw⟩ := exists_eq_d_of_pOpcycles_eq_zero (resolutionI M 0) q _ h
  obtain ⟨v, hv⟩ := (dualResolutionStep (resolutionModule M 0)).exists_eq_d (y : M.M) ⟨w, hw⟩
  obtain ⟨v', hv'mem, hv'⟩ := exists_mem_grading_eq_d M y.property hv
  exact pOpcycles_eq_zero_of_eq_d M (q - 1) q (by ring) y v' hv'mem hv'

/-- **`Coker(d_M) → Coker(d_{I₀})` is injective**, which is Stacks 09KT(2) for the zeroth step
of the resolution. -/
theorem opcycles_resolutionAug₀_eq_zero (q : ℤ)
    (z : ((forgetToCochainComplex A).obj M).opcycles q)
    (h : HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionAug₀ M)) q z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := pOpcycles_surjective M q z
  exact pOpcycles_eq_zero_of_resolutionAug₀ M q y h

/-- Exactness of the complex of cokernels at `Coker(d_{I₀})`. -/
theorem opcycles_exact_one (q : ℤ)
    (x : ((forgetToCochainComplex A).obj (resolutionI M 0)).opcycles q)
    (h : HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionMap M 0)) q x = 0) :
    ∃ z, HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionAug₀ M)) q z = x := by
  obtain ⟨y, rfl⟩ := pOpcycles_surjective (resolutionI M 0) q x
  obtain ⟨s, hs⟩ := exists_grading_pOpcycles_resolutionφ M 0 q y h
  exact ⟨((forgetToCochainComplex A).obj M).pOpcycles q s, by
    rw [opcyclesMap_pOpcycles]; exact hs⟩

/-- Exactness of the complex of cokernels at `Coker(d_{I_{p+1}})`. -/
theorem opcycles_exact_succ (p : ℕ) (q : ℤ)
    (x : ((forgetToCochainComplex A).obj (resolutionI M (p + 1))).opcycles q)
    (h : HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionMap M (p + 1))) q x = 0) :
    ∃ z, HomologicalComplex.opcyclesMap
      ((forgetToCochainComplex A).map (resolutionMap M p)) q z = x := by
  obtain ⟨y, rfl⟩ := pOpcycles_surjective (resolutionI M (p + 1)) q x
  obtain ⟨s, hs⟩ := exists_grading_pOpcycles_resolutionφ M (p + 1) q y h
  obtain ⟨t, htmem, ht⟩ := (resolutionφ M p).exists_mem_grading_cokernelπ (n := q) s.property
  refine ⟨((forgetToCochainComplex A).obj (resolutionI M p)).pOpcycles q ⟨t, htmem⟩, ?_⟩
  rw [opcyclesMap_pOpcycles]
  refine Eq.trans (congrArg (((forgetToCochainComplex A).obj
    (resolutionI M (p + 1))).pOpcycles q) ?_) hs
  refine Subtype.ext ?_
  rw [Hom.gradedMap_apply, Hom.gradedMap_apply, resolutionMap_toFun_apply, ht]

/-- The `p`-th differential of the complex of cokernels is induced by `fₚ`. -/
theorem opcyclesMap_resolutionDouble_d (p : ℕ) (q : ℤ)
    (x : ((forgetToCochainComplex A).obj (resolutionI M p)).opcycles q) :
    HomologicalComplex.opcyclesMap ((resolutionDouble M).d p (p + 1)) q x
      = HomologicalComplex.opcyclesMap
          ((forgetToCochainComplex A).map (resolutionMap M p)) q x := by
  rw [resolutionDouble_d_eq]

/-- **The second exactness hypothesis of Stacks 09J0**: for every `q` the complex of cokernels
`0 → Coker(d_M^q) → Coker(d_{I₀}^q) → Coker(d_{I₁}^q) → ⋯` is exact. -/
theorem acyclic_opcycles_augment_resolution (q : ℤ) :
    (((HomologicalComplex.opcyclesFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
      q).mapHomologicalComplex (ComplexShape.up ℕ)).obj (resolutionAugmented M)).Acyclic := by
  intro j
  rcases j with _ | p
  · rw [HomologicalComplex.exactAt_iff' _ 0 0 1
      CochainComplex.prev_nat_zero (ComplexShape.next_eq' _ rfl),
      CategoryTheory.ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    refine ⟨0, ?_⟩
    rw [opcycles_resolutionAug₀_eq_zero M q x₂ hx₂]
    exact map_zero _
  · rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2)
      (CochainComplex.prev_nat_succ p) (ComplexShape.next_eq' _ rfl),
      CategoryTheory.ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    rcases p with _ | p
    · have hx : HomologicalComplex.opcyclesMap
          ((forgetToCochainComplex A).map (resolutionMap M 0)) q x₂ = 0 :=
        (opcyclesMap_resolutionDouble_d M 0 q x₂).symm.trans hx₂
      exact opcycles_exact_one M q x₂ hx
    · have hx : HomologicalComplex.opcyclesMap
          ((forgetToCochainComplex A).map (resolutionMap M (p + 1))) q x₂ = 0 :=
        (opcyclesMap_resolutionDouble_d M (p + 1) q x₂).symm.trans hx₂
      obtain ⟨z, hz⟩ := opcycles_exact_succ M p q x₂ hx
      exact ⟨z, (opcyclesMap_resolutionDouble_d M p q z).trans hz⟩

/-! ### Quasi-isomorphy of the augmentation -/

/-- **Stacks 09KU, second half: the augmentation `M ⟶ I` of the resolution tower is a
quasi-isomorphism.** Stacks 09J0, in the bridged form
`HomologicalComplex₂.quasiIso_of_isProductTotal`, is applied to the double complex
`K^{p,q} = Iₚ^q`, the identification of the complex of abelian groups underlying `I` with
`Tot_π(K)`, and the two exactness statements above. -/
theorem quasiIso_resolutionAug :
    QuasiIso ((forgetToCochainComplex A).map (resolutionAug M)) :=
  HomologicalComplex₂.quasiIso_of_isProductTotal
    (K := resolutionDouble M)
    ((forgetToCochainComplex A).map (resolutionAug₀ M)) (resolutionAug₀_w M)
    ((forgetToCochainComplex A).map (resolutionAug M))
    (acyclic_augment_resolution M) (acyclic_opcycles_augment_resolution M)
    (towerTotalProductTotalIso (resolutionI M) (resolutionMap M) (resolutionMap_resolutionMap M))
    (toProductTotal_towerTotal (resolutionI M) (resolutionMap M) (resolutionMap_resolutionMap M)
      M (resolutionAug M) (resolutionAug₀ M)
      (resolutionTotal.π_resolutionAug_zero M)
      (fun i x => resolutionTotal.π_resolutionAug_succ M i x)
      (resolutionAug₀_w M))

end Resolution

end DifferentialGradedModule

end
