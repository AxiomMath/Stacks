module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison

@[expose] public section

/-!
# The exterior power of a direct sum of sheaves of modules

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, and `F`, `G` sheaves of
`O♯`-modules with chosen exterior algebras. For each `n` the wedge product assembles a morphism
of sheaves of modules

`⨁_{p + q = n} (⋀ᵖ F ⊗_{O♯} ⋀^q G) ⟶ ⋀ⁿ (F ⊞ G)`,

namely the one whose `(p, q)`-component multiplies the images of the two factors under the
functorial maps `⋀ᵖ F ⟶ ⋀ᵖ (F ⊞ G)` and `⋀^q G ⟶ ⋀^q (F ⊞ G)`, and this morphism is an
isomorphism. This is the Künneth decomposition of an exterior power, upgraded from the stalkwise
statement of `SheafOfModules.exteriorPowerBiprodStalkEquivDirectSum` to an isomorphism of
sheaves.

## Main definitions

* `SheafOfModules.prodWedgeHom`: the `(p, q)`-component `⋀ᵖ F ⊗ ⋀^q G ⟶ ⋀^{p+q} H` attached to a
  pair of morphisms `F ⟶ H`, `G ⟶ H`: the tensor product of the two functorial maps on exterior
  powers, followed by the multiplication of the exterior algebra of `H`.
* `SheafOfModules.exteriorPowerProdSummand` and `SheafOfModules.exteriorPowerProdHom`: the
  summands of the direct sum, and the morphism out of it obtained from the components by the
  universal property of the coproduct.
* `SheafOfModules.exteriorPowerBiprodHom` and `SheafOfModules.exteriorPowerBiprodIso`: the
  comparison for a binary biproduct, and the isomorphism it is.

## Main results

* `Stacks.GradedAlgebra.mul_homogeneousProd`: the product of two ordered products of degree-one
  local sections of a graded algebra is the ordered product of the concatenated family.
* `SheafOfModules.prodWedgeHom_tensorSheafUnit`: the component morphism, computed on the image of
  a pure tensor of two wedges of local sections.
* `SheafOfModules.span_germWedgeSet_eq_top`: germs of wedges of local sections span the stalk of
  an exterior power.
* `SheafOfModules.stalkMapL_prodWedgeHom`: the stalk of the component morphism, read through the
  stalkwise Künneth decomposition, is the inclusion of the `(p, q)` summand.
* `SheafOfModules.exteriorPowerStalkEquivDirectSumOfSplit_comp_stalkCoprodEquiv`: the stalk of
  the comparison morphism, read through the identifications of both stalks, is the direct sum of
  the comparisons of Tag 01CB.
* `SheafOfModules.isIso_exteriorPowerProdHom` and
  `SheafOfModules.isIso_exteriorPowerBiprodHom`: the comparison morphism is an isomorphism, for
  an arbitrary splitting datum and for a binary biproduct.

## Implementation notes

The index set of the direct sum is `ULift {pq : ℕ × ℕ // pq.1 + pq.2 = n}`: the coproduct of a
family of sheaves of modules on `X : TopCat.{u}` and the identification of its stalk with the
direct sum of the stalks (`SheafOfModules.stalkCoprodEquiv`) are available for index types in
`Type u`, and the antidiagonal lives in `Type 0`.

The multiplication of a `SheafOfModules.GradedAlgebra` is given only on local sections, as a
`SheafOfModules.BilinearMap`; the morphism out of the sheafified tensor product that it descends
to is `SheafOfModules.GradedAlgebra.mulSheaf`, and `mulSheaf_unit` is the section formula that
makes it computable. Everything below is then pinned down on the image of a pure tensor of two
wedges of local sections, and germs of such sections span every stalk, which is what the
identification of the stalk map rests on.
-/

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace Opposite
open scoped DirectSum TensorProduct

universe v u w a

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc)

/-- **The product of two ordered products of degree-one local sections is the ordered product of
the concatenated family.** Both sides have degree `p + q`, and the two spellings `(p : ℤ) + (q :ℤ)`
and `((p + q : ℕ) : ℤ)` of that degree are definitionally equal, so no transport appears. -/
theorem mul_homogeneousProd (U : Cᵒᵖ) (p q : ℕ)
    (z : Fin p → (Pc 1).obj U) (w : Fin q → (Pc 1).obj U) :
    (A.mul (p : ℤ) (q : ℤ)).app U (A.homogeneousProd U p z) (A.homogeneousProd U q w) =
      A.homogeneousProd U (p + q) (Fin.append z w) := by
  have hlist : (List.ofFn fun i => A.incl 1 (Fin.append z w i)) =
      (List.ofFn fun i => A.incl (X := U) 1 (z i)) ++ (List.ofFn fun i => A.incl 1 (w i)) := by
    rw [show (fun i => A.incl (X := U) 1 (Fin.append z w i)) =
      (fun y => A.incl (X := U) 1 y) ∘ Fin.append z w from rfl, ← List.map_ofFn,
      List.ofFn_fin_append, List.map_append, List.map_ofFn, List.map_ofFn]
    rfl
  have h1 : A.incl ((p : ℤ) + (q : ℤ))
        ((A.mul (p : ℤ) (q : ℤ)).app U (A.homogeneousProd U p z) (A.homogeneousProd U q w)) =
      A.incl ((p : ℤ) + (q : ℤ)) (A.homogeneousProd U (p + q) (Fin.append z w)) := by
    rw [← A.incl_mul_incl (p : ℤ) (q : ℤ), A.incl_homogeneousProd, A.incl_homogeneousProd,
      show A.incl ((p : ℤ) + (q : ℤ)) (A.homogeneousProd U (p + q) (Fin.append z w)) =
        (List.ofFn fun i => A.incl 1 (Fin.append z w i)).prod from
        A.incl_homogeneousProd U (p + q) (Fin.append z w), hlist, List.prod_append]
  exact ((A.proj_incl U ((p : ℤ) + (q : ℤ)) _).symm.trans
    (congrArg (A.proj U ((p : ℤ) + (q : ℤ))) h1)).trans
      (A.proj_incl U ((p : ℤ) + (q : ℤ)) _)

end Stacks.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}} {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)}
  {M N : SheafOfModules.{w} (toRingCat J Osharp)}

/-- A unital homomorphism of sheaves of graded algebras which extends a morphism `f : M ⟶ N` of
sheaves of modules carries the ordered product of the images of `s₀, …, s_{p-1}` under the
degree-one generator of its source to the ordered product of the images of `f s₀, …, f s_{p-1}`
under the degree-one generator of its target. -/
theorem UnitalHom.app_homogeneousProd_comp {ii : M ⟶ A.piece 1} {kk : N ⟶ B.piece 1}
    (g : UnitalHom A B) (f : M ⟶ N) (hg : ii ≫ g.app 1 = f ≫ kk) (V : Cᵒᵖ) (p : ℕ)
    (s : Fin p → M.val.obj V) :
    (g.app (p : ℤ)).val.app V (A.toPresheafGradedAlgebra.homogeneousProd V p
        fun i => ii.val.app V (s i)) =
      B.toPresheafGradedAlgebra.homogeneousProd V p
        fun i => kk.val.app V (f.val.app V (s i)) := by
  refine (g.app_homogeneousProd V p _).trans ?_
  refine congrArg (B.toPresheafGradedAlgebra.homogeneousProd V p) (funext fun i => ?_)
  exact congrArg (fun h : M ⟶ B.piece 1 => h.val.app V (s i)) hg

end SheafOfModules.GradedAlgebra

namespace Stacks

/-! ### Generic lemmas on exterior powers of a product of modules -/

section Generic

variable {R : Type*} [CommRing R]

/-- The equivalence of exterior powers induced by a linear equivalence takes a wedge of vectors
to the wedge of their images. -/
theorem exteriorPowerCongr_ιMulti {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (n : ℕ) (e : M ≃ₗ[R] N) (w : Fin n → M) :
    exteriorPowerCongr n e (exteriorPower.ιMulti R n w) =
      exteriorPower.ιMulti R n fun i => e (w i) := by
  refine Subtype.ext ?_
  rw [exteriorPowerCongr_coe, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti]
  rfl

/-- The inverse of the Künneth decomposition of `⋀^{p+q} (M × N)` takes the `(p, q)` block
generator `(a₀ ∧ ⋯) ⊗ (b₀ ∧ ⋯)` to the wedge of the `aᵢ` pushed into the first factor followed by
the `bⱼ` pushed into the second. -/
theorem prodEquivDirectSum_symm_lof_ιMulti {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (p q : ℕ)
    (a : Fin p → M) (b : Fin q → N) :
    (exteriorPower.prodEquivDirectSum (R := R) (M := M) (N := N) (p + q)).symm
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(p, q), rfl⟩
          (exteriorPower.ιMulti R p a ⊗ₜ[R] exteriorPower.ιMulti R q b)) =
      exteriorPower.ιMulti R (p + q)
        (Fin.append (fun i => LinearMap.inl R M N (a i)) fun j => LinearMap.inr R M N (b j)) := by
  refine Subtype.ext ?_
  rw [exteriorPower.prodEquivDirectSum_symm_lof_tmul_coe, exteriorPower.ιMulti_apply_coe,
    exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.ιMulti_mul_ιMulti]
  rfl

/-- The Künneth decomposition of `⋀^{p+q} (M × N)` takes the wedge of `p` vectors from the first
factor followed by `q` vectors from the second to the `(p, q)` block generator. -/
theorem prodEquivDirectSum_ιMulti_append {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (p q : ℕ)
    (a : Fin p → M) (b : Fin q → N) :
    exteriorPower.prodEquivDirectSum (R := R) (M := M) (N := N) (p + q)
        (exteriorPower.ιMulti R (p + q)
          (Fin.append (fun i => LinearMap.inl R M N (a i)) fun j => LinearMap.inr R M N (b j))) =
      DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
        (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(p, q), rfl⟩
        (exteriorPower.ιMulti R p a ⊗ₜ[R] exteriorPower.ιMulti R q b) := by
  rw [← prodEquivDirectSum_symm_lof_ιMulti p q a b, LinearEquiv.apply_symm_apply]

/-- A summandwise family of linear equivalences, read on the `i`-th summand of a direct sum, is
the `i`-th member of the family. -/
theorem mapRange_linearEquiv_lof {ι : Type*} [DecidableEq ι]
    (β₁ β₂ : ι → Type*) [∀ i, AddCommGroup (β₁ i)] [∀ i, Module R (β₁ i)]
    [∀ i, AddCommGroup (β₂ i)] [∀ i, Module R (β₂ i)]
    (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) (i : ι) (z : β₁ i) :
    DFinsupp.mapRange.linearEquiv e (DirectSum.lof R ι β₁ i z) =
      DirectSum.lof R ι β₂ i (e i z) := by
  rw [DFinsupp.mapRange.linearEquiv_apply]
  exact DFinsupp.mapRange_single

/-- **The Künneth decomposition on a wedge of split vectors.** Suppose `MH` is identified with
`MF × MG`, and the degreewise identifications `SF k ≅ ⋀^k MF`, `SG k ≅ ⋀^k MG` are given. A wedge
of `p + q` vectors of `MH` whose images under the splitting are the `aᵢ` pushed into the first
factor followed by the `bⱼ` pushed into the second goes to the `(p, q)` block generator
`(a₀ ∧ ⋯) ⊗ (b₀ ∧ ⋯)`.

This is the algebraic heart of the identification of the stalk map of the comparison morphism:
all of the sheaf-theoretic content enters through the four hypotheses. -/
theorem exteriorPowerProdDirectSum_ιMulti {MF MG MH : Type*} [AddCommGroup MF] [Module R MF]
    [AddCommGroup MG] [Module R MG] [AddCommGroup MH] [Module R MH]
    {SF SG : ℕ → Type*} [∀ k, AddCommGroup (SF k)] [∀ k, Module R (SF k)]
    [∀ k, AddCommGroup (SG k)] [∀ k, Module R (SG k)]
    (eF : ∀ k, SF k ≃ₗ[R] ⋀[R]^k MF) (eG : ∀ k, SG k ≃ₗ[R] ⋀[R]^k MG)
    (e₀ : MH ≃ₗ[R] MF × MG) (p q : ℕ)
    (a : Fin p → MF) (b : Fin q → MG) (w : Fin (p + q) → MH)
    (hw : (fun i => e₀ (w i)) = Fin.append (fun i => LinearMap.inl R MF MG (a i))
      fun j => LinearMap.inr R MF MG (b j))
    (zF : SF p) (hzF : eF p zF = exteriorPower.ιMulti R p a)
    (zG : SG q) (hzG : eG q zG = exteriorPower.ιMulti R q b) :
    DFinsupp.mapRange.linearEquiv (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p + q} =>
        TensorProduct.congr (eF pq.1.1).symm (eG pq.1.2).symm)
        (exteriorPower.prodEquivDirectSum (p + q)
          (exteriorPowerCongr (p + q) e₀ (exteriorPower.ιMulti R (p + q) w))) =
      DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
        (fun pq => TensorProduct R (SF pq.1.1) (SG pq.1.2)) ⟨(p, q), rfl⟩ (zF ⊗ₜ[R] zG) := by
  rw [exteriorPowerCongr_ιMulti, hw, prodEquivDirectSum_ιMulti_append]
  refine Eq.trans (mapRange_linearEquiv_lof
    (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p + q} =>
      TensorProduct R ↥(⋀[R]^pq.1.1 MF) ↥(⋀[R]^pq.1.2 MG))
    (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p + q} =>
      TensorProduct R (SF pq.1.1) (SG pq.1.2))
    (fun pq => TensorProduct.congr (eF pq.1.1).symm (eG pq.1.2).symm) ⟨(p, q), rfl⟩
    (exteriorPower.ιMulti R p a ⊗ₜ[R] exteriorPower.ιMulti R q b)) ?_
  rw [TensorProduct.congr_tmul, ← hzF, ← hzG, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- Reading an equality of linear maps `f ∘ T⁻¹ = g` at a point: `f z = g (T z)`. -/
theorem apply_of_comp_symm_eq {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (T : M ≃ₗ[R] N) (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (h : f.comp T.symm.toLinearMap = g) (z : M) : f z = g (T z) := by
  have hz := LinearMap.congr_fun h (T z)
  rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hz

section ULiftDirectSum

variable {R : Type*} [CommRing R] {ι : Type u} [DecidableEq ι]
  {beta : ULift.{v} ι → Type*} {gamma : ι → Type*}
  [∀ i, AddCommMonoid (beta i)] [∀ i, Module R (beta i)]
  [∀ i, AddCommMonoid (gamma i)] [∀ i, Module R (gamma i)]
  (e : ∀ i : ULift.{v} ι, beta i ≃ₗ[R] gamma i.down)

/-- **The comparison from a direct sum indexed by a `ULift` of an index type to the direct sum
over the index type itself**, assembled from a family of linear equivalences between the
summands. -/
noncomputable def directSumUliftComparison :
    DirectSum (ULift.{v} ι) beta →ₗ[R] DirectSum ι gamma :=
  DirectSum.toModule R (ULift.{v} ι) (DirectSum ι gamma)
    fun i => (DirectSum.lof R ι gamma i.down).comp (e i).toLinearMap

/-- The inverse of `Stacks.directSumUliftComparison`. -/
noncomputable def directSumUliftComparisonInv :
    DirectSum ι gamma →ₗ[R] DirectSum (ULift.{v} ι) beta :=
  DirectSum.toModule R ι (DirectSum (ULift.{v} ι) beta)
    fun k => (DirectSum.lof R (ULift.{v} ι) beta (ULift.up k)).comp
      (e (ULift.up k)).symm.toLinearMap

/-- The inverse comparison is a left inverse. -/
theorem directSumUliftComparisonInv_comp :
    (directSumUliftComparisonInv e).comp (directSumUliftComparison e) = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, directSumUliftComparison,
    DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe,
    directSumUliftComparisonInv, DirectSum.toModule_lof,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/-- The inverse comparison is a right inverse. -/
theorem directSumUliftComparison_comp_inv :
    (directSumUliftComparison e).comp (directSumUliftComparisonInv e) = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, directSumUliftComparisonInv,
    DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe,
    directSumUliftComparison, DirectSum.toModule_lof,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- The comparison on the `i`-th summand is the `i`-th member of the family. -/
theorem directSumUliftComparison_lof (i : ULift.{v} ι) (t : beta i) :
    directSumUliftComparison e (DirectSum.lof R (ULift.{v} ι) beta i t) =
      DirectSum.lof R ι gamma i.down (e i t) := by
  rw [directSumUliftComparison, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

/-- **The comparison is bijective.** -/
theorem bijective_directSumUliftComparison : Function.Bijective (directSumUliftComparison e) :=
  Function.bijective_iff_has_inverse.2 ⟨directSumUliftComparisonInv e,
    fun z => LinearMap.congr_fun (directSumUliftComparisonInv_comp e) z,
    fun z => LinearMap.congr_fun (directSumUliftComparison_comp_inv e) z⟩


end ULiftDirectSum

/-- **Bijectivity transported along a factorization.** If a linear map `f`, pre-composed with a
linear equivalence and post-composed with another, is a bijective linear map, then `f` is
bijective. -/
theorem bijective_of_comp_eq {R : Type*} [CommRing R] {M N P Q : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q]
    (E : P ≃ₗ[R] Q) (f : N →ₗ[R] P) (T : M ≃ₗ[R] N) (g : M →ₗ[R] Q)
    (h : E.toLinearMap.comp (f.comp T.toLinearMap) = g) (hg : Function.Bijective g) :
    Function.Bijective f := by
  have hfun : (f : N → P) = fun y => E.symm (g (T.symm y)) := by
    refine funext fun y => ?_
    have hy := LinearMap.congr_fun h (T.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hy
    rw [← hy, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact E.symm.bijective.comp (hg.comp T.symm.bijective)

end Generic

/-- **Two linear maps out of a tensor product agree as soon as they agree on the pure tensors of
pairs drawn from spanning sets of the two factors.** -/
theorem TensorProduct.linearMap_ext_of_span₂ {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    {SM : Set M} {SN : Set N} (hM : Submodule.span R SM = ⊤) (hN : Submodule.span R SN = ⊤)
    (f g : TensorProduct R M N →ₗ[R] P)
    (h : ∀ m ∈ SM, ∀ n ∈ SN, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) :
    f = g := by
  have step : ∀ n ∈ SN, ∀ m : M, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n) := by
    intro n hn
    have := LinearMap.ext_on (R := R) (s := SM) hM
      (f := f.comp ((_root_.TensorProduct.mk R M N).flip n))
      (g := g.comp ((_root_.TensorProduct.mk R M N).flip n))
      (fun m hm => h m hm n hn)
    exact fun m => LinearMap.congr_fun this m
  refine _root_.TensorProduct.ext' fun m n => ?_
  have := LinearMap.ext_on (R := R) (s := SN) hN
    (f := f.comp (_root_.TensorProduct.mk R M N m))
    (g := g.comp (_root_.TensorProduct.mk R M N m))
    (fun n hn => step n hn m)
  exact LinearMap.congr_fun this n

end Stacks

namespace SheafOfModules

/-! ### The stalk of a split sheaf of modules, on germs -/

section Split

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk map of `g` applied to the germ of the image of a section under `f` is the germ of
its image under any morphism `h` with `f ≫ g = h`. -/
theorem stalkMapL_germ_comp (x : ↥X)
    {M N P : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (f : M ⟶ N) (g : N ⟶ P) (h : M ⟶ P) (hfg : f ≫ g = h) (U : Opens ↥X) (hx : x ∈ U)
    (m : M.val.obj (op U)) :
    PresheafOfModules.stalkMapL x g.val
        (TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) m)) =
      TopCat.Presheaf.germ P.val.presheaf U x hx (h.val.app (op U) m) :=
  (PresheafOfModules.stalkMapL_germ x g.val U hx (f.val.app (op U) m)).trans
    (congrArg (fun k : M ⟶ P => TopCat.Presheaf.germ P.val.presheaf U x hx (k.val.app (op U) m))
      hfg)

variable (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
  (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G) (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
  (htot : pF ≫ iF + pG ≫ iG = 𝟙 H)

/-- The splitting of a stalk carries the germ of a section coming from `F` to that germ, placed
in the first factor. -/
theorem stalkProdEquivOfSplit_germ_left (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot
        (TopCat.Presheaf.germ H.val.presheaf U x hx (iF.val.app (op U) m)) =
      LinearMap.inl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  rw [stalkProdEquivOfSplit_apply]
  refine Prod.ext ?_ ?_
  · exact stalkMapL_germ_comp x iF pF (𝟙 F) hF U hx m
  · exact (stalkMapL_germ_comp x iF pG 0 hFG U hx m).trans (map_zero _)

/-- The splitting of a stalk carries the germ of a section coming from `G` to that germ, placed
in the second factor. -/
theorem stalkProdEquivOfSplit_germ_right (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : G.val.obj (op U)) :
    stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot
        (TopCat.Presheaf.germ H.val.presheaf U x hx (iG.val.app (op U) m)) =
      LinearMap.inr ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)
        (TopCat.Presheaf.germ G.val.presheaf U x hx m) := by
  rw [stalkProdEquivOfSplit_apply]
  refine Prod.ext ?_ ?_
  · exact (stalkMapL_germ_comp x iG pF 0 hGF U hx m).trans (map_zero _)
  · exact stalkMapL_germ_comp x iG pG (𝟙 G) hG U hx m

end Split

/-! ### Stalk maps, and germs of wedges of local sections -/

section Germs

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)

/-- The stalk map of `AlgebraicGeometry.SheafOfModules.stalkFunctor` and the stalk map
`PresheafOfModules.stalkMapL` of the underlying presheaf of modules are the same function. Both
send the germ of a section to the germ of its image, and every element of a stalk is a germ. -/
theorem stalkMap_hom_eq_stalkMapL (x : ↥X)
    {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (f : M ⟶ N)
    (m : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x f).hom m =
      PresheafOfModules.stalkMapL x f.val m := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  exact (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x f U hU s).trans
    (PresheafOfModules.stalkMapL_germ x f.val U hU s).symm

/-- The germs at `x` of the wedges `s₀ ∧ ⋯ ∧ s_{p-1}` of local sections of `F`, as a subset of
the stalk of `⋀ᵖ F`; each wedge is written with the data of the exterior algebra alone, as the
ordered product of the images of the `sᵢ` under its degree-one generator. -/
def germWedgeSet (p : ℕ) (x : ↥X) :
    Set ↑(TopCat.Presheaf.stalk (AF.exteriorPower p).val.presheaf x) :=
  {z | ∃ (U : Opens ↥X) (hx : x ∈ U) (s : Fin p → F.val.obj (op U)),
    z = TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hx
      (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
        fun i => AF.exteriorGenerator.val.app (op U) (s i))}

/-- Every wedge of germs is the germ of a wedge of local sections: a finite family of germs is a
family of germs of sections over one common neighbourhood, and the comparison of Tag 01CH in
degree `p` carries the germ of the wedge of those sections to the wedge of the germs. -/
theorem symm_ιMulti_mem_germWedgeSet (p : ℕ) (x : ↥X)
    (v : Fin p → ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    (AF.exteriorPowerStalkEquiv p x).symm
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p v) ∈
      germWedgeSet AF p x := by
  choose U hU s hs using fun i : Fin p => TopCat.Presheaf.exists_germ_eq F.val.presheaf (v i)
  have hW : x ∈ (⨅ i, U i : Opens ↥X) := by
    have h : x ∈ (↑(⨅ i, U i) : Set ↥X) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    exact h
  refine ⟨(⨅ i, U i : Opens ↥X), hW, fun i => F.val.map (homOfLE (iInf_le U i)).op (s i), ?_⟩
  refine (LinearEquiv.symm_apply_eq (AF.exteriorPowerStalkEquiv p x)).2 ?_
  refine Eq.trans ?_ (exteriorPowerStalkEquiv_germ_homogeneousProd
    AF.exterior AF.exteriorGenerator AF.exterior_isExteriorAlgebra p x
    (⨅ i, U i : Opens ↥X) hW (fun i => F.val.map (homOfLE (iInf_le U i)).op (s i))).symm
  exact congrArg (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p)
    (funext fun i => ((TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE (iInf_le U i)) x hW (s i)).trans (hs i)).symm)

/-- **Germs of wedges of local sections span the stalk of an exterior power.** The stalk of
`⋀ᵖ F` at `x` is `⋀ᵖ (F_x)` (Tag 01CH in degree `p`), in which the wedges of germs span, and
every wedge of germs is a germ of a wedge of local sections
(`SheafOfModules.symm_ιMulti_mem_germWedgeSet`). -/
theorem span_germWedgeSet_eq_top (p : ℕ) (x : ↥X) :
    Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x) (germWedgeSet AF p x) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  have hspan : ∀ y ∈ Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        (Set.range (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p
          (M := ↑(TopCat.Presheaf.stalk F.val.presheaf x)))),
      (AF.exteriorPowerStalkEquiv p x).symm y ∈
        Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x) (germWedgeSet AF p x) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        exact Submodule.subset_span (symm_ιMulti_mem_germWedgeSet AF p x v)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha
  have hz := hspan (AF.exteriorPowerStalkEquiv p x z)
    (by rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top)
  rwa [LinearEquiv.symm_apply_apply] at hz

/-- Tag 01CH in degree `p`, for a package of the three algebras: the germ of the wedge
`s₀ ∧ ⋯ ∧ s_{p-1}` of local sections goes to the wedge of the germs. -/
theorem exteriorPowerStalkEquiv_germ_wedge (p : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin p → F.val.obj (op U)) :
    AF.exteriorPowerStalkEquiv p x
        (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hx
          (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
            fun i => AF.exteriorGenerator.val.app (op U) (s i))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p
        fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (s i) :=
  exteriorPowerStalkEquiv_germ_homogeneousProd AF.exterior AF.exteriorGenerator
    AF.exterior_isExteriorAlgebra p x U hx s

/-- The inverse form of `SheafOfModules.exteriorPowerStalkEquiv_germ_wedge`: a wedge of germs of
local sections is the germ of the wedge of those sections. -/
theorem exteriorPowerStalkEquiv_symm_ιMulti_germ (p : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin p → F.val.obj (op U)) :
    (AF.exteriorPowerStalkEquiv p x).symm
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p
          fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (s i)) =
      TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hx
        (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun i => AF.exteriorGenerator.val.app (op U) (s i)) :=
  (LinearEquiv.symm_apply_eq _).2 (exteriorPowerStalkEquiv_germ_wedge AF p x U hx s).symm

/-- A wedge of local sections may be shrunk to a smaller neighbourhood of the point without
changing its germ: restricting the sections and wedging again gives the same germ. -/
theorem germ_homogeneousProd_res (p : ℕ) (x : ↥X) {U V : Opens ↥X} (hUV : V ≤ U)
    (hxU : x ∈ U) (hxV : x ∈ V) (s : Fin p → F.val.obj (op U)) :
    TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hxU
        (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun i => AF.exteriorGenerator.val.app (op U) (s i)) =
      TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf V x hxV
        (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op V) p
          fun i => AF.exteriorGenerator.val.app (op V) (F.val.map (homOfLE hUV).op (s i))) := by
  refine Eq.trans (TopCat.Presheaf.germ_res_apply (AF.exteriorPower p).val.presheaf
    (homOfLE hUV) x hxV (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
      fun i => AF.exteriorGenerator.val.app (op U) (s i))).symm ?_
  refine congrArg (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf V x hxV) ?_
  refine Eq.trans (AF.exterior.toPresheafGradedAlgebra.homogeneousProd_naturality
    (homOfLE hUV).op p (fun i => AF.exteriorGenerator.val.app (op U) (s i))) ?_
  exact congrArg (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op V) p)
    (funext fun i => (PresheafOfModules.naturality_apply AF.exteriorGenerator.val
      (homOfLE hUV).op (s i)).symm)

end Germs

/-! ### The stalk of a tensor product of exterior powers, on germs -/

section TwoBundles

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)

/-- A pure tensor of two germs of wedges of local sections, pulled back along the comparison of
Tag 01CB, is the germ of the image of the pure tensor of the two wedges restricted to a common
neighbourhood. -/
theorem tensorSheafStalkEquiv_symm_germ_wedge (p q : ℕ) (x : ↥X) {U V W : Opens ↥X}
    (hWU : W ≤ U) (hWV : W ≤ V) (hxU : x ∈ U) (hxV : x ∈ V) (hxW : x ∈ W)
    (s : Fin p → F.val.obj (op U)) (t : Fin q → G.val.obj (op V)) :
    (PresheafOfModules.tensorSheafStalkEquiv Osharp (AF.exteriorPower p)
          (AG.exteriorPower q) x).symm
        (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hxU
            (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
              fun i => AF.exteriorGenerator.val.app (op U) (s i)) ⊗ₜ
          TopCat.Presheaf.germ (AG.exteriorPower q).val.presheaf V x hxV
            (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op V) q
              fun j => AG.exteriorGenerator.val.app (op V) (t j))) =
      PresheafOfModules.tensorSheafGerm Osharp (AF.exteriorPower p) (AG.exteriorPower q) x W hxW
        (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op W) p
          fun i => AF.exteriorGenerator.val.app (op W) (F.val.map (homOfLE hWU).op (s i)))
        (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op W) q
          fun j => AG.exteriorGenerator.val.app (op W) (G.val.map (homOfLE hWV).op (t j))) := by
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  refine Eq.trans (congrArg₂ (fun y z => y ⊗ₜ z)
    (germ_homogeneousProd_res AF p x hWU hxU hxW s)
    (germ_homogeneousProd_res AG q x hWV hxV hxW t)) ?_
  exact (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp (AF.exteriorPower p)
    (AG.exteriorPower q) x W hxW _ _).symm

end TwoBundles

/-! ### The wedge-product component morphism -/

section WedgeHom

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **The wedge product `⋀ᵖ F ⊗ ⋀^q G ⟶ ⋀^{p+q} H`** attached to morphisms `iF : F ⟶ H` and
`iG : G ⟶ H`: tensor the two functorial maps on exterior powers, then multiply in the exterior
algebra of `H`. -/
noncomputable def prodWedgeHom (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower p)).obj
        (AG.exteriorPower q) ⟶
      A.exteriorPower (p + q) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map (AF.exterior_isExteriorAlgebra.pieceMap
      A.exterior_isExteriorAlgebra iF (p : ℤ))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).map
          (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ))) ≫
    GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)

/-- **The wedge-product component morphism on a pure tensor of two wedges of local sections.**
It takes the image of `(s₀ ∧ ⋯ ∧ s_{p-1}) ⊗ (t₀ ∧ ⋯ ∧ t_{q-1})` to the wedge
`iF s₀ ∧ ⋯ ∧ iF s_{p-1} ∧ iG t₀ ∧ ⋯ ∧ iG t_{q-1}`, each wedge being written as the ordered
product of the images of the sections under the relevant degree-one generator. -/
theorem prodWedgeHom_tensorSheafUnit (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (s : Fin p → F.val.obj U) (t : Fin q → G.val.obj U) :
    (prodWedgeHom AF AG A iF iG p q).val.app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower p) (AG.exteriorPower q)).app U
          (AF.exterior.toPresheafGradedAlgebra.homogeneousProd U p
              (fun i => AF.exteriorGenerator.val.app U (s i)) ⊗ₜ
            AG.exterior.toPresheafGradedAlgebra.homogeneousProd U q
              fun j => AG.exteriorGenerator.val.app U (t j))) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd U (p + q)
        (Fin.append (fun i => A.exteriorGenerator.val.app U (iF.val.app U (s i)))
          fun j => A.exteriorGenerator.val.app U (iG.val.app U (t j))) := by
  have hmap := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    Osharp (AF.exteriorPower p) (AG.exteriorPower q)
    ((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app (p : ℤ))
    ((AG.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iG).app (q : ℤ)) U
    (AF.exterior.toPresheafGradedAlgebra.homogeneousProd U p
      fun i => AF.exteriorGenerator.val.app U (s i))
    (AG.exterior.toPresheafGradedAlgebra.homogeneousProd U q
      fun j => AG.exteriorGenerator.val.app U (t j))
  have hF := GradedAlgebra.UnitalHom.app_homogeneousProd_comp
    (AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF) iF
    (AF.exterior_isExteriorAlgebra.map_app_one A.exterior_isExteriorAlgebra iF) U p s
  have hG := GradedAlgebra.UnitalHom.app_homogeneousProd_comp
    (AG.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iG) iG
    (AG.exterior_isExteriorAlgebra.map_app_one A.exterior_isExteriorAlgebra iG) U q t
  have hmul := GradedAlgebra.mulSheaf_unit A.exterior (p : ℤ) (q : ℤ) U
    (A.exterior.toPresheafGradedAlgebra.homogeneousProd U p
      fun i => A.exteriorGenerator.val.app U (iF.val.app U (s i)))
    (A.exterior.toPresheafGradedAlgebra.homogeneousProd U q
      fun j => A.exteriorGenerator.val.app U (iG.val.app U (t j)))
  refine Eq.trans (congrArg
    (fun z => (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)).val.app U z) hmap) ?_
  refine Eq.trans (congrArg
    (fun z => (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)).val.app U
      ((PresheafOfModules.tensorSheafUnit (A.exterior.piece (p : ℤ))
        (A.exterior.piece (q : ℤ))).app U z))
    (congrArg₂ (fun y z => y ⊗ₜ z) hF hG)) ?_
  exact hmul.trans (A.exterior.toPresheafGradedAlgebra.mul_homogeneousProd U p q
    (fun i => A.exteriorGenerator.val.app U (iF.val.app U (s i)))
    (fun j => A.exteriorGenerator.val.app U (iG.val.app U (t j))))


/-- Applying a function pointwise to a concatenated family concatenates the images. -/
private theorem comp_fin_append {α β : Type*} (f : α → β) {p q : ℕ} (a : Fin p → α)
    (b : Fin q → α) :
    (fun i => f (Fin.append a b i)) = Fin.append (fun i => f (a i)) fun j => f (b j) := by
  refine funext (Fin.addCases (fun i => ?_) fun j => ?_)
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- The Künneth decomposition of a stalk, written out as the composite of its four factors: the
comparison of Tag 01CH in degree `n`, transport along the splitting of the stalk, the Künneth
decomposition of an exterior power of a product of modules, and the degreewise comparisons of
Tag 01CH for the two summands. -/
theorem exteriorPowerStalkEquivDirectSumOfSplit_apply (n : ℕ) (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G) (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H)
    (z : ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x iF pF iG pG hF hG hFG hGF
        htot z =
      DFinsupp.mapRange.linearEquiv (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
          TensorProduct.congr (AF.exteriorPowerStalkEquiv pq.1.1 x).symm
            (AG.exteriorPowerStalkEquiv pq.1.2 x).symm)
        (exteriorPower.prodEquivDirectSum n
          (exteriorPowerCongr n
            (stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot)
            (A.exteriorPowerStalkEquiv n x z))) := rfl

/-- The stalk map of the wedge-product component morphism, on the germ of the image of a pure
tensor of two wedges of local sections: it is the germ of the wedge of the images of the `sᵢ`
under `iF` followed by the images of the `tⱼ` under `iG`. -/
theorem stalkMapL_prodWedgeHom_tensorSheafGerm (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ) (x : ↥X)
    (U : Opens ↥X) (hx : x ∈ U) (s : Fin p → F.val.obj (op U)) (t : Fin q → G.val.obj (op U)) :
    PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val
        (PresheafOfModules.tensorSheafGerm Osharp (AF.exteriorPower p) (AG.exteriorPower q) x U hx
          (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
            fun i => AF.exteriorGenerator.val.app (op U) (s i))
          (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) q
            fun j => AG.exteriorGenerator.val.app (op U) (t j))) =
      TopCat.Presheaf.germ (A.exteriorPower (p + q)).val.presheaf U x hx
        (A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) (p + q)
          fun i => A.exteriorGenerator.val.app (op U)
            (Fin.append (fun i' => iF.val.app (op U) (s i'))
              (fun j => iG.val.app (op U) (t j)) i)) := by
  have happ := prodWedgeHom_tensorSheafUnit AF AG A iF iG p q (op U) s t
  have hgerm := PresheafOfModules.stalkMapL_germ x
    (prodWedgeHom AF AG A iF iG p q).val U hx
    ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower p) (AG.exteriorPower q)).app (op U)
      (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
          (fun i => AF.exteriorGenerator.val.app (op U) (s i)) ⊗ₜ
        AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) q
          fun j => AG.exteriorGenerator.val.app (op U) (t j)))
  have hfin := (comp_fin_append (fun y => A.exteriorGenerator.val.app (op U) y)
    (fun i => iF.val.app (op U) (s i)) fun j => iG.val.app (op U) (t j)).symm
  exact hgerm.trans ((congrArg
    (TopCat.Presheaf.germ (A.exteriorPower (p + q)).val.presheaf U x hx) happ).trans
      (congrArg (fun z => TopCat.Presheaf.germ (A.exteriorPower (p + q)).val.presheaf U x hx
        (A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) (p + q) z)) hfin))


/-- **The stalk map of the wedge-product component morphism, on a germ of a pure tensor of two
wedges of local sections over a common neighbourhood**: read through the Künneth decomposition of
the stalk, it is the inclusion of the `(p, q)` summand. -/
theorem exteriorPowerStalkEquivDirectSumOfSplit_stalkMapL_prodWedgeHom_germ (p q : ℕ) (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G) (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H)
    (U : Opens ↥X) (hx : x ∈ U) (s : Fin p → F.val.obj (op U)) (t : Fin q → G.val.obj (op U)) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG
        hF hG hFG hGF htot
        (PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val
          (PresheafOfModules.tensorSheafGerm Osharp (AF.exteriorPower p) (AG.exteriorPower q) x U hx
            (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
              fun i => AF.exteriorGenerator.val.app (op U) (s i))
            (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) q
              fun j => AG.exteriorGenerator.val.app (op U) (t j)))) =
      DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x) {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x))
        ⟨(p, q), rfl⟩
        (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hx
            (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
              fun i => AF.exteriorGenerator.val.app (op U) (s i)) ⊗ₜ
          TopCat.Presheaf.germ (AG.exteriorPower q).val.presheaf U x hx
            (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) q
              fun j => AG.exteriorGenerator.val.app (op U) (t j))) := by
  have h3 : (fun i => stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot
        (TopCat.Presheaf.germ H.val.presheaf U x hx
          (Fin.append (fun i' => iF.val.app (op U) (s i'))
            (fun j => iG.val.app (op U) (t j)) i))) =
      Fin.append
        (fun i => LinearMap.inl ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx (s i)))
        fun j => LinearMap.inr ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)
          (TopCat.Presheaf.germ G.val.presheaf U x hx (t j)) := by
    refine (comp_fin_append (fun y => stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot
      (TopCat.Presheaf.germ H.val.presheaf U x hx y)) _ _).trans ?_
    exact congrArg₂ Fin.append
      (funext fun i => stalkProdEquivOfSplit_germ_left iF pF iG pG hF hG hFG hGF htot x U hx (s i))
      (funext fun j => stalkProdEquivOfSplit_germ_right iF pF iG pG hF hG hFG hGF htot x U hx
        (t j))
  refine Eq.trans (congrArg (fun z =>
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG
      hF hG hFG hGF htot z)
    (stalkMapL_prodWedgeHom_tensorSheafGerm AF AG A iF iG p q x U hx s t)) ?_
  refine Eq.trans (exteriorPowerStalkEquivDirectSumOfSplit_apply AF AG A (p + q) x iF pF iG pG
    hF hG hFG hGF htot _) ?_
  refine Eq.trans (congrArg (fun y => DFinsupp.mapRange.linearEquiv
      (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p + q} =>
        TensorProduct.congr (AF.exteriorPowerStalkEquiv pq.1.1 x).symm
          (AG.exteriorPowerStalkEquiv pq.1.2 x).symm)
      (exteriorPower.prodEquivDirectSum (p + q)
        (exteriorPowerCongr (p + q)
          (stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot) y)))
    (exteriorPowerStalkEquiv_germ_wedge A (p + q) x U hx
      (Fin.append (fun i' => iF.val.app (op U) (s i')) fun j => iG.val.app (op U) (t j)))) ?_
  exact Stacks.exteriorPowerProdDirectSum_ιMulti (fun k => AF.exteriorPowerStalkEquiv k x)
    (fun k => AG.exteriorPowerStalkEquiv k x)
    (stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot) p q
    (fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (s i))
    (fun j => TopCat.Presheaf.germ G.val.presheaf U x hx (t j))
    (fun i => TopCat.Presheaf.germ H.val.presheaf U x hx
      (Fin.append (fun i' => iF.val.app (op U) (s i'))
        (fun j => iG.val.app (op U) (t j)) i)) h3
    _ (exteriorPowerStalkEquiv_germ_wedge AF p x U hx s)
    _ (exteriorPowerStalkEquiv_germ_wedge AG q x U hx t)

variable (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
  (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G) (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
  (htot : pF ≫ iF + pG ≫ iG = 𝟙 H)

/-- The same identification for a pure tensor of two germs of wedges of local sections over
possibly different neighbourhoods: both are shrunk to a common one. -/
theorem exteriorPowerStalkEquivDirectSumOfSplit_stalkMapL_prodWedgeHom_tmul (p q : ℕ) (x : ↥X)
    {U V W : Opens ↥X} (hWU : W ≤ U) (hWV : W ≤ V)
    (hxU : x ∈ U) (hxV : x ∈ V) (hxW : x ∈ W)
    (s : Fin p → F.val.obj (op U)) (t : Fin q → G.val.obj (op V)) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG hF hG hFG hGF htot
        (PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val
          ((PresheafOfModules.tensorSheafStalkEquiv Osharp (AF.exteriorPower p)
              (AG.exteriorPower q) x).symm
            (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hxU
                (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
                  fun i => AF.exteriorGenerator.val.app (op U) (s i)) ⊗ₜ
              TopCat.Presheaf.germ (AG.exteriorPower q).val.presheaf V x hxV
                (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op V) q
                  fun j => AG.exteriorGenerator.val.app (op V) (t j))))) =
      DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x) {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) ⟨(p, q), rfl⟩
        (TopCat.Presheaf.germ (AF.exteriorPower p).val.presheaf U x hxU
            (AF.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) p
              fun i => AF.exteriorGenerator.val.app (op U) (s i)) ⊗ₜ
          TopCat.Presheaf.germ (AG.exteriorPower q).val.presheaf V x hxV
            (AG.exterior.toPresheafGradedAlgebra.homogeneousProd (op V) q
              fun j => AG.exteriorGenerator.val.app (op V) (t j))) := by
  refine Eq.trans (congrArg (fun y =>
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG hF hG hFG hGF htot
      (PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val y))
    (tensorSheafStalkEquiv_symm_germ_wedge AF AG p q x hWU hWV hxU hxV hxW s t)) ?_
  refine Eq.trans (exteriorPowerStalkEquivDirectSumOfSplit_stalkMapL_prodWedgeHom_germ AF AG A
    p q x iF pF iG pG hF hG hFG hGF htot W hxW
    (fun i => F.val.map (homOfLE hWU).op (s i))
    (fun j => G.val.map (homOfLE hWV).op (t j))) ?_
  exact congrArg (DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
      (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
        ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) ⟨(p, q), rfl⟩)
    (congrArg₂ (fun y z => y ⊗ₜ z) (germ_homogeneousProd_res AF p x hWU hxU hxW s).symm
      (germ_homogeneousProd_res AG q x hWV hxV hxW t).symm)

/-- **The stalk map of the wedge-product component morphism is the inclusion of the `(p, q)`
summand**, read through the comparison of Tag 01CB on the source and the Künneth decomposition
`SheafOfModules.exteriorPowerStalkEquivDirectSumOfSplit` on the target.

Both sides are linear, and germs of wedges of local sections span each of the two factors of the
tensor product of stalks (`SheafOfModules.span_germWedgeSet_eq_top`), so the identification on
pure tensors of such germs determines it. -/
theorem stalkMapL_prodWedgeHom (p q : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp
      (AF.exteriorPower p) (AG.exteriorPower q)).presheaf x)) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG hF hG hFG hGF htot
        (PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val z) =
      DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x) {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) ⟨(p, q), rfl⟩
        (PresheafOfModules.tensorSheafStalkEquiv Osharp (AF.exteriorPower p)
          (AG.exteriorPower q) x z) := by
  refine Stacks.apply_of_comp_symm_eq (PresheafOfModules.tensorSheafStalkEquiv Osharp
      (AF.exteriorPower p) (AG.exteriorPower q) x)
    ((exteriorPowerStalkEquivDirectSumOfSplit AF AG A (p + q) x iF pF iG pG hF hG hFG hGF
        htot).toLinearMap.comp
      (PresheafOfModules.stalkMapL x (prodWedgeHom AF AG A iF iG p q).val))
    (DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x) {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
      (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
        ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) ⟨(p, q), rfl⟩) ?_ z
  refine Stacks.TensorProduct.linearMap_ext_of_span₂ (span_germWedgeSet_eq_top AF p x)
    (span_germWedgeSet_eq_top AG q x) _ _ ?_
  rintro ξ ⟨U, hxU, s, rfl⟩ η ⟨V, hxV, t, rfl⟩
  exact exteriorPowerStalkEquivDirectSumOfSplit_stalkMapL_prodWedgeHom_tmul AF AG A iF pF iG pG
    hF hG hFG hGF htot p q x
    (inf_le_left : (U ⊓ V : Opens ↥X) ≤ U) (inf_le_right : (U ⊓ V : Opens ↥X) ≤ V)
    hxU hxV ⟨hxU, hxV⟩ s t

/-! ### The comparison morphism out of the direct sum -/

/-- The `(p, q)` summand `⋀ᵖ F ⊗ ⋀^q G` of the direct sum, indexed by the antidiagonal of `n`
lifted into the universe of the space. -/
noncomputable abbrev exteriorPowerProdSummand (n : ℕ)
    (i : ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower i.down.1.1)).obj
      (AG.exteriorPower i.down.1.2)

/-- The wedge-product component `⋀ᵖ F ⊗ ⋀^q G ⟶ ⋀ⁿ H` for `p + q = n`: the morphism
`SheafOfModules.prodWedgeHom`, with its target transported along `p + q = n`. -/
noncomputable def prodWedgeHomOfEq (p q n : ℕ) (h : p + q = n) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower p)).obj
        (AG.exteriorPower q) ⟶ A.exteriorPower n :=
  prodWedgeHom AF AG A iF iG p q ≫ eqToHom (congrArg (fun m : ℕ => A.exteriorPower m) h)

/-- In degree `p + q` the transport is trivial. -/
theorem prodWedgeHomOfEq_rfl (p q : ℕ) :
    prodWedgeHomOfEq AF AG A iF iG p q (p + q) rfl = prodWedgeHom AF AG A iF iG p q :=
  Category.comp_id _

/-- **The comparison morphism `⨁_{p + q = n} (⋀ᵖ F ⊗ ⋀^q G) ⟶ ⋀ⁿ H`** attached to morphisms
`iF : F ⟶ H` and `iG : G ⟶ H`: on the `(p, q)` summand it is the wedge product
`SheafOfModules.prodWedgeHom`. -/
noncomputable def exteriorPowerProdHom (n : ℕ) :
    (∐ exteriorPowerProdSummand AF AG n) ⟶ A.exteriorPower n :=
  Sigma.desc fun i => prodWedgeHomOfEq AF AG A iF iG i.down.1.1 i.down.1.2 n i.down.2

/-- `SheafOfModules.stalkMapL_prodWedgeHom`, transported along `p + q = n`. -/
theorem stalkMapL_prodWedgeHomOfEq (p q n : ℕ) (h : p + q = n) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp
      (AF.exteriorPower p) (AG.exteriorPower q)).presheaf x)) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x iF pF iG pG hF hG hFG hGF htot
        (PresheafOfModules.stalkMapL x (prodWedgeHomOfEq AF AG A iF iG p q n h).val z) =
      DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x) {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) ⟨(p, q), h⟩
        (PresheafOfModules.tensorSheafStalkEquiv Osharp (AF.exteriorPower p)
          (AG.exteriorPower q) x z) := by
  subst h
  rw [prodWedgeHomOfEq_rfl]
  exact stalkMapL_prodWedgeHom AF AG A iF pF iG pG hF hG hFG hGF htot p q x z

/-- **The stalk map of the comparison morphism, read through the two identifications of the
stalks.** The stalk of the direct sum is the direct sum of the stalks
(`SheafOfModules.stalkCoprodEquiv`), the stalk of `⋀ⁿ H` is `⨁_{p + q = n} (⋀ᵖ F)_x ⊗ (⋀^q G)_x`
(`SheafOfModules.exteriorPowerStalkEquivDirectSumOfSplit`), and in those terms the stalk map is
the direct sum of the identifications `(⋀ᵖ F ⊗ ⋀^q G)_x ≅ (⋀ᵖ F)_x ⊗ (⋀^q G)_x` of Tag 01CB. -/
theorem exteriorPowerStalkEquivDirectSumOfSplit_comp_stalkCoprodEquiv (n : ℕ) (x : ↥X) :
    (exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x iF pF iG pG hF hG hFG hGF
        htot).toLinearMap.comp
      ((PresheafOfModules.stalkMapL x (exteriorPowerProdHom AF AG A iF iG n).val).comp
        (stalkCoprodEquiv (exteriorPowerProdSummand AF AG n) x).toLinearMap) =
      Stacks.directSumUliftComparison
        (gamma := fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
          TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
            ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x))
        (fun i => PresheafOfModules.tensorSheafStalkEquiv Osharp
          (AF.exteriorPower i.down.1.1) (AG.exteriorPower i.down.1.2) x) := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun t => ?_
  have h1 : (stalkCoprodEquiv (exteriorPowerProdSummand AF AG n) x)
        (DirectSum.lof ↑(TopCat.Presheaf.stalk Osharp.obj x)
          (ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = n})
          (fun i =>
            ↑(TopCat.Presheaf.stalk (exteriorPowerProdSummand AF AG n i).val.presheaf x)) i t) =
      PresheafOfModules.stalkMapL x (Sigma.ι (exteriorPowerProdSummand AF AG n) i).val t := by
    rw [DirectSum.lof_eq_of]
    exact stalkCoprodEquiv_of (exteriorPowerProdSummand AF AG n) x i t
  have h2 : PresheafOfModules.stalkMapL x (exteriorPowerProdHom AF AG A iF iG n).val
        (PresheafOfModules.stalkMapL x (Sigma.ι (exteriorPowerProdSummand AF AG n) i).val t) =
      PresheafOfModules.stalkMapL x
        (prodWedgeHomOfEq AF AG A iF iG i.down.1.1 i.down.1.2 n i.down.2).val t :=
    LinearMap.congr_fun (stalkMapL_comp_of_comp_eq_comp x
      (Sigma.ι (exteriorPowerProdSummand AF AG n) i)
      (exteriorPowerProdHom AF AG A iF iG n) _ (Sigma.ι_desc _ i)) t
  refine Eq.trans (congrArg (fun y =>
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x iF pF iG pG hF hG hFG hGF htot
      (PresheafOfModules.stalkMapL x (exteriorPowerProdHom AF AG A iF iG n).val y)) h1) ?_
  refine Eq.trans (congrArg (fun y =>
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x iF pF iG pG hF hG hFG hGF htot y) h2) ?_
  refine Eq.trans (stalkMapL_prodWedgeHomOfEq AF AG A iF pF iG pG hF hG hFG hGF htot
    i.down.1.1 i.down.1.2 n i.down.2 x t) ?_
  exact (Stacks.directSumUliftComparison_lof
        (gamma := fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
          TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
            ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x))
        (fun i => PresheafOfModules.tensorSheafStalkEquiv Osharp
          (AF.exteriorPower i.down.1.1) (AG.exteriorPower i.down.1.2) x) i t).symm

include pF pG hF hG hFG hGF htot in
/-- **The stalk map of the comparison morphism is bijective at every point.** -/
theorem bijective_stalkMapL_exteriorPowerProdHom (n : ℕ) (x : ↥X) :
    Function.Bijective
      (PresheafOfModules.stalkMapL x (exteriorPowerProdHom AF AG A iF iG n).val) :=
  Stacks.bijective_of_comp_eq _ _ _ _
    (exteriorPowerStalkEquivDirectSumOfSplit_comp_stalkCoprodEquiv AF AG A iF pF iG pG hF hG
      hFG hGF htot n x)
    (Stacks.bijective_directSumUliftComparison _)

include pF pG hF hG hFG hGF htot in
/-- **The Künneth comparison for an exterior power of a split sheaf of modules is an
isomorphism.** For a splitting datum `F ⇄ H ⇄ G` the wedge product assembles the summands
`⋀ᵖ F ⊗ ⋀^q G` with `p + q = n` into `⋀ⁿ H`, and the resulting morphism of sheaves of modules is
an isomorphism: it is bijective on every stalk, where it is the Künneth decomposition
`SheafOfModules.exteriorPowerStalkEquivDirectSumOfSplit`. -/
theorem isIso_exteriorPowerProdHom (n : ℕ) :
    IsIso (exteriorPowerProdHom AF AG A iF iG n) := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (exteriorPowerProdHom AF AG A iF iG n)).2 fun x => ?_
  have hb := bijective_stalkMapL_exteriorPowerProdHom AF AG A iF pF iG pG hF hG hFG hGF htot n x
  have hfun := funext (stalkMap_hom_eq_stalkMapL x (exteriorPowerProdHom AF AG A iF iG n))
  rw [show ⇑(AlgebraicGeometry.SheafOfModules.stalkMap _ x _).hom = _ from hfun]
  exact hb

end WedgeHom

/-! ### The exterior power of a binary biproduct -/

section Biprod

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  [HasBinaryBiproduct F G]
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) (F ⊞ G))

/-- At the biproduct datum, the Künneth decomposition of a stalk for a splitting is the one
`SheafOfModules.exteriorPowerBiprodStalkEquivDirectSum` records for a biproduct. -/
theorem exteriorPowerStalkEquivDirectSumOfSplit_biprod (n : ℕ) (x : ↥X) :
    exteriorPowerStalkEquivDirectSumOfSplit AF AG A n x biprod.inl biprod.fst biprod.inr
        biprod.snd biprod.inl_fst biprod.inr_snd biprod.inl_snd biprod.inr_fst biprod.total =
      exteriorPowerBiprodStalkEquivDirectSum AF AG A n x :=
  rfl

/-- **The comparison morphism `⨁_{p + q = n} (⋀ᵖ F ⊗ ⋀^q G) ⟶ ⋀ⁿ (F ⊞ G)`**: on the `(p, q)`
summand it is the wedge product of the images of the two factors under the functorial maps
induced by the two biproduct injections. -/
noncomputable abbrev exteriorPowerBiprodHom (n : ℕ) :
    (∐ exteriorPowerProdSummand AF AG n) ⟶ A.exteriorPower n :=
  exteriorPowerProdHom AF AG A biprod.inl biprod.inr n

/-- **The exterior power of a direct sum of sheaves of modules.** For sheaves of `O♯`-modules `F`
and `G` on a topological space with chosen exterior algebras, and a chosen exterior algebra of
their biproduct, the wedge product

`⨁_{p + q = n} (⋀ᵖ F ⊗_{O♯} ⋀^q G) ⟶ ⋀ⁿ (F ⊞ G)`

is an isomorphism of sheaves of modules. -/
theorem isIso_exteriorPowerBiprodHom (n : ℕ) :
    IsIso (exteriorPowerBiprodHom AF AG A n) :=
  isIso_exteriorPowerProdHom AF AG A biprod.inl biprod.fst biprod.inr biprod.snd
    biprod.inl_fst biprod.inr_snd biprod.inl_snd biprod.inr_fst biprod.total n

/-- **The Künneth decomposition of an exterior power of a direct sum**, as an isomorphism of
sheaves of modules `⨁_{p + q = n} (⋀ᵖ F ⊗ ⋀^q G) ≅ ⋀ⁿ (F ⊞ G)`. -/
noncomputable def exteriorPowerBiprodIso (n : ℕ) :
    (∐ exteriorPowerProdSummand AF AG n) ≅ A.exteriorPower n :=
  letI := isIso_exteriorPowerBiprodHom AF AG A n
  asIso (exteriorPowerBiprodHom AF AG A n)

/-- The underlying morphism of the Künneth isomorphism is the comparison morphism. -/
@[simp]
theorem exteriorPowerBiprodIso_hom (n : ℕ) :
    (exteriorPowerBiprodIso AF AG A n).hom = exteriorPowerBiprodHom AF AG A n :=
  rfl

end Biprod

end SheafOfModules
