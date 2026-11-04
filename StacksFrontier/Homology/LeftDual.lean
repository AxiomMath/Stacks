module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Category.ModuleCat.LeftDual
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.TensorHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left duals of complexes of modules

Let `R` be a commutative ring. A cochain complex `M^•` of `R`-modules has a left dual in the
monoidal category `CochainComplex (ModuleCat R) ℤ` precisely when it is bounded and each term
`M^n` is a finite projective `R`-module. In that case any left dual `N^•` is again bounded with
finite projective terms, each homogeneous piece `(N^{-n}, η_n, ε_n)` is a left dual of `M^n` in
the monoidal category of `R`-modules, and the differential of `N^•` is `-(-1)^n` times the
transpose of the differential of `M^•` under the identification `N^n = Hom_R(M^{-n}, R)`.

Once a left dual exists, tensoring with it computes the Hom complex: for any complex `K` there
is a canonical isomorphism `K ⊗ N ≅ Hom^•(M, K)`, natural in `K`, which on the summand
`K^p ⊗ N^q` is the evaluation pairing with no additional sign.

## Main definitions

* `CochainComplex.LeftDual.IsLinearDualPairing`: an exact pairing of complexes whose homogeneous
  pieces are the ordinary linear-dual pairings and whose differential on the dual is the signed
  transpose.
* `CochainComplex.LeftDual.signedDual`: the complex with `n`-th term `Hom_R(M^{-n}, R)` and
  differential `-(-1)^n` times the transpose of `d_M`.

## Main results

* `CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective`: a left dual of a complex
  of modules is bounded with finite projective terms and realizes the signed linear-dual pairing;
  conversely every bounded complex of finite projective modules has `signedDual` as a left dual.
* `CochainComplex.LeftDual.signedDual_d_apply`: the signed transpose formula for the differential
  of `signedDual`.
* `CochainComplex.LeftDual.signedDual_bounded`: `signedDual` reflects the bounds of the original
  complex.
* `CochainComplex.LeftDual.tensorLeftDualIsoHomComplex`: tensoring with a left dual `N` of `M` is
  canonically and naturally isomorphic to the Hom complex out of `M`, with the evaluation pairing
  as its formula on homogeneous tensors.

## Implementation notes

`IsLinearDualPairing` records the decomposition of coevaluation and evaluation into homogeneous
components together with the properties those components have: the finite sum recording
coevaluation, the identification of evaluation on each homogeneous summand, the fact that each
homogeneous component is itself an exact pairing of modules, that the chosen identifications with
the linear duals carry evaluation to application, and the signed transpose formula for the
differential. Stating the last item through the termwise linear-dual equivalences makes it
independent of a choice of bases.

Because `ExactPairing` is a structure and not a `Prop`, the classification is phrased for an
arbitrary chosen pairing `p : ExactPairing M N` rather than for the mere existence of one.

The proofs about the total complex raise `synthInstance.maxHeartbeats` and `maxRecDepth`, and
several of them relax `backward.isDefEq.respectTransparency`, because the summand inclusions
`ιTensorObj` are definitionally coproduct inclusions indexed by a subtype of `ℤ × ℤ` and the
proofs must see through that packaging.

The isomorphism `K ⊗ N ≅ Hom^•(M, K)` is obtained by uniqueness of right adjoints: `- ⊗ N` is
right adjoint to `- ⊗ M` because of the exact pairing, and `Hom^•(M, -)` is right adjoint to
`- ⊗ M` by the currying isomorphism of Stacks 0A5Y. It is recorded as a family in `K` together
with its naturality and its value on every homogeneous tensor, which is what makes the word
"canonical" precise; the component formula uses the evaluation of the given pairing directly, so
the statement does not choose a separate identification of `N` with `signedDual M`.

## References

* [The Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [The Stacks Project, Tag 0FNL](https://stacks.math.columbia.edu/tag/0FNL)
-/

@[expose] public section


-- `TensorProduct` is deliberately not opened: its `⊗` would make every monoidal tensor product
-- of `ModuleCat R` objects ambiguous. The `⊗ₜ[R]` notation for elements is global.
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex

universe u v

namespace CochainComplex.LeftDual

/-- An exact pairing of complexes is the termwise linear-dual pairing when its coevaluation and
evaluation are finite sums of exact homogeneous pairings, the chosen identifications with linear
duals carry evaluation to application, and the differential on the dual is the signed transpose
of the original differential. -/
def IsLinearDualPairing (R : Type u) [CommRing R]
    (M N : CochainComplex (ModuleCat R) ℤ)
    (p : ExactPairing M N) : Prop :=
  let := p
  ∃ (s : Finset ℤ)
      (η : ∀ n : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X n ⊗ N.X (-n))
      (ε : ∀ n : ℤ, N.X (-n) ⊗ M.X n ⟶ 𝟙_ (ModuleCat R))
      (e : ∀ n : ℤ, Module.Dual R (M.X n) ≃ₗ[R] N.X (-n)),
    (η_ M N).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom ≫
          ∑ n ∈ s, η n ≫
            HomologicalComplex.ιTensorObj M N n (-n) 0 (by omega) ∧
      (∀ n : ℤ,
        HomologicalComplex.ιTensorObj N M (-n) n 0 (by omega) ≫ (ε_ M N).f 0 =
          ε n ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv) ∧
      (∀ n : ℤ, ∃ q : ExactPairing (M.X n) (N.X (-n)),
        @ExactPairing.coevaluation _ _ _ _ _ q = η n ∧
          @ExactPairing.evaluation _ _ _ _ _ q = ε n) ∧
      (∀ (n : ℤ) (x : N.X (-n)) (m : M.X n),
        (ε n).hom (x ⊗ₜ[R] m) = (e n).symm x m) ∧
      (∀ (n : ℤ) (x : N.X n),
        (N.d n (n + 1)).hom x =
          (-n.negOnePow : ℤˣ) •
            (by
              simpa only [neg_neg] using
                (e (-(n + 1)))
                  ((Module.Dual.transpose (R := R) (M.d (-(n + 1)) (-n)).hom)
                    ((e (-n)).symm (by simpa only [neg_neg] using x)))))

section Helpers

variable {R : Type u} [CommRing R]

/-- The restriction of the differential of a total complex to a summand `K^p ⊗ L^q`. -/
private theorem ιTensorObj_d (K L : CochainComplex (ModuleCat R) ℤ)
    (p q b : ℤ) (h : p + q = b) :
    ιTensorObj K L p q b h ≫ (K ⊗ L).d b (b + 1) =
      (K.d p (p + 1) ▷ L.X q) ≫
          ιTensorObj K L (p + 1) q (b + 1) (by omega) +
        p.negOnePow • ((K.X p ◁ L.d q (q + 1)) ≫
          ιTensorObj K L p (q + 1) (b + 1) (by omega)) := by
  have hd : (K ⊗ L).d b (b + 1) =
      mapBifunctor.D₁ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b (b + 1) +
      mapBifunctor.D₂ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b (b + 1) :=
    mapBifunctor.d_eq K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b (b + 1)
  rw [hd, Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)
      q (b + 1) (by change p + 1 + q = b + 1; omega),
    mapBifunctor.d₂_eq _ _ _ _ p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)
      (b + 1) (by change p + (q + 1) = b + 1; omega)]
  show (1 : ℤˣ) • _ + p.negOnePow • _ = _
  rw [one_smul]
  rfl

/-- Since evaluation is a morphism of complexes into the unit complex, its two restrictions to
the summands of degree `-1` of the total complex cancel. -/
private theorem evaluation_d (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (n k : ℤ) (h : n + k = -1) :
    (N.d n (n + 1) ▷ M.X k) ≫
        ιTensorObj N M (n + 1) k 0 (by omega) ≫ ev.f 0 +
      n.negOnePow • ((N.X n ◁ M.d k (k + 1)) ≫
        ιTensorObj N M n (k + 1) 0 (by omega) ≫ ev.f 0) = 0 := by
  have hd : (N ⊗ M).d (-1) 0 ≫ ev.f 0 = 0 := by
    rw [← ev.comm]
    show ev.f (-1) ≫
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) 0).obj
        (𝟙_ (ModuleCat R))).d (-1) 0 = 0
    rw [single_obj_d, comp_zero]
  have hi := congrArg (fun f => ιTensorObj N M n k (-1) h ≫ f) hd
  rw [← Category.assoc] at hi
  have ht := ιTensorObj_d N M n k (-1) h
  change ιTensorObj N M n k (-1) h ≫ (N ⊗ M).d (-1) 0 =
    (N.d n (n + 1) ▷ M.X k) ≫ ιTensorObj N M (n + 1) k 0 _ +
    n.negOnePow • ((N.X n ◁ M.d k (k + 1)) ≫ ιTensorObj N M n (k + 1) 0 _) at ht
  rw [ht, Preadditive.add_comp, Linear.units_smul_comp] at hi
  simpa only [Category.assoc, comp_zero] using hi

/-- The elementwise form of `evaluation_d`, with the successor degrees supplied as equalities. -/
private theorem evaluation_d_apply (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (n n' k k' : ℤ) (hn : n + 1 = n') (hk : k + 1 = k') (h : n + k = -1)
    (x : N.X n) (m : M.X k) :
    ((ιTensorObj N M n' k 0 (by omega) ≫ ev.f 0 ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
        ((N.d n n').hom x ⊗ₜ[R] m)) +
      n.negOnePow •
        ((ιTensorObj N M n k' 0 (by omega) ≫ ev.f 0 ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
            (x ⊗ₜ[R] (M.d k k').hom m)) = 0 := by
  subst n' k'
  have he := congrArg
    (fun f => f ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom)
    (evaluation_d M N ev n k h)
  rw [Preadditive.add_comp, Linear.units_smul_comp, zero_comp] at he
  simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom he) (x ⊗ₜ[R] m)

/-- Projection of a coproduct in `ModuleCat R` onto a summand, read through the identification
of the coproduct with the direct sum. -/
private theorem coprodIsoDirectSum_hom_component {ι : Type v}
    (Z : ι → ModuleCat.{max u v} R) [DecidableEq ι] [HasCoproduct Z] (i : ι) :
    (ModuleCat.coprodIsoDirectSum Z).hom ≫
      ModuleCat.ofHom (DirectSum.component R ι (fun i => Z i) i) = Sigma.π Z i := by
  apply Sigma.hom_ext
  intro j
  by_cases h : j = i
  · subst j
    simp only [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, Sigma.ι_π_eq_id]
    exact ModuleCat.hom_ext (DirectSum.component_comp_lof_same R (M := fun i => Z i) i)
  · rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, Sigma.ι_π_of_ne _ h]
    apply ModuleCat.hom_ext
    simpa [h] using DirectSum.component_comp_lof R (M := fun i => Z i) i j

/-- An element of a coproduct in `ModuleCat R` has finitely many nonzero components. -/
private theorem finite_support_of_coproduct_element {ι : Type v}
    (Z : ι → ModuleCat.{max u v} R) [DecidableEq ι] [HasCoproduct Z]
    (x : (∐ Z : ModuleCat.{max u v} R)) :
    ∃ s : Finset ι,
      x = ∑ i ∈ s, (Sigma.ι Z i).hom ((Sigma.π Z i).hom x) ∧
      ∀ i ∉ s, (Sigma.π Z i).hom x = 0 := by
  classical
  let e := ModuleCat.coprodIsoDirectSum Z
  let z := e.hom.hom x
  have hz (i : ι) : (Sigma.π Z i).hom x = z i := by
    rw [← coprodIsoDirectSum_hom_component]
    rfl
  refine ⟨z.support, ?_, ?_⟩
  · have he := congrArg e.inv.hom (DirectSum.sum_support_of z)
    change e.inv.hom (∑ i ∈ z.support, DirectSum.lof R ι (fun i => Z i) i (z i)) =
      e.inv.hom z at he
    simp only [map_sum] at he
    simp only [e, ModuleCat.lof_coprodIsoDirectSum_inv_apply] at he
    have hid : e.inv.hom z = x := e.hom_inv_id_apply x
    rw [hid] at he
    simpa only [hz] using he.symm
  · intro i hi
    rw [hz]
    exact DFinsupp.notMem_support_iff.mp hi

/-- The associator of total complexes, restricted to a summand `K^p ⊗ L^q ⊗ H^r`. -/
@[reassoc]
public theorem ι_associator_hom (K L H : CochainComplex (ModuleCat R) ℤ)
    (p q r a b t : ℤ) (hpq : p + q = a) (hqr : q + r = b) (hat : a + r = t) :
    (ιTensorObj K L p q a hpq ▷ H.X r) ≫
      ιTensorObj (K ⊗ L) H a r t hat ≫ (α_ K L H).hom.f t =
    (α_ (K.X p) (L.X q) (H.X r)).hom ≫
      (K.X p ◁ ιTensorObj L H q r b hqr) ≫
        ιTensorObj K (L ⊗ H) p b t (by omega) := by
  have h := GradedObject.Monoidal.ιTensorObj₃'_associator_hom
    K.X L.X H.X p q r t (by omega)
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X H.X p q r t (by omega) a hpq,
    GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X H.X p q r t (by omega) b hqr] at h
  exact h

/-- The inverse associator of total complexes, restricted to a summand `K^p ⊗ L^q ⊗ H^r`. -/
@[reassoc]
private theorem ι_associator_inv (K L H : CochainComplex (ModuleCat R) ℤ)
    (p q r a b t : ℤ) (hpq : p + q = a) (hqr : q + r = b) (hat : a + r = t) :
    (K.X p ◁ ιTensorObj L H q r b hqr) ≫
      ιTensorObj K (L ⊗ H) p b t (by omega) ≫ (α_ K L H).inv.f t =
    (α_ (K.X p) (L.X q) (H.X r)).inv ≫
      (ιTensorObj K L p q a hpq ▷ H.X r) ≫
        ιTensorObj (K ⊗ L) H a r t hat := by
  have h := GradedObject.Monoidal.ιTensorObj₃_associator_inv
    K.X L.X H.X p q r t (by omega)
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X H.X p q r t (by omega) a hpq,
    GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X H.X p q r t (by omega) b hqr] at h
  exact h

/-- A tensor product of morphisms of complexes, restricted to a summand `K^p ⊗ L^q`. -/
private theorem ι_tensorHom (K L K' L' : CochainComplex (ModuleCat R) ℤ)
    (f : K ⟶ K') (g : L ⟶ L') (p q t : ℤ) (h : p + q = t) :
    ιTensorObj K L p q t h ≫ (f ⊗ₘ g).f t =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj K' L' p q t h :=
  GradedObject.Monoidal.ι_tensorHom f.f g.f p q t h

/-- A left whiskering of complexes, restricted to a summand `K^p ⊗ L^q`. -/
@[reassoc]
private theorem ι_whiskerLeft (K L L' : CochainComplex (ModuleCat R) ℤ)
    (g : L ⟶ L') (p q t : ℤ) (h : p + q = t) :
    ιTensorObj K L p q t h ≫ (K ◁ g).f t =
      (K.X p ◁ g.f q) ≫ ιTensorObj K L' p q t h := by
  simpa only [id_f, id_tensorHom] using ι_tensorHom K L K L' (𝟙 K) g p q t h

/-- A right whiskering of complexes, restricted to a summand `K^p ⊗ L^q`. -/
@[reassoc]
private theorem ι_whiskerRight (K K' L : CochainComplex (ModuleCat R) ℤ)
    (f : K ⟶ K') (p q t : ℤ) (h : p + q = t) :
    ιTensorObj K L p q t h ≫ (f ▷ L).f t =
      (f.f p ▷ L.X q) ≫ ιTensorObj K' L p q t h := by
  simpa only [id_f, tensorHom_id] using ι_tensorHom K L K' L f (𝟙 L) p q t h

/-- Off the diagonal, a homogeneous summand of coevaluation contributes nothing to the first
snake identity. -/
@[reassoc]
private theorem right_snake_summand_eq_zero (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (i n : ℤ) (h : i ≠ n) :
    (ιTensorObj M N i (-i) 0 (by omega) ▷ M.X n) ≫
      ιTensorObj (M ⊗ N) M 0 n n (by omega) ≫
        (α_ M N M).hom.f n ≫ (M ◁ ev).f n = 0 := by
  have he : ev.f (-i + n) = 0 :=
    (isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))
      (-i + n) (by omega)).eq_of_tgt _ _
  rw [ι_associator_hom_assoc M N M i (-i) n 0 (-i + n) n
    (by omega) rfl (by omega), ι_whiskerLeft, he]
  simp

/-- Off the diagonal, a homogeneous summand of coevaluation contributes nothing to the second
snake identity. -/
@[reassoc]
private theorem left_snake_summand_eq_zero (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (i n : ℤ) (h : i ≠ -n) :
    (N.X n ◁ ιTensorObj M N i (-i) 0 (by omega)) ≫
      ιTensorObj N (M ⊗ N) n 0 n (by omega) ≫
        (α_ N M N).inv.f n ≫ (ev ▷ N).f n = 0 := by
  have he : ev.f (n + i) = 0 :=
    (isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))
      (n + i) (by omega)).eq_of_tgt _ _
  rw [ι_associator_inv_assoc N M N n i (-i) (n + i) 0 n
    rfl (by omega) (by omega), ι_whiskerRight, he]
  simp

/-- Projection of a total complex onto the summand `M^i ⊗ N^j`. -/
private noncomputable def tensorProjection (M N : CochainComplex (ModuleCat R) ℤ)
    (i j k : ℤ) (h : i + j = k) : (M ⊗ N).X k ⟶ M.X i ⊗ N.X j :=
  Sigma.π (fun a : {a : ℤ × ℤ // a.1 + a.2 = k} => M.X a.1.1 ⊗ N.X a.1.2)
    ⟨(i, j), h⟩

/-- A morphism from the unit into degree `0` of a total complex has finitely many nonzero
homogeneous components, and is the sum of them. -/
private theorem finite_support_of_hom_to_tensor (M N : CochainComplex (ModuleCat R) ℤ)
    (f : 𝟙_ (ModuleCat R) ⟶ (M ⊗ N).X 0) :
    ∃ s : Finset ℤ,
      f = ∑ n ∈ s, f ≫ tensorProjection M N n (-n) 0 (by omega) ≫
        ιTensorObj M N n (-n) 0 (by omega) ∧
      ∀ n ∉ s, f ≫ tensorProjection M N n (-n) 0 (by omega) = 0 := by
  classical
  let Z := fun a : {a : ℤ × ℤ // a.1 + a.2 = 0} => M.X a.1.1 ⊗ N.X a.1.2
  obtain ⟨t, ht, hz⟩ := finite_support_of_coproduct_element Z (f.hom 1)
  have hinj : Function.Injective (fun a : {a : ℤ × ℤ // a.1 + a.2 = 0} => a.val.1) := by
    rintro ⟨⟨i, j⟩, h⟩ ⟨⟨i', j'⟩, h'⟩ he
    dsimp at he
    have : j = j' := by omega
    subst i' j'
    rfl
  refine ⟨t.image (fun a => a.val.1), ?_, ?_⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, Finset.sum_image (fun a _ b _ h => hinj h)]
    refine ht.trans ?_
    apply Finset.sum_congr rfl
    rintro ⟨⟨i, j⟩, h⟩ _
    obtain rfl : j = -i := by omega
    rfl
  · intro n hn
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (Sigma.π Z ⟨(n, -n), by omega⟩).hom (f.hom 1) = 0
    exact hz _ fun h => hn (Finset.mem_image_of_mem (fun a => a.val.1) h)

/-- The right unitor of complexes, restricted to the summand `M^n ⊗ R`. -/
@[reassoc]
private theorem ι_rightUnitor_hom (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ιTensorObj M (𝟙_ (CochainComplex (ModuleCat R) ℤ)) n 0 n (by omega) ≫
      (ρ_ M).hom.f n =
    (M.X n ◁ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom) ≫
      (ρ_ (M.X n)).hom := by
  have h : (ρ_ M).inv.f n = (ρ_ (M.X n)).inv ≫
      (M.X n ◁ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv) ≫
        ιTensorObj M (𝟙_ (CochainComplex (ModuleCat R) ℤ)) n 0 n (by omega) :=
    rightUnitor'_inv M n
  apply (cancel_epi ((ρ_ (M.X n)).inv ≫
    (M.X n ◁ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv))).mp
  simp only [Category.assoc]
  rw [← reassoc_of% h]
  simp

/-- The left unitor of complexes, restricted to the summand `R ⊗ M^n`. -/
@[reassoc]
private theorem ι_leftUnitor_hom (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) M 0 n n (by omega) ≫
      (λ_ M).hom.f n =
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom ▷ M.X n) ≫
      (λ_ (M.X n)).hom := by
  have h : (λ_ M).inv.f n = (λ_ (M.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ M.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) M 0 n n (by omega) :=
    leftUnitor'_inv M n
  apply (cancel_epi ((λ_ (M.X n)).inv ≫
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ M.X n))).mp
  simp only [Category.assoc]
  rw [← reassoc_of% h]
  simp

/-- On the diagonal, the first snake identity restricts to the homogeneous snake identity. -/
private theorem right_snake_summand_diagonal
    (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) (n : ℤ) :
    (ιTensorObj M N n (-n) 0 (by omega) ▷ M.X n) ≫
      ιTensorObj (M ⊗ N) M 0 n n (by omega) ≫
        (α_ M N M).hom.f n ≫ (M ◁ ev).f n ≫ (ρ_ M).hom.f n =
    (α_ (M.X n) (N.X (-n)) (M.X n)).hom ≫
      (M.X n ◁ (ιTensorObj N M (-n) n 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom)) ≫
      (ρ_ (M.X n)).hom := by
  rw [ι_associator_hom_assoc M N M n (-n) n 0 0 n
    (by omega) (by omega) (by omega), ι_whiskerLeft_assoc, ι_rightUnitor_hom]
  simp only [whiskerLeft_comp, Category.assoc]

/-- On the diagonal, the second snake identity restricts to the homogeneous snake identity. -/
private theorem left_snake_summand_diagonal
    (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) (n : ℤ) :
    (N.X (-n) ◁ ιTensorObj M N n (-n) 0 (by omega)) ≫
      ιTensorObj N (M ⊗ N) (-n) 0 (-n) (by omega) ≫
        (α_ N M N).inv.f (-n) ≫ (ev ▷ N).f (-n) ≫ (λ_ N).hom.f (-n) =
    (α_ (N.X (-n)) (M.X n) (N.X (-n))).inv ≫
      ((ιTensorObj N M (-n) n 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom) ▷ N.X (-n)) ≫
      (λ_ (N.X (-n))).hom := by
  rw [ι_associator_inv_assoc N M N (-n) n (-n) 0 0 (-n)
    (by omega) (by omega) (by omega), ι_whiskerRight_assoc, ι_leftUnitor_hom]
  simp only [comp_whiskerRight, Category.assoc]

/-- A degree carrying no homogeneous component of coevaluation is a zero term of `M`. -/
private theorem isZero_of_not_mem_coevaluation_support
    (M N : CochainComplex (ModuleCat R) ℤ) [ExactPairing M N]
    (s : Finset ℤ) (η : ∀ i : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ N.X (-i))
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      (η_ M N).f 0 = ∑ i ∈ s, η i ≫ ιTensorObj M N i (-i) 0 (by omega))
    (n : ℤ) (hn : n ∉ s) : IsZero (M.X n) := by
  have he : (λ_ M).inv ≫ (η_ M N ▷ M) ≫ (α_ M N M).hom ≫
      (M ◁ ε_ M N) ≫ (ρ_ M).hom = 𝟙 M := by
    rw [ExactPairing.evaluation_coevaluation_assoc]
    simp
  have hh := congrArg (fun f : M ⟶ M => f.f n) he
  simp only [comp_f, id_f] at hh
  have hl : (λ_ M).inv.f n = (λ_ (M.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ M.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) M 0 n n (by omega) :=
    leftUnitor'_inv M n
  rw [hl] at hh
  simp only [Category.assoc] at hh
  rw [ι_whiskerRight_assoc, ← comp_whiskerRight_assoc, hη,
    sum_whiskerRight, Preadditive.sum_comp] at hh
  have hz : (∑ i ∈ s, (η i ≫ ιTensorObj M N i (-i) 0 (by omega)) ▷ M.X n ≫
      ιTensorObj (M ⊗ N) M 0 n n (by omega) ≫ (α_ M N M).hom.f n ≫
        (M ◁ ε_ M N).f n ≫ (ρ_ M).hom.f n) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    rw [right_snake_summand_eq_zero_assoc M N (ε_ M N) i n
      (by rintro rfl; exact hn hi), zero_comp, comp_zero]
  rw [hz, comp_zero] at hh
  exact (IsZero.iff_id_eq_zero _).mpr hh.symm

/-- A degree whose negative carries no homogeneous component of coevaluation is a zero term
of `N`. -/
private theorem isZero_of_neg_not_mem_coevaluation_support
    (M N : CochainComplex (ModuleCat R) ℤ) [ExactPairing M N]
    (s : Finset ℤ) (η : ∀ i : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ N.X (-i))
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      (η_ M N).f 0 = ∑ i ∈ s, η i ≫ ιTensorObj M N i (-i) 0 (by omega))
    (n : ℤ) (hn : -n ∉ s) : IsZero (N.X n) := by
  have he : (ρ_ N).inv ≫ (N ◁ η_ M N) ≫ (α_ N M N).inv ≫
      (ε_ M N ▷ N) ≫ (λ_ N).hom = 𝟙 N := by
    rw [ExactPairing.coevaluation_evaluation_assoc]
    simp
  have hh := congrArg (fun f : N ⟶ N => f.f n) he
  simp only [comp_f, id_f] at hh
  have hl : (ρ_ N).inv.f n = (ρ_ (N.X n)).inv ≫
      (N.X n ◁ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv) ≫
        ιTensorObj N (𝟙_ (CochainComplex (ModuleCat R) ℤ)) n 0 n (by omega) :=
    rightUnitor'_inv N n
  rw [hl] at hh
  simp only [Category.assoc] at hh
  rw [ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, hη,
    whiskerLeft_sum, Preadditive.sum_comp] at hh
  have hz : (∑ i ∈ s, N.X n ◁ (η i ≫ ιTensorObj M N i (-i) 0 (by omega)) ≫
      ιTensorObj N (M ⊗ N) n 0 n (by omega) ≫ (α_ N M N).inv.f n ≫
        (ε_ M N ▷ N).f n ≫ (λ_ N).hom.f n) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [whiskerLeft_comp]
    simp only [Category.assoc]
    rw [left_snake_summand_eq_zero_assoc M N (ε_ M N) i n
      (by rintro rfl; exact hn hi), zero_comp, comp_zero]
  rw [hz, comp_zero] at hh
  exact (IsZero.iff_id_eq_zero _).mpr hh.symm

/-- A complex whose terms vanish outside a finite set of degrees is bounded. -/
private theorem bounded_of_isZero_outside (M : CochainComplex (ModuleCat R) ℤ)
    (s : Finset ℤ) (hz : ∀ n ∉ s, IsZero (M.X n)) :
    ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := s.finite_toSet.bddAbove
  obtain ⟨a, ha⟩ := s.finite_toSet.bddBelow
  refine ⟨a, b, (M.isStrictlyGE_iff a).mpr ?_, (M.isStrictlyLE_iff b).mpr ?_⟩
  · intro i hi
    exact hz i (fun h => (not_le_of_gt hi) (ha h))
  · intro i hi
    exact hz i (fun h => (not_le_of_gt hi) (hb h))

/-- A complex admitting a left dual is bounded, and so is the dual. -/
private theorem bounded_of_exactPairing (M N : CochainComplex (ModuleCat R) ℤ)
    [ExactPairing M N] : (∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) ∧
      ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b := by
  classical
  obtain ⟨s, hs, _⟩ := finite_support_of_hom_to_tensor M N
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ (η_ M N).f 0)
  let η := fun i =>
    (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ (η_ M N).f 0 ≫
      tensorProjection M N i (-i) 0 (by omega)
  exact ⟨bounded_of_isZero_outside M s (isZero_of_not_mem_coevaluation_support M N s η hs),
    bounded_of_isZero_outside N (s.image (-·)) fun n hn =>
      isZero_of_neg_not_mem_coevaluation_support M N s η hs n
        fun h => hn (Finset.mem_image.2 ⟨-n, h, neg_neg n⟩)⟩

/-- The signed linear dual of a complex of modules: its `n`-th term is `Hom_R(M^{-n}, R)` and its
differential is `-(-1)^n` times the transpose of the differential of `M`. -/
@[sga "4½ Dualite 2.1", sga "5 X 3.7" "partial"]
noncomputable abbrev signedDual (M : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (Module.Dual R (M.X (-n))))
    (fun n => ModuleCat.ofHom
      ((-n.negOnePow : ℤˣ) • Module.Dual.transpose (M.d (-(n + 1)) (-n)).hom))
    (by
      intro n
      apply ModuleCat.hom_ext
      ext f m
      change (- (n + 1).negOnePow : ℤˣ) •
        (((-n.negOnePow : ℤˣ) •
          Module.Dual.transpose (M.d (-(n + 1)) (-n)).hom f)
            ((M.d (-(n + 1 + 1)) (-(n + 1))).hom m)) = 0
      have hd := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (M.d_comp_d (-(n + 1 + 1)) (-(n + 1)) (-n))) m
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at hd
      simp [Module.Dual.transpose_apply, hd])

/-- The differential of the signed linear dual is the signed transpose of the differential. -/
theorem signedDual_d_apply (M : CochainComplex (ModuleCat R) ℤ)
    (n : ℤ) (f : Module.Dual R (M.X (-n))) (m : M.X (-(n + 1))) :
    ((signedDual M).d n (n + 1)).hom f m =
      (-n.negOnePow : ℤˣ) • f ((M.d (-(n + 1)) (-n)).hom m) := by
  dsimp only [signedDual, CochainComplex.of]
  rw [CochainComplex.of_d]
  rfl

/-- A zero term of `M` gives a zero term of the signed linear dual. -/
private theorem signedDual_isZero (M : CochainComplex (ModuleCat R) ℤ)
    (n : ℤ) (h : IsZero (M.X (-n))) : IsZero ((signedDual M).X n) := by
  let := ModuleCat.isZero_iff_subsingleton.mp h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  show Subsingleton (Module.Dual R (M.X (-n)))
  infer_instance

/-- The signed linear dual of a complex supported in `[a, b]` is supported in `[-b, -a]`. -/
theorem signedDual_bounded (M : CochainComplex (ModuleCat R) ℤ)
    (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b] :
    (signedDual M).IsStrictlyGE (-b) ∧ (signedDual M).IsStrictlyLE (-a) := by
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact signedDual_isZero M i (M.isZero_of_isStrictlyLE b (-i) (by omega))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact signedDual_isZero M i (M.isZero_of_isStrictlyGE a (-i) (by omega))

/-- In degree `n`, the first snake composite is the homogeneous snake composite attached to the
`n`-th component of coevaluation. -/
private theorem right_snake_component
    (M N : CochainComplex (ModuleCat R) ℤ)
    (ce : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ N)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (s : Finset ℤ) (η : ∀ i : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ N.X (-i))
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      ce.f 0 = ∑ i ∈ s, η i ≫ ιTensorObj M N i (-i) 0 (by omega))
    (hzero : ∀ i ∉ s, η i = 0) (n : ℤ) :
    ((λ_ M).inv ≫ (ce ▷ M) ≫ (α_ M N M).hom ≫
      (M ◁ ev) ≫ (ρ_ M).hom).f n =
    (λ_ (M.X n)).inv ≫ (η n ▷ M.X n) ≫
      (α_ (M.X n) (N.X (-n)) (M.X n)).hom ≫
      (M.X n ◁ (ιTensorObj N M (-n) n 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom)) ≫
      (ρ_ (M.X n)).hom := by
  classical
  simp only [comp_f]
  have hu : (λ_ M).inv.f n = (λ_ (M.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ M.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) M 0 n n (by omega) :=
    leftUnitor'_inv M n
  rw [hu]
  simp only [Category.assoc]
  rw [ι_whiskerRight_assoc, ← comp_whiskerRight_assoc, hη,
    sum_whiskerRight, Preadditive.sum_comp]
  congr 1
  rw [Finset.sum_eq_single n]
  · rw [comp_whiskerRight]
    simp only [Category.assoc]
    rw [right_snake_summand_diagonal]
  · intro i hi hne
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    rw [right_snake_summand_eq_zero_assoc M N ev i n hne]
    simp
  · intro hn
    rw [hzero n hn]
    simp

/-- In degree `-n`, the second snake composite is the homogeneous snake composite attached to the
`n`-th component of coevaluation. -/
private theorem left_snake_component
    (M N : CochainComplex (ModuleCat R) ℤ)
    (ce : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ N)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (s : Finset ℤ) (η : ∀ i : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ N.X (-i))
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      ce.f 0 = ∑ i ∈ s, η i ≫ ιTensorObj M N i (-i) 0 (by omega))
    (hzero : ∀ i ∉ s, η i = 0) (n : ℤ) :
    ((ρ_ N).inv ≫ (N ◁ ce) ≫ (α_ N M N).inv ≫
      (ev ▷ N) ≫ (λ_ N).hom).f (-n) =
    (ρ_ (N.X (-n))).inv ≫ (N.X (-n) ◁ η n) ≫
      (α_ (N.X (-n)) (M.X n) (N.X (-n))).inv ≫
      ((ιTensorObj N M (-n) n 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom) ▷ N.X (-n)) ≫
      (λ_ (N.X (-n))).hom := by
  classical
  simp only [comp_f]
  have hu : (ρ_ N).inv.f (-n) = (ρ_ (N.X (-n))).inv ≫
      (N.X (-n) ◁ (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv) ≫
        ιTensorObj N (𝟙_ (CochainComplex (ModuleCat R) ℤ)) (-n) 0 (-n) (by omega) :=
    rightUnitor'_inv N (-n)
  rw [hu]
  simp only [Category.assoc]
  rw [ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, hη,
    whiskerLeft_sum, Preadditive.sum_comp]
  congr 1
  rw [Finset.sum_eq_single n]
  · rw [whiskerLeft_comp]
    simp only [Category.assoc]
    rw [left_snake_summand_diagonal]
  · intro i hi hne
    rw [whiskerLeft_comp]
    simp only [Category.assoc]
    rw [left_snake_summand_eq_zero_assoc M N ev i (-n) (by simpa using hne)]
    simp
  · intro hn
    rw [hzero n hn]
    simp

/-- Each homogeneous component of an exact pairing of complexes is an exact pairing of the
corresponding terms. -/
private theorem homogeneous_exactPairing
    (M N : CochainComplex (ModuleCat R) ℤ) [ExactPairing M N]
    (s : Finset ℤ) (η : ∀ i : ℤ, 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ N.X (-i))
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      (η_ M N).f 0 = ∑ i ∈ s, η i ≫ ιTensorObj M N i (-i) 0 (by omega))
    (hzero : ∀ i ∉ s, η i = 0) (n : ℤ) :
    ∃ q : ExactPairing (M.X n) (N.X (-n)),
      @ExactPairing.coevaluation _ _ _ _ _ q = η n ∧
      @ExactPairing.evaluation _ _ _ _ _ q =
        ιTensorObj N M (-n) n 0 (by omega) ≫ (ε_ M N).f 0 ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom := by
  let ε := ιTensorObj N M (-n) n 0 (by omega) ≫ (ε_ M N).f 0 ≫
    (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom
  have hr := right_snake_component M N (η_ M N) (ε_ M N) s η hη hzero n
  have hl := left_snake_component M N (η_ M N) (ε_ M N) s η hη hzero n
  rw [ExactPairing.evaluation_coevaluation_assoc] at hr
  rw [ExactPairing.coevaluation_evaluation_assoc] at hl
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, id_f] at hr hl
  let q : ExactPairing (M.X n) (N.X (-n)) := {
    coevaluation' := η n
    evaluation' := ε
    coevaluation_evaluation' := by
      apply (cancel_epi (ρ_ (N.X (-n))).inv).mp
      apply (cancel_mono (λ_ (N.X (-n))).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.id_comp, Iso.inv_hom_id_assoc] using hl.symm
    evaluation_coevaluation' := by
      apply (cancel_epi (λ_ (M.X n)).inv).mp
      apply (cancel_mono (ρ_ (M.X n)).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.id_comp, Iso.inv_hom_id_assoc] using hr.symm }
  exact ⟨q, rfl, rfl⟩

/-- The differential of a left dual is the signed transpose, in the form needed for
`IsLinearDualPairing`: the degrees are supplied as equalities and the identifications with the
linear duals are transported along them. -/
private theorem signed_transpose_cast
    (M N : CochainComplex (ModuleCat R) ℤ)
    (ev : N ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (i j n n' : ℤ) (h₀ : -i = n) (h₁ : -j = n')
    (hn : n + 1 = n') (hi : j + 1 = i)
    (e₀ : Module.Dual R (M.X i) ≃ₗ[R] N.X (-i))
    (e₁ : Module.Dual R (M.X j) ≃ₗ[R] N.X (-j))
    (he₀ : ∀ (x : N.X (-i)) (m : M.X i),
      (ιTensorObj N M (-i) i 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
        (x ⊗ₜ[R] m) = e₀.symm x m)
    (he₁ : ∀ (x : N.X (-j)) (m : M.X j),
      (ιTensorObj N M (-j) j 0 (by omega) ≫ ev.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
        (x ⊗ₜ[R] m) = e₁.symm x m)
    (x : N.X n) :
    (N.d n n').hom x = (-n.negOnePow : ℤˣ) •
      (Eq.mp (congrArg ModuleCat.carrier (congrArg N.X h₁))
        (e₁ (Module.Dual.transpose (M.d j i).hom
          (e₀.symm (Eq.mpr (congrArg ModuleCat.carrier (congrArg N.X h₀)) x))))) := by
  subst n n'
  show (N.d (-i) (-j)).hom x = (-(-i).negOnePow : ℤˣ) •
    e₁ (Module.Dual.transpose (M.d j i).hom (e₀.symm x))
  apply e₁.symm.injective
  rw [map_zsmul_unit, e₁.symm_apply_apply]
  ext m
  have hh := evaluation_d_apply M N ev (-i) (-j) j i hn hi (by omega) x m
  rw [he₀, he₁] at hh
  show e₁.symm ((N.d (-i) (-j)).hom x) m =
    (-(-i).negOnePow : ℤˣ) • e₀.symm x ((M.d j i).hom m)
  simpa using eq_neg_of_add_eq_zero_left hh

-- This proof picks, degree by degree, a homogeneous exact pairing and the identification of
-- its dual term with a linear dual, and then discharges five separate obligations against
-- those choices; the default heartbeat budget is not enough for that.
/-- A left dual of a complex has finite projective terms, as does the complex itself, and the
pairing is the termwise linear-dual pairing with signed transpose differential. -/
private theorem isLinearDualPairing_of_exactPairing
    (M N : CochainComplex (ModuleCat R) ℤ) (p : ExactPairing M N) :
    (∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) ∧
    (∀ n : ℤ, Module.Finite R (N.X n) ∧ Module.Projective R (N.X n)) ∧
    IsLinearDualPairing R M N p := by
  classical
  let := p
  obtain ⟨s, hs, hz⟩ := finite_support_of_hom_to_tensor M N
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ (η_ M N).f 0)
  let η := fun i =>
    (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ (η_ M N).f 0 ≫
      tensorProjection M N i (-i) 0 (by omega)
  let ε := fun i => ιTensorObj N M (-i) i 0 (by omega) ≫ (ε_ M N).f 0 ≫
    (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom
  have hq (n : ℤ) := homogeneous_exactPairing M N s η hs hz n
  choose q hqη hqε using hq
  have ht (n : ℤ) : Module.Finite R (M.X n) ∧ Module.Projective R (M.X n) ∧
      Module.Finite R (N.X (-n)) ∧ Module.Projective R (N.X (-n)) ∧
      ∃ e : Module.Dual R (M.X n) ≃ₗ[R] N.X (-n),
        ∀ (x : N.X (-n)) (m : M.X n), (ε n).hom (x ⊗ₜ[R] m) = e.symm x m := by
    let := q n
    obtain ⟨h₁, h₂, h₃, h₄, e, _, he⟩ :=
      ModuleCat.LeftDual.finite_projective_and_linearDual_equiv_of_exactPairing
        R (M.X n) (N.X (-n))
    exact ⟨h₁, h₂, h₃, h₄, e, by simpa only [hqε n] using he⟩
  choose hM₁ hM₂ hN₁ hN₂ e he using ht
  refine ⟨fun n => ⟨hM₁ n, hM₂ n⟩,
    fun n => by
      have h := And.intro (hN₁ (-n)) (hN₂ (-n))
      rw [neg_neg] at h
      exact h,
    s, η, ε, e, ?_, ?_, ?_, he, ?_⟩
  · apply (cancel_epi (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv).mp
    simpa only [η, Category.assoc, Iso.inv_hom_id_assoc] using hs
  · intro n
    simp only [ε, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro n
    exact ⟨q n, hqη n, hqε n⟩
  · intro n x
    exact signed_transpose_cast M N (ε_ M N) (-n) (-(n + 1)) n (n + 1)
      (by omega) (by omega) rfl (by omega) (e (-n)) (e (-(n + 1)))
      (he (-n)) (he (-(n + 1))) x

/-- The identity tensors of two finite projective modules are compatible with a linear map: the
map on the right factor and its transpose on the left factor agree. -/
private theorem identityTensor_naturality
    (A B : Type u) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B) :
    TensorProduct.map LinearMap.id f (ModuleCat.LeftDual.identityTensor R A) =
      TensorProduct.map (Module.Dual.transpose f) LinearMap.id
        (ModuleCat.LeftDual.identityTensor R B) := by
  apply (dualTensorHom_bijective (R := R) (M := A) (N := B)).injective
  have h₁ := LinearMap.congr_fun (dualTensorHom_comp_lTensor (R := R) (M := A) f)
    (ModuleCat.LeftDual.identityTensor R A)
  have h₂ := LinearMap.congr_fun
    (dualTensorHom_comp_rTensor_dualMap (R := R) (P := B) f)
      (ModuleCat.LeftDual.identityTensor R B)
  simp only [LinearMap.comp_apply, ModuleCat.LeftDual.dualTensorHom_identityTensor,
    LinearMap.compRight_apply, LinearMap.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The canonical coevaluations of finite projective modules are natural: whiskering by a map on
the left agrees with whiskering by its transpose on the right. -/
private theorem canonical_coevaluation_naturality
    (A B : ModuleCat R) [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] (f : A ⟶ B) :
    let := ModuleCat.LeftDual.finiteProjectiveExactPairing R A
    let := ModuleCat.LeftDual.finiteProjectiveExactPairing R B
    η_ A (ModuleCat.of R (Module.Dual R A)) ≫
      (f ▷ ModuleCat.of R (Module.Dual R A)) =
    η_ B (ModuleCat.of R (Module.Dual R B)) ≫
      (B ◁ ModuleCat.ofHom (Module.Dual.transpose f.hom)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  show TensorProduct.map f.hom LinearMap.id
    ((1 : R) • TensorProduct.comm R _ _ (ModuleCat.LeftDual.identityTensor R A)) =
    TensorProduct.map LinearMap.id (Module.Dual.transpose f.hom)
      ((1 : R) • TensorProduct.comm R _ _ (ModuleCat.LeftDual.identityTensor R B))
  rw [one_smul, one_smul, TensorProduct.map_comm, TensorProduct.map_comm,
    identityTensor_naturality]

/-- The canonical exact pairing of `M^i` with the `j`-th term of the signed linear dual, for
`i + j = 0`. -/
@[instance_reducible]
private noncomputable def dualPairing
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (i j : ℤ) (h : i + j = 0) : ExactPairing (M.X i) ((signedDual M).X j) := by
  have hij : i = -j := by omega
  subst i
  letI := (hM (-j)).1
  letI := (hM (-j)).2
  exact ModuleCat.LeftDual.finiteProjectiveExactPairing R (M.X (-j))

/-- Evaluation of the signed linear dual in degree `0`, assembled from its homogeneous
components. -/
private noncomputable def dualEvaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) :
    ((signedDual M) ⊗ M).X 0 ⟶ 𝟙_ (ModuleCat R) :=
  Sigma.desc (fun a : {a : ℤ × ℤ // a.1 + a.2 = 0} =>
    @ExactPairing.evaluation _ _ _ _ _ (dualPairing M hM a.1.2 a.1.1 (by omega)))

/-- Evaluation of the signed linear dual restricts on each summand to the canonical evaluation. -/
private theorem ι_dualEvaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (i j : ℤ) (h : i + j = 0) :
    ιTensorObj (signedDual M) M i j 0 h ≫ dualEvaluation M hM =
      @ExactPairing.evaluation _ _ _ _ _ (dualPairing M hM j i (by omega)) :=
  Sigma.ι_desc _ _

/-- `ιTensorObj_d` with the successor degrees supplied as equalities. -/
private theorem ιTensorObj_d_at (M N : CochainComplex (ModuleCat R) ℤ)
    (i i' j j' k k' : ℤ) (hi : i + 1 = i') (hj : j + 1 = j')
    (hk : k + 1 = k') (h : i + j = k) :
    ιTensorObj M N i j k h ≫ (M ⊗ N).d k k' =
      (M.d i i' ▷ N.X j) ≫ ιTensorObj M N i' j k' (by omega) +
      i.negOnePow • ((M.X i ◁ N.d j j') ≫ ιTensorObj M N i j' k' (by omega)) := by
  subst i' j' k'
  exact ιTensorObj_d M N i j k h

/-- Evaluation of the signed linear dual kills the differential, so it is a morphism of
complexes into the unit complex. -/
private theorem dualEvaluation_d (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) :
    ((signedDual M) ⊗ M).d (-1) 0 ≫ dualEvaluation M hM = 0 := by
  apply Sigma.hom_ext
  rintro ⟨⟨i, j⟩, hij⟩
  change i + j = -1 at hij
  show ιTensorObj (signedDual M) M i j (-1) hij ≫
    (((signedDual M) ⊗ M).d (-1) 0 ≫ dualEvaluation M hM) = _
  have hj : j = -(i + 1) := by omega
  subst j
  rw [← Category.assoc, ιTensorObj_d_at (signedDual M) M i (i + 1)
    (-(i + 1)) (-i) (-1) 0 rfl (by omega) (by omega),
    Preadditive.add_comp, Linear.units_smul_comp]
  simp only [Category.assoc, ι_dualEvaluation]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x m
  show ((signedDual M).d i (i + 1)).hom x m +
    i.negOnePow • x ((M.d (-(i + 1)) (-i)).hom m) = 0
  rw [signedDual_d_apply]
  simp

/-- Evaluation of the signed linear dual, as a morphism of complexes into the unit complex. -/
private noncomputable def dualEvaluationHom (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) :
    (signedDual M) ⊗ M ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ) :=
  mkHomToSingle (dualEvaluation M hM) (by
    intro i hi
    have : i = -1 := by change i + 1 = 0 at hi; omega
    subst i
    exact dualEvaluation_d M hM)

/-- Left whiskering commutes with the action of a unit of `ℤ`. -/
private theorem whiskerLeft_units_smul (A B C : ModuleCat R) (u : ℤˣ) (f : B ⟶ C) :
    A ◁ (u • f) = u • (A ◁ f) :=
  map_zsmul_unit ((tensorLeft A).mapAddHom) u f

/-- The two homogeneous components of coevaluation adjacent to degree `n` cancel against the
differentials, which is the sign rule for the differential of the signed linear dual. -/
private theorem dualCoevaluation_d (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) (n : ℤ) :
    (@ExactPairing.coevaluation _ _ _ _ _
      (dualPairing M hM (-(n + 1)) (n + 1) (by omega))) ≫
      (M.d (-(n + 1)) (-n) ▷ (signedDual M).X (n + 1)) +
    (-n).negOnePow • ((@ExactPairing.coevaluation _ _ _ _ _
      (dualPairing M hM (-n) n (by omega))) ≫
      (M.X (-n) ◁ (signedDual M).d n (n + 1))) = 0 := by
  let := (hM (-(n + 1))).1
  let := (hM (-(n + 1))).2
  let := (hM (-n)).1
  let := (hM (-n)).2
  have hd : (signedDual M).d n (n + 1) =
      (-n.negOnePow : ℤˣ) • ModuleCat.ofHom
        (Module.Dual.transpose (M.d (-(n + 1)) (-n)).hom) := by
    apply ModuleCat.hom_ext
    ext f m
    exact signedDual_d_apply M n f m
  rw [hd, whiskerLeft_units_smul, Linear.comp_units_smul, smul_smul]
  have hn : (-n).negOnePow * (-n.negOnePow : ℤˣ) = -1 := by
    rcases Int.units_eq_one_or n.negOnePow with h | h <;>
      simp only [Int.negOnePow_neg, h] <;> decide
  rw [hn, Units.neg_smul, one_smul]
  show _ + -_ = 0
  rw [add_neg_eq_zero]
  exact canonical_coevaluation_naturality (M.X (-(n + 1))) (M.X (-n))
    (M.d (-(n + 1)) (-n))

/-- Two finitely supported families on `ℤ` whose terms cancel after a shift have opposite
sums. -/
private theorem sum_add_eq_zero_of_shift {A : Type*} [AddCommGroup A]
    (s : Finset ℤ) (f g : ℤ → A) (hf : ∀ i ∉ s, f i = 0)
    (hg : ∀ i ∉ s, g i = 0) (h : ∀ i, f i + g (i + 1) = 0) :
    (∑ i ∈ s, f i) + ∑ i ∈ s, g i = 0 := by
  classical
  have he (i : ℤ) : f i = -g (i + 1) := eq_neg_of_add_eq_zero_left (h i)
  have hs : ∑ i ∈ s, f i = ∑ i ∈ s, -g i := by
    apply Finset.sum_bij_ne_zero (fun i _ _ => i + 1)
    · intro i hi hne
      by_contra hn
      exact hne (by rw [he, hg _ hn, neg_zero])
    · intros
      omega
    · intro j hj hne
      have hne' : f (j - 1) ≠ 0 := by simpa only [he, sub_add_cancel] using hne
      exact ⟨j - 1, Classical.byContradiction fun hn => hne' (hf _ hn), hne', by omega⟩
    · intro i _ _
      exact he i
  rw [hs, Finset.sum_neg_distrib, neg_add_cancel]

/-- The `i`-th homogeneous component of the coevaluation of the signed linear dual. -/
private noncomputable abbrev homogeneousCoevaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (i : ℤ) : 𝟙_ (ModuleCat R) ⟶ M.X i ⊗ (signedDual M).X (-i) :=
  @ExactPairing.coevaluation _ _ _ _ _ (dualPairing M hM i (-i) (by omega))

/-- `dualCoevaluation_d`, pushed into the degree-`1` term of the total complex, with the
successor degrees supplied as equalities. -/
private theorem dualCoevaluation_d_tensor
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (i i' j j' : ℤ) (hi : i + 1 = i') (hj : j + 1 = j')
    (h₀ : i + j' = 0) (h₁ : i' + j = 0) :
    ((@ExactPairing.coevaluation _ _ _ _ _ (dualPairing M hM i j' h₀)) ≫
      (M.d i i' ▷ (signedDual M).X j') ≫
        ιTensorObj M (signedDual M) i' j' 1 (by omega)) +
    i'.negOnePow • ((@ExactPairing.coevaluation _ _ _ _ _ (dualPairing M hM i' j h₁)) ≫
      (M.X i' ◁ (signedDual M).d j (j + 1)) ≫
        ιTensorObj M (signedDual M) i' (j + 1) 1 (by omega)) = 0 := by
  subst j'
  obtain rfl : i' = -j := by omega
  obtain rfl : i = -(j + 1) := by omega
  have h := congrArg (fun f => f ≫
    ιTensorObj M (signedDual M) (-j) (j + 1) 1 (by omega))
      (dualCoevaluation_d M hM j)
  simpa only [Preadditive.add_comp, Linear.units_smul_comp, zero_comp, Category.assoc] using h

/-- The homogeneous components of coevaluation cancel in consecutive degrees. -/
private theorem homogeneousCoevaluation_d
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) (i : ℤ) :
    (homogeneousCoevaluation M hM i ≫ (M.d i (i + 1) ▷ (signedDual M).X (-i)) ≫
      ιTensorObj M (signedDual M) (i + 1) (-i) 1 (by omega)) +
    (i + 1).negOnePow • (homogeneousCoevaluation M hM (i + 1) ≫
      (M.X (i + 1) ◁ (signedDual M).d (-(i + 1)) (-(i + 1) + 1)) ≫
      ιTensorObj M (signedDual M) (i + 1) (-(i + 1) + 1) 1 (by omega)) = 0 :=
  dualCoevaluation_d_tensor M hM i (i + 1) (-(i + 1)) (-i)
    rfl (by omega) (by omega) (by omega)

/-- In a degree where `M` vanishes, the homogeneous component of coevaluation vanishes. -/
private theorem homogeneousCoevaluation_eq_zero
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (i : ℤ) (hi : IsZero (M.X i)) : homogeneousCoevaluation M hM i = 0 :=
  ((tensorRight ((signedDual M).X (-i))).map_isZero hi).eq_of_tgt _ _

/-- The finite sum of homogeneous components of coevaluation is a cocycle, hence extends to a
morphism from the unit complex. -/
private theorem sum_homogeneousCoevaluation_d
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (s : Finset ℤ) (hs : ∀ i ∉ s, homogeneousCoevaluation M hM i = 0) :
    (∑ i ∈ s, homogeneousCoevaluation M hM i ≫
      ιTensorObj M (signedDual M) i (-i) 0 (by omega)) ≫
        (M ⊗ signedDual M).d 0 1 = 0 := by
  classical
  rw [Preadditive.sum_comp]
  simp only [Category.assoc]
  have hd (i : ℤ) := ιTensorObj_d M (signedDual M) i (-i) 0 (by omega)
  change ∀ i : ℤ, ιTensorObj M (signedDual M) i (-i) 0 _ ≫
    (M ⊗ signedDual M).d 0 1 = _ at hd
  simp only [hd, Preadditive.comp_add, Linear.comp_units_smul]
  rw [Finset.sum_add_distrib]
  exact sum_add_eq_zero_of_shift _ _ _ (fun i hi => by rw [hs i hi, zero_comp])
    (fun i hi => by rw [hs i hi, zero_comp, smul_zero]) (homogeneousCoevaluation_d M hM)

/-- For a complex strictly bounded between `a` and `b`, the homogeneous components of
coevaluation vanish in every degree outside `[a, b]`. -/
private theorem homogeneousCoevaluation_eq_zero_of_notMem_Icc
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b] (i : ℤ) (hi : i ∉ Finset.Icc a b) :
    homogeneousCoevaluation M hM i = 0 := by
  apply homogeneousCoevaluation_eq_zero
  by_cases h : i < a
  · exact M.isZero_of_isStrictlyGE a i h
  · exact M.isZero_of_isStrictlyLE b i (by
      simp only [Finset.mem_Icc] at hi
      omega)

/-- The evaluation of the signed linear dual, restricted to a bidegree, is the termwise
evaluation. -/
private theorem ι_dualEvaluationHom_f
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) (n : ℤ) :
    ιTensorObj (signedDual M) M (-n) n 0 (by omega) ≫ (dualEvaluationHom M hM).f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom =
      @ExactPairing.evaluation _ _ _ _ _ (dualPairing M hM n (-n) (by omega)) := by
  simp only [dualEvaluationHom, mkHomToSingle_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ι_dualEvaluation]

/-- The left snake identity for a coevaluation of the signed linear dual built from the
homogeneous components. -/
private theorem signedDual_coevaluation_evaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (s : Finset ℤ) (ce : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ signedDual M)
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ ce.f 0 =
      ∑ i ∈ s, homogeneousCoevaluation M hM i ≫
        ιTensorObj M (signedDual M) i (-i) 0 (by omega))
    (hz : ∀ i ∉ s, homogeneousCoevaluation M hM i = 0) :
    signedDual M ◁ ce ≫ (α_ _ _ _).inv ≫ dualEvaluationHom M hM ▷ signedDual M =
      (ρ_ (signedDual M)).hom ≫ (λ_ (signedDual M)).inv := by
  apply (cancel_epi (ρ_ (signedDual M)).inv).mp
  apply (cancel_mono (λ_ (signedDual M)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro n
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, -k = n := ⟨-n, neg_neg n⟩
  rw [left_snake_component M (signedDual M) ce _ s
    (homogeneousCoevaluation M hM) hη hz k, ι_dualEvaluationHom_f]
  let := dualPairing M hM k (-k) (by omega)
  show (ρ_ ((signedDual M).X (-k))).inv ≫
    ((signedDual M).X (-k) ◁ η_ (M.X k) ((signedDual M).X (-k))) ≫
    (α_ _ _ _).inv ≫ (ε_ (M.X k) ((signedDual M).X (-k)) ▷ _) ≫
    (λ_ _).hom = 𝟙 _
  rw [ExactPairing.coevaluation_evaluation_assoc]
  simp

/-- The right snake identity for a coevaluation of the signed linear dual built from the
homogeneous components. -/
private theorem signedDual_evaluation_coevaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i))
    (s : Finset ℤ) (ce : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ signedDual M)
    (hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫ ce.f 0 =
      ∑ i ∈ s, homogeneousCoevaluation M hM i ≫
        ιTensorObj M (signedDual M) i (-i) 0 (by omega))
    (hz : ∀ i ∉ s, homogeneousCoevaluation M hM i = 0) :
    ce ▷ M ≫ (α_ _ _ _).hom ≫ M ◁ dualEvaluationHom M hM = (λ_ M).hom ≫ (ρ_ M).inv := by
  apply (cancel_epi (λ_ M).inv).mp
  apply (cancel_mono (ρ_ M).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro n
  rw [right_snake_component M (signedDual M) ce _ s
    (homogeneousCoevaluation M hM) hη hz n, ι_dualEvaluationHom_f]
  let := dualPairing M hM n (-n) (by omega)
  show (λ_ (M.X n)).inv ≫ (η_ (M.X n) ((signedDual M).X (-n)) ▷ _) ≫
    (α_ _ _ _).hom ≫ (M.X n ◁ ε_ (M.X n) ((signedDual M).X (-n))) ≫
    (ρ_ _).hom = 𝟙 _
  rw [ExactPairing.evaluation_coevaluation_assoc]
  simp

/-- Every bounded complex of finite projective modules has the signed linear dual as a left
dual. -/
private theorem exists_exactPairing_of_bounded_finiteProjective
    (M : CochainComplex (ModuleCat R) ℤ)
    (hbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hM : ∀ i : ℤ, Module.Finite R (M.X i) ∧ Module.Projective R (M.X i)) :
    ∃ p : ExactPairing M (signedDual M), IsLinearDualPairing R M (signedDual M) p := by
  classical
  obtain ⟨a, b, ha, hb⟩ := hbounded
  have hz := homogeneousCoevaluation_eq_zero_of_notMem_Icc M hM a b
  let ce₀ := ∑ i ∈ Finset.Icc a b, homogeneousCoevaluation M hM i ≫
    ιTensorObj M (signedDual M) i (-i) 0 (by omega)
  have hce : ∀ k : ℤ, (ComplexShape.up ℤ).Rel 0 k →
      ce₀ ≫ (M ⊗ signedDual M).d 0 k = 0 := by
    intro k hk
    obtain rfl : k = 1 := by
      change 0 + 1 = k at hk
      omega
    exact sum_homogeneousCoevaluation_d M hM _ hz
  let ce : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ signedDual M :=
    mkHomFromSingle ce₀ hce
  have hη : (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      ce.f 0 = ce₀ := by
    simp only [ce, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  let p : ExactPairing M (signedDual M) := {
    coevaluation' := ce
    evaluation' := dualEvaluationHom M hM
    coevaluation_evaluation' := signedDual_coevaluation_evaluation M hM _ ce hη hz
    evaluation_coevaluation' := signedDual_evaluation_coevaluation M hM _ ce hη hz }
  exact ⟨p, (isLinearDualPairing_of_exactPairing M (signedDual M) p).2.2⟩

end Helpers

/-- A complex of modules and a chosen left dual are bounded complexes of finite projective
modules, and the pairing is the termwise linear-dual pairing with signed transpose differential.
Conversely, every bounded complex of finite projective modules admits exactly this construction
as a left dual. -/
@[stacks 0FNK]
theorem exactPairing_iff_bounded_finiteProjective (R : Type u) [CommRing R] :
    (∀ (M N : CochainComplex (ModuleCat R) ℤ) (p : ExactPairing M N),
      (∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) ∧
        (∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b) ∧
        (∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) ∧
        (∀ n : ℤ, Module.Finite R (N.X n) ∧ Module.Projective R (N.X n)) ∧
        IsLinearDualPairing R M N p) ∧
      (∀ M : CochainComplex (ModuleCat R) ℤ,
        (∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) →
        (∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) →
        ∃ (N : CochainComplex (ModuleCat R) ℤ) (p : ExactPairing M N),
          (∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b) ∧
            IsLinearDualPairing R M N p) := by
  refine ⟨fun M N p => ?_, fun M hb hM => ?_⟩
  · let := p
    exact ⟨(bounded_of_exactPairing M N).1, (bounded_of_exactPairing M N).2,
      isLinearDualPairing_of_exactPairing M N p⟩
  · obtain ⟨p, hp⟩ := exists_exactPairing_of_bounded_finiteProjective M hb hM
    let := p
    exact ⟨signedDual M, p, (bounded_of_exactPairing M (signedDual M)).2, hp⟩

/-! ## Tensoring with the left dual -/

section TensorLeftDual

variable {R : Type u} [CommRing R]

open CochainComplex CochainComplex.HomComplex

-- The proofs below rewrite through the terms of `HomComplexR`, which are `ModuleCat.of R` of a
-- type of cochains; unification has to unfold that, so reducible-transparency `isDefEq` is
-- disabled throughout this section.
set_option backward.isDefEq.respectTransparency false

/-- The currying isomorphism of Stacks 0A5Y on a homogeneous summand, with the degrees supplied
as equalities rather than as sums. -/
public lemma curryIso_hom_apply_degree
    (K L M : CochainComplex (ModuleCat R) ℤ) (n r s t p q : ℤ)
    (hrs : r + s = t) (htp : t + n = p) (hrq : r + n = q)
    (α : Cochain K (HomComplexR R L M) n) (x : K.X r) (y : L.X s) :
    ((((Stacks.HomComplex.Currying.curryIso K L M).hom.f n).hom α).v t p htp).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
        (((α.v r q hrq).hom x).v s p (by omega)).hom y := by
  subst q
  exact Stacks.HomComplex.Currying.curryIso_hom_apply K L M n r s t p hrs htp α x y

/-- The transpose of a morphism `φ : K ⟶ Hom^•(L, M)` evaluates on the summand `K^r ⊗ L^s` as
`φ` evaluated first at `x` and then at `y`. -/
private lemma tensorHomEquiv_apply
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (φ : K ⟶ HomComplexR R L M) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((Stacks.HomComplex.MonoidalClosed.tensorHomEquiv K L M φ).f t).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
        (((φ.f r).hom x).v s t (by omega)).hom y := by
  have h := curryIso_hom_apply_degree K L M 0 r s t t r
    hrs (add_zero t) (add_zero r) (Cochain.ofHom φ) x y
  rw [← Stacks.HomComplex.MonoidalClosed.ofHom_tensorHomEquiv] at h
  simp only [Cochain.ofHom_v] at h
  convert h using 1

/-- The tensor–Hom adjunction `(- ⊗ M) ⊣ Hom^•(M, -)` on cochain complexes, obtained from the
transpose bijection of Stacks 0A5Y. -/
noncomputable def tensorHomAdjunction
    (M : CochainComplex (ModuleCat R) ℤ) :
    tensorRight M ⊣ Stacks.HomComplex.MonoidalClosed.homComplexFunctor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K L => (Stacks.HomComplex.MonoidalClosed.tensorHomEquiv K M L).symm
      homEquiv_naturality_left_symm :=
        Stacks.HomComplex.MonoidalClosed.tensorHomEquiv_naturality_left
      homEquiv_naturality_right := by
        intro K L L' f g
        change (Stacks.HomComplex.MonoidalClosed.tensorHomEquiv K M L').symm (f ≫ g) =
          (Stacks.HomComplex.MonoidalClosed.tensorHomEquiv K M L).symm f ≫
            Stacks.HomComplex.TensorHomMap.postcomp R M L L' g
        apply (Stacks.HomComplex.MonoidalClosed.tensorHomEquiv K M L').injective
        rw [Equiv.apply_symm_apply,
          Stacks.HomComplex.MonoidalClosed.tensorHomEquiv_naturality_right,
          Equiv.apply_symm_apply] }

/-- The functorial action of the Hom complex in its second variable alone is
postcomposition. -/
private theorem homCxMap_id_postcomp
    (M K L : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ L) :
    Stacks.HomComplex.TensorHomComparison.HomCxMap M M K L (𝟙 M) f =
      Stacks.HomComplex.TensorHomMap.postcomp R M K L f := by
  ext n z
  apply Cochain.ext
  intro i j hij
  show (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg M M K L (𝟙 M) f n z).v i j hij =
    (z.comp (Cochain.ofHom f) (add_zero n)).v i j hij
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v, Cochain.comp_v _ _ _ i j j hij (add_zero
    j)]
  simp

/-- The counit of the adjunction `(- ⊗ M) ⊣ (- ⊗ N)` attached to an exact pairing is the
evaluation of the pairing, read through the associator and the right unitor. -/
private theorem tensorRightAdjunction_counit
    {C : Type*} [Category C] [MonoidalCategory C] (M N K : C) [ExactPairing M N] :
    (tensorRightAdjunction M N).counit.app K =
      (α_ K N M).hom ≫ (K ◁ ε_ M N) ≫ (ρ_ K).hom := by
  show (𝟙 (K ⊗ N) ▷ M) ≫ _ = _
  rw [id_whiskerRight, Category.id_comp]
  rfl

/-- The counit of `(- ⊗ M) ⊣ (- ⊗ N)`, evaluated on the summand `(K^p ⊗ N^q) ⊗ M^{-q}`: it
sends `(x ⊗ y) ⊗ m` to `ε(y ⊗ m) • x`. -/
private theorem tensorRightAdjunction_counit_apply
    (M N K : CochainComplex (ModuleCat R) ℤ) [ExactPairing M N]
    (n p q : ℤ) (hpq : p + q = n)
    (x : K.X p) (y : N.X q) (m : M.X (-q)) :
    (((tensorRightAdjunction M N).counit.app K).f p).hom
      ((ιTensorObj (K ⊗ N) M n (-q) p (by omega)).hom
        (((ιTensorObj K N p q n hpq).hom (x ⊗ₜ[R] y)) ⊗ₜ[R] m)) =
      ((ιTensorObj N M q (-q) 0 (by omega) ≫ (ε_ M N).f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
          (y ⊗ₜ[R] m)) • x := by
  have h := ι_associator_hom K N M p q (-q) n 0 p hpq (by omega) (by omega)
  have h' := congrArg (fun f => f ≫ (K ◁ ε_ M N).f p ≫ (ρ_ K).hom.f p) h
  simp only [Category.assoc] at h'
  rw [reassoc_of% (ι_whiskerLeft K (N ⊗ M) _ (ε_ M N) p 0 p (add_zero p)),
    ι_rightUnitor_hom] at h'
  rw [tensorRightAdjunction_counit]
  show (((ιTensorObj K N p q n hpq ▷ M.X (-q)) ≫
    ιTensorObj (K ⊗ N) M n (-q) p (by omega) ≫
    (α_ K N M).hom.f p ≫ (K ◁ ε_ M N).f p ≫ (ρ_ K).hom.f p).hom
      ((x ⊗ₜ[R] y) ⊗ₜ[R] m)) = _
  rw [h']
  rfl

/-- **Stacks 0FNL.** For a complex `M` with left dual `N`, the canonical sign-free tensor–Hom
morphism is a natural isomorphism `K ⊗ N ≅ Hom^•(M, K)`. On the summand `K^p ⊗ N^q`, its
component in `Hom(M^{-q}, K^p)` sends `x ⊗ y` to the map `m ↦ ε(y ⊗ m) • x`. -/
@[stacks 0FNL]
theorem tensorLeftDualIsoHomComplex
    (M N : CochainComplex (ModuleCat R) ℤ) (pairing : ExactPairing M N) :
    letI := pairing
    ∃ e : ∀ K : CochainComplex (ModuleCat R) ℤ,
        K ⊗ N ≅ HomComplexR R M K,
      (∀ (K : CochainComplex (ModuleCat R) ℤ) (n p q : ℤ) (hpq : p + q = n)
          (x : K.X p) (y : N.X q) (m : M.X (-q)),
        (((((e K).hom.f n).hom
            ((ιTensorObj K N p q n hpq).hom (x ⊗ₜ[R] y))) : Cochain M K n).v
              (-q) p (by omega)).hom m =
          ((ιTensorObj N M q (-q) 0 (by omega) ≫ (ε_ M N).f 0 ≫
              (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom
            (y ⊗ₜ[R] m)) • x) ∧
        ∀ (K L : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ L),
          (e K).hom ≫ Stacks.HomComplex.TensorHomComparison.HomCxMap M M K L (𝟙 M) f =
            (f ▷ N) ≫ (e L).hom := by
  let := pairing
  let a := tensorRightAdjunction M N
  let b := tensorHomAdjunction M
  let e := a.rightAdjointUniq b
  refine ⟨fun K => e.app K, ?_, ?_⟩
  · intro K n p q hpq x y m
    have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app a b K
    change ((tensorHomAdjunction M).homEquiv (K ⊗ N) K).symm
      (e.hom.app K) = a.counit.app K at h
    rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at h
    change Stacks.HomComplex.MonoidalClosed.tensorHomEquiv (K ⊗ N) M K (e.hom.app K) = a.counit.app
      K at h
    have hc := tensorHomEquiv_apply
      (K ⊗ N) M K (e.hom.app K) n (-q) p (by omega)
      ((ιTensorObj K N p q n hpq).hom (x ⊗ₜ[R] y)) m
    rw [h] at hc
    exact
      hc.symm.trans (tensorRightAdjunction_counit_apply M N K n p q hpq x y m)
  · intro K L f
    rw [homCxMap_id_postcomp]
    exact (e.hom.naturality f).symm

end TensorLeftDual

end CochainComplex.LeftDual

end
