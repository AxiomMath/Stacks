module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The kernel of `E ⊗ F → Sym² F` along a split injection

Let `S` be a commutative ring and `f : E → F` a linear map with a retraction, whose cokernel
`g : F → G` has projective target. Write

`μ_h : E ⊗ N → Sym² N`, `e ⊗ v ↦ h(e) · v`

for a linear map `h : E → N`. The multiplication `μ_f : E ⊗ F → Sym² F` is the first map of the
sequence `E ⊗ F → Sym² F → Sym² G → 0` of Stacks Tag 00DO, and `μ_id : E ⊗ E → Sym² E` is the
multiplication of `E`. Then `1 ⊗ f : E ⊗ E → E ⊗ F` carries the kernel of `μ_id` onto the
kernel of `μ_f`, with no hypothesis on `2`.

## Main definitions

* `SymPow.ιOne`: the degree-one generator `N → Sym¹ N`.
* `SymPow.sqMul`: the map `μ_h : E ⊗ N → Sym² N`, `e ⊗ v ↦ ι(h e) · ι v`.

## Main results

* `SymPow.sqMul_id_surjective`: `μ_id : E ⊗ E → Sym² E` is surjective.
* `SymPow.sqMul_comp_lTensor`: `μ_N ∘ (1 ⊗ h) = Sym²(h) ∘ μ_id`, for any `h : E → N`.
* `SymPow.exists_lTensor_eq_of_sqMul_eq_zero`: every element of the kernel of `μ_f` is the image
  under `1 ⊗ f` of an element of the kernel of `μ_id`, when `f` has a retraction and its
  cokernel is projective.
-/

@[expose] public noncomputable section

open TensorProduct

namespace SymPow

variable {S : Type*} [CommRing S]
  {E F G N : Type*} [AddCommGroup E] [Module S E] [AddCommGroup F] [Module S F]
  [AddCommGroup G] [Module S G] [AddCommGroup N] [Module S N]

/-! ### The multiplication `E ⊗ N → Sym² N` -/

/-- The image of `SymmetricAlgebra.ι` lies in `Sym¹ N`. -/
theorem ι_mem_symmetricPower_one (v : N) :
    SymmetricAlgebra.ι S N v ∈ symmetricPower 1 S N := by
  change _ ∈ (LinearMap.range (SymmetricAlgebra.ι S N)) ^ 1
  rw [pow_one]
  exact LinearMap.mem_range_self _ v

variable (S N) in
/-- The degree-one generator `N → Sym¹ N`. -/
def ιOne : N →ₗ[S] symmetricPower 1 S N :=
  (SymmetricAlgebra.ι S N).codRestrict (symmetricPower 1 S N) ι_mem_symmetricPower_one

/-- The degree-one generator `ιOne`, viewed in the symmetric algebra, is `SymmetricAlgebra.ι`. -/
theorem ιOne_coe (v : N) : (ιOne S N v : SymmetricAlgebra S N) = SymmetricAlgebra.ι S N v :=
  rfl

/-- The multiplication `μ_h : E ⊗ N → Sym² N`, `e ⊗ v ↦ ι(h e) · ι v`. -/
def sqMul (h : E →ₗ[S] N) : E ⊗[S] N →ₗ[S] symmetricPower (1 + 1) S N :=
  symMulMap 1 h ∘ₗ LinearMap.lTensor E (ιOne S N)

/-- `μ_h (e ⊗ v) = ι(h e) · ι v` in the symmetric algebra. -/
theorem sqMul_tmul (h : E →ₗ[S] N) (e : E) (v : N) :
    (sqMul h (e ⊗ₜ v) : SymmetricAlgebra S N) =
      SymmetricAlgebra.ι S N (h e) * SymmetricAlgebra.ι S N v :=
  rfl

/-- The degree-one generator `N → Sym¹ N` is surjective. -/
private theorem ιOne_surjective_aux : Function.Surjective (ιOne S N) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ LinearMap.range (SymmetricAlgebra.ι S N) := by
    have : y ∈ (LinearMap.range (SymmetricAlgebra.ι S N)) ^ 1 := hy
    rwa [pow_one] at this
  obtain ⟨v, rfl⟩ := hy'
  exact ⟨v, rfl⟩

/-- The multiplication `E ⊗ Symᵏ E → Sym^{k+1} E` is surjective. -/
private theorem symMulMap_id_surjective_aux (k : ℕ) :
    Function.Surjective (symMulMap k (LinearMap.id : E →ₗ[S] E)) := by
  intro y
  have hle : symmetricPower (k + 1) S E ≤
      (LinearMap.range (symMulMap k (LinearMap.id : E →ₗ[S] E))).map (Submodule.subtype _) := by
    change (LinearMap.range (SymmetricAlgebra.ι S E)) ^ (k + 1) ≤ _
    rw [pow_succ', Submodule.mul_le]
    rintro _ ⟨a, rfl⟩ n hn
    exact ⟨symMulMap k LinearMap.id (a ⊗ₜ ⟨n, hn⟩), LinearMap.mem_range_self _ _, rfl⟩
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := hle y.2
  exact ⟨w, Subtype.ext hz⟩

/-- The multiplication `E ⊗ E → Sym² E` is surjective. -/
theorem sqMul_id_surjective : Function.Surjective (sqMul (LinearMap.id : E →ₗ[S] E)) :=
  (symMulMap_id_surjective_aux 1).comp (LinearMap.lTensor_surjective E ιOne_surjective_aux)

/-- `μ_N ∘ (1 ⊗ h) = Sym²(h) ∘ μ_id`. -/
theorem sqMul_comp_lTensor (h : E →ₗ[S] N) :
    sqMul h ∘ₗ LinearMap.lTensor E h = symMap (1 + 1) h ∘ₗ sqMul LinearMap.id := by
  refine TensorProduct.ext' fun e e' => Subtype.ext ?_
  change SymmetricAlgebra.ι S N (h e) * SymmetricAlgebra.ι S N (h e') =
    symAlgMap h (SymmetricAlgebra.ι S E e * SymmetricAlgebra.ι S E e')
  rw [map_mul, symAlgMap_ι, symAlgMap_ι]

/-- `μ_h ((1 ⊗ h) z) = Sym²(h) (μ_id z)`. -/
theorem sqMul_lTensor_apply (h : E →ₗ[S] N) (z : E ⊗[S] E) :
    sqMul h (LinearMap.lTensor E h z) = symMap (1 + 1) h (sqMul LinearMap.id z) :=
  DFunLike.congr_fun (sqMul_comp_lTensor h) z

/-- A retraction `r` of `f` satisfies `r (f e) = e`. -/
private theorem apply_eq_of_comp_eq_id {f : E →ₗ[S] F} {r : F →ₗ[S] E}
    (hrf : r ∘ₗ f = LinearMap.id) (e : E) : r (f e) = e :=
  LinearMap.congr_fun hrf e

/-- Along a retraction `r` of `f`, `μ_id ∘ (1 ⊗ r) = Sym²(r) ∘ μ_f`. -/
theorem sqMul_id_comp_lTensor_retraction (f : E →ₗ[S] F) (r : F →ₗ[S] E)
    (hrf : r ∘ₗ f = LinearMap.id) :
    sqMul LinearMap.id ∘ₗ LinearMap.lTensor E r = symMap (1 + 1) r ∘ₗ sqMul f := by
  refine TensorProduct.ext' fun e v => Subtype.ext ?_
  change SymmetricAlgebra.ι S E e * SymmetricAlgebra.ι S E (r v) =
    symAlgMap r (SymmetricAlgebra.ι S F (f e) * SymmetricAlgebra.ι S F v)
  rw [map_mul, symAlgMap_ι, symAlgMap_ι, apply_eq_of_comp_eq_id hrf]

/-! ### Detecting the mixed part -/

section Detect

/-- An `S`-module `M` as a module over `Sᵐᵒᵖ`, through the commutativity of `S`. -/
local instance opModule (M : Type*) [AddCommGroup M] [Module S M] : Module Sᵐᵒᵖ M :=
  Module.compHom M (RingHom.fromOpposite (RingHom.id S) fun a b => Commute.all a b)

/-- The `S`- and `Sᵐᵒᵖ`-actions on an `S`-module `M` agree. -/
local instance isCentralScalar (M : Type*) [AddCommGroup M] [Module S M] :
    IsCentralScalar S M :=
  ⟨fun _ _ => rfl⟩

/-- The algebra homomorphism `Λ : Sym F → (S ⊕ E) ⊗ (S ⊕ G)`, `v ↦ r(v) ⊗ 1 + 1 ⊗ g(v)`. -/
def detect (r : F →ₗ[S] E) (g : F →ₗ[S] G) :
    SymmetricAlgebra S F →ₐ[S] TrivSqZeroExt S E ⊗[S] TrivSqZeroExt S G :=
  SymmetricAlgebra.lift
    ((Algebra.TensorProduct.includeLeft (R := S) (S := S) (A := TrivSqZeroExt S E)
        (B := TrivSqZeroExt S G)).toLinearMap ∘ₗ TrivSqZeroExt.inrHom S E ∘ₗ r +
      (Algebra.TensorProduct.includeRight (R := S) (A := TrivSqZeroExt S E)
        (B := TrivSqZeroExt S G)).toLinearMap ∘ₗ TrivSqZeroExt.inrHom S G ∘ₗ g)

/-- `Λ (ι v) = r(v) ⊗ 1 + 1 ⊗ g(v)`. -/
theorem detect_ι (r : F →ₗ[S] E) (g : F →ₗ[S] G) (v : F) :
    detect r g (SymmetricAlgebra.ι S F v) =
      TrivSqZeroExt.inr (r v) ⊗ₜ 1 + 1 ⊗ₜ TrivSqZeroExt.inr (g v) := by
  rw [detect, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- `Λ ∘ μ_f` is `e ⊗ v ↦ e ⊗ g(v)`, embedded in `(S ⊕ E) ⊗ (S ⊕ G)`. -/
theorem detect_sqMul (f : E →ₗ[S] F) (r : F →ₗ[S] E) (g : F →ₗ[S] G)
    (hrf : r ∘ₗ f = LinearMap.id) (hgf : g ∘ₗ f = 0) (z : E ⊗[S] F) :
    detect r g (sqMul f z : SymmetricAlgebra S F) =
      TensorProduct.map (TrivSqZeroExt.inrHom S E) (TrivSqZeroExt.inrHom S G)
        (LinearMap.lTensor E g z) := by
  have hlin : (detect r g).toLinearMap ∘ₗ (symmetricPower (1 + 1) S F).subtype ∘ₗ sqMul f =
      TensorProduct.map (TrivSqZeroExt.inrHom S E) (TrivSqZeroExt.inrHom S G) ∘ₗ
        LinearMap.lTensor E g := by
    refine TensorProduct.ext' fun e v => ?_
    have hg : g (f e) = 0 := by rw [← LinearMap.comp_apply g f, hgf, LinearMap.zero_apply]
    change detect r g (SymmetricAlgebra.ι S F (f e) * SymmetricAlgebra.ι S F v) =
      TrivSqZeroExt.inr e ⊗ₜ TrivSqZeroExt.inr (g v)
    rw [map_mul, detect_ι, detect_ι, apply_eq_of_comp_eq_id hrf, hg,
      TrivSqZeroExt.inr_zero, TensorProduct.tmul_zero, add_zero, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      TrivSqZeroExt.inr_mul_inr, TensorProduct.zero_tmul, zero_add, mul_one, one_mul]
  exact DFunLike.congr_fun hlin z

/-- The map `E ⊗ G → (S ⊕ E) ⊗ (S ⊕ G)` induced by the two inclusions `inr` is injective. -/
theorem map_inrHom_injective :
    Function.Injective (TensorProduct.map (TrivSqZeroExt.inrHom S E)
      (TrivSqZeroExt.inrHom S G)) := by
  have h : TensorProduct.map (TrivSqZeroExt.sndHom S E) (TrivSqZeroExt.sndHom S G) ∘ₗ
      TensorProduct.map (TrivSqZeroExt.inrHom S E) (TrivSqZeroExt.inrHom S G) =
        LinearMap.id := by
    refine TensorProduct.ext' fun e g => ?_
    rfl
  exact Function.LeftInverse.injective (g := TensorProduct.map (TrivSqZeroExt.sndHom S E)
    (TrivSqZeroExt.sndHom S G)) fun z => DFunLike.congr_fun h z

end Detect

/-! ### Splitting along a projective cokernel -/

/-- In a short exact sequence of modules with projective cokernel, the injection has a left
inverse. -/
theorem exists_leftInverse_of_shortExact (f : E →ₗ[S] F) (g : F →ₗ[S] G)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) [Module.Projective S G] :
    ∃ r : F →ₗ[S] E, r ∘ₗ f = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hsurj
  have h := ((LinearMap.exact_iff.2 hex.symm).split_tfae').out 1 2
  exact (h.1 ⟨hinj, s, hs⟩).2

/-! ### The kernel -/

/-- A retraction `r` of `f` satisfies `(1 ⊗ r) ((1 ⊗ f) z) = z`. -/
private theorem lTensor_apply_eq_of_comp_eq_id (Q : Type*) [AddCommGroup Q] [Module S Q]
    {f : E →ₗ[S] F} {r : F →ₗ[S] E} (hrf : r ∘ₗ f = LinearMap.id) (z : Q ⊗[S] E) :
    LinearMap.lTensor Q r (LinearMap.lTensor Q f z) = z := by
  rw [← LinearMap.lTensor_comp_apply, hrf, LinearMap.lTensor_id, LinearMap.id_apply]

/-- `1 ⊗ f` is injective when `f` has a retraction. -/
theorem lTensor_injective_of_retraction (Q : Type*) [AddCommGroup Q] [Module S Q]
    (f : E →ₗ[S] F) (r : F →ₗ[S] E) (hrf : r ∘ₗ f = LinearMap.id) :
    Function.Injective (LinearMap.lTensor Q f) := by
  exact Function.LeftInverse.injective (g := LinearMap.lTensor Q r)
    (lTensor_apply_eq_of_comp_eq_id Q hrf)

/-- The kernel of `μ_f : E ⊗ F → Sym² F` is the image of the kernel of `μ_id : E ⊗ E → Sym² E`
under `1 ⊗ f`, when `f` has a retraction `r`, `g` is a cokernel of `f` and `G` is projective. -/
theorem exists_lTensor_eq_of_sqMul_eq_zero (f : E →ₗ[S] F) (g : F →ₗ[S] G)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) [Module.Projective S G]
    (r : F →ₗ[S] E) (hrf : r ∘ₗ f = LinearMap.id)
    (z : E ⊗[S] F) (hz : sqMul f z = 0) :
    ∃ w : E ⊗[S] E, sqMul LinearMap.id w = 0 ∧ LinearMap.lTensor E f w = z := by
  have hgf : g ∘ₗ f = 0 := LinearMap.ext fun e => hfg.apply_apply_eq_zero e
  have hrfe := apply_eq_of_comp_eq_id hrf
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property g LinearMap.id hg
  let s : G →ₗ[S] F := s₀ - f ∘ₗ r ∘ₗ s₀
  have hgs : ∀ c, g (s c) = c := fun c => by
    change g (s₀ c - f (r (s₀ c))) = c
    rw [map_sub, hfg.apply_apply_eq_zero, sub_zero, apply_eq_of_comp_eq_id hs₀]
  have hrs : ∀ c, r (s c) = 0 := fun c => by
    change r (s₀ c - f (r (s₀ c))) = 0
    rw [map_sub, hrfe, sub_self]
  have hsplit : f ∘ₗ r + s ∘ₗ g = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨e, he⟩ := (hfg (v - f (r v) - s (g v))).1 (by
      rw [map_sub, map_sub, hfg.apply_apply_eq_zero, hgs, sub_zero, sub_self])
    have he0 : e = 0 := by
      have := congrArg r he
      rwa [hrfe, map_sub, map_sub, hrfe, hrs, sub_self, sub_zero] at this
    rw [he0, map_zero] at he
    change f (r v) + s (g v) = v
    rw [eq_comm, ← sub_eq_zero, ← sub_sub]
    exact he.symm
  have hw : sqMul LinearMap.id (LinearMap.lTensor E r z) = 0 := by
    rw [← LinearMap.comp_apply (sqMul LinearMap.id), sqMul_id_comp_lTensor_retraction f r hrf,
      LinearMap.comp_apply, hz, map_zero]
  refine ⟨LinearMap.lTensor E r z, hw, ?_⟩
  · set z' := z - LinearMap.lTensor E f (LinearMap.lTensor E r z) with hz'
    have h1 : LinearMap.lTensor E r z' = 0 := by
      rw [hz', map_sub, lTensor_apply_eq_of_comp_eq_id E hrf, sub_self]
    have h2 : sqMul f z' = 0 := by
      rw [hz', map_sub, sqMul_lTensor_apply, hw, map_zero, hz, sub_zero]
    have h3 : LinearMap.lTensor E g z' = 0 := by
      refine map_inrHom_injective ?_
      rw [← detect_sqMul f r g hrf hgf z', h2, map_zero, ZeroMemClass.coe_zero, map_zero]
    have h4 : z' = 0 := by
      have hz'' : z' = LinearMap.lTensor E f (LinearMap.lTensor E r z') +
          LinearMap.lTensor E s (LinearMap.lTensor E g z') := by
        rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, ← LinearMap.add_apply,
          ← LinearMap.lTensor_add, hsplit, LinearMap.lTensor_id, LinearMap.id_apply]
      rw [hz'', h1, h3, map_zero, map_zero, add_zero]
    exact (sub_eq_zero.1 h4).symm

/-! ### Read through `Sym¹` -/

/-- `Sym¹ f ∘ ιOne = ιOne ∘ f`. -/
theorem symMap_one_comp_ιOne (f : E →ₗ[S] F) : symMap 1 f ∘ₗ ιOne S E = ιOne S F ∘ₗ f :=
  LinearMap.ext fun e => Subtype.ext (symAlgMap_ι f e)

/-- The degree-one generator `N → Sym¹ N` is surjective. -/
theorem ιOne_surjective : Function.Surjective (ιOne S N) :=
  ιOne_surjective_aux

/-- `μ_h ∘ (1 ⊗ Sym^k h) = Sym^{k+1} h ∘ μ_id`, on `E ⊗ Sym^k E`. -/
theorem symMulMap_comp_lTensor_symMap (k : ℕ) (h : E →ₗ[S] N) :
    symMulMap k h ∘ₗ LinearMap.lTensor E (symMap k h) =
      symMap (k + 1) h ∘ₗ symMulMap k LinearMap.id := by
  refine TensorProduct.ext' fun e y => Subtype.ext ?_
  change SymmetricAlgebra.ι S N (h e) * symAlgMap h (y : SymmetricAlgebra S E) =
    symAlgMap h (SymmetricAlgebra.ι S E e * (y : SymmetricAlgebra S E))
  rw [map_mul, symAlgMap_ι]

/-- The multiplication `E ⊗ Symᵏ E → Sym^{k+1} E` is surjective. -/
theorem symMulMap_id_surjective (k : ℕ) :
    Function.Surjective (symMulMap k (LinearMap.id : E →ₗ[S] E)) :=
  symMulMap_id_surjective_aux k

/-- `1 ⊗ Symᵏ f` is injective when `f` has a retraction. -/
theorem lTensor_symMap_injective (k : ℕ) (f : E →ₗ[S] F) (r : F →ₗ[S] E)
    (hrf : r ∘ₗ f = LinearMap.id) :
    Function.Injective (LinearMap.lTensor E (symMap k f)) :=
  lTensor_injective_of_retraction E (symMap k f) (symMap k r) (by
    rw [← symMap_comp, hrf, symMap_id])

/-- The kernel of `E ⊗ Symᵏ F → Sym^{k+1} F` for `k = 1` lies in the image of `1 ⊗ Symᵏ f`,
when `f` has a retraction, `g` is a cokernel of `f` and `G` is projective. -/
theorem exists_lTensor_symMap_eq_of_symMulMap_eq_zero (k : ℕ) (hk : k = 1)
    (f : E →ₗ[S] F) (g : F →ₗ[S] G)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) [Module.Projective S G]
    (r : F →ₗ[S] E) (hrf : r ∘ₗ f = LinearMap.id)
    (z : E ⊗[S] symmetricPower k S F) (hz : symMulMap k f z = 0) :
    ∃ w : E ⊗[S] symmetricPower k S E, LinearMap.lTensor E (symMap k f) w = z := by
  subst hk
  obtain ⟨z₀, rfl⟩ := LinearMap.lTensor_surjective E (ιOne_surjective (S := S) (N := F)) z
  obtain ⟨w₀, -, hw₀⟩ := exists_lTensor_eq_of_sqMul_eq_zero f g hfg hg r hrf z₀ hz
  refine ⟨LinearMap.lTensor E (ιOne S E) w₀, ?_⟩
  rw [← LinearMap.lTensor_comp_apply, symMap_one_comp_ιOne, LinearMap.lTensor_comp_apply, hw₀]

section Generator

/-- An `S`-module `M` as a module over `Sᵐᵒᵖ`, through the commutativity of `S`. -/
local instance opModule' (M : Type*) [AddCommGroup M] [Module S M] : Module Sᵐᵒᵖ M :=
  Module.compHom M (RingHom.fromOpposite (RingHom.id S) fun a b => Commute.all a b)

/-- The `S`- and `Sᵐᵒᵖ`-actions on an `S`-module `M` agree. -/
local instance isCentralScalar' (M : Type*) [AddCommGroup M] [Module S M] :
    IsCentralScalar S M :=
  ⟨fun _ _ => rfl⟩

/-- `SymmetricAlgebra.ι` is injective. -/
theorem symmetricAlgebra_ι_injective : Function.Injective (SymmetricAlgebra.ι S N) := by
  intro v w h
  have key : ∀ u, TrivSqZeroExt.snd (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom S N)
      (SymmetricAlgebra.ι S N u)) = u := fun u => by
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  rw [← key v, ← key w, h]

end Generator

/-- The degree-one generator `N → Sym¹ N` is bijective. -/
theorem ιOne_bijective : Function.Bijective (ιOne S N) :=
  ⟨fun _ _ h => symmetricAlgebra_ι_injective (congrArg Subtype.val h), ιOne_surjective⟩

end SymPow

end
