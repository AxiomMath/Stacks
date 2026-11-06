module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.SupportBounds
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkLength
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The length of a module on a scheme at a point

For a module `ℱ` on a scheme `X` and a point `x`, the *length of `ℱ` at `x`* is the length of
the stalk `ℱ_x` over the local ring of `X` at `x`. It vanishes on a zero module, it is additive
along a short exact sequence, it is unchanged by an isomorphism and by pushing forward along a
closed immersion, it vanishes off the image of such a pushforward, and along a finite filtration
by subobjects running from `⊥` to `⊤` it is the sum of the lengths of the successive quotients.

## Main definitions

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegrees`.

* `stalkLength`: the length of the stalk of a module at a point, over the local ring there.
* `filtrationQuotient`: the successive quotient of a monotone chain of subobjects.

## Main results

* `length_eq_of_surjective_smul_eq` and `length_eq_of_addEquiv_of_surjective_smul`: length is
  insensitive to a change of rings along a surjection, in two shapes — two actions on one
  abelian group, and two groups identified by a semilinear additive isomorphism. This is
  [Stacks, Tag 00IX] part (2) for rings that are not assumed commutative.
* `stalkLength_eq_zero_of_isZero`, `stalkLength_add_of_shortExact`, `stalkLength_of_iso`.
* `stalkLength_pushforward`: `len_{i(z)}(i_*ℳ) = len_z(ℳ)` for a closed immersion `i`, which is
  [Stacks, Tag 0EE3] for a closed immersion of schemes.
* `stalkLength_eq_zero_of_notMem_range`: `i_*ℳ` has length zero at a point outside the image.
* `fin_sum_telescope_add`: a telescoping sum in `ℕ∞`.
* `stalkLength_eq_sum_of_subobject_filtration`: **the length at `x` of a module carrying a
  finite monotone chain of subobjects from `⊥` to `⊤` is the sum of the lengths at `x` of the
  successive quotients.**

## Implementation notes

`stalkLength` is defined over the `RingCat`-valued stalk
`TopCat.Presheaf.stalk X.ringCatSheaf.obj x`. `AlgebraicGeometry.Scheme.ringCatSheaf` is
reducible whereas `Stacks.RingedSpace.structureSheafRing` is not, so `rw` and `simp` do not cross
between the two spellings of the stalk. Additivity is therefore proved with
`SheafOfModules.stalkMap`, which is stated over the `RingCat`-valued stalk, rather than with
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 00IX](https://stacks.math.columbia.edu/tag/00IX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-! ### Length under a surjective change of rings -/

/-- **Two module structures on one abelian group, related by a surjective ring map, give the
same length.** -/
theorem length_eq_of_surjective_smul_eq {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    (h : ∀ (r : R) (m : M), φ r • m = r • m) :
    Module.length R M = Module.length S M := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  exact
    { toFun := fun N =>
        { carrier := {m : M | m ∈ N}
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun s m hm => by
            obtain ⟨r, rfl⟩ := hφ s
            exact (h r m) ▸ N.smul_mem r hm }
      invFun := fun N =>
        { carrier := {m : M | m ∈ N}
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun r m hm => (h r m) ▸ N.smul_mem (φ r) hm }
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl
      map_rel_iff' := Iff.rfl }

/-- **Length transfer along a surjection and a semilinear additive isomorphism.** -/
theorem length_eq_of_addEquiv_of_surjective_smul {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module S N] (e : M ≃+ N) (he : ∀ (r : R) (m : M), e (r • m) = φ r • e m) :
    Module.length R M = Module.length S N :=
  let : Module R N := Module.compHom N φ
  have hlin : Module.length R M = Module.length R N :=
    ({ e with map_smul' := he } : M ≃ₗ[R] N).length_eq
  hlin.trans (length_eq_of_surjective_smul_eq φ hφ N fun _ _ => rfl)

/-! ### The length of a module at a point -/

/-- **The length of `ℱ` at `x`**: the length of the stalk `ℱ_x` as a module over the local ring
of `X` at `x`. -/
def stalkLength {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ∞ :=
  Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
    (SheafOfModules.stalkObj X.ringCatSheaf x F)

/-- **A zero module has length zero at every point.** -/
theorem stalkLength_eq_zero_of_isZero {X : Scheme.{u}} (F : X.Modules) (hF : IsZero F) (x : X) :
    stalkLength F x = 0 := by
  have : Subsingleton (SheafOfModules.stalkObj X.ringCatSheaf x F) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map_isZero hF)
  exact Module.length_eq_zero

/-- **The length at `x` is additive along a short exact sequence.** -/
theorem stalkLength_add_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (x : X) :
    stalkLength S.X₂ x = stalkLength S.X₁ x + stalkLength S.X₃ x := by
  have := hS.mono_f
  have := hS.epi_g
  have hfi := _root_.AlgebraicGeometry.stalk_map_injective_of_mono S.f x
  have hgs := _root_.AlgebraicGeometry.stalk_map_surjective_of_epi S.g x
  have hex := (ShortComplex.ab_exact_iff_function_exact
    (SheafOfModules.stalkShortComplex X.ringCatSheaf S x)).1
    ((SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf S).1 hS.exact x)
  exact Module.length_eq_add_of_exact
    (SheafOfModules.stalkMap X.ringCatSheaf x S.f).hom
    (SheafOfModules.stalkMap X.ringCatSheaf x S.g).hom hfi hgs hex

/-- **Isomorphic modules have the same length at every point.** -/
theorem stalkLength_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    stalkLength F x = stalkLength G x := by
  have hz : IsZero (0 : X.Modules) := isZero_zero _
  have hse : (ShortComplex.mk e.hom (0 : G ⟶ (0 : X.Modules)) comp_zero).ShortExact :=
    { exact := (ShortComplex.exact_iff_epi _ rfl).2 (inferInstanceAs (Epi e.hom))
      mono_f := inferInstanceAs (Mono e.hom)
      epi_g := hz.epi _ }
  have h := stalkLength_add_of_shortExact _ hse x
  rw [stalkLength_eq_zero_of_isZero _ hz, add_zero] at h
  exact h.symm

/-- **The length is unchanged by pushing forward along a closed immersion.** -/
theorem stalkLength_pushforward {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Z.Modules) (z : Z) :
    stalkLength ((Scheme.Modules.pushforward i).obj M) (i.base z) = stalkLength M z :=
  Stacks.ClosedImmersion.length_stalkObj_pushforward i M z

/-- **A direct image has length zero outside the image of the closed immersion.** -/
theorem stalkLength_eq_zero_of_notMem_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (x : X) (hx : x ∉ Set.range i.base) :
    stalkLength ((Scheme.Modules.pushforward i).obj M) x = 0 := by
  have hsupp : x ∉ _root_.SheafOfModules.supp ((Scheme.Modules.pushforward i).obj M) := by
    intro hmem
    refine hx ?_
    have := Stacks.AlgebraicGeometry.CoherentDevissageGlue.supp_pushforward_subset_support_ker
      i M hmem
    rwa [Stacks.AffineClosedUnion.support_ker_eq_range i] at this
  have : Subsingleton
      (SheafOfModules.stalkObj X.ringCatSheaf x ((Scheme.Modules.pushforward i).obj M)) :=
    not_nontrivial_iff_subsingleton.mp fun hn =>
      hsupp ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr hn)
  exact Module.length_eq_zero

/-! ### The length along a finite filtration -/

/-- **A telescoping sum in `ℕ∞`.** If `v (j + 1) = v j + w j` for every `j`, then
`v (last n) = v 0 + ∑ j, w j`. -/
theorem fin_sum_telescope_add {n : ℕ} (v : Fin (n + 1) → ℕ∞) (w : Fin n → ℕ∞)
    (h : ∀ j, v j.succ = v j.castSucc + w j) :
    v (Fin.last n) = v 0 + ∑ j : Fin n, w j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => v i.succ) (fun i => w i.succ) (by
      intro i
      simpa [Fin.castSucc_succ] using h i.succ)
    have hend : v (Fin.last n).succ = v (Fin.last (n + 1)) := by simp [Fin.succ_last]
    have h0 := h (0 : Fin (n + 1))
    simp only [Fin.castSucc_zero] at h0
    rw [← hend, ht, h0, add_assoc]

/-- **The successive quotient of a monotone chain of subobjects**, as the cokernel of the
inclusion of one term in the next. -/
abbrev filtrationQuotient {X : Scheme.{u}} {F : X.Modules} {n : ℕ}
    (G : Fin (n + 1) → Subobject F) (hG : Monotone G) (j : Fin n) : X.Modules :=
  cokernel (Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ))

/-- **Each step of a monotone chain of subobjects is a short exact sequence.** -/
theorem shortExact_filtrationStep {X : Scheme.{u}} {F : X.Modules} {n : ℕ}
    (G : Fin (n + 1) → Subobject F) (hG : Monotone G) (j : Fin n) :
    (ShortComplex.mk (Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ))
      (cokernel.π _) (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- **The length at `x` is the sum of the lengths of the successive quotients of a finite
filtration** running from `⊥` to `⊤`. -/
theorem stalkLength_eq_sum_of_subobject_filtration {X : Scheme.{u}} (F : X.Modules) {n : ℕ}
    (G : Fin (n + 1) → Subobject F) (hG : Monotone G) (hstart : G 0 = ⊥)
    (hfinish : G (Fin.last n) = ⊤) (x : X) :
    stalkLength F x = ∑ j : Fin n, stalkLength (filtrationQuotient G hG j) x := by
  have h := fin_sum_telescope_add (fun j => stalkLength (G j : X.Modules) x)
    (fun j => stalkLength (filtrationQuotient G hG j) x)
    (fun j => stalkLength_add_of_shortExact _ (shortExact_filtrationStep G hG j) x)
  have hzero : IsZero ((G 0 : Subobject F) : X.Modules) := by
    rw [hstart]
    exact (isZero_zero X.Modules).of_iso Subobject.botCoeIsoZero
  have he : ((G (Fin.last n) : Subobject F) : X.Modules) ≅ F :=
    Subobject.isoOfEq _ _ hfinish ≪≫ asIso (⊤ : Subobject F).arrow
  rw [stalkLength_eq_zero_of_isZero _ hzero, zero_add] at h
  rwa [← stalkLength_of_iso he x]

end Stacks.AlgebraicGeometry.ComponentDegrees

end
