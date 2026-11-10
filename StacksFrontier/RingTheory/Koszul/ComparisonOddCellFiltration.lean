module

public import StacksFrontier.Algebra.DifferentialGraded.Module.ExhaustiveCellFiltration
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraOverKoszul
public import StacksFrontier.RingTheory.Koszul.OppositeTensorCellFiltration
public import StacksFrontier.RingTheory.Koszul.PowPairTensorIsomorphism

/-!
# The odd part of the comparison algebra is graded free over the Koszul algebra `K_N`

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The comparison algebra
`B_{N,t} = R⟨x, z, u⟩` of Tag 0GZ7 receives `K_N` by the homomorphism `κ : K_N → B_{N,t}` of
`Koszul.koszulToComparison`, which sends the generator of `K_N` to the odd generator `z`. That
homomorphism factors through the odd part `R⟨x, z⟩`, and it is *not* scaled by a power of `f`:
`d z = f^N` already, so no transition homomorphism intervenes. Consequently `R⟨x, z⟩` is graded
free over `K_N` on the two monomials `1` and `x`, and this file proves that it is therefore
orthogonal on the left to the acyclic differential graded `K_N`-modules.

The proof identifies `R⟨x, z⟩` with the tensor product `K_N ⊗_R K_t`. The odd part is the Koszul
algebra of the pair `(f^t, f^N)`, with `d x = f^t` on the first coordinate of `R²` and
`d z = f^N` on the second; exchanging the two coordinates turns it into the Koszul algebra
`K_{N,t}` of the pair `(f^N, f^t)` of `Koszul.powPairAlgebra`, which is `K_N ⊗_R K_t` by
`Koszul.powPairToTensor`. Under the composite `κ` becomes the inclusion `a ↦ a ⊗ 1` of the left
tensor factor, so the identification is one of differential graded `K_N`-modules, and
`Koszul.leftOrthogonal_acyclic_oppTensorModule` applies.

## Main definitions

* `Koszul.comparisonSwap`: the linear involution of `R²` exchanging the two coordinates.
* `Koszul.comparisonOddToPowPair`: the resulting isomorphism of the odd part `R⟨x, z⟩` with the
  Koszul algebra of the pair `(f^N, f^t)`.
* `Koszul.comparisonOddToTensor`: the composite isomorphism `R⟨x, z⟩ → K_N ⊗_R K_t`.
* `Koszul.comparisonOddRestrictedModule`: the odd part `R⟨x, z⟩`, as a left differential graded
  `K_N`-module.
* `DifferentialGradedModule.restrictRegularMap` and
  `DifferentialGradedModule.restrictRegularIso`: an isomorphism of differential graded algebras
  compatible with two structure maps out of a third one, read as an isomorphism of the two
  restricted regular modules.

## Main results

* `Koszul.comparisonOddToTensor_bijective`: the composite is bijective, hence an isomorphism of
  differential graded algebras.
* `Koszul.comparisonOddToTensor_koszulToComparisonOdd`: under the composite, `κ` becomes the
  inclusion of the left tensor factor. This is the statement that `κ` carries no power of `f`.
* `Koszul.leftOrthogonal_acyclic_comparisonOddRestrictedModule`: the odd part of `B_{N,t}`,
  viewed as a left differential graded `K_N`-module, is orthogonal on the left to the acyclic
  modules.
* `Koszul.leftOrthogonal_acyclic_shift_comparisonOddRestrictedModule`: the same for every shift
  of it. The shifts are the graded pieces of the cell decomposition of `B_{N,t}` itself over
  `K_N` by the divided-power monomials `u⁽ᵐ⁾`, the `m`-th piece being the odd part placed in the
  degree of `u⁽ᵐ⁾`, so this is the orthogonality hypothesis of
  `DifferentialGradedModule.ExhaustiveCellData` for that decomposition.

## Implementation notes

Both algebra homomorphisms out of an exterior algebra are compared on the generators `ι v` with
`ExteriorAlgebra.hom_ext`, and the two exterior maps compose because the underlying linear maps
do: `Koszul.comparisonSwap ∘ Koszul.zInclusion = Koszul.powPairCoord 0`, which is the one-line
computation carrying the whole identification.

The transport of a restricted regular module along an isomorphism of the ambient algebra is
stated for a variable third algebra, since only the compatibility
`ψ ∘ κ_P = κ_Q` of the structure maps is used; the compatibility of the right actions is then
the multiplicativity of `ψ`, read on the graded opposite algebras, where the Koszul signs on the
two sides are the same and therefore cancel without being mentioned.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 09JG](https://stacks.math.columbia.edu/tag/09JG), the graded opposite
  algebra.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ExteriorAlgebra

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R]

/-- If `ψ ∘ κP = κQ`, then the same holds for the maps induced on the graded opposite
algebras. -/
theorem oppHom_comp_apply {S P Q : DifferentialGradedAlgebra.{u, u} R} {κP : S.Hom P}
    {κQ : S.Hom Q} (ψ : P.Hom Q)
    (h : ∀ a : S.A, ψ.toAlgebraHom (κP.toAlgebraHom a) = κQ.toAlgebraHom a)
    (a : (oppAlgebra S).A) :
    (oppHom ψ).toAlgebraHom ((oppHom κP).toAlgebraHom a) = (oppHom κQ).toAlgebraHom a := by
  rw [oppHom_apply κP a, oppHom_apply ψ, LinearEquiv.apply_symm_apply, h, oppHom_apply κQ a]

/-- The multiplicativity of the isomorphism, in the form in which the compatibility of the two
right actions needs it: the right action of the graded opposite of `S` on a restricted regular
module is multiplication by the image of the scalar. -/
theorem oppHom_mul_oppHom {S P Q : DifferentialGradedAlgebra.{u, u} R} {κP : S.Hom P}
    {κQ : S.Hom Q} (ψ : P.Hom Q)
    (h : ∀ a : S.A, ψ.toAlgebraHom (κP.toAlgebraHom a) = κQ.toAlgebraHom a)
    (x : (oppAlgebra P).A) (a : (oppAlgebra S).A) :
    (oppHom ψ).toAlgebraHom (x * (oppHom κP).toAlgebraHom a)
      = (oppHom ψ).toAlgebraHom x * (oppHom κQ).toAlgebraHom a := by
  rw [map_mul, oppHom_comp_apply ψ h a]

/-- **An isomorphism of differential graded algebras compatible with two structure maps out of a
third one transports one restricted regular module to the other.** Both restricted modules are
right modules over the graded opposite of `S`, and the map is the isomorphism read on the graded
opposite algebras. -/
def restrictRegularMap {S P Q : DifferentialGradedAlgebra.{u, u} R} (κP : S.Hom P) (κQ : S.Hom Q)
    (ψ : P.Hom Q) (h : ∀ a : S.A, ψ.toAlgebraHom (κP.toAlgebraHom a) = κQ.toAlgebraHom a) :
    restrictScalars (oppHom κP) (regularModule (oppAlgebra P)) ⟶
      restrictScalars (oppHom κQ) (regularModule (oppAlgebra Q)) where
  toFun := (oppHom ψ).toAlgebraHom.toLinearMap
  map_smul := fun x a => oppHom_mul_oppHom ψ h x a
  map_grading n x hx := (oppHom ψ).map_grading n x hx
  map_d := LinearMap.ext fun x => (oppHom ψ).map_d x

/-- The transported map is bijective as soon as the isomorphism of algebras is: the two
identifications of underlying graded modules with those of the graded opposite algebras are
linear equivalences. -/
theorem restrictRegularMap_bijective {S P Q : DifferentialGradedAlgebra.{u, u} R} (κP : S.Hom P)
    (κQ : S.Hom Q) (ψ : P.Hom Q)
    (h : ∀ a : S.A, ψ.toAlgebraHom (κP.toAlgebraHom a) = κQ.toAlgebraHom a)
    (hψ : Function.Bijective ψ.toAlgebraHom) :
    Function.Bijective (restrictRegularMap κP κQ ψ h).toFun := by
  have hfun : ∀ x, (restrictRegularMap κP κQ ψ h).toFun x
      = (opposite R Q).equiv.symm (ψ.toAlgebraHom ((opposite R P).equiv x)) :=
    fun x => oppHom_apply ψ x
  constructor
  · intro x y hxy
    rw [hfun, hfun] at hxy
    exact (opposite R P).equiv.injective
      (hψ.1 ((opposite R Q).equiv.symm.injective hxy))
  · intro y
    obtain ⟨b, hb⟩ := hψ.2 ((opposite R Q).equiv y)
    refine ⟨(opposite R P).equiv.symm b, ?_⟩
    rw [hfun, LinearEquiv.apply_symm_apply, hb, LinearEquiv.symm_apply_apply]

/-- **The two restricted regular modules are isomorphic.** This is
`DifferentialGradedModule.restrictRegularMap` for a bijective isomorphism of algebras. -/
def restrictRegularIso {S P Q : DifferentialGradedAlgebra.{u, u} R} (κP : S.Hom P) (κQ : S.Hom Q)
    (ψ : P.Hom Q) (h : ∀ a : S.A, ψ.toAlgebraHom (κP.toAlgebraHom a) = κQ.toAlgebraHom a)
    (hψ : Function.Bijective ψ.toAlgebraHom) :
    restrictScalars (oppHom κP) (regularModule (oppAlgebra P)) ≅
      restrictScalars (oppHom κQ) (regularModule (oppAlgebra Q)) :=
  Hom.isoOfBijective (restrictRegularMap κP κQ ψ h)
    (restrictRegularMap_bijective κP κQ ψ h hψ)

end DifferentialGradedModule

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule DifferentialGraded.Bimodule
open DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-! ### Exchanging the two odd generators -/

/-- **The linear involution of `R²` exchanging the two coordinates.** It carries the second
coordinate, which is where the odd part `R⟨x, z⟩` of `B_{N,t}` has the generator `z` with
`d z = f^N`, to the first coordinate, which is where the Koszul algebra `K_{N,t}` of the pair
`(f^N, f^t)` has its generator with the same differential. -/
def comparisonSwap (R : Type u) [CommRing R] : (Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v := fun i => v (Equiv.swap (0 : Fin 2) 1 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `i`-th coordinate of `comparisonSwap R v` is the coordinate of `v` at the exchanged
index. -/
@[simp] theorem comparisonSwap_apply (v : Fin 2 → R) (i : Fin 2) :
    comparisonSwap R v i = v (Equiv.swap (0 : Fin 2) 1 i) := rfl

/-- The exchange of coordinates is an involution. -/
theorem comparisonSwap_comp_self (R : Type u) [CommRing R] :
    comparisonSwap R ∘ₗ comparisonSwap R = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [LinearMap.comp_apply, comparisonSwap_apply, comparisonSwap_apply, LinearMap.id_apply,
    Equiv.swap_apply_self]

/-- **The exchange of coordinates carries the structure map of `K_N` into the odd part to the
structure map of `K_N` into the Koszul algebra of the pair `(f^N, f^t)`.** -/
theorem comparisonSwap_comp_zInclusion (R : Type u) [CommRing R] :
    comparisonSwap R ∘ₗ zInclusion R = powPairCoord R 0 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [LinearMap.comp_apply, comparisonSwap_apply, zInclusion_apply, powPairCoord_apply]
  fin_cases i <;> simp

/-- **The functional of the Koszul algebra of the pair `(f^N, f^t)` pulls back along the exchange
of coordinates to the functional of the odd part `R⟨x, z⟩`.** -/
theorem seqDual_comp_comparisonSwap (f : R) (N t : ℕ) :
    seqDual (powPairSeq f N t) ∘ₗ comparisonSwap R = seqDual (comparisonSeq f N t) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, seqDual_apply, seqDual_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    powPairSeq_zero, powPairSeq_one, comparisonSeq_zero, comparisonSeq_one,
    comparisonSwap_apply, comparisonSwap_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-! ### The odd part as a tensor product -/

/-- **The odd part `R⟨x, z⟩` of `B_{N,t}` is the Koszul algebra of the pair `(f^N, f^t)`**, read
with the two generators exchanged. -/
def comparisonOddToPowPair (f : R) (N t : ℕ) :
    (comparisonOddAlgebra f N t).Hom (powPairAlgebra f N t) where
  toAlgebraHom := ExteriorAlgebra.map (comparisonSwap R)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin 2 → R) (Fin 2 → R) (comparisonSwap R) ha
  map_d a := by
    change ExteriorAlgebra.map (comparisonSwap R)
        (contraction (seqDual (comparisonSeq f N t)) a) =
      contraction (seqDual (powPairSeq f N t)) (ExteriorAlgebra.map (comparisonSwap R) a)
    rw [← seqDual_comp_comparisonSwap f N t]
    exact (contractLeft_exteriorAlgebraMap (comparisonSwap R)
      (seqDual (powPairSeq f N t)) a).symm

/-- The underlying algebra homomorphism of `Koszul.comparisonOddToPowPair` is the map of exterior
algebras induced by `Koszul.comparisonSwap`. -/
@[simp] theorem comparisonOddToPowPair_toAlgebraHom (f : R) (N t : ℕ) :
    (comparisonOddToPowPair f N t).toAlgebraHom = ExteriorAlgebra.map (comparisonSwap R) := rfl

/-- The exchange of coordinates is its own inverse on exterior algebras. -/
theorem map_comparisonSwap_comp_self (R : Type u) [CommRing R] :
    (ExteriorAlgebra.map (comparisonSwap R)).comp (ExteriorAlgebra.map (comparisonSwap R))
      = AlgHom.id R (ExteriorAlgebra R (Fin 2 → R)) := by
  rw [ExteriorAlgebra.map_comp_map, comparisonSwap_comp_self, ExteriorAlgebra.map_id]

/-- The homomorphism `Koszul.comparisonOddToPowPair` is bijective. -/
theorem comparisonOddToPowPair_bijective (f : R) (N t : ℕ) :
    Function.Bijective (comparisonOddToPowPair f N t).toAlgebraHom := by
  exact Function.Involutive.bijective fun a => AlgHom.congr_fun (map_comparisonSwap_comp_self R) a

/-- `K_{N,t} → K_N ⊗_R K_t` is bijective: it is the two-sided inverse of
`Koszul.powPairFromTensor`. -/
theorem powPairToTensorAlgHom_bijective (f : R) (n t : ℕ) :
    Function.Bijective (powPairToTensorAlgHom f n t) :=
  Function.bijective_iff_has_inverse.2
    ⟨(powPairFromTensor f n t).toAlgebraHom,
      fun x => AlgHom.congr_fun (powPairFromTensor_powPairToTensor f n t) x,
      fun y => AlgHom.congr_fun (powPairToTensor_powPairFromTensor f n t) y⟩

/-- **The odd part `R⟨x, z⟩` of `B_{N,t}` is the tensor product `K_N ⊗_R K_t`.** -/
def comparisonOddToTensor (f : R) (N t : ℕ) :
    (comparisonOddAlgebra f N t).Hom (powTensorAlgebra f N t) :=
  (powPairToTensor f N t).comp (comparisonOddToPowPair f N t)

/-- The homomorphism `Koszul.comparisonOddToTensor` from `R⟨x, z⟩` to `K_N ⊗_R K_t` is
bijective. -/
theorem comparisonOddToTensor_bijective (f : R) (N t : ℕ) :
    Function.Bijective (comparisonOddToTensor f N t).toAlgebraHom :=
  (powPairToTensorAlgHom_bijective f N t).comp (comparisonOddToPowPair_bijective f N t)

/-- The exchange of coordinates carries the structure map `K_N → R⟨x, z⟩` to the structure map
`K_N → K_{N,t}`. -/
theorem map_comparisonSwap_comp_map_zInclusion (R : Type u) [CommRing R] :
    (ExteriorAlgebra.map (comparisonSwap R)).comp (ExteriorAlgebra.map (zInclusion R))
      = ExteriorAlgebra.map (powPairCoord R 0) := by
  rw [ExteriorAlgebra.map_comp_map, comparisonSwap_comp_zInclusion]

/-- **Under the identification of the odd part with `K_N ⊗_R K_t`, the structure map
`κ : K_N → R⟨x, z⟩` becomes the inclusion `a ↦ a ⊗ 1` of the left tensor factor.** No power of
`f` appears: the generator of `K_N` goes to `z`, whose differential is already `f^N`. -/
theorem comparisonOddToTensor_koszulToComparisonOdd (f : R) (N t : ℕ)
    (a : (powOne f N).A) :
    (comparisonOddToTensor f N t).toAlgebraHom
        ((koszulToComparisonOdd f N t).toAlgebraHom a) =
      (tensorInclLeft (powOne f N) (powOne f t)).toAlgebraHom a := by
  have hswap : (comparisonOddToPowPair f N t).toAlgebraHom
      ((koszulToComparisonOdd f N t).toAlgebraHom a) =
      (koszulToPowPairLeft f N t).toAlgebraHom a := by
    change ExteriorAlgebra.map (comparisonSwap R)
      (ExteriorAlgebra.map (zInclusion R) a) = ExteriorAlgebra.map (powPairCoord R 0) a
    exact AlgHom.congr_fun (map_comparisonSwap_comp_map_zInclusion R) a
  have hleft : (tensorInclLeft (powOne f N) (powOne f t)).toAlgebraHom a =
      GradedTensorProduct.includeLeft (powOne f N).grading (powOne f t).grading a := rfl
  change (powPairToTensorAlgHom f N t)
    ((comparisonOddToPowPair f N t).toAlgebraHom
      ((koszulToComparisonOdd f N t).toAlgebraHom a)) = _
  rw [hswap, hleft, ← powPairFromTensor_includeLeft f N t a]
  exact AlgHom.congr_fun (powPairToTensor_powPairFromTensor f N t) _

/-! ### Orthogonality to the acyclic modules -/

/-- **The odd part `R⟨x, z⟩` of `B_{N,t}`, as a left differential graded `K_N`-module**, with
`K_N` acting through the structure map `κ`. Left modules are recorded as right modules over the
graded opposite algebra. -/
def comparisonOddRestrictedModule (f : R) (N t : ℕ) :
    DifferentialGradedModule.{u, u, u} (oppAlgebra (powOne f N)) :=
  restrictScalars (oppHom (koszulToComparisonOdd f N t))
    (regularModule (oppAlgebra (comparisonOddAlgebra f N t)))

/-- **The odd part of `B_{N,t}` is isomorphic, as a left differential graded `K_N`-module, to
`K_N ⊗_R K_t` with `K_N` acting on the left factor.** -/
def comparisonOddRestrictedIso (f : R) (N t : ℕ) :
    comparisonOddRestrictedModule f N t ≅
      oppTensorModule (powOne f N) (seqDual fun i => (fun _ : Fin 1 => f) i ^ t) :=
  restrictRegularIso (koszulToComparisonOdd f N t)
    (tensorInclLeft (powOne f N) (powOne f t)) (comparisonOddToTensor f N t)
    (comparisonOddToTensor_koszulToComparisonOdd f N t)
    (comparisonOddToTensor_bijective f N t)

/-- **The odd part `R⟨x, z⟩` of the comparison algebra `B_{N,t}`, viewed as a left differential
graded `K_N`-module, is orthogonal on the left to the acyclic modules.** It is graded free over
`K_N` on the two monomials `1` and `x`, because the structure map `κ : K_N → B_{N,t}` sends the
generator of `K_N` to `z` with no power of `f` attached; the statement is read off from the
identification with `K_N ⊗_R K_t`. -/
theorem leftOrthogonal_acyclic_comparisonOddRestrictedModule (f : R) (N t : ℕ) :
    (acyclic' (oppAlgebra (powOne f N))).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra (powOne f N))).obj
        (comparisonOddRestrictedModule f N t)) :=
  leftOrthogonal_acyclic_of_iso _ (comparisonOddRestrictedIso f N t).symm
    (leftOrthogonal_acyclic_oppTensorModule (powOne f N)
      (seqDual fun i => (fun _ : Fin 1 => f) i ^ t))

/-- **Every shift of the odd part of `B_{N,t}`, as a left differential graded `K_N`-module, is
orthogonal on the left to the acyclic modules.** As a graded left `K_N`-module `B_{N,t}` is the
direct sum over the divided-power monomials `u⁽ᵐ⁾` of copies of its odd part, the `m`-th copy
sitting in the degree of `u⁽ᵐ⁾`, and the differential of `B_{N,t}` lowers the divided-power
degree; this is the orthogonality of the graded pieces of that decomposition, the hypothesis
`DifferentialGradedModule.ExhaustiveCellData.layer_leftOrthogonal` asks for. -/
theorem leftOrthogonal_acyclic_shift_comparisonOddRestrictedModule (f : R) (N t : ℕ) (k : ℤ) :
    (acyclic' (oppAlgebra (powOne f N))).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra (powOne f N))).obj
        (shift (comparisonOddRestrictedModule f N t) k)) :=
  leftOrthogonal_acyclic_shift k (leftOrthogonal_acyclic_comparisonOddRestrictedModule f N t)

end Koszul

end
