module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedTaylorComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change of a semilinear map, and the comparison of [Stacks, Tag 07JH] as a map

`Crystalline.IsTwistedTaylorComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TwistedTaylorComparison.lean` carries its comparison
as
an `f`-**semilinear** map `T : M →ₛₗ[f] B ⊗_D M`.  The source's comparison is not a semilinear map
out of `M` but a `B`-linear map

`c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`,

and the cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean` is a statement about composites of
those maps.  Passing from `T` to `c_{f,g}` is a base change, and it is exactly here that the single
`Algebra D B` instance of the predicate fails: `LinearMap.liftBaseChange` of `T` would be the map
`b ⊗ m ↦ b · T m`, and that is `D`-balanced iff

`(g(d) · b) · T m = b · T (d · m) = b · f(d) · T m`    for all `d`, `b`, `m`,

which — `Crystalline.eq_of_balanced` below — forces `f = g`.  So the tensor product the comparison
comes out of is not `B ⊗_D M` for the structure map but `B ⊗_D M` for the `D`-algebra structure
**along `f`**, and the two cannot be the same instance on the same type.

This module supplies that type.  `Crystalline.TwistedScalars f` is `B` carried with
`f.toAlgebra` in place of the ambient `Algebra D B`, and
`Crystalline.semilinearBaseChange` is the `B`-linear map

`TwistedScalars f ⊗_D M →ₗ[B] N`,   `b ⊗ m ↦ b · T m`,

attached to any `f`-semilinear `T : M →ₛₗ[f] N` into any `B`-module `N`.  Because `N` is arbitrary
it may itself be `TwistedScalars g ⊗_D M`, and that is what makes the cocycle expressible:
`Crystalline.semilinearBaseChange_comp` says the base change of `c ∘ T` is `c ∘` the base change of
`T`, so the composite of two comparisons is again one.

## Main definitions

* `Crystalline.TwistedScalars` — `B` as a `D`-algebra along a ring homomorphism `f : D →+* B`
  other than the structure map, with `Crystalline.TwistedScalars.mk` and
  `Crystalline.TwistedScalars.val` the two directions of the identity and
  `Crystalline.TwistedScalars.ringEquiv` the statement that only the `D`-algebra structure differs.
* `Crystalline.semilinearBaseChange` — the base change `b ⊗ m ↦ b · T m` of an `f`-semilinear map,
  as a `B`-linear map out of `TwistedScalars f ⊗_D M`.
* `Crystalline.SecondDividedPowerMap.comparison` — the reading of a
  `Crystalline.IsTwistedTaylorComparison` as the source's `c_{f,g}`.

## Main results

* `Crystalline.semilinearBaseChange_tmul`, `..._mk_tmul` and `..._one_tmul` — its values; the last
  says the comparison restricted to the generators `1 ⊗ m` is `T` itself, which is the sense in
  which no information is lost.
* `Crystalline.semilinearBaseChange_unique` — it is the only `B`-linear map with those values on
  the generators, so the passage from `T` to `c_{f,g}` is a bijection onto the `B`-linear maps.
* `Crystalline.semilinearBaseChange_comp` — **the composition law**, `(c ∘ T)~ = c ∘ T~`.  With
  `N := TwistedScalars g ⊗_D M` this says the composite of the base changes of two comparisons is
  the base change of a third, which is what it means to state the cocycle of
  `StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean` as an identity between maps
  rather than between sums.
* `Crystalline.eq_of_balanced` — **the defect of the untwisted base change, proved**: if
  `b ⊗ m ↦ b · T m` is `D`-balanced for a second ring homomorphism `g` in place of `f`, and some
  `T m` has no nonzero annihilator, then `f = g`.  So the type synonym is not a convenience; the
  untwisted base change exists only at the degenerate datum.  Compare
  `Crystalline.ringHom_eq_algebraMap_of_untwisted`, which draws the same conclusion from the
  untwisted *Taylor* identity.
* `Crystalline.hasTaylorSum_comparison` — the comparison map of a twisted Taylor comparison carries
  the Taylor series on the generators, so nothing of
  `Crystalline.IsTwistedTaylorComparison` is lost in the passage.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Nothing here is about crystals; the subject is a base change of modules.

**The cocycle is not proved here either.**  What this module removes is the obstruction to
*stating* it as an identity of maps: with `Crystalline.semilinearBaseChange` a comparison is a
`B`-linear map and `Crystalline.semilinearBaseChange_comp` composes two of them.  Proving the
identity still needs the convergence facts of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean` together with uniqueness of the
sum of a Taylor series, which `Crystalline.hasTaylorSum_unique` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorHausdorff.lean` supplies from `p ^ N = 0`; and
the predicate `Crystalline.IsTwistedTaylorComparison` fixes the target of its comparison at
`B ⊗_D M` for the structure map, so relating three *distinct* divided power maps needs that target
generalised to `TwistedScalars h ⊗_D M`.  That generalisation is now a change of type and nothing
more, which it was not before this module.

**No hypothesis is carried silently.**  `hannih` in `Crystalline.eq_of_balanced` — that no nonzero
element of `B` annihilates `T m` — is the same hypothesis
`Crystalline.ringHom_eq_algebraMap_of_untwisted` carries and is discharged there at `M = D`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open scoped TensorProduct

universe u uI v w w'

namespace Crystalline

/-! ### `B` as a `D`-algebra along a ring homomorphism -/

/-- **`B` regarded as a `D`-algebra along the ring homomorphism `f`** rather than along a structure
map it may already carry.  This is the source of the comparison `c_{f,g}` of the proof of
[Stacks, Tag 07JH]: `M ⊗_{D,f} B` is the tensor product over the `D`-module structure `d · b = f(d)
b`, and `Crystalline.eq_of_balanced` shows that no other `D`-algebra structure on `B` will do.

It is a type synonym because the two structures are needed at once: the comparison runs between
them, so they cannot be the same instance on the same type. -/
def TwistedScalars {D : Type u} {B : Type v} [CommSemiring D] [Semiring B] (_f : D →+* B) :
    Type v := B

namespace TwistedScalars

variable {D : Type u} {B : Type v} [CommRing D] [CommRing B] {f : D →+* B}

/-- The underlying element of `B` of an element of the twist. -/
def val (b : TwistedScalars f) : B := b

/-- An element of `B`, regarded in the twist along `f`. -/
def mk (f : D →+* B) (b : B) : TwistedScalars f := b

variable (f) in
/-- The twist has the commutative ring structure of `B`. -/
instance : CommRing (TwistedScalars f) := inferInstanceAs (CommRing B)

variable (f) in
/-- The twist is a `D`-algebra with structure map `f`. -/
instance : Algebra D (TwistedScalars f) := f.toAlgebra

variable (f) in
/-- The twist is a `B`-module by left multiplication in `B`. -/
instance : Module B (TwistedScalars f) := inferInstanceAs (Module B B)

variable (f) in
/-- The `D`-action and the `B`-action on the twist commute. -/
instance : SMulCommClass D B (TwistedScalars f) :=
  ⟨fun d b c ↦ mul_left_comm (f d) b c⟩

/-- The underlying element of `mk f b` is `b`. -/
@[simp] theorem val_mk (b : B) : (mk f b).val = b := rfl

/-- An element of the twist is `mk f` of its underlying element. -/
@[simp] theorem mk_val (b : TwistedScalars f) : mk f b.val = b := rfl

/-- The `B`-action on the twist is multiplication in `B`. -/
@[simp] theorem val_smul (b : B) (c : TwistedScalars f) : (b • c).val = b * c.val := rfl

/-- The underlying element of the identity of the twist is `1 : B`. -/
@[simp] theorem val_one : (1 : TwistedScalars f).val = 1 := rfl

variable (f) in
/-- **Only the `D`-algebra structure is twisted**: the twist has the same underlying ring as `B`.
-/
def ringEquiv : TwistedScalars f ≃+* B := RingEquiv.refl B

/-- **The structure map of the twist is `f`.**  This is the whole content of the definition. -/
theorem algebraMap_apply (d : D) : algebraMap D (TwistedScalars f) d = mk f (f d) := rfl

/-- The `D`-action on the twist is multiplication by `f`. -/
theorem smul_val (d : D) (b : TwistedScalars f) : (d • b).val = f d * b.val := rfl

end TwistedScalars

/-! ### The base change of a semilinear map -/

section BaseChange

variable {D : Type u} {B : Type v} [CommRing D] [CommRing B] {f : D →+* B}
  {M : Type w} [AddCommGroup M] [Module D M] {N : Type w'} [AddCommGroup N] [Module B N]

/-- **The base change of an `f`-semilinear map**, that is the comparison `c_{f,g}` of the proof of
[Stacks, Tag 07JH] read off the datum of `Crystalline.IsTwistedTaylorComparison`: the `B`-linear
map

`TwistedScalars f ⊗_D M →ₗ[B] N`,   `b ⊗ m ↦ b · T m`.

It is `D`-balanced because the `D`-action on `Crystalline.TwistedScalars f` is along `f`, which is
the semilinearity rule of `T`; `Crystalline.eq_of_balanced` shows it is balanced for no other
`D`-algebra structure on `B`. -/
noncomputable def semilinearBaseChange (T : M →ₛₗ[f] N) :
    TwistedScalars f ⊗[D] M →ₗ[B] N where
  toFun := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : TwistedScalars f ↦
      AddMonoidHom.mk' (fun m : M ↦ b.val • T m) (fun x y ↦ by simp [smul_add]))
      (fun b b' ↦ by
        ext m
        change (b + b').val • T m = b.val • T m + b'.val • T m
        change (b.val + b'.val) • T m = _
        rw [add_smul]))
    (fun d b m ↦ by
      change (d • b).val • T m = b.val • T (d • m)
      rw [map_smulₛₗ]
      change (f d * b.val) • T m = b.val • ((f d) • T m)
      rw [mul_smul, smul_comm])
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
        rw [TensorProduct.smul_tmul']
        change (b • c).val • T m = b • (c.val • T m)
        rw [TwistedScalars.val_smul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The base change sends `b ⊗ m` to `b.val • T m`. -/
@[simp] theorem semilinearBaseChange_tmul (T : M →ₛₗ[f] N) (b : TwistedScalars f) (m : M) :
    semilinearBaseChange T (b ⊗ₜ[D] m) = b.val • T m := rfl

/-- The base change on a generator written with an element of `B`. -/
theorem semilinearBaseChange_mk_tmul (T : M →ₛₗ[f] N) (b : B) (m : M) :
    semilinearBaseChange T (TwistedScalars.mk f b ⊗ₜ[D] m) = b • T m := rfl

/-- **The base change restricted to the generators `1 ⊗ m` is the original map**, so nothing is
lost in passing from the semilinear map to the `B`-linear one. -/
@[simp] theorem semilinearBaseChange_one_tmul (T : M →ₛₗ[f] N) (m : M) :
    semilinearBaseChange T ((1 : TwistedScalars f) ⊗ₜ[D] m) = T m := by
  rw [semilinearBaseChange_tmul, TwistedScalars.val_one, one_smul]

/-- A generator of the twisted tensor product is a `B`-multiple of a generator `1 ⊗ m`. -/
@[sga "3 VIIA 4.1.4" "special case"]
theorem tmul_eq_smul_one_tmul (b : TwistedScalars f) (m : M) :
    b ⊗ₜ[D] m = b.val • ((1 : TwistedScalars f) ⊗ₜ[D] m) := by
  rw [TensorProduct.smul_tmul']
  congr 1
  change b = b.val • (1 : TwistedScalars f)
  exact (mul_one b.val).symm

/-- **Two `B`-linear maps out of the twisted tensor product agreeing on the generators `1 ⊗ m` are
equal.**  The generators `b ⊗ m` are the `B`-multiples of those, by
`Crystalline.tmul_eq_smul_one_tmul`. -/
theorem baseChange_ext {c c' : TwistedScalars f ⊗[D] M →ₗ[B] N}
    (h : ∀ m : M, c ((1 : TwistedScalars f) ⊗ₜ[D] m) = c' ((1 : TwistedScalars f) ⊗ₜ[D] m)) :
    c = c' := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul b m => rw [tmul_eq_smul_one_tmul, map_smul, map_smul, h m]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The base change is the unique `B`-linear map restricting to `T` on the generators.**  So the
passage of `Crystalline.semilinearBaseChange` from an `f`-semilinear map to a `B`-linear map on
`M ⊗_{D,f} B` is a bijection, and the source's `c_{f,g}` and this library's `T` carry the same
information. -/
theorem semilinearBaseChange_unique (T : M →ₛₗ[f] N)
    (c : TwistedScalars f ⊗[D] M →ₗ[B] N)
    (hc : ∀ m : M, c ((1 : TwistedScalars f) ⊗ₜ[D] m) = T m) :
    c = semilinearBaseChange T :=
  baseChange_ext fun m ↦ by rw [hc m, semilinearBaseChange_one_tmul]

/-- **The composition law of the base change**: `(c ∘ T)~ = c ∘ T~` for a `B`-linear `c`.

This is what makes the cocycle of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean` expressible as an identity of
maps.
Taking `N` to be `TwistedScalars g ⊗_D M` and `c` to be the base change of a second comparison, the
right-hand side is the composite `c_{g,h} ∘ c_{f,g}` of two comparisons and the left-hand side is
the base change of a single semilinear map, so the composite is again a comparison in the sense of
this module. -/
theorem semilinearBaseChange_comp {P : Type w'} [AddCommGroup P] [Module B P]
    (T : M →ₛₗ[f] N) (c : N →ₗ[B] P) :
    semilinearBaseChange (c.comp T) = c.comp (semilinearBaseChange T) :=
  (semilinearBaseChange_unique _ _ fun m ↦ by
    rw [LinearMap.comp_apply, semilinearBaseChange_one_tmul]
    rfl).symm

/-- **The composite of two comparisons is a comparison**, which is the cocycle
`c_{g,h} ∘ c_{f,g} = c_{f,h}` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCocycle.lean` as an identity of maps rather than
of sums.

This is `Crystalline.semilinearBaseChange_comp` at the target `TwistedScalars g ⊗_D M`, and its
point is that the target of a base change may itself be a twisted tensor product: so `c_{f,g}` and
`c_{g,h}` really do compose, and their composite is the base change of the single `f`-semilinear
map `c_{g,h} ∘ T₁`.  It is this statement that `Crystalline.IsTwistedTaylorComparison` could not
make, its comparison having `B ⊗_D M` for the structure map as a fixed target; the content the
cocycle still needs is that `c_{g,h} ∘ T₁` is the comparison of the datum `f, h`, which is
`Crystalline.hasTaylorSum_taylorComposite_diff` together with uniqueness of the sum of a Taylor
series. -/
theorem semilinearBaseChange_comp_semilinearBaseChange {g h : D →+* B}
    (T₁ : M →ₛₗ[f] (TwistedScalars g ⊗[D] M)) (T₂ : M →ₛₗ[g] (TwistedScalars h ⊗[D] M)) :
    semilinearBaseChange ((semilinearBaseChange T₂).comp T₁) =
      (semilinearBaseChange T₂).comp (semilinearBaseChange T₁) :=
  semilinearBaseChange_comp T₁ (semilinearBaseChange T₂)

end BaseChange

/-! ### The untwisted base change asserts that the two maps agree -/

section Defect

variable {D : Type u} {B : Type v} [CommRing D] [CommRing B] {f : D →+* B}
  {M : Type w} [AddCommGroup M] [Module D M] {N : Type w'} [AddCommGroup N] [Module B N]

/-- **The defect of the untwisted base change, proved.**  Let `T` be `f`-semilinear.  If the
assignment `b ⊗ m ↦ b · T m` is `D`-balanced for the `D`-algebra structure on `B` given by a
*second* ring homomorphism `g` — the hypothesis `hbal`, which is exactly what
`LinearMap.liftBaseChange` would need in order to produce a map out of `B ⊗_D M` for that
structure — and if some value `T m` is annihilated by no nonzero element of `B`, then `f = g`.

So `Crystalline.TwistedScalars` is not a convenience: the base change of a semilinear map exists
over the structure map only at the degenerate datum.  This is the same collapse that
`Crystalline.ringHom_eq_algebraMap_of_untwisted` exhibits for the untwisted *Taylor* identity, and
it is proved here from the balancedness alone, with no series and no convergence. -/
theorem eq_of_balanced (T : M →ₛₗ[f] N) (g : D →+* B)
    (hbal : ∀ (d : D) (b : B) (m : M), (g d * b) • T m = b • T (d • m))
    {m : M} (hannih : ∀ b : B, b • T m = 0 → b = 0) (d : D) :
    f d = g d := by
  have h := hbal d 1 m
  rw [mul_one, one_smul, map_smulₛₗ] at h
  refine sub_eq_zero.mp (hannih _ ?_)
  rw [sub_smul, ← h, sub_self]

end Defect

/-! ### The comparison of [Stacks, Tag 07JH] as a map -/

section Comparison

variable {p : ℕ} {D : DividedPowerRing.{u}} {B : DividedPowerRing.{u}}
  [Algebra (D : Type u) (B : Type u)] {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} {f : SecondDividedPowerMap D B} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **The comparison `c_{f,g}` of the proof of [Stacks, Tag 07JH]**, read off an `f`-semilinear
map: the `B`-linear map

`M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`,   `b ⊗ m ↦ b · T m`,

with the source's two `D`-algebra structures on `B` carried by `Crystalline.TwistedScalars f` and
by the ambient `Algebra D B`.  By `Crystalline.semilinearBaseChange_unique` it is the only
`B`-linear map sending `1 ⊗ m` to `T m`. -/
noncomputable def SecondDividedPowerMap.comparison
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) :
    TwistedScalars f.ringHom ⊗[(D : Type u)] M →ₗ[(B : Type u)]
      ((B : Type u) ⊗[(D : Type u)] M) :=
  semilinearBaseChange T

/-- The comparison sends the generator `1 ⊗ m` to `T m`. -/
@[simp] theorem SecondDividedPowerMap.comparison_one_tmul
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) (m : M) :
    f.comparison T ((1 : TwistedScalars f.ringHom) ⊗ₜ[(D : Type u)] m) = T m :=
  semilinearBaseChange_one_tmul T m

/-- **The comparison map carries the Taylor series of [Stacks, Tag 07JH] on the generators.**  So
the passage from the semilinear datum of `Crystalline.IsTwistedTaylorComparison` to the source's
`B`-linear `c_{f,g}` loses nothing: the defining property of the predicate is a property of the
map. -/
theorem hasTaylorSum_comparison {xi : ι → (B : Type u)}
    {T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)}
    (hT : IsTwistedTaylorComparison p D B M f thetaPow xi T) (m : M) :
    HasTaylorSum p D B M thetaPow xi m
      (f.comparison T ((1 : TwistedScalars f.ringHom) ⊗ₜ[(D : Type u)] m)) := by
  rw [SecondDividedPowerMap.comparison_one_tmul]
  exact hT m

/-- **The untwisted comparison asserts `f = g`, in the form the base change needs.**  This is
`Crystalline.eq_of_balanced` at the structure map, so it is the statement that
`Crystalline.SecondDividedPowerMap.comparison` cannot be defined out of the untwisted tensor
product `B ⊗_D M` unless the datum is degenerate. -/
theorem ringHom_eq_algebraMap_of_balanced
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M))
    (hbal : ∀ (d : (D : Type u)) (b : (B : Type u)) (m : M),
      (algebraMap (D : Type u) (B : Type u) d * b) • T m = b • T (d • m))
    {m : M} (hannih : ∀ b : (B : Type u), b • T m = 0 → b = 0) (d : (D : Type u)) :
    f.ringHom d = algebraMap (D : Type u) (B : Type u) d :=
  eq_of_balanced T (algebraMap (D : Type u) (B : Type u)) hbal hannih d

end Comparison

end Crystalline

end
