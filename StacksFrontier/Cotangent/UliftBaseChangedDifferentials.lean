module

public import StacksFrontier.Cotangent.ExtendScalars
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentials

/-!
# The universe lift of a base-changed module of Kähler differentials

Let `A → P → B` be maps of commutative rings in `Type u`. The sheaf `Ω₁ = B̲ ⊗_𝒪 Ω_{𝒪/A}` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentials.lean` has sections

```
ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]
```

in `Type (u + 1)`, because the morphism of topoi of [Stacks, Tag 08PR] is formed at a
coefficient universe at least `u + 1`, whereas the module `B ⊗_P Ω[P⁄A]` of
`CommAlgCat.overDifferentials`, which is how the proof of [Stacks, Tag 08PU] describes the same
sheaf, lives in `Type u`. This file identifies the two: the lifted tensor product is the
universe lift of the tensor product, semilinearly over `ULift.ringEquiv : ULift B ≃+* B`.

The comparison is not a formality only because the two tensor products are taken over
*different* rings, `ULift P` and `P`. Both directions are therefore written out: down, by the
universal property of `ULift B ⊗_{ULift P} -` applied to `b ⊗ w ↦ up (b.down ⊗ d w)`; up, by the
balanced-map universal property of `B ⊗_P -` applied to `b ⊗ ω ↦ up b ⊗ u ω`, where `d` and `u`
are the comparison maps `KaehlerDifferential.uliftDown` and `KaehlerDifferential.uliftUp` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentials.lean`. Nothing about `Ω` is reproved:
the two round trips are the two round trips of `KaehlerDifferential.uliftLinearEquiv`.

## Main definitions

* `KaehlerDifferential.uliftBaseChangeDownBilinear` and
  `KaehlerDifferential.uliftBaseChangeDown`: the comparison map
  `ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A] → ULift (B ⊗_P Ω[P⁄A])`, and the `ULift P`-bilinear
  map it is the extension of.
* `KaehlerDifferential.uliftBaseChangeUp`: the comparison map in the other direction, as a
  homomorphism of additive groups out of `B ⊗_P Ω[P⁄A]`.
* `KaehlerDifferential.uliftBaseChangeEquiv`: **the universe lift of a base-changed module of
  Kähler differentials**, the resulting isomorphism
  `ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A] ≃ₗ[ULift B] ULift (B ⊗_P Ω[P⁄A])`.

## Main results

* `KaehlerDifferential.uliftBaseChangeDown_tmul` and
  `KaehlerDifferential.uliftBaseChangeUp_tmul`: the values of the two comparison maps on a pure
  tensor.
* `KaehlerDifferential.uliftBaseChangeEquiv_hom_mk` and
  `KaehlerDifferential.uliftBaseChangeEquiv_inv_mk`: the two directions of the isomorphism on
  the pure differentials, `b ⊗ d (up p) ↦ up (b.down ⊗ d p)` and `up (b ⊗ d p) ↦ up b ⊗ d (up p)`.
  These pin the isomorphism down, because the pure differentials generate.
* `KaehlerDifferential.uliftBaseChange_naturality`: **the comparison is natural in the
  algebra.** For a second `A`-algebra `Q` over `B` and a ring map `g : P →+* Q`, the square
  formed by the comparison at `P`, the comparison at `Q`, a pushforward `ψ` of the `Type u`
  modules along `g` and a pushforward `φ` of the lifted modules along the universe lift of `g`
  commutes.
* `KaehlerDifferential.uliftBaseChange_source_eq` and
  `KaehlerDifferential.uliftBaseChange_target_eq`: at the `P`-algebra structure `f.toAlgebra` of
  a ring map `f : P →+* B`, the two sides of the comparison are *equal*, and not merely
  isomorphic, to the scalar extension of `Ω[ULift P⁄ULift A]` along the universe lift of `f`,
  which is what the sections of `CommAlgCat.polynomialRelativeDifferentialsBaseChange` are, and
  to the scalar extension of `Ω[P⁄A]` along `f`, which is `CommAlgCat.overDifferentials`.

## Implementation notes

**Which algebra structures.** The `ULift A`-algebra structure on `ULift P` and the
`ULift P`-algebra structure on `ULift B` are the ones instance resolution produces from
`ULift.algebra'`, exactly as in the `Lift` section of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentials.lean`, whose `uliftDown` and `uliftUp`
are used here; the implementation note of that file explains why the first is not the structure
`CommRingCat.KaehlerDifferential` installs and how `KaehlerDifferential.uliftLinearEquiv`
transports between the two. The `P`-algebra structure on `B` is an arbitrary instance, so that
the statements apply in particular to `f.toAlgebra` for a ring map `f : P →+* B` — which is the
case that matters, since the scalar multiplication of `f.toAlgebra` is `p • b = f p * b` on the
nose, hence also that of the `Module.compHom B f` underlying `ModuleCat.extendScalars f`, so at
that instance `B ⊗_P Ω[P⁄A]` *is* the module `CommAlgCat.overDifferentials` of an augmented
algebra and no transport is needed to read these statements there.

**The `ULift B`-module structures.** Instance resolution equips
`ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]` with the `ULift B`-action obtained from its `B`-action
by `ULift.module`, not with `TensorProduct.leftModule` at `ULift B` directly; the two agree, but
not syntactically, so `TensorProduct.AlgebraTensorModule.lift` cannot be used to build the
comparison — its output is linear for the other one. The comparison is therefore assembled from
the plain `TensorProduct.lift` of a `ULift P`-bilinear map, and its `ULift B`-linearity is
checked on pure tensors, where it holds by `TensorProduct.smul_tmul'`.

**Why naturality is stated for arbitrary pushforwards.** The `Type u` pushforward of the source
is `CommAlgCat.overDifferentialsPush`, which is defined for a morphism of `Over B` in
`CommAlgCat A`; stating naturality for it would require `B` to be an `A`-algebra and both
augmentations to be `A`-algebra maps, hypotheses the comparison itself does not need. Naturality
is therefore stated for *any* pair of maps taking the expected values on the pure
differentials: `CommAlgCat.overDifferentialsPush` is one such by
`CommAlgCat.overDifferentialsPush_mk`, and its universe lift is another. Since a map out of
`B ⊗_P Ω[P⁄A]` is determined by those values, nothing is lost — the hypotheses characterise the
pushforwards rather than restrict them. For the same reason the compatibility of the two
augmentations with `g`, which is what makes the pushforwards exist, is not needed for the square
to commute and is not assumed. The proof is the extensionality principle
`ModuleCat.baseChange_kaehlerDifferential_hom_ext` applied to the two composites.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace KaehlerDifferential

section UliftBaseChange

attribute [local instance] ULift.algebra'

variable (A : Type u) [CommRing A] (P : Type u) [CommRing P] [Algebra A P]
    (B : Type u) [CommRing B] [Algebra P B]

/-- The `ULift P`-bilinear map underlying `KaehlerDifferential.uliftBaseChangeDown`: it sends a
section `b` of `ULift B` and a differential `w` of `ULift P` over `ULift A` to the universe lift
of `b.down ⊗ d w`, where `d` is `KaehlerDifferential.uliftDown`. -/
def uliftBaseChangeDownBilinear :
    ULift.{v} B →ₗ[ULift.{v} P]
      Ω[ULift.{v} P⁄ULift.{v} A] →ₗ[ULift.{v} P] ULift.{v} (B ⊗[P] Ω[P⁄A]) :=
  LinearMap.mk₂ (ULift.{v} P)
    (fun b w => ULift.up (b.down ⊗ₜ[P] uliftDown.{u, v} A P w))
    (fun b b' w => by
      simp only [ULift.add_down, TensorProduct.add_tmul]
      rfl)
    (fun _ _ _ => rfl)
    (fun b w w' => by
      simp only [map_add, TensorProduct.tmul_add]
      rfl)
    (fun q b w => by
      have h : uliftDown.{u, v} A P (q.down • w) = q.down • uliftDown.{u, v} A P w :=
        (uliftDownRestrict.{u, v} A P).map_smul q.down w
      rw [ULift.smul_def, h, TensorProduct.tmul_smul]
      rfl)

/-- **The comparison map down.** The `ULift B`-linear map
`ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A] → ULift (B ⊗_P Ω[P⁄A])` sending `b ⊗ w` to the universe
lift of `b.down ⊗ d w`. -/
def uliftBaseChangeDown :
    ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A] →ₗ[ULift.{v} B]
      ULift.{v} (B ⊗[P] Ω[P⁄A]) where
  toFun := ⇑(TensorProduct.lift (uliftBaseChangeDownBilinear.{u, v} A P B))
  map_add' := map_add _
  map_smul' c z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- `KaehlerDifferential.uliftBaseChangeDown` on a pure tensor. -/
@[simp]
theorem uliftBaseChangeDown_tmul (b : ULift.{v} B) (w : Ω[ULift.{v} P⁄ULift.{v} A]) :
    uliftBaseChangeDown.{u, v} A P B (b ⊗ₜ[ULift.{v} P] w) =
      ULift.up (b.down ⊗ₜ[P] uliftDown.{u, v} A P w) :=
  rfl

/-- **The comparison map up.** The homomorphism of additive groups
`B ⊗_P Ω[P⁄A] → ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]` sending `b ⊗ ω` to `up b ⊗ u ω`, where
`u` is `KaehlerDifferential.uliftUp`. It is not asked to be linear over anything: the two tensor
products are formed over different rings, and all that is wanted of it is that it invert
`KaehlerDifferential.uliftBaseChangeDown`. -/
def uliftBaseChangeUp :
    (B ⊗[P] Ω[P⁄A]) →+ ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A] :=
  TensorProduct.liftAddHom
    { toFun := fun b =>
        { toFun := fun w =>
            (ULift.up b : ULift.{v} B) ⊗ₜ[ULift.{v} P] uliftUp.{u, v} A P w
          map_zero' := by simp
          map_add' := fun w w' => by simp only [map_add, TensorProduct.tmul_add] }
      map_zero' := AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        rw [show (ULift.up (0 : B) : ULift.{v} B) = 0 from rfl, TensorProduct.zero_tmul]
      map_add' := fun b b' => AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
        rw [show (ULift.up (b + b') : ULift.{v} B) = ULift.up b + ULift.up b' from rfl,
          TensorProduct.add_tmul] }
    fun p b w => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [map_smul, show (p • uliftUp.{u, v} A P w) =
          (ULift.up p : ULift.{v} P) • uliftUp.{u, v} A P w from
            (IsScalarTower.algebraMap_smul (ULift.{v} P) p (uliftUp.{u, v} A P w)).symm,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl

/-- `KaehlerDifferential.uliftBaseChangeUp` on a pure tensor. -/
@[simp]
theorem uliftBaseChangeUp_tmul (b : B) (ω : Ω[P⁄A]) :
    uliftBaseChangeUp.{u, v} A P B (b ⊗ₜ[P] ω) =
      (ULift.up b : ULift.{v} B) ⊗ₜ[ULift.{v} P] uliftUp.{u, v} A P ω :=
  rfl

/-- **The universe lift of a base-changed module of Kähler differentials.** For commutative
rings `A → P → B` in `Type u`, the module

```
ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]
```

is the universe lift of `B ⊗_P Ω[P⁄A]`: the comparison is `ULift B`-linear for the
`ULift B`-module structure that the universe lift and restriction of scalars along
`ULift.ringEquiv : ULift B ≃+* B` put on `B ⊗_P Ω[P⁄A]`, and it sends `up b ⊗ d (up p)` to
`up (b ⊗ d p)`. At the instance `f.toAlgebra` of a ring map `f : P →+* B` this is the
identification between the sections of the sheaf
`CommAlgCat.polynomialRelativeDifferentialsBaseChange` over an object `(P, α)` of the site
`C_{B/A}` and the module `CommAlgCat.overDifferentials (P, α)`. -/
def uliftBaseChangeEquiv :
    ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A] ≃ₗ[ULift.{v} B]
      ULift.{v} (B ⊗[P] Ω[P⁄A]) := by
  have hup : ∀ z : ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A],
      uliftBaseChangeUp.{u, v} A P B (uliftBaseChangeDown.{u, v} A P B z).down = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact map_zero _
    | tmul b w =>
        rw [uliftBaseChangeDown_tmul]
        change uliftBaseChangeUp.{u, v} A P B (b.down ⊗ₜ[P] uliftDown.{u, v} A P w) = _
        rw [uliftBaseChangeUp_tmul, uliftUp_uliftDown]
    | add x y hx hy => rw [map_add, ULift.add_down, map_add, hx, hy]
  have hdown : ∀ y : B ⊗[P] Ω[P⁄A],
      uliftBaseChangeDown.{u, v} A P B (uliftBaseChangeUp.{u, v} A P B y) = ULift.up y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul b ω => rw [uliftBaseChangeUp_tmul, uliftBaseChangeDown_tmul, uliftDown_uliftUp]
    | add x y hx hy => rw [map_add, map_add, hx, hy]; rfl
  exact
    { uliftBaseChangeDown.{u, v} A P B with
      invFun := fun x => uliftBaseChangeUp.{u, v} A P B x.down
      left_inv := hup
      right_inv := fun x => by obtain ⟨y⟩ := x; exact hdown y }

/-- **The comparison on the pure differentials.** The isomorphism
`KaehlerDifferential.uliftBaseChangeEquiv` sends `b ⊗ d (up p)` to `up (b.down ⊗ d p)`. Together
with `KaehlerDifferential.uliftBaseChangeEquiv_inv_mk` this pins it down, since the pure
differentials generate. -/
theorem uliftBaseChangeEquiv_hom_mk (b : ULift.{v} B) (p : P) :
    uliftBaseChangeEquiv.{u, v} A P B
        (b ⊗ₜ[ULift.{v} P] KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) (ULift.up p)) =
      ULift.up (b.down ⊗ₜ[P] KaehlerDifferential.D A P p) := by
  change uliftBaseChangeDown.{u, v} A P B _ = _
  rw [uliftBaseChangeDown_tmul, uliftDown_d]

/-- **The inverse comparison on the pure differentials.** The inverse of
`KaehlerDifferential.uliftBaseChangeEquiv` sends `up (b ⊗ d p)` to `up b ⊗ d (up p)`. -/
theorem uliftBaseChangeEquiv_inv_mk (b : B) (p : P) :
    (uliftBaseChangeEquiv.{u, v} A P B).symm
        (ULift.up (b ⊗ₜ[P] KaehlerDifferential.D A P p)) =
      (ULift.up b : ULift.{v} B) ⊗ₜ[ULift.{v} P]
        KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) (ULift.up p) := by
  rw [LinearEquiv.symm_apply_eq, uliftBaseChangeEquiv_hom_mk]

/-- **Naturality of the comparison.** Let `Q` be a second `A`-algebra with a `B`-algebra
structure and let `g : P →+* Q` be a ring map. Let `ψ` push `B ⊗_P Ω[P⁄A]` to `B ⊗_Q Ω[Q⁄A]`
along `g`, in the sense that it sends the pure differential `1 ⊗ d p` to `1 ⊗ d (g p)`, and let
`φ` do the same for the lifted modules along the universe lift of `g`. Then the square formed by
`ψ`, `φ` and the comparisons at `P` and at `Q` commutes.

Both pushforwards are hypotheses rather than constructions: `CommAlgCat.overDifferentialsPush`
is such a `ψ` by `CommAlgCat.overDifferentialsPush_mk`, and a map out of `B ⊗_P Ω[P⁄A]` is
determined by its values on the pure differentials, so this is the naturality of the comparison
with respect to the pushforwards and not a weaker statement. -/
theorem uliftBaseChange_naturality (Q : Type u) [CommRing Q] [Algebra A Q] [Algebra Q B]
    (g : P →+* Q)
    (φ : ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A] →ₗ[ULift.{v} B]
      ULift.{v} B ⊗[ULift.{v} Q] Ω[ULift.{v} Q⁄ULift.{v} A])
    (hφ : ∀ p : P, φ ((1 : ULift.{v} B) ⊗ₜ[ULift.{v} P]
          KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) (ULift.up p)) =
        (1 : ULift.{v} B) ⊗ₜ[ULift.{v} Q]
          KaehlerDifferential.D (ULift.{v} A) (ULift.{v} Q) (ULift.up (g p)))
    (ψ : (B ⊗[P] Ω[P⁄A]) →ₗ[B] (B ⊗[Q] Ω[Q⁄A]))
    (hψ : ∀ p : P, ψ ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p) =
        (1 : B) ⊗ₜ[Q] KaehlerDifferential.D A Q (g p))
    (z : ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A]) :
    uliftBaseChangeEquiv.{u, v} A Q B (φ z) =
      ULift.up (ψ (uliftBaseChangeEquiv.{u, v} A P B z).down) := by
  let L : ULift.{v} (B ⊗[P] Ω[P⁄A]) →ₗ[ULift.{v} B] ULift.{v} (B ⊗[Q] Ω[Q⁄A]) :=
    { toFun := fun x => ULift.up (ψ x.down)
      map_add' := fun x y => by
        rw [show ((x + y).down : B ⊗[P] Ω[P⁄A]) = x.down + y.down from rfl, map_add]
        rfl
      map_smul' := fun c x => by
        rw [show ((c • x).down : B ⊗[P] Ω[P⁄A]) = c.down • x.down from rfl, map_smul]
        rfl }
  have key : ModuleCat.ofHom ((uliftBaseChangeEquiv.{u, v} A Q B).toLinearMap ∘ₗ φ) =
      ModuleCat.ofHom (L ∘ₗ (uliftBaseChangeEquiv.{u, v} A P B).toLinearMap) := by
    refine ModuleCat.baseChange_kaehlerDifferential_hom_ext _ _ fun r => ?_
    obtain ⟨p⟩ := r
    change uliftBaseChangeEquiv.{u, v} A Q B (φ _) =
      ULift.up (ψ (uliftBaseChangeEquiv.{u, v} A P B _).down)
    erw [hφ p, uliftBaseChangeEquiv_hom_mk, uliftBaseChangeEquiv_hom_mk]
    exact congrArg ULift.up (hψ p).symm
  exact ConcreteCategory.congr_hom key z

end UliftBaseChange

/-! ### The two sides of the comparison, at the algebra structure of a ring map -/

section RingHomShape

attribute [local instance] ULift.algebra'

variable (A : Type u) [CommRing A] (P : Type u) [CommRing P] [Algebra A P]
    (B : Type u) [CommRing B] (f : P →+* B)

/-- **The source of the comparison is the universe-lifted base change.** At the `P`-algebra
structure of a ring map `f : P →+* B`, the module `ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]` is
the scalar extension along the universe lift of `f` of the differentials of `ULift P` over
`ULift A` — which is what the sections of
`CommAlgCat.polynomialRelativeDifferentialsBaseChange` over an object of the site `C_{B/A}`
are. The two are the same object, not merely isomorphic ones. -/
theorem uliftBaseChange_source_eq :
    letI : Algebra P B := f.toAlgebra
    ModuleCat.of (ULift.{v} B) (ULift.{v} B ⊗[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A]) =
      (ModuleCat.extendScalars (RingHom.ulift.{v, v} f)).obj
        (ModuleCat.of (ULift.{v} P) Ω[ULift.{v} P⁄ULift.{v} A]) :=
  rfl

/-- **The target of the comparison is `CommAlgCat.overDifferentials`.** At the `P`-algebra
structure of a ring map `f : P →+* B`, the module `B ⊗_P Ω[P⁄A]` is the scalar extension of
`Ω[P⁄A]` along `f`, which is the definition of `CommAlgCat.overDifferentials` for an
`A`-algebra `P` augmented to `B` by `f`. The two are the same object. -/
theorem uliftBaseChange_target_eq :
    letI : Algebra P B := f.toAlgebra
    ModuleCat.of B (B ⊗[P] Ω[P⁄A]) =
      (ModuleCat.extendScalars f).obj (ModuleCat.of P Ω[P⁄A]) :=
  rfl

end RingHomShape

end KaehlerDifferential

end
