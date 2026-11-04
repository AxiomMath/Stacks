module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# The derivation attached to a split surjection of presheaves of commutative rings

Let `π : A ⟶ Q` be a morphism of presheaves of commutative rings admitting a section
`sec : Q ⟶ A`, that is `sec ≫ π = 𝟙 Q`, and let `M` be a presheaf of `A`-modules which the
kernel of `π` annihilates.  Then the sectionwise difference
```
  δ(x) = x - sec (π x)
```
takes values in the kernel of `π`, and for every additive family `κ` on `A` which is
`A`-semilinear *at sections of that kernel*, the family `x ↦ κ (δ x)` is a relative derivation
of `A` with values in `M` — relative to any base `ψ : R₀ ⟶ A` whose image `sec` fixes.

This is the sheaf-theoretic form of the ring-level statement behind
[Stacks Project, Tag 02HP]: for a surjection of rings `A ⟶ Q` with a section, `a ↦ a - s(π a)`
is a derivation with values in the kernel modulo its square.  Mathlib's
`Algebra.derivationOfSectionOfKerSqZero` is the affine case; the point of the present form is
that no square-zero hypothesis is needed, because the coefficient module `M` is assumed
annihilated by the kernel, which is what makes the correction term vanish.

## Main definitions

* `PresheafOfModules.splitSurjectionDerivation`: the derivation `x ↦ κ (x - sec (π x))`.

## Main results

* `PresheafOfModules.splitSurjectionDerivation_d`: its value formula.
* `PresheafOfModules.splitSurjectionDiff_mem_ker`: the difference lands in the kernel of `π`.
* `PresheafOfModules.splitSurjectionDiff_mul`: the exact Leibniz identity the difference
  satisfies, `δ (x * y) = x * δ y + sec (π y) * δ x`, with no error term at all.

## Implementation notes

**Why the Leibniz rule has no error term and the square-zero hypothesis is not needed.**  A
direct computation gives `δ (x * y) = x * δ y + sec (π y) * δ x` *exactly*
(`splitSurjectionDiff_mul`): the two correction terms cancel because `sec` is a ring
homomorphism.  The Leibniz rule asked of a derivation has `y * δ x` where this has
`sec (π y) * δ x`, and the two differ by `δ y * δ x`, a product of a section of the kernel with
a section of the kernel; `κ` of it vanishes because `κ` is semilinear and the kernel annihilates
`M`.  So what replaces the square-zero hypothesis of the affine statement is the hypothesis
`hann` that the kernel annihilates the coefficients, which for a module pulled back along `π`
is automatic.

**Why `κ` is a total family rather than a map out of the kernel.**  A map out of the kernel is
what a consumer has, but passing it as such makes every statement below carry a proof argument
`π x = 0` whose `Subsingleton` bookkeeping is pure noise.  A consumer composes its map out of
the kernel with the retraction `δ` onto the kernel — which exists precisely because `π` is
split — and hands in the composite; the semilinearity hypothesis `κ_smul` is then needed only
where it holds, namely at sections of the kernel.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R₀ A Q : Cᵒᵖ ⥤ CommRingCat.{w}}
  (π : A ⟶ Q) (sec : Q ⟶ A)

/-- The sectionwise difference `x - sec (π x)` of a split surjection of presheaves of
commutative rings. -/
def splitSurjectionDiff (U : Cᵒᵖ) (x : A.obj U) : A.obj U :=
  x - (sec.app U).hom ((π.app U).hom x)

/-- The value of `PresheafOfModules.splitSurjectionDiff` at `x` is `x - sec (π x)`. -/
@[simp]
theorem splitSurjectionDiff_apply (U : Cᵒᵖ) (x : A.obj U) :
    splitSurjectionDiff π sec U x = x - (sec.app U).hom ((π.app U).hom x) :=
  rfl

/-- The section acts as a right inverse of the projection on sections. -/
theorem app_sec_app_π (hsec : sec ≫ π = 𝟙 Q) (U : Cᵒᵖ) (x : A.obj U) :
    (π.app U).hom ((sec.app U).hom ((π.app U).hom x)) = (π.app U).hom x :=
  congrArg (fun m : CommRingCat.Hom (Q.obj U) (Q.obj U) => m.hom ((π.app U).hom x))
    (congrArg (fun n : Q ⟶ Q => n.app U) hsec)

/-- **The difference takes its values in the kernel of the projection.** -/
theorem splitSurjectionDiff_mem_ker (hsec : sec ≫ π = 𝟙 Q) (U : Cᵒᵖ) (x : A.obj U) :
    (π.app U).hom (splitSurjectionDiff π sec U x) = 0 := by
  rw [splitSurjectionDiff_apply, map_sub, app_sec_app_π π sec hsec U x, sub_self]

/-- **The exact multiplicative identity satisfied by the difference**, with no error term: the
two correction terms cancel because the section is a ring homomorphism. -/
theorem splitSurjectionDiff_mul (U : Cᵒᵖ) (x y : A.obj U) :
    splitSurjectionDiff π sec U (x * y) =
      x * splitSurjectionDiff π sec U y +
        (sec.app U).hom ((π.app U).hom y) * splitSurjectionDiff π sec U x := by
  simp only [splitSurjectionDiff_apply, map_mul]
  ring

/-- The difference vanishes on a section fixed by the composite of the projection and the
section. -/
theorem splitSurjectionDiff_eq_zero_of_eq (U : Cᵒᵖ) (x : A.obj U)
    (hx : (sec.app U).hom ((π.app U).hom x) = x) :
    splitSurjectionDiff π sec U x = 0 := by
  rw [splitSurjectionDiff_apply, hx, sub_self]

/-- The difference commutes with the restriction maps. -/
theorem splitSurjectionDiff_map {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj U) :
    (A.map f).hom (splitSurjectionDiff π sec U x) =
      splitSurjectionDiff π sec V ((A.map f).hom x) := by
  have hπ := ConcreteCategory.congr_hom (π.naturality f) x
  have hs := ConcreteCategory.congr_hom (sec.naturality f) ((π.app U).hom x)
  simp only [splitSurjectionDiff_apply, map_sub]
  exact congrArg₂ (· - ·) rfl (hs.symm.trans (congrArg (sec.app V).hom hπ).symm)

variable (M : PresheafOfModules.{w} (A ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
  (κ : ∀ U : Cᵒᵖ, A.obj U →+ M.obj U)

/-- **The derivation attached to a split surjection.**  For a split surjection `π : A ⟶ Q` of
presheaves of commutative rings, a presheaf of `A`-modules `M` annihilated by the kernel of `π`,
and an additive family `κ` which is natural and `A`-semilinear at sections of that kernel, the
family `x ↦ κ (x - sec (π x))` is a `ψ`-relative derivation of `A` with values in `M`, for any
base `ψ : R₀ ⟶ A` whose sections the section `sec` fixes.

This is the sheaf form of the derivation of [Stacks Project, Tag 02HP]. -/
noncomputable def splitSurjectionDerivation (hsec : sec ≫ π = 𝟙 Q) (ψ : R₀ ⟶ A)
    (hann : ∀ (U : Cᵒᵖ) (x : A.obj U), (π.app U).hom x = 0 →
      ∀ m : M.obj U, x • m = 0)
    (κ_smul : ∀ (U : Cᵒᵖ) (a x : A.obj U), (π.app U).hom x = 0 →
      κ U (a * x) = a • κ U x)
    (κ_map : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj U),
      M.map f (κ U x) = κ V ((A.map f).hom x))
    (hψ : ∀ (U : Cᵒᵖ) (t : R₀.obj U),
      (sec.app U).hom ((π.app U).hom ((ψ.app U).hom t)) = (ψ.app U).hom t) :
    M.Derivation' ψ where
  d {U} := (κ U).comp
    (AddMonoidHom.mk' (splitSurjectionDiff π sec U) (fun x y => by
      simp only [splitSurjectionDiff_apply, map_add]
      abel))
  d_mul {U} x y := by
    change κ U (splitSurjectionDiff π sec U (x * y)) =
      x • κ U (splitSurjectionDiff π sec U y) + y • κ U (splitSurjectionDiff π sec U x)
    rw [splitSurjectionDiff_mul π sec U x y, map_add,
      κ_smul U x _ (splitSurjectionDiff_mem_ker π sec hsec U y),
      κ_smul U _ _ (splitSurjectionDiff_mem_ker π sec hsec U x)]
    refine congrArg₂ (· + ·) rfl ?_
    have h0 := hann U (splitSurjectionDiff π sec U y)
      (splitSurjectionDiff_mem_ker π sec hsec U y) (κ U (splitSurjectionDiff π sec U x))
    rw [splitSurjectionDiff_apply, sub_smul, sub_eq_zero] at h0
    exact h0.symm
  d_map {U V} f x := by
    change κ V (splitSurjectionDiff π sec V ((A.map f).hom x)) =
      M.map f (κ U (splitSurjectionDiff π sec U x))
    rw [κ_map f, splitSurjectionDiff_map π sec f x]
  d_app {U} t := by
    change κ U (splitSurjectionDiff π sec U ((ψ.app U).hom t)) = 0
    rw [splitSurjectionDiff_eq_zero_of_eq π sec U _ (hψ U t), map_zero]

/-- **The value formula of `PresheafOfModules.splitSurjectionDerivation`**: it is `κ` applied to
the difference. -/
theorem splitSurjectionDerivation_d (hsec : sec ≫ π = 𝟙 Q) (ψ : R₀ ⟶ A)
    (hann : ∀ (U : Cᵒᵖ) (x : A.obj U), (π.app U).hom x = 0 →
      ∀ m : M.obj U, x • m = 0)
    (κ_smul : ∀ (U : Cᵒᵖ) (a x : A.obj U), (π.app U).hom x = 0 →
      κ U (a * x) = a • κ U x)
    (κ_map : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj U),
      M.map f (κ U x) = κ V ((A.map f).hom x))
    (hψ : ∀ (U : Cᵒᵖ) (t : R₀.obj U),
      (sec.app U).hom ((π.app U).hom ((ψ.app U).hom t)) = (ψ.app U).hom t)
    (U : Cᵒᵖ) (x : A.obj U) :
    (splitSurjectionDerivation π sec M κ hsec ψ hann κ_smul κ_map hψ).d x =
      κ U (splitSurjectionDiff π sec U x) :=
  rfl

end PresheafOfModules

end
