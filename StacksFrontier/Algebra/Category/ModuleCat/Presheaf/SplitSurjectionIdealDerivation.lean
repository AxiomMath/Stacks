module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SplitSurjectionDerivation

/-!
# Stacks 02HP's derivation when the kernel of a split surjection is presented by a module

Let `π : A ⟶ Q` be a morphism of presheaves of commutative rings admitting a section
`sec : Q ⟶ A`.  `PresheafOfModules.splitSurjectionDerivation` of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SplitSurjectionDerivation.lean` turns the
difference `δ x = x - sec (π x)` into a relative derivation, once it is given a coefficient
family `κ` on `A` which is additive, natural, and `A`-semilinear at sections of the kernel
of `π`.  This file builds such a `κ` out of the one datum a geometric consumer has: a
**presentation of the kernel of `π` by a family of sections**, that is a family of types `N U`
with an injection `ιN : N U ⟶ A U` whose range over every object is exactly the kernel of `π`,
together with a map `ν` out of it into the coefficients.

Because `δ` lands in the kernel of `π`, the preimage of `δ x` under `ιN` exists and is unique,
so `x ↦ ν (ιN⁻¹ (δ x))` is a well-defined coefficient family, and its additivity, naturality and
semilinearity at the kernel come from the corresponding properties of `ιN` and `ν`.

## Main definitions

* `PresheafOfModules.kernelPreimage`: the preimage in `N` of the difference `δ x`.
* `PresheafOfModules.idealCoefficient`: the coefficient family `x ↦ ν (ιN⁻¹ (δ x))`.
* `PresheafOfModules.splitIdealDerivation`: the resulting relative derivation.

## Main results

* `PresheafOfModules.kernelPreimage_add`, `PresheafOfModules.kernelPreimage_mul` and
  `PresheafOfModules.kernelPreimage_map`: the preimage is compatible with the addition, the
  scalar action and the restriction maps of the presentation — the three properties the
  coefficient family needs.
* `PresheafOfModules.splitIdealDerivation_d`: its value formula, `x ↦ ν (ιN⁻¹ (δ x))`.
* `PresheafOfModules.splitIdealDerivation_d_iota`: **the derivation restricted to the kernel is
  `ν`.**  On a section of `N`, read inside `A`, the derivation takes the value `ν` takes.  This
  is the clause a consumer that needs to recognise the derivation on an ideal uses.

## Implementation notes

**Why the preimage is taken with `Function.invFun` rather than through a categorical kernel.**
The datum `splitSurjectionDerivation` consumes is a *family of additive maps on sections*, not a
morphism of presheaves; and the retraction of `A` onto the kernel of `π` is `δ`, which is not
`A`-linear — it is the derivation itself.  So there is no morphism of presheaves of modules to
factor through a kernel object, and the preimage has to be taken sectionwise.  Injectivity of
`ιN` on sections makes that preimage unique, which is what gives every one of its properties:
each is proved by applying `ιN` to both sides and comparing inside `A`.

**Why the presentation is a family of plain types and plain functions.**  The kernel of `π`
arises geometrically as the sections of a sheaf of modules, and the sheaf of rings it is a module
over is the one a *different* construction produces — the direct image of an inverse-image sheaf
of rings, where `A` is the sheaf of commutative rings whose underlying sheaf of rings that is.
The two are definitionally equal, but deciding it is past the heartbeat budget at a geometric
instantiation, and a consumer that has to ascribe its module to the ring `A ⋙ forget₂` cannot
even state its data.  Taking the presentation as a family of types with an addition, a scalar
multiplication, restriction maps and an injection — each a plain function with its compatibility
as a hypothesis — reduces every obligation on the consumer to a statement about *sections*, which
is where such identifications are cheap.  Nothing is lost: the data need not be the module's own
structure maps, only satisfy the compatibilities.

**Everything is stated at presheaf level, over `A ⋙ forget₂ CommRingCat RingCat`.**  That is the
spelling `PresheafOfModules.splitSurjectionDerivation` writes its coefficient module in.  At
sheaf level, over `Stacks.ringSheaf J A`, the scalar type is definitionally but not syntactically
the same and `a • m` does not elaborate at all — instance search does not unfold
`CategoryTheory.sheafCompose`.  A consumer holding sheaves passes `.val` and `.hom`.

## References

* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the derivation attached
  to a section of a surjection, whose sheaf form this completes.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R₀ A Q : Cᵒᵖ ⥤ CommRingCat.{w}}
  (π : A ⟶ Q) (sec : Q ⟶ A)
  (W : PresheafOfModules.{w} (Q ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- The coefficients of the derivation: a presheaf of `Q`-modules, read as a presheaf of
`A`-modules through `π`.  The kernel of `π` annihilates it, which is what replaces the
square-zero hypothesis of the affine statement. -/
noncomputable abbrev splitCoefficients :
    PresheafOfModules.{w} (A ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  (restrictScalars (Functor.whiskerRight π (forget₂ CommRingCat.{w} RingCat.{w}))).obj W

/-- The difference is additive. -/
theorem splitSurjectionDiff_add (U : Cᵒᵖ) (x y : A.obj U) :
    splitSurjectionDiff π sec U (x + y) =
      splitSurjectionDiff π sec U x + splitSurjectionDiff π sec U y := by
  simp only [splitSurjectionDiff_apply, map_add]
  abel

/-- The difference fixes a section killed by the projection. -/
theorem splitSurjectionDiff_eq_self (U : Cᵒᵖ) (x : A.obj U) (hx : (π.app U).hom x = 0) :
    splitSurjectionDiff π sec U x = x := by
  rw [splitSurjectionDiff_apply, hx, map_zero, sub_zero]

variable (Nty : Cᵒᵖ → Type w) (iota : ∀ U : Cᵒᵖ, Nty U → A.obj U)
  (hsec : sec ≫ π = 𝟙 Q)
  (hrange : ∀ (U : Cᵒᵖ) (x : A.obj U), (π.app U).hom x = 0 → ∃ y : Nty U, iota U y = x)

/-- The difference of the split surjection, with its preimage taken in the presentation `N` of
the kernel.  The preimage exists because the difference lands in the kernel, and it is unique
once `ιN` is injective, which is the hypothesis `hinj` of the statements below. -/
noncomputable def kernelPreimage (U : Cᵒᵖ) (x : A.obj U) : Nty U :=
  Classical.choose (hrange U _ (splitSurjectionDiff_mem_ker π sec hsec U x))

/-- The defining property of the preimage. -/
theorem iota_kernelPreimage (U : Cᵒᵖ) (x : A.obj U) :
    iota U (kernelPreimage π sec Nty iota hsec hrange U x) =
      splitSurjectionDiff π sec U x :=
  Classical.choose_spec (hrange U _ (splitSurjectionDiff_mem_ker π sec hsec U x))

variable (nu : ∀ U : Cᵒᵖ, Nty U → (splitCoefficients π W).obj U)
  (nadd : ∀ U : Cᵒᵖ, Nty U → Nty U → Nty U)
  (nsmul : ∀ U : Cᵒᵖ, A.obj U → Nty U → Nty U)
  (nmap : ∀ {U V : Cᵒᵖ}, (U ⟶ V) → Nty U → Nty V)
  (hinj : ∀ (U : Cᵒᵖ) (y z : Nty U), iota U y = iota U z → y = z)
  (hzero : ∀ (U : Cᵒᵖ) (y : Nty U), (π.app U).hom (iota U y) = 0)
  (hiotaAdd : ∀ (U : Cᵒᵖ) (y z : Nty U), iota U (nadd U y z) = iota U y + iota U z)
  (hiotaSmul : ∀ (U : Cᵒᵖ) (a : A.obj U) (y : Nty U), iota U (nsmul U a y) = a * iota U y)
  (hiotaMap : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (y : Nty U),
    iota V (nmap f y) = (A.map f).hom (iota U y))

/-- A section of `N` whose image in `A` is the difference is the preimage. -/
private theorem kernelPreimage_eq_of_iota_eq
    (hinj : ∀ (U : Cᵒᵖ) (y z : Nty U), iota U y = iota U z → y = z)
    {U : Cᵒᵖ} {x : A.obj U} {y : Nty U} (h : iota U y = splitSurjectionDiff π sec U x) :
    kernelPreimage π sec Nty iota hsec hrange U x = y :=
  hinj U _ _ ((iota_kernelPreimage π sec Nty iota hsec hrange U x).trans h.symm)

include hinj hiotaAdd in
/-- The preimage is additive. -/
theorem kernelPreimage_add (U : Cᵒᵖ) (x y : A.obj U) :
    kernelPreimage π sec Nty iota hsec hrange U (x + y) =
      nadd U (kernelPreimage π sec Nty iota hsec hrange U x)
        (kernelPreimage π sec Nty iota hsec hrange U y) :=
  kernelPreimage_eq_of_iota_eq π sec Nty iota hsec hrange hinj <| by
    rw [hiotaAdd, iota_kernelPreimage π sec Nty iota hsec hrange,
      iota_kernelPreimage π sec Nty iota hsec hrange, splitSurjectionDiff_add]

include hinj hiotaSmul in
/-- The preimage is semilinear at a section killed by the projection. -/
theorem kernelPreimage_mul (U : Cᵒᵖ) (a x : A.obj U) (hx : (π.app U).hom x = 0) :
    kernelPreimage π sec Nty iota hsec hrange U (a * x) =
      nsmul U a (kernelPreimage π sec Nty iota hsec hrange U x) :=
  kernelPreimage_eq_of_iota_eq π sec Nty iota hsec hrange hinj <| by
    rw [hiotaSmul, iota_kernelPreimage π sec Nty iota hsec hrange,
      splitSurjectionDiff_eq_self π sec U x hx,
      splitSurjectionDiff_eq_self π sec U _ (by rw [map_mul, hx, mul_zero])]

include hinj hiotaMap in
/-- The preimage commutes with restriction. -/
theorem kernelPreimage_map {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj U) :
    kernelPreimage π sec Nty iota hsec hrange V ((A.map f).hom x) =
      nmap f (kernelPreimage π sec Nty iota hsec hrange U x) :=
  kernelPreimage_eq_of_iota_eq π sec Nty iota hsec hrange hinj <| by
    rw [hiotaMap, iota_kernelPreimage π sec Nty iota hsec hrange, splitSurjectionDiff_map]

include hinj in
/-- The preimage is unchanged by taking the difference first, the difference being
idempotent. -/
theorem kernelPreimage_splitSurjectionDiff (U : Cᵒᵖ) (x : A.obj U) :
    kernelPreimage π sec Nty iota hsec hrange U (splitSurjectionDiff π sec U x) =
      kernelPreimage π sec Nty iota hsec hrange U x :=
  kernelPreimage_eq_of_iota_eq π sec Nty iota hsec hrange hinj <| by
    rw [iota_kernelPreimage π sec Nty iota hsec hrange, splitSurjectionDiff_eq_self π sec U _
      (splitSurjectionDiff_mem_ker π sec hsec U x)]

include hinj hzero in
/-- The preimage of a section of `N`, read inside `A`, is that section. -/
theorem kernelPreimage_iota (U : Cᵒᵖ) (y : Nty U) :
    kernelPreimage π sec Nty iota hsec hrange U (iota U y) = y :=
  kernelPreimage_eq_of_iota_eq π sec Nty iota hsec hrange hinj
    (splitSurjectionDiff_eq_self π sec U _ (hzero U y)).symm

/-! ### The coefficient map and the derivation -/

variable (hnuAdd : ∀ (U : Cᵒᵖ) (y z : Nty U), nu U (nadd U y z) = nu U y + nu U z)
  (hnuSmul : ∀ (U : Cᵒᵖ) (a : A.obj U) (y : Nty U), nu U (nsmul U a y) = a • nu U y)
  (hnuMap : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (y : Nty U),
    nu V (nmap f y) = (splitCoefficients π W).map f (nu U y))

include hinj hiotaAdd hnuAdd in
/-- **The coefficient map of Stacks 02HP**: the difference of the split surjection, read in the
presentation of the kernel, and carried into the coefficients by `ν`. -/
noncomputable def idealCoefficient (U : Cᵒᵖ) :
    A.obj U →+ (splitCoefficients π W).obj U :=
  AddMonoidHom.mk' (fun x ↦ nu U (kernelPreimage π sec Nty iota hsec hrange U x)) (fun x y ↦
    Eq.trans
      (congrArg (nu U)
        (kernelPreimage_add π sec Nty iota hsec hrange nadd hinj hiotaAdd U x y))
      (hnuAdd U _ _))

include hinj hiotaAdd hnuAdd in
/-- The value of the coefficient map. -/
theorem idealCoefficient_apply (U : Cᵒᵖ) (x : A.obj U) :
    idealCoefficient π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd hnuAdd U x =
      nu U (kernelPreimage π sec Nty iota hsec hrange U x) :=
  rfl

variable (ψ : R₀ ⟶ A)
  (hψ : ∀ (U : Cᵒᵖ) (t : R₀.obj U),
    (sec.app U).hom ((π.app U).hom ((ψ.app U).hom t)) = (ψ.app U).hom t)

include hinj hiotaAdd hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap hψ in
/-- **The derivation of Stacks 02HP, with the kernel of the split surjection presented
sectionwise.**  For a split surjection `π : A ⟶ Q` of presheaves of commutative rings whose
kernel is presented over each object by `N` through an injection `ιN` into `A`, and for
coefficients obtained from `N` by a semilinear natural `ν`, the family
`x ↦ ν (ιN⁻¹ (x - sec (π x)))` is a `ψ`-relative derivation of `A` with values in the
coefficients. -/
noncomputable def splitIdealDerivation :
    PresheafOfModulesOfCommRing.Derivation' (splitCoefficients π W) ψ :=
  splitSurjectionDerivation π sec _
    (idealCoefficient π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd hnuAdd) hsec ψ
    (fun U x hx m ↦ by
      have key : ((Functor.whiskerRight π (forget₂ CommRingCat.{w} RingCat.{w})).app U).hom x •
          (show W.obj U from m) = 0 := by
        rw [show ((Functor.whiskerRight π (forget₂ CommRingCat.{w} RingCat.{w})).app U).hom x = 0
          from hx, zero_smul]
      exact Eq.trans (ModuleCat.restrictScalars.smul_def _ x m) key)
    (fun U a x hx ↦
      Eq.trans
        (idealCoefficient_apply π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd hnuAdd U _)
        (Eq.trans
          (congrArg (nu U)
            (kernelPreimage_mul π sec Nty iota hsec hrange nsmul hinj hiotaSmul U a x hx))
          (Eq.trans (hnuSmul U a _)
            (congrArg (fun t ↦ a • t)
              (idealCoefficient_apply π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd
                hnuAdd U x).symm))))
    (fun {U V} f x ↦
      Eq.trans
        (congrArg (fun t ↦ (splitCoefficients π W).map f t)
          (idealCoefficient_apply π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd hnuAdd U x))
        (Eq.trans (hnuMap f _).symm
          (Eq.trans
            (congrArg (nu V)
              (kernelPreimage_map π sec Nty iota hsec hrange nmap hinj hiotaMap f x).symm)
            (idealCoefficient_apply π sec W Nty iota hsec hrange nu nadd hinj hiotaAdd hnuAdd V
              ((A.map f).hom x)).symm)))
    hψ

include hinj hiotaAdd hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap hψ in
/-- The value formula of `PresheafOfModules.splitIdealDerivation`, as the definition gives it. -/
theorem splitIdealDerivation_d_splitSurjectionDiff (U : Cᵒᵖ) (x : A.obj U) :
    (splitIdealDerivation π sec W Nty iota hsec hrange nu nadd nsmul nmap hinj hiotaAdd
      hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap ψ hψ).d x =
      nu U (kernelPreimage π sec Nty iota hsec hrange U
        (splitSurjectionDiff π sec U x)) :=
  rfl

include hinj hiotaAdd hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap hψ in
/-- **The value formula of `PresheafOfModules.splitIdealDerivation`.** -/
theorem splitIdealDerivation_d (U : Cᵒᵖ) (x : A.obj U) :
    (splitIdealDerivation π sec W Nty iota hsec hrange nu nadd nsmul nmap hinj hiotaAdd
      hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap ψ hψ).d x =
      nu U (kernelPreimage π sec Nty iota hsec hrange U x) :=
  Eq.trans
    (splitIdealDerivation_d_splitSurjectionDiff π sec W Nty iota hsec hrange nu nadd nsmul nmap hinj
      hiotaAdd hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap ψ hψ U x)
    (congrArg (nu U)
      (kernelPreimage_splitSurjectionDiff π sec Nty iota hsec hrange hinj U x))

include hinj hzero hiotaAdd hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap hψ in
/-- **The derivation restricted to the kernel is `ν`.**  On a section of `N`, read inside `A`,
the derivation takes the value `ν` takes. -/
theorem splitIdealDerivation_d_iota (U : Cᵒᵖ) (y : Nty U) :
    (splitIdealDerivation π sec W Nty iota hsec hrange nu nadd nsmul nmap hinj hiotaAdd
      hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap ψ hψ).d (iota U y) = nu U y :=
  Eq.trans
    (splitIdealDerivation_d π sec W Nty iota hsec hrange nu nadd nsmul nmap hinj hiotaAdd
      hiotaSmul hiotaMap hnuAdd hnuSmul hnuMap ψ hψ U (iota U y))
    (congrArg (nu U) (kernelPreimage_iota π sec Nty iota hsec hrange hinj hzero U y))

end PresheafOfModules

end
