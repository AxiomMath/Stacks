module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsInclusionHom
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.IdealTrivializationCover
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormCalculus

/-!
# Evaluating forms with logarithmic poles on local sections of the ideal sheaf

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` the closed subscheme cut out by `I`, with
ideal sheaf `ℐ`. A local section `φ` of `Ω^p_{X/S}(log Y) = SheafHom(ℐ, 𝒦^p)`
(`AlgebraicGeometry.Scheme.Hom.logPolesForms`) over an open `W` is an `𝒪`-linear map from `ℐ` to
the forms vanishing on `Y`, over every open inside `W`. This file names its value
`φ(a) ∈ Ω^p_{X/S}(W')` at a local section `a` of `ℐ` over `W' ≤ W`
(`AlgebraicGeometry.Scheme.Hom.logEval`) and records that a section is determined by these values.

On an open `U` carrying a trivialization `θ` of `ℐ`, with basis element `b` and local equation
`t`, a form `z` vanishing on `Y` defines the logarithmic form `a ↦ θ(a) z`, written `t⁻¹ z`
informally (`Stacks.Divisors.IdealTrivialization.logOfCoord`); every logarithmic form over an open
inside `U` is of this kind, with `z = φ(b)`
(`Stacks.Divisors.IdealTrivialization.logOfCoord_logEval_basis`).

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- A local function, read as a scalar of the sections of the ideal sheaf. -/
abbrev toIdealScalar {W : X.Opens} (r : Γ(X, W)) :
    (structureSheafRing X.toRingedSpace).obj.obj (op W) := r

/-- **The value of a form with logarithmic poles at a local section of the ideal sheaf.** For a
section `φ` of `Ω^p_{X/S}(log Y)` over `W` and a section `a` of `ℐ` over `W' ≤ W`, the `p`-form
`φ(a)` over `W'`, which vanishes on `Y`. -/
def logEval {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    Γ(relativeDifferentialForms f (p : ℤ), W') :=
  PresheafOfModules.Hom.app (formRestrictionKernel f I p).ι.val (op W')
    (((φ : (restrFun X.presheaf W).obj (Stacks.Divisors.negativeTwist I).val ⟶
        (restrFun X.presheaf W).obj (formRestrictionKernelSheaf f I p).val).app
      (op (Over.mk (homOfLE h)))).hom a)

variable {f I}

/-- The value of a logarithmic form is the image under the inclusion of the form obtained by
applying `φ`. -/
private theorem logEval_congr {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) {a : (Stacks.Divisors.negativeTwist I).val.obj (op W')}
    {z : (restrFun X.presheaf W).obj (formRestrictionKernelSheaf f I p).val |>.obj
      (op (Over.mk (homOfLE h)))}
    (hz : (φ.app (op (Over.mk (homOfLE h)))).hom a = z) :
    logEval f I φ h a = PresheafOfModules.Hom.app (formRestrictionKernel f I p).ι.val (op W') z :=
  congrArg _ hz

/-- The value of a logarithmic form vanishes on `Y`. -/
theorem formRestriction_logEval {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app (op W') (logEval f I φ h a) = 0 :=
  (mem_formRestrictionKernel f I p (op W') _).1 (Subtype.property _)

/-- Evaluating a restricted logarithmic form is evaluating the form. -/
theorem logEval_res {p : ℕ} {W W₁ : X.Opens} (h₁ : W₁ ≤ W)
    (φ : (logPolesForms f I p).val.obj (op W)) {W' : X.Opens} (h : W' ≤ W₁)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I ((logPolesForms f I p).val.map (homOfLE h₁).op φ) h a =
      logEval f I φ (h.trans h₁) a :=
  rfl

/-- The value of a sum of logarithmic forms is the sum of their values. -/
theorem logEval_add {p : ℕ} {W : X.Opens} (φ ψ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (φ + ψ) h a = logEval f I φ h a + logEval f I ψ h a :=
  (logEval_congr (φ + ψ) h rfl).trans (map_add _ _ _)

/-- The zero logarithmic form has value zero at every local section of the ideal sheaf. -/
theorem logEval_zero {p : ℕ} {W : X.Opens} {W' : X.Opens} (h : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (0 : (logPolesForms f I p).val.obj (op W)) h a = 0 :=
  add_eq_left.mp ((logEval_add (0 : (logPolesForms f I p).val.obj (op W)) 0 h a).symm.trans
    (congrArg (fun φ => logEval f I φ h a) (add_zero _)))

/-- Evaluating a multiple of a logarithmic form. -/
theorem logEval_smul_left {p : ℕ} {W : X.Opens} (r : Γ(X, W))
    (φ : (logPolesForms f I p).val.obj (op W)) {W' : X.Opens} (h : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I ((show X.ringCatSheaf.obj.obj (op W) from r) • φ) h a =
      X.presheaf.map (homOfLE h).op r • logEval f I φ h a :=
  ((formRestrictionKernel f I p).ι.val.app (op W')).hom.map_smul _ _

/-- A logarithmic form is `𝒪`-linear in the section of the ideal sheaf. -/
theorem logEval_smul {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W'))
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I φ h (toIdealScalar r • a) = r • logEval f I φ h a :=
  (logEval_congr φ h ((φ.app (op (Over.mk (homOfLE h)))).hom.map_smul (toIdealScalar r) a)).trans
    (((formRestrictionKernel f I p).ι.val.app (op W')).hom.map_smul _ _)

/-- A logarithmic form is additive in the section of the ideal sheaf. -/
theorem logEval_add_right {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (h : W' ≤ W) (a a' : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I φ h (a + a') = logEval f I φ h a + logEval f I φ h a' :=
  (logEval_congr φ h ((φ.app (op (Over.mk (homOfLE h)))).hom.map_add a a')).trans (map_add _ _ _)

/-- A logarithmic form commutes with restriction of the section of the ideal sheaf. -/
theorem logEval_map {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    {W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I φ (h'.trans h) ((Stacks.Divisors.negativeTwist I).val.map (homOfLE h').op a) =
      (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h').op (logEval f I φ h a) := by
  have hn := PresheafOfModules.naturality_apply
    (φ : (restrFun X.presheaf W).obj (Stacks.Divisors.negativeTwist I).val ⟶
        (restrFun X.presheaf W).obj (formRestrictionKernelSheaf f I p).val)
    (Over.homMk (U := Over.mk (homOfLE (h'.trans h))) (V := Over.mk (homOfLE h))
      (homOfLE h') (Subsingleton.elim _ _)).op a
  exact (logEval_congr φ _ hn).trans
    (PresheafOfModules.naturality_apply (formRestrictionKernel f I p).ι.val (homOfLE h').op _)

/-- **A logarithmic form is determined by its values.** -/
theorem logEval_ext {p : ℕ} {W : X.Opens} {φ ψ : (logPolesForms f I p).val.obj (op W)}
    (hφψ : ∀ (W' : X.Opens) (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')),
      logEval f I φ h a = logEval f I ψ h a) : φ = ψ := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  induction V using Opposite.rec with | op V => ?_
  cases V with
  | mk W' r g =>
    obtain ⟨⟨⟩⟩ := r
    exact Subtype.ext (hφψ W' g.le a)


/-- Restriction of forms is semilinear over restriction of functions. -/
theorem forms_map_smul {p : ℤ} {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W))
    (z : Γ(relativeDifferentialForms f p, W)) :
    (relativeDifferentialForms f p).presheaf.map (homOfLE h).op (r • z) =
      (X.presheaf.map (homOfLE h).op r) •
        (relativeDifferentialForms f p).presheaf.map (homOfLE h).op z :=
  Scheme.Modules.map_smul _ (homOfLE h) r z

/-- Restricting a form twice is restricting it once. -/
theorem forms_map_map {p : ℤ} {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (z : Γ(relativeDifferentialForms f p, W)) :
    (relativeDifferentialForms f p).presheaf.map (homOfLE h').op
        ((relativeDifferentialForms f p).presheaf.map (homOfLE h).op z) =
      (relativeDifferentialForms f p).presheaf.map (homOfLE (h'.trans h)).op z := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **A form with logarithmic poles from its values.** A family of `p`-forms `g(a)` over `W' ≤ W`,
one for each local section `a` of the ideal sheaf over `W'`, which is additive and `𝒪`-linear
in `a`, commutes with restriction and vanishes on `Y`, is a section of `Ω^p_{X/S}(log Y)` over
`W`. -/
def logPolesFormsMk {p : ℕ} {W : X.Opens}
    (g : ∀ (W' : X.Opens), W' ≤ W → (Stacks.Divisors.negativeTwist I).val.obj (op W') →
      Γ(relativeDifferentialForms f (p : ℤ), W'))
    (hadd : ∀ W' (h : W' ≤ W) a a', g W' h (a + a') = g W' h a + g W' h a')
    (hsmul : ∀ W' (h : W' ≤ W) (r : Γ(X, W')) a,
      g W' h (toIdealScalar r • a) = r • g W' h a)
    (hres : ∀ W' W'' (h : W' ≤ W) (h' : W'' ≤ W') a,
      g W'' (h'.trans h) ((Stacks.Divisors.negativeTwist I).val.map (homOfLE h').op a) =
        (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h').op (g W' h a))
    (hmem : ∀ W' (h : W' ≤ W) a,
      (formRestriction I.subschemeι f (p : ℤ)).val.app (op W') (g W' h a) = 0) :
    (logPolesForms f I p).val.obj (op W) :=
  (show (restrFun X.presheaf W).obj (Stacks.Divisors.negativeTwist I).val ⟶
      (restrFun X.presheaf W).obj (formRestrictionKernelSheaf f I p).val from
  { app := fun V => ModuleCat.homAddEquiv.symm
      { toFun := fun a => ⟨g V.unop.left V.unop.hom.le a,
          (mem_formRestrictionKernel f I p _ _).2 (hmem _ _ a)⟩
        map_add' := fun a a' => Subtype.ext (hadd _ _ a a')
        map_smul' := fun r a => Subtype.ext (hsmul _ _ r a) }
    naturality := fun {V V'} k => ModuleCat.hom_ext (LinearMap.ext fun a => Subtype.ext
      (hres V.unop.left V'.unop.left V.unop.hom.le k.unop.left.le a)) })

/-- The values of `logPolesFormsMk g` are the `g(a)`. -/
theorem logEval_logPolesFormsMk {p : ℕ} {W : X.Opens}
    (g : ∀ (W' : X.Opens), W' ≤ W → (Stacks.Divisors.negativeTwist I).val.obj (op W') →
      Γ(relativeDifferentialForms f (p : ℤ), W'))
    (hadd hsmul hres hmem) {W' : X.Opens} (h : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (logPolesFormsMk g hadd hsmul hres hmem) h a = g W' h a :=
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- Multiplying a form vanishing on `Y` by a local function and restricting it keeps it
vanishing on `Y`. -/
theorem formRestriction_smul_map {p : ℕ} {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, W'))
    (z : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hz : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) z = 0) :
    (formRestriction I.subschemeι f (p : ℤ)).val.app (op W')
      (c • (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op z) = 0 := by
  refine (((formRestriction I.subschemeι f (p : ℤ)).val.app (op W')).hom.map_smul _ _).trans ?_
  refine (congrArg _ ((PresheafOfModules.naturality_apply
    (formRestriction I.subschemeι f (p : ℤ)).val (homOfLE h).op z).trans ?_)).trans (smul_zero _)
  rw [hz]
  exact map_zero _

/-- **The logarithmic form `t⁻¹ z`** over an open `W ≤ U`, for a form `z` vanishing on `Y`: the
map `a ↦ θ(a) z` from the ideal sheaf to the forms vanishing on `Y`. -/
def logOfCoord {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (z : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hz : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) z = 0) :
    (logPolesForms f I p).val.obj (op W) :=
  logPolesFormsMk
    (fun W' h a => (e.coordLE (h.trans hW) a) •
      (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op z)
    (fun W' h a a' => by
      rw [show e.coordLE (h.trans hW) (a + a') =
        e.coordLE (h.trans hW) a + e.coordLE (h.trans hW) a' from map_add _ a a']
      exact add_smul _ _ _)
    (fun W' h r a => by
      rw [show e.coordLE (h.trans hW) (toIdealScalar r • a) =
        r * e.coordLE (h.trans hW) a from map_smul _ r a]
      exact mul_smul _ _ _)
    (fun W' W'' h h' a => by
      rw [forms_map_smul, forms_map_map]
      congr 2
      exact e.θ_naturality (homOfLE (h.trans hW)) (homOfLE h') a)
    (fun W' h a => formRestriction_smul_map h _ z hz)

/-- The values of `t⁻¹ z`: at `a`, the multiple `θ(a) z`. -/
theorem logEval_logOfCoord {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (z : Γ(relativeDifferentialForms f (p : ℤ), W))
    (hz : (formRestriction I.subschemeι f (p : ℤ)).val.app (op W) z = 0)
    {W' : X.Opens} (h : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (e.logOfCoord hW z hz) h a =
      (e.coordLE (h.trans hW) a) •
        (relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op z :=
  rfl

end Stacks.Divisors.IdealTrivialization

end
