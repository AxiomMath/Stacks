module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Multiplication by a global section, as an endomorphism of the identity functor

Let `R` be a sheaf of rings on a site whose rings of sections are commutative. A compatible
family of local sections of `R` — an element of `(R.obj ⋙ forget RingCat).sections` — acts on
every sheaf of `R`-modules by multiplication, naturally in the module, hence defines an
endomorphism of the identity functor of `SheafOfModules R`. For a site with a terminal object
`T`, in particular for the site of opens of a topological space with `T = ⊤`, a single section
`f ∈ R(T)` restricts to such a compatible family and therefore acts in the same way.

This is the form in which multiplication by a global section is consumed by the inverse-system
results of Stacks 0H39 and 0BLB, which are stated for an arbitrary
`f : End (𝟭 (SheafOfModules R))`.

## Main definitions

* `Stacks.SheafOfModules.globalSectionToEnd`: multiplication by a compatible family of
  sections, as an endomorphism of the identity functor.
* `Stacks.SheafOfModules.terminalSection`: the compatible family obtained by restricting a
  section over a terminal object.
* `Stacks.SheafOfModules.terminalSectionToEnd`: multiplication by a section over a terminal
  object.

## Main results

* `Stacks.SheafOfModules.globalSectionToEnd_apply` and `terminalSectionToEnd_apply`: on local
  sections the endomorphism is scalar multiplication by the corresponding local scalar.
* `Stacks.SheafOfModules.globalSectionToEnd_pow_apply` and `terminalSectionToEnd_pow_apply`:
  its powers act by the corresponding powers of that scalar.

## Implementation notes

Commutativity of the rings of sections is assumed in the form `∀ U, IsMulCommutative
(R.obj.obj U)`, which is what makes multiplication by a section `R.obj X`-linear and hence a
morphism of sheaves of modules. The module universe is independent of the universes of the
site and of the sheaf of rings.

## References

* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]

open scoped IsMulCommutative

/-- Multiplication by a compatible family of local sections, on every sheaf of modules. The
commutativity assumption expresses that the structure sheaf is a sheaf of commutative
rings. -/
def globalSectionToEnd (f : (R.obj ⋙ forget RingCat).sections) :
    End (𝟭 (_root_.SheafOfModules.{m} R)) where
  app M := ⟨{
    app U := ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (f.val U))
    naturality := by
      intro U V i; ext x
      change f.val V • M.val.map i x = M.val.map i (f.val U • x)
      rw [M.val.map_smul]
      exact congrArg (fun r => r • M.val.map i x) (f.property i).symm }⟩
  naturality M N g := by
    ext U x; exact (g.val.app U).hom.map_smul (f.val U) x |>.symm

/-- On local sections, the natural endomorphism is scalar multiplication. -/
@[simp] theorem globalSectionToEnd_apply
    (f : (R.obj ⋙ forget RingCat).sections)
    (M : _root_.SheafOfModules.{m} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((globalSectionToEnd R f).app M).val.app U x = f.val U • x := rfl

/-- Powers of the natural endomorphism multiply by the corresponding scalar powers. -/
@[simp] theorem globalSectionToEnd_pow_apply
    (f : (R.obj ⋙ forget RingCat).sections)
    (M : _root_.SheafOfModules.{m} R) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((globalSectionToEnd R f) ^ n).app M).val.app U x = (f.val U) ^ n • x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    show (((globalSectionToEnd R f) ^ n).app M).val.app U (f.val U • x) = _
    rw [ih, ← mul_smul, ← pow_succ]

/-- The product of two of these endomorphisms acts on local sections by the product of the two
local scalars. -/
@[simp] theorem globalSectionToEnd_mul_apply
    (f g : (R.obj ⋙ forget RingCat).sections)
    (M : _root_.SheafOfModules.{m} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((globalSectionToEnd R f * globalSectionToEnd R g).app M).val.app U x =
      (f.val U * g.val U) • x := by
  show f.val U • g.val U • x = _
  rw [mul_smul]

/-- **Multiplication by a global section is multiplicative in the section.** Stated with the
product of the two families given pointwise by the hypothesis `hc`, because
`(R.obj ⋙ forget RingCat).sections` carries no `Mul` instance: a `c` whose value over every
object is the product of the values of `a` and of `b` there acts as the composite of the two
endomorphisms. -/
theorem globalSectionToEnd_mul_of_val (a b c : (R.obj ⋙ forget RingCat).sections)
    (hc : ∀ U, c.val U = a.val U * b.val U) :
    globalSectionToEnd.{v, u, w, m} R c = globalSectionToEnd R a * globalSectionToEnd R b := by
  refine NatTrans.ext (funext fun M => ?_)
  ext U x
  rw [globalSectionToEnd_apply, globalSectionToEnd_mul_apply, hc]

/-- Restrict a section over a terminal object to a compatible family of local sections. -/
def terminalSection (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T)) :
    (R.obj ⋙ forget RingCat).sections where
  val U := R.obj.map (hT.from U.unop).op f
  property {U V} i := by
    change R.obj.map i (R.obj.map (hT.from U.unop).op f) = _
    rw [← RingCat.comp_apply, ← R.obj.map_comp]
    congr 3; exact Quiver.Hom.unop_inj (hT.hom_ext _ _)

/-- Multiplication by a section over a terminal object. On a ringed space, take `T = ⊤` and
`f ∈ Γ(X, 𝒪_X)`. -/
def terminalSectionToEnd (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T)) :
    End (𝟭 (_root_.SheafOfModules.{m} R)) :=
  globalSectionToEnd R (terminalSection R T hT f)

/-- The scalar acting on sections over `U` is the restriction to `U` of the global scalar. -/
@[simp] theorem terminalSectionToEnd_apply
    (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T))
    (M : _root_.SheafOfModules.{m} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((terminalSectionToEnd R T hT f).app M).val.app U x =
      R.obj.map (hT.from U.unop).op f • x := rfl

/-- **A section over a terminal object killing every local section of a sheaf of modules kills
that sheaf of modules.** Multiplication by `f` is a morphism of sheaves of modules, so it is
determined by what it does to the sections over each object; if the local scalar `f|_U` kills
every section over every `U`, that morphism is the zero morphism.

This is the step from a section-level annihilation statement — the shape in which
[Stacks, Tag 0GA0] annihilates the cohomology sheaves of a derived pullback — to the vanishing
`η.app M = 0` of the central endomorphism, which is the shape in which the hypercohomology
annihilation behind [Stacks, Tag 0GA1] consumes it. -/
theorem terminalSectionToEnd_app_eq_zero (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T))
    (M : _root_.SheafOfModules.{m} R)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U), R.obj.map (hT.from U.unop).op f • x = 0) :
    (terminalSectionToEnd R T hT f).app M = 0 := by
  ext U x
  exact h U x

/-- Powers act by powers of the restricted global scalar on local sections. -/
@[simp] theorem terminalSectionToEnd_pow_apply
    (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T))
    (M : _root_.SheafOfModules.{m} R) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((terminalSectionToEnd R T hT f) ^ n).app M).val.app U x =
      (R.obj.map (hT.from U.unop).op f) ^ n • x := by
  simp only [terminalSectionToEnd, globalSectionToEnd_pow_apply, terminalSection]

end Stacks.SheafOfModules
