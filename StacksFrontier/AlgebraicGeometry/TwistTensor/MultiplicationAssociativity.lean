module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical twist multiplication on `Proj S` is associative

Let `S` be a graded ring and `X = Proj S`. For every pair of integers `a`, `b` there is the
canonical multiplication map

`𝒪_X(a) ⊗_{𝒪_X} 𝒪_X(b) ⟶ 𝒪_X(a + b)`

of `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`. This file proves that
these maps are *associative*, as an equality of morphisms of sheaves of modules out of the
twice-iterated tensor product `(𝒪(a) ⊗ 𝒪(b)) ⊗ 𝒪(c)`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistTensor.projStructureRing` and
  `Stacks.AlgebraicGeometry.TwistTensor.monoidalCategoryProj`: the structure sheaf of `Proj S`
  read as a sheaf of rings at the `CategoryTheory.Sheaf.toRingCat` spelling, and the monoidal
  structure of Tag 01CA named at that spelling so that instance search finds it there.
* `Stacks.AlgebraicGeometry.TwistTensor.twist`,
  `Stacks.AlgebraicGeometry.TwistTensor.twistTensorObj` and
  `Stacks.AlgebraicGeometry.TwistTensor.twistMul`: `twistingSheaf`, the tensor product of two
  twists in the tensor-bifunctor spelling, and `twistMultiplicationMap` **retyped** at those.
  Nothing new is defined: the bodies are the existing declarations.
* `Stacks.AlgebraicGeometry.TwistTensor.mulSection`: **the product of two local sections** of
  `𝒪(a)` and `𝒪(b)`, as a local section of `𝒪(a + b)` — the image of their pure tensor under
  the multiplication map.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.twist_eq` and
  `Stacks.AlgebraicGeometry.TwistTensor.twistMul_eq`: the retyping changes no term; both hold by
  `rfl`.
* `Stacks.AlgebraicGeometry.TwistTensor.mulSection_apply` and
  `Stacks.AlgebraicGeometry.TwistTensor.mulSection_assoc`: the product of two local sections
  multiplies their values at each point, and is associative up to the transport along
  `a + b + c = a + (b + c)`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc`: **the main result.**
  `twistMul a b ▷ 𝒪(c) ≫ twistMul (a + b) c` equals
  `(α_ _ _ _).hom ≫ 𝒪(a) ◁ twistMul b c ≫ twistMul a (b + c)` followed by the `eqToHom` of
  `a + (b + c) = a + b + c`. Arbitrary integer degrees, arbitrary graded ring, no hypothesis in
  the style of Tag 01MU.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc_inv`: the same equality with the associator
  moved to the other side as `(α_ _ _ _).inv`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc_of`: the same equality with both composites
  carried to a common target degree `e` by two transports.

## Implementation notes

**The spelling bridge, and how it is crossed.** `twistMultiplicationMap` has source
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf (Proj 𝒮).toRingedSpace`, while the
tensor product whose associator and whiskerings have pure-tensor formulas — and for which an
extensionality principle for a twice-iterated product exists — is
`Stacks.SheafOfModules.Tensor.sheafTensor`, the one underlying
`Stacks.TensorSheafWorld.monoidalCategory`. **The two are definitionally equal**, and the crossing
is made exactly once, in the body of `twistMul`, by `:=`, which tolerates defeq.

**Why the crossing is made there and nowhere else.** `twistMul` is typed with source
`twistTensorObj`, the *bifunctor* spelling, rather than with the notation `⊗`. That is not
cosmetic. The hypothesis of `PresheafOfModules.tensorSheaf_hom_ext₂` is stated in the bifunctor
spelling, so every proof step below matches the goal it produces by delta-reduction alone. Had
`twistMul` been typed at `⊗`, each step would instead have had to unify `⊗` against the bifunctor
value *inside* a term containing an iterated tensor product of sections — and unfolding `⊗` means
unfolding `monoidalCategoryProj`, `Stacks.TensorSheafWorld.monoidalCategory` and
`Stacks.SheafOfModules.Strict.monoidalCategory` in a deep position, where the elaborator exhausts
its recursion depth on the right-hand composite. The same consideration is why
`projStructureRing` is a `def` and not an `abbrev` — it has to be a `DiscrTree` key of its own
for `monoidalCategoryProj` to be found at it — and why `Stacks.SheafOfModules.OnSpace.monoidal`
is *not* used even though its tensor product is the one `twistMultiplicationMap` is stated over:
no twice-iterated extensionality principle exists in that spelling, and transporting one into it
is this same crossing in a deep position.

**The computation is carried out on sections.** The whole arithmetic content is
`mulSection_assoc`, an equality between *sections* in which no composite of morphisms and no
tensor product appears; it is proved pointwise, where a section of `𝒪(d)` over `U` is a dependent
function on the points of `U` (`AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleSections` is a
`Submodule` of a function type), so `twist_section_ext` is a `Subtype.ext`, the two values are
`(s(x) * t(x)) * u(x)` and `s(x) * (t(x) * u(x))` in the homogeneous localization at `x` by
`mulSection_apply`, and `mul_assoc` finishes. `twistMul_assoc` then only has to recognise both
composites as iterated `mulSection`s, which is four applications of the section formulas of
Tag 01CA, in the shape of `Stacks.TensorSheafWorld.mulSheaf_assoc`, the same statement for a
sheaf of graded algebras.

**No `rw` crosses a spelling.** `twistMul_assoc_inv` and `twistMul_assoc_of` are given in term
mode for the reason recorded in `TensorSheafWorldBridge`: a rewrite whose motive spans the two
spellings of the tensor product is not type-correct at `implicit` transparency, and `rw` reports a
missing pattern rather than the cause. `twistMul_assoc_of` instead `subst`s the degree equation,
after which the two `eqToHom`s are identified by proof irrelevance.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO) — the twists of the
  structure sheaf on `Proj S` and the canonical maps between them.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU) — the open on which the
  multiplication maps are isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open PresheafOfModules
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistTensor

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### The monoidal structure, named at the spelling the twists use -/

/-- The site of `Proj S`: the open-cover topology on its opens. -/
abbrev projSite : GrothendieckTopology (Opens (ProjectiveSpectrum.top 𝒮)) :=
  Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)

/-- The structure sheaf of `Proj S`, read as a sheaf of (not necessarily commutative) rings at
the `CategoryTheory.Sheaf.toRingCat` spelling. This is a `def` rather than an `abbrev` so that
it is a `DiscrTree` key of its own, which is what lets `monoidalCategoryProj` be found by
instance search; see the implementation notes. -/
def projStructureRing : Sheaf (projSite 𝒮) RingCat.{u} :=
  CategoryTheory.Sheaf.toRingCat (projSite 𝒮) (ProjectiveSpectrum.Proj.structureSheaf 𝒮)

/-- The ring presheaf underlying the structure sheaf of `Proj S` is a sheaf. This is the
hypothesis the pure-tensor formulas of Tag 01CA take. -/
theorem isSheaf_structureRingPresheaf :
    Presheaf.IsSheaf (projSite 𝒮)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj) :=
  (CategoryTheory.Sheaf.toRingCat (projSite 𝒮)
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property

/-- **The monoidal structure of Tag 01CA on sheaves of modules on `Proj S`**, named at the
`projStructureRing` spelling of the structure sheaf of rings. Its tensor product is the value of
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is definitionally
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` — the source of
`twistMultiplicationMap`. -/
@[instance_reducible]
def monoidalCategoryProj : MonoidalCategory (SheafOfModules.{u} (projStructureRing 𝒮)) :=
  Stacks.TensorSheafWorld.monoidalCategory (ProjectiveSpectrum.Proj.structureSheaf 𝒮)

attribute [local instance] monoidalCategoryProj

/-- The `a`-th twist of the structure sheaf of `Proj S`, ascribed at the ring-sheaf spelling
`monoidalCategoryProj` is registered at. The body is `twistingSheaf`; the ascription is the
whole content. -/
@[ega "II 2.5.10"]
def twist (a : ℤ) : SheafOfModules.{u} (projStructureRing 𝒮) := twistingSheaf 𝒮 a

/-- The tensor product of two twists, written as the value of
`Stacks.SheafOfModules.Tensor.sheafTensor` rather than with the notation `⊗`. This is the
spelling in which `PresheafOfModules.tensorSheaf_hom_ext₂` states its hypothesis, and typing
`twistMul` at it — rather than at `⊗` — is what keeps the two spellings of the tensor product
from meeting inside a large term; see the implementation notes. -/
abbrev twistTensorObj (a b : ℤ) : SheafOfModules.{u} (projStructureRing 𝒮) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj
    (twist 𝒮 a)).obj (twist 𝒮 b)

/-- **The canonical multiplication map `𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)`**, retyped so that its source
is `twistTensorObj`, the tensor-bifunctor spelling of the tensor product. The body is
`twistMultiplicationMap`; its own source,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, is definitionally equal to that, and
this is the one place the two spellings are identified. -/
def twistMul (a b : ℤ) : twistTensorObj 𝒮 a b ⟶ twist 𝒮 (a + b) :=
  twistMultiplicationMap 𝒮 a b

/-- **The retyping changes no term**: `twist` is `twistingSheaf`. -/
theorem twist_eq (a : ℤ) : twist 𝒮 a = twistingSheaf 𝒮 a := rfl

/-- **The retyping changes no term**: `twistMul` is `twistMultiplicationMap`. This is the precise
sense in which the two spellings of the source tensor product are definitionally equal. -/
theorem twistMul_eq (a b : ℤ) : twistMul 𝒮 a b = twistMultiplicationMap 𝒮 a b := rfl

/-! ### Sections, pointwise -/

/-- **A local section of a twist is determined by its values at the points.** The sections of
`𝒪(d)` over `U` are a `Submodule` of the dependent functions on the points of `U`, so this is
`Subtype.ext` together with `funext`. -/
theorem twist_section_ext {d : ℤ} (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s t : (twist 𝒮 d).val.obj U) (h : ∀ x : U.unop, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext h)

/-- Transport of the twists along an equality of degrees does not change the value of a section
at a point. -/
theorem eqToHom_twist_val_app_apply {d d' : ℤ} (h : d = d')
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (s : (twist 𝒮 d).val.obj U) (x : U.unop) :
    ((eqToHom (congrArg (twist 𝒮) h)).val.app U s).1 x = s.1 x := by
  subst h; rfl

/-- A composite of morphisms of sheaves of modules, on a local section. -/
theorem comp_val_app_apply {A B C : SheafOfModules.{u} (projStructureRing 𝒮)} (f : A ⟶ B)
    (g : B ⟶ C) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (s : A.val.obj U) :
    (f ≫ g).val.app U s = g.val.app U (f.val.app U s) := rfl

/-! ### The product of two local sections -/

/-- **The product of two local sections of twists**: the image of their pure tensor under the
multiplication map, as a local section of `𝒪(a + b)` over the same open. -/
def mulSection (a b : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 a).val.obj U) (t : (twist 𝒮 b).val.obj U) : (twist 𝒮 (a + b)).val.obj U :=
  (twistMul 𝒮 a b).val.app U
    ((tensorSheafUnit (twist 𝒮 a) (twist 𝒮 b)).app U (s ⊗ₜ t))

/-- **The product of two local sections multiplies their values at each point**, in the
homogeneous localization there. This is `twistMultiplicationMap_tmul`, read at the monoidal
spelling of the tensor product. -/
theorem mulSection_apply (a b : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 a).val.obj U) (t : (twist 𝒮 b).val.obj U) (x : U.unop) :
    (mulSection 𝒮 a b U s t).1 x = s.1 x * t.1 x :=
  twistMultiplicationMap_tmul 𝒮 a b U.unop s t x

/-- **The product of local sections of twists is associative**, modulo the transport along
`a + b + c = a + (b + c)`. Both sides are sections of `𝒪(a + b + c)` over `U`, so this is a
pointwise statement, and pointwise it is `mul_assoc` in the homogeneous localization. -/
theorem mulSection_assoc (a b c : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (p : (twist 𝒮 a).val.obj U) (q : (twist 𝒮 b).val.obj U)
    (r : (twist 𝒮 c).val.obj U) :
    mulSection 𝒮 (a + b) c U (mulSection 𝒮 a b U p q) r =
      (eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)).val.app U
        (mulSection 𝒮 a (b + c) U p (mulSection 𝒮 b c U q r)) := by
  refine twist_section_ext 𝒮 U _ _ fun x ↦ ?_
  refine Eq.trans ?_ (eqToHom_twist_val_app_apply 𝒮 (add_assoc a b c).symm U _ x).symm
  simp only [mulSection_apply]
  exact mul_assoc _ _ _

/-! ### Associativity -/

/-- **Associativity of the canonical twist multiplication on `Proj S`, at module level.** The two
ways of multiplying `𝒪(a) ⊗ 𝒪(b) ⊗ 𝒪(c)` down to a single twist agree, as morphisms of sheaves of
modules out of `(𝒪(a) ⊗ 𝒪(b)) ⊗ 𝒪(c)`; the `eqToHom` is the transport along
`a + b + c = a + (b + c)`, which is the only reason the two targets are not literally the same
object.

The degrees are arbitrary integers and `S` is an arbitrary graded ring: nothing here needs the
multiplication maps to be isomorphisms, so no hypothesis in the style of Tag 01MU appears. -/
@[ega "II 8.1.5" "partial"]
theorem twistMul_assoc (a b c : ℤ) :
    twistMul 𝒮 a b ▷ twist 𝒮 c ≫ twistMul 𝒮 (a + b) c =
      (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).hom ≫
        twist 𝒮 a ◁ twistMul 𝒮 b c ≫ twistMul 𝒮 a (b + c) ≫
          eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext₂
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮)
    (F := twist 𝒮 a) (G := twist 𝒮 b) (H := twist 𝒮 c) (Q := twist 𝒮 (a + b + c))
    fun U p q r ↦ ?_
  have hL : (twistMul 𝒮 a b ▷ twist 𝒮 c ≫ twistMul 𝒮 (a + b) c).val.app U
        ((tensorSheafUnit (twistTensorObj 𝒮 a b) (twist 𝒮 c)).app U
          ((tensorSheafUnit (twist 𝒮 a) (twist 𝒮 b)).app U (p ⊗ₜ q) ⊗ₜ r)) =
      mulSection 𝒮 (a + b) c U (mulSection 𝒮 a b U p q) r :=
    (comp_val_app_apply 𝒮 _ _ U _).trans
      (congrArg ((twistMul 𝒮 (a + b) c).val.app U)
        (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮) U
          (twistMul 𝒮 a b) (twist 𝒮 c) _ r))
  have h1 : (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).hom.val.app U
        ((tensorSheafUnit (twistTensorObj 𝒮 a b) (twist 𝒮 c)).app U
          ((tensorSheafUnit (twist 𝒮 a) (twist 𝒮 b)).app U (p ⊗ₜ q) ⊗ₜ r)) =
      (tensorSheafUnit (twist 𝒮 a) (twistTensorObj 𝒮 b c)).app U
        (p ⊗ₜ (tensorSheafUnit (twist 𝒮 b) (twist 𝒮 c)).app U (q ⊗ₜ r)) :=
    Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮)
      (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c) U p q r
  have h2 : (twist 𝒮 a ◁ twistMul 𝒮 b c).val.app U
        ((tensorSheafUnit (twist 𝒮 a) (twistTensorObj 𝒮 b c)).app U
          (p ⊗ₜ (tensorSheafUnit (twist 𝒮 b) (twist 𝒮 c)).app U (q ⊗ₜ r))) =
      (tensorSheafUnit (twist 𝒮 a) (twist 𝒮 (b + c))).app U
        (p ⊗ₜ mulSection 𝒮 b c U q r) :=
    Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮) U
      (twist 𝒮 a) (twistMul 𝒮 b c) p _
  have h3 : (twistMul 𝒮 a (b + c)).val.app U
        ((tensorSheafUnit (twist 𝒮 a) (twist 𝒮 (b + c))).app U
          (p ⊗ₜ mulSection 𝒮 b c U q r)) =
      mulSection 𝒮 a (b + c) U p (mulSection 𝒮 b c U q r) := rfl
  refine hL.trans ((mulSection_assoc 𝒮 a b c U p q r).trans ?_)
  refine congrArg ((eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)).val.app U) ?_
  exact (h3.symm.trans (congrArg ((twistMul 𝒮 a (b + c)).val.app U) h2.symm)).trans
    (congrArg (fun w ↦ (twistMul 𝒮 a (b + c)).val.app U
      ((twist 𝒮 a ◁ twistMul 𝒮 b c).val.app U w)) h1.symm)

/-- **Associativity with the associator on the other side**: `twistMul_assoc` rearranged, as an
equality of morphisms out of `𝒪(a) ⊗ (𝒪(b) ⊗ 𝒪(c))`. -/
theorem twistMul_assoc_inv (a b c : ℤ) :
    (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).inv ≫ twistMul 𝒮 a b ▷ twist 𝒮 c ≫
        twistMul 𝒮 (a + b) c =
      twist 𝒮 a ◁ twistMul 𝒮 b c ≫ twistMul 𝒮 a (b + c) ≫
        eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm) := by
  refine Eq.trans ?_ (Iso.inv_hom_id_assoc
    (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c))
    (twist 𝒮 a ◁ twistMul 𝒮 b c ≫ twistMul 𝒮 a (b + c) ≫
      eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)))
  exact congrArg (fun φ ↦ (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).inv ≫ φ)
    (twistMul_assoc 𝒮 a b c)

/-- **Associativity with the two sums carried to a common degree.** Both composites are followed
by the transport to an arbitrary degree `e` equal to the sum of the three. -/
theorem twistMul_assoc_of {e : ℤ} (a b c : ℤ) (h₁ : a + b + c = e) (h₂ : a + (b + c) = e) :
    twistMul 𝒮 a b ▷ twist 𝒮 c ≫ twistMul 𝒮 (a + b) c ≫
        eqToHom (congrArg (twist 𝒮) h₁) =
      (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).hom ≫
        twist 𝒮 a ◁ twistMul 𝒮 b c ≫ twistMul 𝒮 a (b + c) ≫
          eqToHom (congrArg (twist 𝒮) h₂) := by
  subst h₁
  exact Eq.trans (congrArg (fun ψ ↦ twistMul 𝒮 a b ▷ twist 𝒮 c ≫ ψ)
    (Category.comp_id (twistMul 𝒮 (a + b) c))) (twistMul_assoc 𝒮 a b c)

end Stacks.AlgebraicGeometry.TwistTensor

end
