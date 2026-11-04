module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ColonIdealComparison
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport

/-!
# The stalk of the first denominator quotient

The first quotient `Q₁ = F / I F` of [Stacks, Tag 02SW] is the cokernel of the first canonical
map of [Stacks, Tag 02P2]. Taking stalks of sheaves of modules on a scheme is exact, so the
stalk of `Q₁` at a point `x` is the quotient of the stalk of `F` by the range of the stalk of
that map; and because `I F` is *by definition* the image of the action `I ⊗ F ⟶ F`, that range
is the range of the stalk of the action. So

  `(Q₁)ₓ ≅ Fₓ / (the range of the stalk of `I ⊗ F ⟶ F`)`.

This is the shape in which the coefficient of `[Q₁]` at a point enters the proof of Tag 02SW
part (4): the coefficient is `Stacks.Chow.sheafMultiplicity Q₁ x`, which is the length of the
left-hand side.

## Main definitions

* `Stacks.Chow.cokernelStalkLinearEquiv` — the stalk of a cokernel, for an arbitrary morphism
  of modules on a scheme.
* `Stacks.Chow.denominatorQuotientStalkLinearEquiv` — the displayed identification.

## Main results

* `Stacks.Chow.surjective_stalkLinearMap_of_epi` — the stalk map of an epimorphism is
  surjective.
* `Stacks.Chow.range_stalkLinearMap_comp` — precomposing with a morphism whose stalk map is
  surjective leaves the range of a stalk map unchanged.
* `Stacks.Chow.ker_stalkLinearMap_cokernel_π` — the stalk of the projection onto a cokernel has
  the range of the stalk map as its kernel.
* `Stacks.Chow.range_stalkLinearMap_denominatorIdealTimesModuleι` — the product `I F` and the
  action of `I` on `F` have the same range on every stalk.

## Implementation notes

What is **not** proved here, and is what the length computation of Tag 02SW part (4) needs on
top of it: that the range of the stalk of the action is `Ideal.denominatorIdeal a b` acting on
`Fₓ`, for a local ratio `a / b` of `s` at `x`. That identification has two halves, neither of
which exists in the library at this commit. The first is a sections-level formula for the
action, `η(d ⊗ n) = ι(d) · n`, which needs a sections-level formula for
`AlgebraicGeometry.tensorProductLeftUnitor`; combined with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ` and
`stalkMap_sheafifyUnit_isIso` it would give the range as the stalk of the denominator ideal
acting on `Fₓ`. The second is that that stalk is `Ideal.denominatorIdeal a b`, which follows
from `Stacks.Chow.range_denominatorIdealι_app_eq_coe_denominatorIdeal` on the basic opens of a
trivializing affine, by choosing germ representatives — `Stacks.ColonLocalization` is not
needed for it, since the basic-open presentation of
`Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen` is already available on a
basis of neighbourhoods of `x`.

Three spellings of one stalk are in play and instance search distinguishes them. The module
structure on the stalk of a sheaf of modules on a scheme is found only when the module is
written at the declared type `X.Modules`, so the three objects of Tag 02P2 — which
`StacksFrontier.AlgebraicGeometry.Meromorphic.IdealTimesModule` builds at the spelling
`SheafOfModules X.ringCatSheaf` — are re-ascribed here as `abbrev`s with declared type
`X.Modules`; a type ascription on the term does not work, because instance search re-infers the
type from the term. For the same reason the category instance on `X.Modules` is a copy of the
one on `SheafOfModules`, so an epimorphism in one reading is invisible to instance search in the
other, and `Stacks.Chow.epi_modules` transports it by hand, as
`AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules` does in the other direction.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (stalkFunctor)

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- Sheafification of presheaves of abelian groups on the opens of `X`. -/
local instance : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of `X`, the morphisms of presheaves of abelian groups inverted by
sheafification are exactly the locally bijective ones. -/
local instance : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheaves of modules over the structure sheaf of `X` form an abelian category. -/
local instance : Abelian (_root_.SheafOfModules.{u} X.ringCatSheaf) := inferInstance

/-- An epimorphism of sheaves of modules over the structure sheaf, read at the `X.Modules`
category. This is the converse direction of
`AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules`, and it is needed for the same reason:
the category instance on `X.Modules` is a copy of the one on `SheafOfModules`, so an
epimorphism in one reading is invisible to instance search in the other. -/
theorem epi_modules {M N : X.Modules} (f : M ⟶ N)
    (hf : @Epi (_root_.SheafOfModules.{u} X.ringCatSheaf) inferInstance M N f) : Epi f :=
  ⟨fun g h hcomp => hf.left_cancellation g h hcomp⟩

/-- **The stalk map of an epimorphism is surjective.** Taking stalks preserves colimits, so the
cokernel of the stalk map is the stalk of the cokernel, which is a zero module. -/
theorem surjective_stalkLinearMap_of_epi {A B : X.Modules} (f : A ⟶ B) (hf : Epi f) (x : X) :
    Function.Surjective (AlgebraicGeometry.stalkLinearMap A B f x) :=
  have := hf
  (AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel f x).2
    ((AlgebraicGeometry.Scheme.Modules.notMem_supp_iff_isZero_stalk (cokernel f) x).2
      (Functor.map_isZero _ (isZero_cokernel_of_epi f)))

/-- **Precomposing with a morphism whose stalk map is surjective does not change the range of a
stalk map.** -/
theorem range_stalkLinearMap_comp {A A' B : X.Modules} (u : A ⟶ A') (v : A' ⟶ B) (x : X)
    (hu : Function.Surjective (AlgebraicGeometry.stalkLinearMap A A' u x)) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap A B (u ≫ v) x) =
      LinearMap.range (AlgebraicGeometry.stalkLinearMap A' B v x) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨w, rfl⟩ := hz
    exact ⟨AlgebraicGeometry.stalkLinearMap A A' u x w,
      (AlgebraicGeometry.Scheme.Modules.stalkLinearMap_comp u v x w).symm⟩
  · intro z hz
    obtain ⟨w, rfl⟩ := hz
    obtain ⟨w', rfl⟩ := hu w
    exact ⟨w', AlgebraicGeometry.Scheme.Modules.stalkLinearMap_comp u v x w'⟩

/-- **The stalk of the projection onto a cokernel has the range of the stalk map as kernel.**
Exactness of a short complex of sheaves of modules is a stalkwise condition, and
`A ⟶ B ⟶ cokernel f` is exact. -/
theorem ker_stalkLinearMap_cokernel_π {A B : X.Modules} (f : A ⟶ B) (x : X) :
    LinearMap.ker (AlgebraicGeometry.stalkLinearMap B (cokernel f) (cokernel.π f) x) =
      LinearMap.range (AlgebraicGeometry.stalkLinearMap A B f x) := by
  have hx := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
      (O := X.ringCatSheaf) (ShortComplex.cokernelSequence f)).1
    (ShortComplex.cokernelSequence_exact f) x
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hx
  exact SetLike.ext fun z => ⟨fun hz => hx.ge hz, fun hz => hx.le hz⟩

/-- **The stalk of a cokernel is the quotient of the stalk by the range of the stalk map.**
Taking stalks is exact, so the stalk of `cokernel f` is the quotient of the stalk of `B` by the
range of the stalk map of `f`: the stalk of `cokernel.π f` is surjective, being the stalk map of
an epimorphism, and its kernel is that range. -/
def cokernelStalkLinearEquiv {A B : X.Modules} (f : A ⟶ B) (x : X) :
    (B.presheaf.stalk x ⧸ LinearMap.range (AlgebraicGeometry.stalkLinearMap A B f x) : Type u)
      ≃ₗ[X.presheaf.stalk x] (cokernel f).presheaf.stalk x :=
  (Submodule.quotEquivOfEq _ _ (ker_stalkLinearMap_cokernel_π f x).symm).trans
    ((AlgebraicGeometry.stalkLinearMap B (cokernel f) (cokernel.π f) x).quotKerEquivOfSurjective
      (surjective_stalkLinearMap_of_epi (cokernel.π f) inferInstance x))

/-! ### The stalk of the first denominator quotient

The three objects of [Stacks, Tag 02P2] are ascribed at the declared type `X.Modules` below.
They are the same objects as the ones `StacksFrontier.AlgebraicGeometry.Meromorphic.IdealTimesModule`
builds, spelled `SheafOfModules X.ringCatSheaf` there; but the module structure on the stalk of
a sheaf of modules on a scheme is found by instance search only at the `X.Modules` spelling, and
instance search is syntactic, so a type ascription on the term does not suffice. -/

/-- `AlgebraicGeometry.denominatorIdeal` tensored with `F`, at the declared type `X.Modules`. -/
abbrev denominatorIdealTensorModule (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorProduct X.sheaf.obj X.ringCatSheaf.property
    (AlgebraicGeometry.denominatorIdeal X L s) F

/-- `AlgebraicGeometry.denominatorIdealTimesModule`, at the declared type `X.Modules`. -/
abbrev denominatorIdealTimesModuleDecl (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) : X.Modules :=
  AlgebraicGeometry.denominatorIdealTimesModule X L F s

/-- `Stacks.Chow.denominatorQuotient`, at the declared type `X.Modules`. -/
abbrev denominatorQuotientDecl (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) : X.Modules :=
  denominatorQuotient X L F s

/-- **The product `I F` and the action of `I` on `F` have the same range on every stalk.** The
product is by definition the image of the action, so the action is the epimorphism onto that
image followed by the inclusion, and the stalk map of an epimorphism is surjective. -/
theorem range_stalkLinearMap_denominatorIdealTimesModuleι (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) (x : X) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap (denominatorIdealTimesModuleDecl L F s) F
        (AlgebraicGeometry.denominatorIdealTimesModuleι X L F s) x) =
      LinearMap.range (AlgebraicGeometry.stalkLinearMap (denominatorIdealTensorModule L F s) F
        (AlgebraicGeometry.denominatorIdealAction X L F s) x) := by
  have hepi := epi_modules
    (Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s))
    (Abelian.imageStrongEpiMonoFactorisation _).e_strong_epi.epi
  conv_rhs => rw [← Abelian.image.fac (AlgebraicGeometry.denominatorIdealAction X L F s)]
  exact (range_stalkLinearMap_comp _ _ x (surjective_stalkLinearMap_of_epi _ hepi x)).symm

/-- **The stalk of the first denominator quotient of [Stacks, Tag 02SW] is the quotient of the
stalk of `F` by the range of the stalk of the action of the ideal of denominators.** This is
`Stacks.Chow.cokernelStalkLinearEquiv` at the first canonical map of [Stacks, Tag 02P2],
composed with `Stacks.Chow.range_stalkLinearMap_denominatorIdealTimesModuleι` so that the
submodule divided out is presented by the action of the ideal on `F` rather than by the product
`I F` the quotient is formed from. -/
def denominatorQuotientStalkLinearEquiv (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) (x : X) :
    (F.presheaf.stalk x ⧸ LinearMap.range (AlgebraicGeometry.stalkLinearMap
        (denominatorIdealTensorModule L F s) F
        (AlgebraicGeometry.denominatorIdealAction X L F s) x) : Type u)
      ≃ₗ[X.presheaf.stalk x] (denominatorQuotientDecl L F s).presheaf.stalk x :=
  (Submodule.quotEquivOfEq _ _
      (range_stalkLinearMap_denominatorIdealTimesModuleι L F s x).symm).trans
    (cokernelStalkLinearEquiv (AlgebraicGeometry.denominatorIdealTimesModuleι X L F s) x)

end Stacks.Chow

end
