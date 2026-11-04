module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorParasiticKernel

/-!
# `QCoh(𝒪_𝒳)` as the Serre quotient of `LQCoh^fbc(𝒪_𝒳)` by the parasitic modules

Let `𝒳` be an algebraic stack and let `Parasitic(𝒪_𝒳) ⊂ Mod(𝒪_𝒳)` be the full subcategory of
parasitic modules (**Stacks 0773**).  **Stacks 07B2** reads off **Stacks 0778** and
**Stacks 0779** the identification

`QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`,

in words: the category of quasi-coherent modules is the category of locally quasi-coherent
modules with the flat base change property divided out by the Serre subcategory consisting of
parasitic objects (Homology, Lemma 12.10.6, **Stacks 02MS**).  It adds that the existence of an
inclusion functor `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` which is left adjoint to the quotient
functor is a key feature of the situation, and closes by pointing at **Stacks 07B5** and
**Stacks 07BA** for the analogous statement on the level of derived categories.

Both assertions are proved here.  The quotient functor is the coherator
`Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778**: by **Stacks 0779** it is exact and its
kernel is exactly the parasitic part, so the parasitic part is a Serre class and the class of
morphisms `Q` inverts is exactly the class of morphisms whose kernel and cokernel are parasitic
— that is `CategoryTheory.ObjectProperty.isoModSerre` of the parasitic part.  Since the
inclusion `i` is fully faithful and `Q` is its right adjoint, `Q` is a localization functor
(`CategoryTheory.Adjunction.isLocalization'`), and this is the displayed identification.  The
second assertion is then the adjunction of **Stacks 0778** read through that identification.

## Main definitions

* `AlgebraicGeometry.Stack.parasiticFlatBaseChangeModules`: the subcategory
  `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` of `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.parasiticIsoModSerre`: the class of morphisms of `LQCoh^fbc(𝒪_𝒳)`
  that become invertible in the Serre quotient by the parasitic part, namely those whose kernel
  and cokernel are parasitic.
* `AlgebraicGeometry.Stack.serreQuotientEquivalenceQuasicoherentModules`: the displayed
  identification of **Stacks 07B2** as an equivalence of categories between the Serre quotient
  `LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` and `QCoh(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.isSerreClass_parasiticFlatBaseChangeModules`: the parasitic part of
  `LQCoh^fbc(𝒪_𝒳)` is a Serre subcategory, the fact **Stacks 07B2** quotes when it divides by
  it.
* `AlgebraicGeometry.Stack.isLocalization_flatBaseChangeQuasicoherator`: **Stacks 07B2**, the
  displayed identification — the coherator of **Stacks 0778** is a localization functor for the
  class of morphisms whose kernel and cokernel are parasitic.
* `AlgebraicGeometry.Stack.serreQuotientAdjunction`: **Stacks 07B2**, the key feature — the
  inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`, read on the Serre quotient through the
  equivalence above, is left adjoint to the quotient functor.

## Implementation notes

### What is data

The displayed identification of the source is an equality of categories, and it is produced as
data twice over: as the property `CategoryTheory.Functor.IsLocalization` of the *given* functor
`Q` of **Stacks 0778**, and as the equivalence
`AlgebraicGeometry.Stack.serreQuotientEquivalenceQuasicoherentModules` between Mathlib's
constructed Serre quotient and `QCoh(𝒪_𝒳)`, built from that localization property by
`CategoryTheory.Localization.equivalenceFromModel`.  Neither is wrapped in an existence
statement.  The adjunction is likewise a term of `CategoryTheory.Adjunction`, not a
`Nonempty`.

### The Serre quotient

The quotient of an abelian category by a Serre subcategory is, in Mathlib, the localization at
`CategoryTheory.ObjectProperty.isoModSerre`, the class of morphisms whose kernel and cokernel
lie in the subcategory; `CategoryTheory.ObjectProperty.SerreClassLocalization` shows that the
localization is again abelian and that the localization functor is exact, which is the content
of **Stacks 02MS** the source cites.  So "`QCoh(𝒪_𝒳)` is the quotient" is exactly
`Q.IsLocalization (Parasitic ∩ LQCoh^fbc).isoModSerre`, and that is what is proved.

That the parasitic part *is* a Serre class is not assumed: it is the kernel of the exact functor
`Q`, by **Stacks 0779** part (1), and the kernel of an exact functor between abelian categories
is a Serre class.  This is the one place where the formalization does not follow the source's
order — the source proves the Serre property first (**Stacks 0774** part (2)(b)) and uses it to
get exactness of `Q`, while here exactness of `Q` comes from the explicit chart description of
**Stacks 0779** part (3) and the Serre property is read off it.  So nothing here consumes
**Stacks 0774** part (2); that part is proved independently, the closure under submodules and
extensions in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSerreSubcategory.lean` and the
closure under quotients in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSheafification.lean`.

### The spelling of the three categories

`Mod(𝒪_𝒳)` is `CategoryTheory.SheafOfModules` over
`AlgebraicGeometry.FibredSite.ringStructureSheafCore`; there is no use of the separate
`AlgebraicGeometry.Scheme.Modules` spelling anywhere in this neighbourhood, and none is
introduced here, so the two cannot be mixed.  `QCoh(𝒪_𝒳)` is
`AlgebraicGeometry.FibredSite.quasicoherentModules` (**Stacks 06WG**) and `LQCoh^fbc(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules` (**Stacks 07AQ**), both full
subcategories of sheaves of modules; the parasitic condition is
`AlgebraicGeometry.Stack.IsParasitic` (**Stacks 0773**), which at `SiteKind.etale` is stated over
the very sheaf of rings `LQCoh^fbc(𝒪_𝒳)` is built on, so the intersection needs no transport.

### The hypotheses carried, and why

The data `hinc`, `hclosed`, `hpres`, `hls`, `hlsD`, `hwp`, `hsep` and the chart data `r`,
`hrpar`, `hrcounit`, `hreq`, `hrfincolim` are exactly the hypotheses under which this library
has **Stacks 0778** and **Stacks 0779**; see
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorParasiticKernel.lean` for what each
of them is and which part of the source it stands for.  Two further inputs are instance
arguments:

* `Abelian (QCoh(𝒪_𝒳))` is **Stacks 06WV** part (2), which the source gets from the equivalence
  `QCoh(𝒪_𝒳) ≅ QCoh(U, R, s, t, c)` of **Stacks 06WV** part (1).  That equivalence is not in
  this library, which carries the abelian structure as a hypothesis wherever it needs it, as in
  `AlgebraicGeometry.FibredSite.isGrothendieckAbelian_quasicoherentModules`.
* `Abelian (LQCoh^fbc(𝒪_𝒳))` is **Stacks 0771** part (2), the weak Serre subcategory property of
  `LQCoh^fbc(𝒪_𝒳)` inside `Mod(𝒳_étale, 𝒪_𝒳)`, which is likewise absent; compare the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentKernelCokernel.lean`.

Both are needed to speak of a Serre class at all, since `isoModSerre` is about kernels and
cokernels in the two categories; neither restates anything **Stacks 07B2** asserts.

## References

* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07B2](https://stacks.math.columbia.edu/tag/07B2)
* [Stacks Project, Tag 07B5](https://stacks.math.columbia.edu/tag/07B5)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe vA uA vC uC vD uD u w

namespace AlgebraicGeometry.Stack

section Abstract

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- A functor which is a localization at a class of morphisms is a localization at any class
equal to it. -/
private lemma isLocalization_of_morphismProperty_eq (L : C ⥤ D)
    {W W' : MorphismProperty C} (hW : W = W') [L.IsLocalization W] : L.IsLocalization W' := by
  subst hW
  infer_instance

/-- **An exact functor between abelian categories inverts exactly the morphisms whose kernel and
cokernel lie in its kernel.**  One direction is
`CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff`; for the other, exactness carries
the kernel and the cokernel of `f` to the kernel and the cokernel of `F f`, which vanish when
`F f` is invertible. -/
private lemma isoModSerre_eq_inverseImage_isomorphisms [Abelian C] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass] (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (hP : P = F.kernel) :
    P.isoModSerre = (MorphismProperty.isomorphisms D).inverseImage F := by
  subst hP
  have hinv : F.kernel.isoModSerre.IsInvertedBy F :=
    (ObjectProperty.isoModSerre_isInvertedBy_iff _ F).2 le_rfl
  refine MorphismProperty.ext _ _ fun {_ _} f => ⟨fun hf => hinv f hf, fun hf => ?_⟩
  have : IsIso (F.map f) := hf
  exact ⟨(PreservesKernel.iso F f).isZero_iff.2 (isZero_kernel_of_mono (F.map f)),
    (PreservesCokernel.iso F f).isZero_iff.2 (isZero_cokernel_of_epi (F.map f))⟩

end Abstract

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The subcategory `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` of `LQCoh^fbc(𝒪_𝒳)`: a locally
quasi-coherent module with the flat base change property lies in it exactly when it is parasitic
(**Stacks 0773**) as a presheaf of modules on `𝒳_étale`. -/
abbrev parasiticFlatBaseChangeModules :
    ObjectProperty (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  fun F => IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val

section Quotient

variable [EssentiallySmall.{u} 𝒳.val.val.obj]
  [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  [Abelian (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  {𝒜 : Type uA} [Category.{vA} 𝒜]
  (r : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids ⥤ 𝒜)
  (hrpar : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsZero (r.obj F) ↔ IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val)
  (hrcounit : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsIso (r.map ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)))
  (hreq : (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc ⋙ r).IsEquivalence)
  (hrfincolim : PreservesFiniteColimits r)

omit [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)]
  [Abelian (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids)] in
include hinc hrpar hrcounit hreq in
/-- **Stacks 0779** part (1), read as an equality of subcategories: the parasitic part of
`LQCoh^fbc(𝒪_𝒳)` is the kernel of the coherator `Q` of **Stacks 0778**. -/
theorem parasiticFlatBaseChangeModules_eq_kernel :
    parasiticFlatBaseChangeModules B E h S hS 𝒳 =
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep).kernel := by
  ext F
  exact (isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    hls hlsD hwp hsep r hrpar hrcounit hreq F).symm

include hinc hrpar hrcounit hreq hrfincolim in
/-- **The parasitic part of `LQCoh^fbc(𝒪_𝒳)` is a Serre subcategory**, the fact
**Stacks 07B2** quotes when it divides `LQCoh^fbc(𝒪_𝒳)` by it.

It is the kernel of the coherator `Q` by **Stacks 0779** part (1), and `Q` is exact by
**Stacks 0779** part (3); the kernel of an exact functor between abelian categories contains the
zero object and is closed under subobjects, quotients and extensions. -/
theorem isSerreClass_parasiticFlatBaseChangeModules :
    (parasiticFlatBaseChangeModules B E h S hS 𝒳).IsSerreClass := by
  have hpl := preservesFiniteLimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep
  have hpc := preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep r hrcounit hreq hrfincolim
  rw [parasiticFlatBaseChangeModules_eq_kernel B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp
    hsep r hrpar hrcounit hreq]
  infer_instance

/-- The class of morphisms of `LQCoh^fbc(𝒪_𝒳)` which become invertible in the Serre quotient by
the parasitic part: those whose kernel and cokernel are parasitic.  This is
`CategoryTheory.ObjectProperty.isoModSerre` of
`AlgebraicGeometry.Stack.parasiticFlatBaseChangeModules`, with the Serre class structure
supplied by `AlgebraicGeometry.Stack.isSerreClass_parasiticFlatBaseChangeModules`. -/
abbrev parasiticIsoModSerre :
    MorphismProperty (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  @ObjectProperty.isoModSerre _ _ _ (parasiticFlatBaseChangeModules B E h S hS 𝒳)
    (isSerreClass_parasiticFlatBaseChangeModules B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp
      hsep r hrpar hrcounit hreq hrfincolim)

include hinc hrpar hrcounit hreq hrfincolim in
/-- **The coherator inverts exactly the morphisms whose kernel and cokernel are parasitic.**

One direction is Mathlib's criterion
`CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff` for an exact functor, whose
hypothesis is that the Serre class is killed by the functor — the forward direction of
**Stacks 0779** part (1).  Conversely, if `Q φ` is invertible then, `Q` being exact, `Q` of the
kernel of `φ` is the kernel of `Q φ` and so vanishes, and likewise for the cokernel, so both are
parasitic by **Stacks 0779** part (1) again. -/
theorem parasiticIsoModSerre_eq_inverseImage_isomorphisms :
    parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar hrcounit
        hreq hrfincolim =
      (MorphismProperty.isomorphisms (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
          𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)).inverseImage
        (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          hinc hclosed hpres hls hlsD hwp hsep) := by
  have := isSerreClass_parasiticFlatBaseChangeModules B E h S hS 𝒳 hinc hclosed hpres hls hlsD
    hwp hsep r hrpar hrcounit hreq hrfincolim
  have := preservesFiniteLimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep
  have := preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep r hrcounit hreq hrfincolim
  exact isoModSerre_eq_inverseImage_isomorphisms _ _
    (parasiticFlatBaseChangeModules_eq_kernel B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp
      hsep r hrpar hrcounit hreq)

include hinc hrpar hrcounit hreq hrfincolim in
/-- **Stacks 07B2**, the displayed identification

`QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.

The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778** is a localization functor for
the class of morphisms whose kernel and cokernel are parasitic, that is, it exhibits
`QCoh(𝒪_𝒳)` as the quotient of `LQCoh^fbc(𝒪_𝒳)` by the Serre subcategory of parasitic objects
(**Stacks 02MS**).

The inclusion `i` is fully faithful and `Q` is its right adjoint (**Stacks 0778**), so `Q` is a
localization functor for the class of morphisms it inverts; by
`AlgebraicGeometry.Stack.parasiticIsoModSerre_eq_inverseImage_isomorphisms` that class is the
one attached to the parasitic part. -/
@[stacks 07B2 "the displayed identification QCoh(𝒪_𝒳) = LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ \
LQCoh^fbc(𝒪_𝒳): the coherator Q of 0778 is a localization functor for the Serre class of \
parasitic objects; over the hypotheses of 0778 and 0779 and the abelian structures of 06WV (2) \
and 0771 (2)"]
theorem isLocalization_flatBaseChangeQuasicoherator :
    (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep).IsLocalization
      (parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar
        hrcounit hreq hrfincolim) := by
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).full
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).faithful
  have := (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).isLocalization'
  exact isLocalization_of_morphismProperty_eq _
    (parasiticIsoModSerre_eq_inverseImage_isomorphisms B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep r hrpar hrcounit hreq hrfincolim).symm

/-- **Stacks 07B2**, the displayed identification as an equivalence of categories.  The Serre
quotient `LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`, built as the localization of
`LQCoh^fbc(𝒪_𝒳)` at the morphisms with parasitic kernel and cokernel, is equivalent to
`QCoh(𝒪_𝒳)`, the equivalence being the one through which the coherator of **Stacks 0778**
factors. -/
@[stacks 07B2 "the displayed identification read as an equivalence of categories between the \
Serre quotient of LQCoh^fbc(𝒪_𝒳) by Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳) and QCoh(𝒪_𝒳); over the \
hypotheses of 0778 and 0779 and the abelian structures of 06WV (2) and 0771 (2)"]
def serreQuotientEquivalenceQuasicoherentModules :
    (parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar hrcounit
        hreq hrfincolim).Localization ≌
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  letI := isLocalization_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls hlsD
    hwp hsep r hrpar hrcounit hreq hrfincolim
  Localization.equivalenceFromModel
    (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      hinc hclosed hpres hls hlsD hwp hsep)
    (parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar hrcounit
      hreq hrfincolim)

/-- **Stacks 07B2**, the key feature: the inclusion
`i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` is left adjoint to the quotient functor.

Read with `QCoh(𝒪_𝒳)` identified with the Serre quotient by
`AlgebraicGeometry.Stack.serreQuotientEquivalenceQuasicoherentModules`, this is an adjunction
between `i` and the canonical quotient functor
`LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.  It is the adjunction of
**Stacks 0778** composed with the adjoint equivalence, transported along the isomorphism which
identifies the quotient functor with the coherator followed by that equivalence. -/
@[stacks 07B2 "the key feature: the inclusion i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) is left adjoint \
to the quotient functor LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳) / Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳); \
over the hypotheses of 0778 and 0779 and the abelian structures of 06WV (2) and 0771 (2)"]
def serreQuotientAdjunction :
    (serreQuotientEquivalenceQuasicoherentModules B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp
          hsep r hrpar hrcounit hreq hrfincolim).functor ⋙
        quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc ⊣
      (parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar hrcounit
        hreq hrfincolim).Q :=
  letI := isLocalization_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls hlsD
    hwp hsep r hrpar hrcounit hreq hrfincolim
  Adjunction.ofNatIsoRight
    ((serreQuotientEquivalenceQuasicoherentModules B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp
        hsep r hrpar hrcounit hreq hrfincolim).toAdjunction.comp
      (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep))
    (Localization.compEquivalenceFromModelInverseIso
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep)
      (parasiticIsoModSerre B E h S hS 𝒳 hinc hclosed hpres hls hlsD hwp hsep r hrpar
        hrcounit hreq hrfincolim))

end Quotient

end AlgebraicGeometry.Stack

end
