module

public import StacksFrontier.Algebra.Module.Pure.ExtResolution
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineQuasiInverse
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic

/-!
# Extensions of associated modules, compared with pure extensions

Let `U = Spec A` be affine and write `M^a` for the `𝒪`-module on `(Sch/U)_τ` associated to an
`A`-module `M`. Tag 0709 asserts that for all `i` there is a canonical isomorphism

`Ext^i_{Mod((Sch/U)_τ, 𝒪)}(M^a, N^a) = Pext^i_A(M, N)`

functorial in `M` and `N`. This module proves it in degree `0`, where it is the statement that
`M ↦ M^a` is fully faithful together with the computation of `Pext⁰`.

## Main results

* `Stacks.Adequate.fullyFaithfulAssociatedTilde` — **`M ↦ M^a` is fully faithful**, with no
  hypothesis. The affine-section functor of the big site over an affine base is fully faithful
  (`Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`), it carries `M^a` to the module
  extension `B ↦ B ⊗_A M` (`Stacks.Adequate.affineSectionsAssociatedTildeIso`, the Tag 06ZJ
  transport), and extension of scalars is fully faithful
  (`AdequateFunctor.fullyFaithfulModuleExtensionFunctorOn`).
* `Stacks.Adequate.homAddEquivExtZero` — `Hom_A(M, N) = Ext⁰_{Mod(𝒪)}(M^a, N^a)`, the
  degree-`0` instance of the source's canonical arrow, natural in both variables by
  `Stacks.Adequate.homAddEquivExtZero_naturality_left` and `_naturality_right`.
* `Stacks.Adequate.pureExtZeroAddEquivExtZero` — **Tag 0709 in degree `0`**.

## Which degree is registered, and what functoriality is covered

Degree `0` needs neither Tag 06ZW nor Tag 06ZG: the comparison is a map on `Hom`, and the two
identifications it is composed of are available outright. The positive degrees are genuinely
separate. They factor through Tag 06ZW, which replaces `Ext^i_{Mod(𝒪)}` by
`Ext^i_{Adeq(𝒪)}`; both tags are registered in every degree in
`StacksFrontier/AlgebraicGeometry/Adequate/HigherExtsAdequate/AdequateExtComparisonAll.lean`
(`Stacks.Adequate.bijective_mapExtAddHom_ι_adequate` and
`Stacks.Adequate.pureExtToExt_bijective_and_natural`).

The tag asks for functoriality in `M` and `N`, and in degree `0` that is naturality of the
isomorphism in both variables. Both halves of the composite carry it:

* the `Ext` half, `Stacks.Adequate.homAddEquivExtZero`, is natural in both variables —
  `Stacks.Adequate.homAddEquivExtZero_naturality_left` and `_naturality_right`;
* the `Pext` half is natural in both variables at the Hom-complex model that computes it —
  `Module.homComplexZeroHom_naturality_left` and `Module.homComplexZeroHom_naturality_right` of
  `StacksFrontier/Algebra/Module/Pure/ExtResolution.lean`.

The second half is stated at the model rather than at `Module.pureExt` itself because the
library equips `Module.pureExt` with no functorial action in either variable: it is defined from
a pure injective resolution chosen by `Classical.choose`, so a first-variable action is
precomposition on `Hom_A(-, Iᐧ)` and a second-variable action needs a comparison map between
two chosen resolutions. Both of those live on the Hom complex, which is where the two naturality
lemmas above are stated, and `Module.pureExtZeroIsoHom` is the identification of its degree-`0`
cohomology with `Hom_A(M, N)`.

## References

* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
* [Stacks Project, Tag 06ZW](https://stacks.math.columbia.edu/tag/06ZW)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **The associated-module functor `M ↦ M^a` is fully faithful**, for `U = Spec A` affine and
any chosen big `τ`-site over it, with no hypothesis.

Its composite with the affine-section functor is the module extension `B ↦ B ⊗_A M`, by
`Stacks.Adequate.affineSectionsAssociatedTildeIso`; extension of scalars is fully faithful
because the `A`-algebras of the site have the base ring among them; and the affine-section
functor is faithful. -/
public def fullyFaithfulAssociatedTilde : (associatedTilde B).FullyFaithful :=
  haveI : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Faithful :=
    (fullyFaithfulAffineSectionsFunctor B).faithful
  Functor.FullyFaithful.ofCompFaithful
    (Functor.FullyFaithful.ofIso
      (AdequateFunctor.fullyFaithfulModuleExtensionFunctorOn.{u}
        (AdequateFunctor.BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow B.cutoff) B.base_mem))
      (affineSectionsAssociatedTildeIso B))

/-- `M ↦ M^a` is additive: its composite with the faithful affine-section functor is the
module extension `B ↦ B ⊗_A M`, which is additive.

This is a theorem rather than an `instance` because declaring instances for the objects of this
chapter changes instance selection in files that do not import this one; consume it with
`haveI`. -/
public lemma additive_associatedTilde : (associatedTilde B).Additive := by
  have : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Faithful :=
    (fullyFaithfulAffineSectionsFunctor B).faithful
  have : (associatedTilde B ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Additive :=
    Functor.additive_of_iso (affineSectionsAssociatedTildeIso B)
  exact Functor.additive_of_comp_faithful _ (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)))

/-- The action of `M ↦ M^a` on homomorphisms, as an additive bijection: it is bijective because
the functor is fully faithful and additive because the functor is additive. -/
public def homAddEquivAssociatedTilde (M N : ModuleCat.{u} A) :
    (M ⟶ N) ≃+ ((associatedTilde B).obj M ⟶ (associatedTilde B).obj N) :=
  haveI : (associatedTilde B).Additive := additive_associatedTilde B
  { toEquiv := (fullyFaithfulAssociatedTilde B).homEquiv
    map_add' := fun _ _ => (associatedTilde B).map_add }

section

variable [HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf)]

/-- **`Hom_A(M, N) = Ext⁰_{Mod((Sch/U)_τ, 𝒪)}(M^a, N^a)`**: the degree-`0` instance of the
canonical arrow of [Stacks, Tag 0709], which sends a homomorphism to the map `M^a ⟶ N^a` it
induces, viewed as a degree-`0` extension class. It is bijective because `M ↦ M^a` is fully
faithful and `CategoryTheory.Abelian.Ext.addEquiv₀` identifies degree-`0` extension classes with
morphisms. -/
public def homAddEquivExtZero (M N : ModuleCat.{u} A) :
    (M ⟶ N) ≃+ Ext ((associatedTilde B).obj M) ((associatedTilde B).obj N) 0 :=
  (homAddEquivAssociatedTilde B M N).trans Ext.addEquiv₀.symm

/-- The canonical degree-`0` arrow sends `c` to the degree-`0` class of `c^a`. -/
private lemma homAddEquivExtZero_apply (M N : ModuleCat.{u} A) (c : M ⟶ N) :
    homAddEquivExtZero B M N c = Ext.mk₀ ((associatedTilde B).map c) := rfl

/-- **The canonical degree-`0` arrow is natural in `M`**: precomposition with `f : M' ⟶ M` on
homomorphisms is composition with the degree-`0` class of `f^a` on extension classes. -/
public lemma homAddEquivExtZero_naturality_left (M M' N : ModuleCat.{u} A) (f : M' ⟶ M)
    (c : M ⟶ N) :
    homAddEquivExtZero B M' N (f ≫ c) =
      (Ext.mk₀ ((associatedTilde B).map f)).comp (homAddEquivExtZero B M N c) (zero_add 0) := by
  simp only [homAddEquivExtZero_apply, Ext.mk₀_comp_mk₀, Functor.map_comp]

/-- **The canonical degree-`0` arrow is natural in `N`**: postcomposition with `g : N ⟶ N'` on
homomorphisms is composition with the degree-`0` class of `g^a` on extension classes. -/
public lemma homAddEquivExtZero_naturality_right (M N N' : ModuleCat.{u} A) (g : N ⟶ N')
    (c : M ⟶ N) :
    homAddEquivExtZero B M N' (c ≫ g) =
      (homAddEquivExtZero B M N c).comp (Ext.mk₀ ((associatedTilde B).map g)) (add_zero 0) := by
  simp only [homAddEquivExtZero_apply, Ext.mk₀_comp_mk₀, Functor.map_comp]

end

/-- **[Stacks, Tag 0709] in degree `0`.** For `U = Spec A` affine and `A`-modules `M`, `N`, the
canonical arrow

`Pext⁰_A(M, N) ⟶ Ext⁰_{Mod((Sch/U)_τ, 𝒪)}(M^a, N^a)`

is an isomorphism, with no hypothesis. It is the composite of two identifications:
`Pext⁰_A(M, N) = Hom_A(M, N)`, because the degree-`0` cohomology of `Hom_A(M, Iᐧ)` is the kernel
of its first differential and that kernel is the image of the augmentation
(`Module.pureExtZeroIsoHom`); and `Hom_A(M, N) = Ext⁰_{Mod(𝒪)}(M^a, N^a)`, because `M ↦ M^a` is
fully faithful (`Stacks.Adequate.homAddEquivExtZero`). Neither Tag 06ZW nor Tag 06ZG enters: in
degree `0` the comparison is a map on `Hom`, so no derived functor and no injective resolution
in a category of functors is needed.

Functoriality in `M` and `N` is the naturality of the two halves, which is
`Stacks.Adequate.homAddEquivExtZero_naturality_left` and `_naturality_right` for the `Ext` half
and `Module.homComplexZeroHom_naturality_left` and `Module.homComplexZeroHom_naturality_right`
for the `Pext` half; see the module documentation for why the latter two are stated at the Hom
complex that computes `Module.pureExt` rather than at `Module.pureExt` itself.

The `letI` preamble is not a list of hypotheses: both entries are the standard derived-category
and `Ext` choices for the sheaves of modules on the site, spelled out rather than registered
because declaring them as `instance`s in this chapter changes instance selection for files that
do not import this one. It matches the preamble of
`Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_zero`, the degree-`0` registration of
Tag 06ZW, so the two share one spelling of each object. -/
@[stacks 0709 "degree 0, where the canonical arrow is the action of M ↦ M^a on Hom composed \
with the computation of Pext in degree 0, and neither Tag 06ZW nor Tag 06ZG is needed; \
functorial in M and N by homAddEquivExtZero_naturality_left/_right together with \
Module.homComplexZeroHom_naturality_left/_right. Every degree is \
pureExtToExt_bijective_and_natural in HigherExtsAdequate/AdequateExtComparisonAll"]
public def pureExtZeroAddEquivExtZero (M N : ModuleCat.{u} A) :
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    Module.pureExt (A := A) M N 0 ≃+
      Ext ((associatedTilde B).obj M) ((associatedTilde B).obj N) 0 := by
  letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
    HasDerivedCategory.standard _
  letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
    hasExt_of_hasDerivedCategory _
  exact ((Module.pureExtZeroIsoHom (A := A) M N).toLinearEquiv.toAddEquiv.trans
    ModuleCat.homAddEquiv.symm).trans (homAddEquivExtZero B M N)

end Stacks.Adequate

end
