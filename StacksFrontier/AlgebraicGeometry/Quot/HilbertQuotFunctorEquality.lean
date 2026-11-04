module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotNaturality

/-!
# `Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00)

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation over a scheme `S` of a
big fppf site.  Stacks 0D00 asserts that the Hilbert functor of `f` (Stacks 0CZY) is the Quot
functor of its structure sheaf (Stacks 09TR).  This file states and proves that equality, in the
only form in which the two functors are directly comparable: an isomorphism of the presheaves
`hilbertPresheaf f` and `(structureSheafQuotSituation f hf).quotSitePresheaf` on the schemes of
the site, commuting with the two canonical morphisms to `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertFamily_hilbertFamilySubobject_eq`: **the converse
  direction, objectwise** — every quotient classified by the Quot functor is the one a family
  classified by the Hilbert functor determines.
* `AlgebraicGeometry.Space.hilbertFamilySubobject_injective`: **the forward direction is
  injective.**
* `AlgebraicGeometry.Space.quotFamilyOverEquiv`: **the two are mutually inverse at a scheme of
  the site.**
* `AlgebraicGeometry.Space.quotFamilyOfHilbertFamilyOver_baseChange`: **naturality in the test
  scheme** of the forward map, over the schemes of the site.
* `AlgebraicGeometry.Space.hilbertPresheafIsoQuotSitePresheaf`: **Stacks 0D00** — the two
  presheaves on the schemes of the site are isomorphic, naturally in the test scheme.
* `AlgebraicGeometry.Space.exists_hilbertPresheafIso_quotSitePresheaf`: **Stacks 0D00, the whole
  statement** — that isomorphism exists and commutes with the two morphisms to `Y`.

## Implementation notes

**The two notions of "submodule" have to be bridged.**  The Hilbert side's datum is a closed
subspace of `X_T`, read through Stacks 03MB as a quasi-coherent sheaf of ideals, that is as a
`SheafOfModules.Submodule` of `𝒪_{X_T}`; the Quot side's datum is a `CategoryTheory.Subobject`
of `F_T`.  The passage is
`Stacks.SheafOfModules.ImageSubsheaf.subobject_mk_monoRangeSubmodule_ι` and
`Stacks.SheafOfModules.ImageSubsheaf.submodule_eq_of_subobject_mk_ι_eq`: every subobject of a
sheaf of modules is the subobject of exactly one submodule.  With that, the converse construction
`AlgebraicGeometry.Space.exists_hilbertFamily_definingIdealSheaf_eq_of_quotConditions` applies to
the kernel of a quotient classified by the Quot functor, and injectivity of `Z ↦ 𝓘_Z`
(`AlgebraicGeometry.Space.definingIdealSheaf_injective`) gives injectivity of the forward map.

**No equivalence of index categories is needed.**  Both sides are presheaves on
`(BigFppfOver B S hS)ᵒᵖ`, the schemes of the site; a section of either is a morphism to `Y`
together with a datum over the resulting test scheme, and a morphism of algebraic spaces is a
morphism of presheaves in the one-field wrapper `CategoryTheory.ObjectProperty.homMk`.  So the
comparison is built directly, with no functor between
`AlgebraicGeometry.Space.SchemesOverPresheaf` and `AlgebraicGeometry.Space.SchemesOver`.

**One declaration per respelling of `X_T`.**  The type of the
`AlgebraicGeometry.Space.QuotFamilyOver.subobject` field is indexed by the morphism to `Y`, so
comparing two spellings of that morphism happens *under*
`AlgebraicGeometry.Space.QuotientSituation.baseChangeModule`.  The equalities
`quotFamilyOver_eta`, `quotFamilyOfHilbertFamilyOver_eq`,
`quotFamilyOfHilbertFamilyOver_subobject` and `quotFamilyOver_baseChange_eta` each make one such
comparison, at a *variable* family, where it holds by `rfl`.

**What the hypotheses are.**  Only `hf`, finite presentation of `f`, which is the standing
assumption of Situation 0CZY in which Stacks 0D00 is stated.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- Left in place, this instance is selected ahead of `SheafOfModules.instAbelian` and leaves the
-- module universe of every subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

variable (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (T : SchemesOverPresheaf B S hS Y)

/-! ### The forward map is injective -/

/-- **The forward map of Stacks 0D00 is injective at one test scheme**: two families classified
by the Hilbert functor with the same quotient of `F_T` are equal. -/
theorem hilbertFamilySubobject_injective :
    Function.Injective (hilbertFamilySubobject f hf T) := fun _ _ h =>
  definingIdealSheaf_hilbertFamily_injective B S hS f T
    (Stacks.SheafOfModules.ImageSubsheaf.submodule_eq_of_subobject_mk_ι_comp_eq
      (baseChangeModuleIsoStructureSheaf f hf T).symm h)

/-! ### The forward map is surjective -/

/-- **The converse direction of Stacks 0D00, objectwise**: a quotient of `F_T` classified by the
Quot functor of `𝒪_X/X/B` is the quotient a family classified by the Hilbert functor of `f`
determines. -/
theorem exists_hilbertFamily_hilbertFamilySubobject_eq
    (K : Subobject ((structureSheafQuotSituation f hf).baseChangeModule
      (structureSheafTestScheme T)))
    (hK : K ∈ (structureSheafQuotSituation f hf).properlySupportedQuotients
      (structureSheafTestScheme T)) :
    ∃ z : HilbertFamily f T, hilbertFamilySubobject f hf T z = K := by
  obtain ⟨I, hmk, ⟨hcok⟩⟩ :=
    Stacks.SheafOfModules.ImageSubsheaf.exists_submodule_of_subobject_comp_iso
      (baseChangeModuleIsoStructureSheaf f hf T) K
  obtain ⟨z, hz⟩ := exists_hilbertFamily_definingIdealSheaf_eq_of_quotConditions B S hS f hf T I
    (SheafOfModules.IsFinitePresentationOnSite.of_iso hcok.symm hK.1.2)
    (IsFlatOver.of_iso B S hS _ hcok.symm hK.1.1.2)
    ((structureSheafQuotSituation f hf).isProperlySupportedOver_of_iso hcok.symm hK.2)
  subst hz
  exact ⟨z, hmk⟩

/-! ### The bijection over a scheme of the site -/

/-- The family classified by the Hilbert functor that a quotient classified by the Quot functor
comes from, over a scheme of the site: the one
`AlgebraicGeometry.Space.exists_hilbertFamily_hilbertFamilySubobject_eq` produces over the test
scheme the quotient lies over. -/
def hilbertFamilyOfQuotFamilyOver {Tsch : BigFppfOver B S hS}
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) :
    HilbertFamily f (CostructuredArrow.mk q.toBase.hom) :=
  (exists_hilbertFamily_hilbertFamilySubobject_eq f hf (CostructuredArrow.mk q.toBase.hom)
    q.subobject q.mem).choose

/-- That family cuts out the given quotient. -/
theorem hilbertFamilySubobject_hilbertFamilyOfQuotFamilyOver {Tsch : BigFppfOver B S hS}
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) :
    hilbertFamilySubobject f hf (CostructuredArrow.mk q.toBase.hom)
        (hilbertFamilyOfQuotFamilyOver f hf q) = q.subobject :=
  (exists_hilbertFamily_hilbertFamilySubobject_eq f hf (CostructuredArrow.mk q.toBase.hom)
    q.subobject q.mem).choose_spec

/-- Reading a family classified by the Hilbert functor as a quotient and back gives the family
again. -/
theorem hilbertFamilyOfQuotFamilyOver_quotFamilyOfHilbertFamilyOver
    {Tsch : BigFppfOver B S hS} (x : HilbertFamilyOver f Tsch) :
    hilbertFamilyOfQuotFamilyOver f hf (quotFamilyOfHilbertFamilyOver f hf x) = x.family :=
  hilbertFamilySubobject_injective f hf (CostructuredArrow.mk x.toBase)
    (hilbertFamilySubobject_hilbertFamilyOfQuotFamilyOver f hf
      (quotFamilyOfHilbertFamilyOver f hf x))

/-- The inverse of the forward map of Stacks 0D00 over a scheme of the site: a quotient
classified by the Quot functor goes to the family it cuts out, over the morphism to `Y` it lies
over. -/
abbrev hilbertFamilyOverOfQuotFamilyOver {Tsch : BigFppfOver B S hS}
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) : HilbertFamilyOver f Tsch :=
  ⟨q.toBase.hom, hilbertFamilyOfQuotFamilyOver f hf q⟩

/-- The subobject the forward map of Stacks 0D00 records is the one the family cuts out. -/
@[simp]
theorem quotFamilyOfHilbertFamilyOver_subobject {Tsch : BigFppfOver B S hS}
    (x : HilbertFamilyOver f Tsch) :
    (quotFamilyOfHilbertFamilyOver f hf x).subobject =
      hilbertFamilySubobject f hf (CostructuredArrow.mk x.toBase) x.family :=
  rfl

/-- A quotient classified by the Quot functor over a scheme of the site is its own three fields. -/
theorem quotFamilyOver_eta {Tsch : BigFppfOver B S hS}
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) :
    (⟨ObjectProperty.homMk q.toBase.hom, q.subobject, q.mem⟩ :
      QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) = q :=
  rfl

/-- **The forward map of Stacks 0D00 over a scheme of the site, with its subobject named.**  The
quotient it produces is the one cut out by the family, so naming that quotient names the whole
section of the Quot presheaf. -/
theorem quotFamilyOfHilbertFamilyOver_eq {Tsch : BigFppfOver B S hS}
    (x : HilbertFamilyOver f Tsch)
    (K : Subobject ((structureSheafQuotSituation f hf).baseChangeModule
      (structureSheafTestScheme (CostructuredArrow.mk x.toBase))))
    (hK : K ∈ (structureSheafQuotSituation f hf).properlySupportedQuotients
      (structureSheafTestScheme (CostructuredArrow.mk x.toBase)))
    (hxK : hilbertFamilySubobject f hf (CostructuredArrow.mk x.toBase) x.family = K) :
    quotFamilyOfHilbertFamilyOver f hf x = ⟨ObjectProperty.homMk x.toBase, K, hK⟩ := by
  subst hxK
  rfl

/-- The forward map of Stacks 0D00 undoes
`AlgebraicGeometry.Space.hilbertFamilyOverOfQuotFamilyOver`. -/
theorem quotFamilyOfHilbertFamilyOver_hilbertFamilyOverOfQuotFamilyOver
    {Tsch : BigFppfOver B S hS}
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) :
    quotFamilyOfHilbertFamilyOver f hf (hilbertFamilyOverOfQuotFamilyOver f hf q) = q :=
  (quotFamilyOfHilbertFamilyOver_eq f hf (hilbertFamilyOverOfQuotFamilyOver f hf q)
      q.subobject q.mem
      (hilbertFamilySubobject_hilbertFamilyOfQuotFamilyOver f hf q)).trans
    (quotFamilyOver_eta f hf q)

/-- `AlgebraicGeometry.Space.hilbertFamilyOverOfQuotFamilyOver` undoes the forward map. -/
theorem hilbertFamilyOverOfQuotFamilyOver_quotFamilyOfHilbertFamilyOver
    {Tsch : BigFppfOver B S hS} (x : HilbertFamilyOver f Tsch) :
    hilbertFamilyOverOfQuotFamilyOver f hf (quotFamilyOfHilbertFamilyOver f hf x) = x := by
  obtain ⟨b, z⟩ := x
  exact congrArg (HilbertFamilyOver.mk b)
    (hilbertFamilyOfQuotFamilyOver_quotFamilyOfHilbertFamilyOver f hf ⟨b, z⟩)

/-- **Stacks 0D00 over a scheme of the site**: the families classified by the Hilbert functor of
`f` over a scheme `T` of the big fppf site are the quotients classified by the Quot functor of
`𝒪_X/X/B` over `T`, by the forward map of Stacks 0D00. -/
def quotFamilyOverEquiv (Tsch : BigFppfOver B S hS) :
    HilbertFamilyOver f Tsch ≃ QuotFamilyOver (structureSheafQuotSituation f hf) Tsch where
  toFun := quotFamilyOfHilbertFamilyOver f hf
  invFun := hilbertFamilyOverOfQuotFamilyOver f hf
  left_inv := hilbertFamilyOverOfQuotFamilyOver_quotFamilyOfHilbertFamilyOver f hf
  right_inv := quotFamilyOfHilbertFamilyOver_hilbertFamilyOverOfQuotFamilyOver f hf

/-! ### Naturality in the test scheme -/

/-- Base change in the Quot presheaf, written out. -/
theorem quotFamilyOver_baseChange_eta {Tsch Tsch' : BigFppfOver B S hS} (g : Tsch' ⟶ Tsch)
    (q : QuotFamilyOver (structureSheafQuotSituation f hf) Tsch) :
    q.baseChange g =
      ⟨(schemeSpaceFunctor B S hS).map g ≫ q.toBase,
        (structureSheafQuotSituation f hf).quotientPullback
          (QuotFamilyOver.restrict g q.toBase) q.subobject,
        (structureSheafQuotSituation f hf).quotientPullback_mem_properlySupportedQuotients
          (QuotFamilyOver.restrict g q.toBase) q.subobject q.mem⟩ :=
  rfl

/-- **The pullback of the quotient a family cuts out is the quotient its base change cuts out**,
over a scheme of the site. -/
theorem quotientPullback_subobject_quotFamilyOfHilbertFamilyOver
    {Tsch Tsch' : BigFppfOver B S hS} (g : Tsch' ⟶ Tsch) (x : HilbertFamilyOver f Tsch) :
    (structureSheafQuotSituation f hf).quotientPullback
        (QuotFamilyOver.restrict g (quotFamilyOfHilbertFamilyOver f hf x).toBase)
        (quotFamilyOfHilbertFamilyOver f hf x).subobject =
      hilbertFamilySubobject f hf (CostructuredArrow.mk (x.baseChange g).toBase)
        (x.baseChange g).family := by
  rw [quotFamilyOfHilbertFamilyOver_subobject]
  exact quotientPullback_hilbertFamilySubobject f hf
    (HilbertFamilyOver.restrict g x.toBase) x.family

/-- **Naturality of the forward map of Stacks 0D00 over the schemes of the site.** -/
theorem quotFamilyOfHilbertFamilyOver_baseChange {Tsch Tsch' : BigFppfOver B S hS}
    (g : Tsch' ⟶ Tsch) (x : HilbertFamilyOver f Tsch) :
    quotFamilyOfHilbertFamilyOver f hf (x.baseChange g) =
      (quotFamilyOfHilbertFamilyOver f hf x).baseChange g :=
  (quotFamilyOfHilbertFamilyOver_eq f hf (x.baseChange g) _ _
      (quotientPullback_subobject_quotFamilyOfHilbertFamilyOver f hf g x).symm).trans
    (quotFamilyOver_baseChange_eta f hf g (quotFamilyOfHilbertFamilyOver f hf x)).symm

/-! ### Stacks 0D00 -/

/-- **Stacks 0D00: `Hilb_{X/B} = Quot_{𝒪_X/X/B}`.**  The Hilbert functor of a morphism
`f : X ⟶ Y` of finite presentation and the Quot functor of its structure sheaf are isomorphic as
presheaves on the schemes of the big fppf site, naturally in the test scheme: over each scheme
`T` the bijection is `AlgebraicGeometry.Space.quotFamilyOverEquiv`, a family `Z ⊆ X_T` going to
the quotient of `F_T` by its defining ideal sheaf, and naturality is
`AlgebraicGeometry.Space.quotFamilyOfHilbertFamilyOver_baseChange`. -/
def hilbertPresheafIsoQuotSitePresheaf :
    hilbertPresheaf f ≅ (structureSheafQuotSituation f hf).quotSitePresheaf :=
  NatIso.ofComponents (fun Tsch => Equiv.toIso (quotFamilyOverEquiv f hf Tsch.unop))
    fun g => ConcreteCategory.hom_ext _ _ fun x =>
      quotFamilyOfHilbertFamilyOver_baseChange f hf g.unop x

/-- That isomorphism does not change the morphism to `Y` a section lies over, so it is an
isomorphism of presheaves *over* `Y`. -/
theorem hilbertPresheafIsoQuotSitePresheaf_hom_comp_quotSitePresheafToBase :
    (hilbertPresheafIsoQuotSitePresheaf f hf).hom ≫
        (structureSheafQuotSituation f hf).quotSitePresheafToBase =
      hilbertPresheafToBase f := by
  refine NatTrans.ext (funext fun Tsch => ?_)
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg ULift.up (congrArg yonedaEquiv
    (quotFamilyOfHilbertFamilyOver_toBase_hom f hf x))

/-- In Situation 0CZY we have `Hilb_{X/B} = Quot_{𝒪_X/X/B}`: the Hilbert functor of `f` and the
Quot functor of its structure sheaf are isomorphic presheaves on the schemes of the big fppf site,
by an isomorphism over `Y`. -/
@[stacks 0D00]
theorem exists_hilbertPresheafIso_quotSitePresheaf :
    ∃ e : hilbertPresheaf f ≅ (structureSheafQuotSituation f hf).quotSitePresheaf,
      e.hom ≫ (structureSheafQuotSituation f hf).quotSitePresheafToBase =
        hilbertPresheafToBase f :=
  ⟨hilbertPresheafIsoQuotSitePresheaf f hf,
    hilbertPresheafIsoQuotSitePresheaf_hom_comp_quotSitePresheafToBase f hf⟩

end AlgebraicGeometry.Space

end
