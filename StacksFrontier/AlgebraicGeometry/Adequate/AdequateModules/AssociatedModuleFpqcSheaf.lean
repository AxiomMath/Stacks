module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernel
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CechExactAffineSections
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement

/-!
# The fpqc sheaf condition for an associated module on a chosen big site

The final paragraph of [Stacks, Tag 06VL] asserts that an adequate module on a chosen big site
satisfies the sheaf condition for fpqc coverings, and says "details omitted".
`Stacks.Adequate.isSheaf_fpqc_of_exists_extension` reduces that assertion to the existence of a
presheaf on *all* schemes over `S` whose restriction to the site is the given presheaf and which
satisfies the two conditions of [Stacks, Tag 03O1]. This module observes that for an associated
module the extension is not merely available but *definitional*, and that it carries the fpqc
sheaf condition outright, so that neither the extension hypothesis nor [Stacks, Tag 03O1] is
needed.

## The observation

`Stacks.Adequate.BigSite.associatedModule`, the module `𝓖ᵃ` of [Stacks, Tag 03DU] (3) on a
chosen big site, has for underlying presheaf `Stacks.Sites.associatedPresheaf S 𝓖 B.toOver`,
which is by definition `B.toOver.op ⋙ AlgebraicGeometry.quasiCoherentPresheafFunctor S 𝓖` — the
presheaf of [Stacks, Tag 03DS] on all of `Sch/S`, restricted along the canonical functor of the
site. That presheaf on `Sch/S` is an fpqc sheaf by [Stacks, Tag 03DT],
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and restriction along the canonical
functor carries fpqc sheaves to fpqc sheaves of the site by
`Stacks.Adequate.isSheaf_fpqc_restriction`. So the fpqc sheaf condition for `𝓖ᵃ` is one
composition of two unconditional theorems.

## Main results

* `Stacks.Adequate.isSheaf_fpqc_associatedPresheaf`, and
  `Stacks.Adequate.isSheaf_fppf_associatedPresheaf`: both sheaf conclusions of the final
  paragraph of [Stacks, Tag 06VL], for an associated module, with no hypothesis.
* `Stacks.Adequate.isSheaf_fpqc_forget_associatedPresheaf`: the same for the underlying
  presheaf of types, which is the form the Čech condition consumes.
* `Stacks.Adequate.isAffineSingletonSheaf_associatedPresheaf`: **the hypothesis `hF` of
  `Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf`, discharged for
  an associated module.** This is the hypothesis that the module documentation of
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/CechExactAffineSections.lean` records
  as owed.
* `Stacks.Adequate.cechExactOn_affineSectionFunctor_associatedModule`: consequently the Čech
  condition of [Stacks, Tag 06VH] for the affine-section functor of `𝓖ᵃ`, with only the
  flatness and surjectivity of the base-changed morphisms remaining.

## Implementation notes

Nothing here passes through [Stacks, Tag 03O1] or through
`Stacks.Adequate.isSheaf_fpqc_of_exists_extension`. That criterion exists for a presheaf of the
site given *abstractly*; the point of this module is that an associated module is not given
abstractly — it is given as a restriction, and the thing being restricted already satisfies the
conclusion. In particular the obstruction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/BigSiteFpqcSheafCriterion.lean` — that
descent along `Spec T ⟶ Spec R` for rings above the cutoff has no route, a faithfully flat
morphism of affines not being of finite presentation — does not arise: the descent is supplied
for the extension directly by [Stacks, Tag 03DT], which is proved by quasi-coherent descent and
not by a limit argument over finitely presented stages.

**What this does not give.** It does not give the final paragraph of [Stacks, Tag 06VL] under
the hypothesis `Stacks.Adequate.IsAdequate` over an arbitrary base. Adequacy of a sheaf of
modules is a condition on its affine-section *functors* — each is a kernel of base changes of a
map of modules over the coordinate ring of an affine of a covering of `S` — and supplies no
presentation of the sheaf itself, hence no extension of its presheaf to `Sch/S`. What carries
adequacy to a presentation of the sheaf is the converse of [Stacks, Tag 06VK], and that is now
available:
`Stacks.Adequate.isAssociatedKernel_of_isAdequate` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedKernelConverse.lean` presents
an adequate module on a chosen big site over an *affine* base as a kernel of associated
modules, so over an affine base the hypothesis of the results below may be replaced by
`Stacks.Adequate.IsAdequate`. Over a general base what the converse gives is
`Stacks.Adequate.hasAssociatedKernelOnEveryAffine_of_isAdequate`, a presentation of each
restriction to an affine of the site and not of the sheaf itself, so the class for which the
final paragraph is available there remains the class of modules presented globally as in
[Stacks, Tag 06VK] (5). The implication
`Stacks.Adequate.isAdequate_of_isAssociatedKernel` runs the other way.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- **The fpqc sheaf condition of the final paragraph of [Stacks, Tag 06VL], for an associated
module.** The presheaf of sections of the pullbacks of a quasi-coherent `𝒪_S`-module to the
schemes of a chosen big site satisfies the sheaf condition for every fpqc covering family of the
site.

No hypothesis, and no appeal to [Stacks, Tag 03O1]: the presheaf *is* the restriction along
`Stacks.Adequate.BigSite.toOver` of the presheaf of [Stacks, Tag 03DS] on all schemes over `S`,
that presheaf is an fpqc sheaf by [Stacks, Tag 03DT], and
`Stacks.Adequate.isSheaf_fpqc_restriction` restricts fpqc sheaves to fpqc sheaves of the
site. -/
public theorem isSheaf_fpqc_associatedPresheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck
      (Stacks.Sites.associatedPresheaf S G B.toOver) :=
  isSheaf_fpqc_restriction B (quasiCoherentPresheafFunctor S G)
    (quasiCoherentPresheaf_isSheaf_fpqc' S G)

/-- **The fppf sheaf conclusion of the final paragraph of [Stacks, Tag 06VL], for an associated
module.** The source states the two conclusions side by side; this is the second, obtained from
the first by `Stacks.Adequate.isSheaf_fppf_of_isSheaf_fpqc`. -/
public theorem isSheaf_fppf_associatedPresheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck
      (Stacks.Sites.associatedPresheaf S G B.toOver) :=
  isSheaf_fppf_of_isSheaf_fpqc B _ (isSheaf_fpqc_associatedPresheaf B G)

/-- The presheaf of types underlying an associated module satisfies the fpqc sheaf condition of
the site. This is the form `Stacks.Adequate.IsAffineSingletonSheaf` and the Čech condition of
[Stacks, Tag 06VH] are stated at. -/
public theorem isSheaf_fpqc_forget_associatedPresheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    Presieve.IsSheaf (fpqcPrecoverageOn B).toGrothendieck
      (Stacks.Sites.associatedPresheaf S G B.toOver ⋙
        CategoryTheory.forget AddCommGrpCat.{u}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ (isSheaf_fpqc_associatedPresheaf B G)

/-- **The sheaf hypothesis of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf`, discharged for an
associated module.** Descent along a flat surjective morphism between affines of the site holds
for the presheaf of an associated module, because such a morphism is an fpqc covering of the
site (`Stacks.Adequate.sieve_generate_singleton_mem_fpqc`) and the presheaf is an fpqc sheaf of
the site by `Stacks.Adequate.isSheaf_fpqc_associatedPresheaf`. -/
public theorem isAffineSingletonSheaf_associatedPresheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    IsAffineSingletonSheaf B
      (Stacks.Sites.associatedPresheaf S G B.toOver ⋙
        CategoryTheory.forget AddCommGrpCat.{u}) :=
  isAffineSingletonSheaf_of_isSheaf_fpqc B _ (isSheaf_fpqc_forget_associatedPresheaf B G)

/-! ### A kernel of associated modules -/

section Kernel

variable (B : BigSite τ S)

/-- The underlying abelian presheaf of a sheaf of modules on a chosen big site, as a functor.
It preserves finite limits, being the forgetful functor to presheaves of modules followed by
the forgetful functor to abelian presheaves. -/
public noncomputable abbrev modulePresheafFunctor :
    SheafOfModules.{u} B.structureSheaf ⥤ (B.categoryᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  SheafOfModules.forget B.structureSheaf ⋙
    PresheafOfModules.toPresheaf.{u} B.structureSheaf.obj

/-- **The fpqc sheaf condition for a kernel of associated modules.** A sheaf of modules on a
chosen big site which is the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent
`𝒪_S`-modules satisfies the sheaf condition for every fpqc covering family of the site.

The fpqc sheaf condition is a limit condition, and `Presheaf.IsSheaf` is closed under limits of
every shape, so it suffices that the underlying abelian presheaf of the kernel is the kernel of
the underlying abelian presheaves — which holds because
`CategoryTheory.SheafOfModules.forget` and `CategoryTheory.PresheafOfModules.toPresheaf`
preserve finite limits — and that the two presheaves being compared are fpqc sheaves of the
site, which is `Stacks.Adequate.isSheaf_fpqc_associatedPresheaf`.

No extension of the *map* `𝓖ᵃ ⟶ 𝓗ᵃ` to the schemes over `S` is needed, and none is available:
the map is a map of sheaves on the site, and only its source and target are restrictions. The
argument runs entirely on the site. -/
public theorem isSheaf_fpqc_of_isKernel (φ : AssociatedModuleMap B)
    (F : SheafOfModules.{u} B.structureSheaf) (e : F ≅ kernel φ.hom) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck F.val.presheaf := by
  have := φ.source_isQuasicoherent
  have := φ.target_isQuasicoherent
  have hcone : Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck
      ((modulePresheafFunctor B).obj (kernel φ.hom)) := by
    refine ObjectProperty.prop_of_isLimit
      (P := Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck)
      (isLimitOfPreserves (modulePresheafFunctor B) (kernelIsKernel φ.hom)) ?_
    rintro (_ | _)
    · exact isSheaf_fpqc_associatedPresheaf B φ.source
    · exact isSheaf_fpqc_associatedPresheaf B φ.target
  exact (Presheaf.isSheaf_of_iso_iff ((modulePresheafFunctor B).mapIso e)).2 hcone

/-- The presheaf of types underlying a kernel of associated modules satisfies the fpqc sheaf
condition of the site. -/
public theorem isSheaf_fpqc_forget_of_isKernel (φ : AssociatedModuleMap B)
    (F : SheafOfModules.{u} B.structureSheaf) (e : F ≅ kernel φ.hom) :
    Presieve.IsSheaf (fpqcPrecoverageOn B).toGrothendieck
      (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ (isSheaf_fpqc_of_isKernel B φ F e)

/-- **The final paragraph of [Stacks, Tag 06VL] for a module presented as in [Stacks, Tag 06VK]
(5).** A sheaf of modules on a chosen big site admitting a presentation as the kernel of a map
of associated modules of quasi-coherent `𝒪_S`-modules satisfies the sheaf condition for the fpqc
covering families of the site, and hence for the fppf ones.

`Stacks.Adequate.isAdequate_of_isAssociatedKernel` shows that such a module is adequate, so this
is the source's conclusion for every module the library presently exhibits as adequate. It is
*not* the conclusion under the hypothesis `Stacks.Adequate.IsAdequate` itself; see the module
documentation. -/
public theorem isSheaf_fpqc_of_isAssociatedKernel (F : SheafOfModules.{u} B.structureSheaf)
    (h : IsAssociatedKernel B F) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck F.val.presheaf :=
  h.elim fun p => isSheaf_fpqc_of_isKernel B p.toAssociatedModuleMap F p.iso

/-- The fppf half of `Stacks.Adequate.isSheaf_fpqc_of_isAssociatedKernel`. The source states the
two conclusions side by side. -/
public theorem isSheaf_fppf_of_isAssociatedKernel (F : SheafOfModules.{u} B.structureSheaf)
    (h : IsAssociatedKernel B F) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck F.val.presheaf :=
  isSheaf_fppf_of_isSheaf_fpqc B _ (isSheaf_fpqc_of_isAssociatedKernel B F h)

/-- **The sheaf hypothesis of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf`, discharged for a
module presented as a kernel of associated modules.** -/
public theorem isAffineSingletonSheaf_of_isAssociatedKernel
    (F : SheafOfModules.{u} B.structureSheaf) (h : IsAssociatedKernel B F) :
    IsAffineSingletonSheaf B
      (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  h.elim fun p =>
    isAffineSingletonSheaf_of_isSheaf_fpqc B _
      (isSheaf_fpqc_forget_of_isKernel B p.toAssociatedModuleMap F p.iso)

/-- **The Čech condition of [Stacks, Tag 06VH] for the affine-section functor of a module
presented as a kernel of associated modules.** The sheaf hypothesis of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf` is discharged by
`Stacks.Adequate.isAffineSingletonSheaf_of_isAssociatedKernel`; what remains of that theorem's
input is only the flatness and surjectivity of the base-changed morphisms
`Spec (C ⊗_A A') → Spec C`, which hold because a base change of a faithfully flat ring map is
faithfully flat but are read off the coproduct hypothesis and are still carried here. -/
public theorem cechExactOn_affineSectionFunctor_of_isAssociatedKernel
    (F : SheafOfModules.{u} B.structureSheaf) (h : IsAssociatedKernel B F)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (A' : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (hflat : ∀ {C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
      (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁),
      IsColimit (BinaryCofan.mk
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA)) →
      Flat ((B.toOver.map ((affineSpecOver B A f).map iB.op)).left))
    (hsurj : ∀ {C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
      (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁),
      IsColimit (BinaryCofan.mk
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA)) →
      Surjective ((B.toOver.map ((affineSpecOver B A f).map iB.op)).left)) :
    AdequateFunctor.CechExactOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) A' :=
  cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf B F A f A'
    (isAffineSingletonSheaf_of_isAssociatedKernel B F h) hflat hsurj

end Kernel

end Stacks.Adequate

end
