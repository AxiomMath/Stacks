module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateAffineSingletonSheaf
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteFpqcFromAffineSingletons
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# An adequate module is an fpqc sheaf, and a sheaf of `𝒪`-modules for the fppf coverings

[Stacks, Tag 06VL] proves that the extended Čech complex of a flat surjection of affines of the
site is exact, and then concludes, in a paragraph for which the source itself says "details
omitted", that an adequate `𝒪`-module "satisfies the sheaf condition for fpqc coverings, and is
a sheaf of `𝒪`-modules on `(Sch/S)_fppf`". **This module is that conclusion.**

## Main results

* `Stacks.Adequate.isAffineSingletonSheaf_of_isAdequate` — an adequate sheaf of modules descends
  along every flat surjective morphism between affine objects of the site, in the shape
  `Stacks.Adequate.IsAffineSingletonSheaf` that the fpqc criterion consumes.
* `Stacks.Adequate.isSheaf_fpqc_of_isAdequate` — **[Stacks, Tag 06VL]**, the first conclusion of
  the "in particular": an adequate sheaf of modules satisfies the sheaf condition for the fpqc
  covering families of the site.
* `Stacks.Adequate.isSheaf_fppf_module_of_isAdequate` — **[Stacks, Tag 06VL]**, the second
  conclusion: the same for the fppf covering families, which is the assertion that an adequate
  `𝒪`-module is a sheaf of `𝒪`-modules for the fppf topology of the site.

## Implementation notes

**Only the degree-zero part of the Čech exactness is consumed.** The source deduces the two
sheaf conclusions from the exactness of the whole extended Čech complex, but what the deduction
uses is exactness at the left end alone — the sheaf condition for the one-member covering
`{Spec B → Spec A}` — together with the sheaf condition `F` carries for the topology of the
site. The first is `Stacks.Adequate.isSheafFor_singleton_of_isAdequate` and the second is
`Stacks.Adequate.isSheaf_forget_presheaf`, the latter with no hypothesis at all, being the sheaf
field of `F`. Nothing below depends on the vanishing of the higher Čech cohomology, which is a
separate part of the tag and is not asserted here.

The step from those two inputs to the fpqc sheaf condition is
`Stacks.Adequate.isSheaf_fpqc_of_affineSingletons`, the big-site form of [Stacks, Tag 03O1] with
no extension hypothesis. The step from fpqc to fppf is
`Stacks.Adequate.isSheaf_fppf_of_isSheaf_fpqc`, an fppf covering family of the site being an
fpqc covering family of the site.

**Types versus modules.** The criterion of [Stacks, Tag 03O1] is a statement about presheaves of
types, and the degree-zero descent is proved in that form, so the type-valued conclusions
`Stacks.Adequate.isSheaf_fpqc_forget_of_isAdequate` and
`Stacks.Adequate.isSheaf_fppf_forget_of_isAdequate` come first. The source's conclusion is about
the `𝒪`-module `F`, which is more than its presheaf of types, and
`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget` upgrades it: a presheaf of abelian groups
whose presheaf of types is a sheaf is a sheaf, the amalgamation being computed element by
element and additive because the restriction maps are jointly injective on a covering sieve.
Mathlib's `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` would do the same but forces the
module universe to agree with the universe of the site; the form used here leaves `m` free.
Since `F.val` is already a presheaf of `B.structureSheaf`-modules, the sheaf condition for its
underlying presheaf of abelian groups is exactly the assertion that `F.val` is a sheaf of
`𝒪`-modules for that topology: `CategoryTheory.SheafOfModules` over a sheaf of rings `R` for a
topology `J` is a `CategoryTheory.PresheafOfModules R.obj` together with a field
`isSheaf : Presheaf.IsSheaf J val.presheaf`, and
`Stacks.Adequate.isSheaf_fppf_module_of_isAdequate` is that field at the fppf topology of the
site. What is *not* done here is bundling the pair into a term of
`CategoryTheory.SheafOfModules`: that needs `𝒪` itself promoted to a sheaf of rings for the
fppf topology of the site, available as
`Stacks.Sites.isSheaf_structurePresheaf_of_mem_fpqcPrecoverage` but a statement about `𝒪`
([Stacks, Tag 03OJ]) rather than about `F`, and no part of [Stacks, Tag 06VL]. The whole content
of the tag's second conclusion is the sheaf condition proved below.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The descent condition of an adequate module -/

/-- **An adequate sheaf of modules descends along a flat surjection of affines of the site.**

This is `Stacks.Adequate.isSheafFor_singleton_of_isAdequate` packaged as
`Stacks.Adequate.IsAffineSingletonSheaf`, the second condition of the big-site form of
[Stacks, Tag 03O1]. It is the degree-zero part of the exactness of the extended Čech complex of
[Stacks, Tag 06VL]: exactness of `0 → F(Spec A) → F(Spec B) → F(Spec (B ⊗_A B))` at the first
two spots is precisely the sheaf condition for the one-member covering `{Spec B → Spec A}`. -/
public theorem isAffineSingletonSheaf_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    IsAffineSingletonSheaf B (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m}) := by
  intro X T g hX hT hflat hsurj
  let := hflat
  let := hsurj
  exact isSheafFor_singleton_of_isAdequate.{u, m} B F hF g hX hT

/-! ### The fpqc sheaf condition -/

/-- The presheaf of types underlying an adequate sheaf of modules satisfies the sheaf condition
for the fpqc covering families of the site. This is the form in which the criterion of
[Stacks, Tag 03O1] delivers the conclusion; see
`Stacks.Adequate.isSheaf_fpqc_of_isAdequate` for the `𝒪`-module form the source asserts. -/
public theorem isSheaf_fpqc_forget_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck
      (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m}) :=
  isSheaf_fpqc_of_affineSingletons B _
    ((isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_forget_presheaf B F))
    (isAffineSingletonSheaf_of_isAdequate.{u, m} B F hF)

/-- **[Stacks, Tag 06VL], the first conclusion of the "in particular".** An adequate sheaf of
modules on a chosen big `τ`-site over `S` satisfies the sheaf condition for the fpqc covering
families of the site.

The source states this as "in particular `𝓕` satisfies the sheaf condition for fpqc coverings
(made out of objects of `(Sch/S)_τ`)", and proves it by "arguing as in the proofs of Descent,
Lemma 023S and Descent, Proposition 023T", with "details omitted". The two inputs it names are
the sheaf condition for `τ`-coverings — which `F` carries by definition,
`Stacks.Adequate.isSheaf_forget_presheaf` — and descent along a faithfully flat covering of an
affine by an affine, which is `Stacks.Adequate.isAffineSingletonSheaf_of_isAdequate`. The
refinement of an arbitrary fpqc covering family of the site by those two is
`Stacks.Adequate.isSheaf_fpqc_of_affineSingletons`. -/
public theorem isSheaf_fpqc_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck F.val.presheaf :=
  Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqc_forget_of_isAdequate.{u, m} B F hF))

/-! ### The fppf sheaf condition -/

/-- The presheaf of types underlying an adequate sheaf of modules satisfies the sheaf condition
for the fppf covering families of the site, an fppf covering family of the site being an fpqc
covering family of the site. -/
public theorem isSheaf_fppf_forget_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck
      (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m}) :=
  isSheaf_fppf_of_isSheaf_fpqc B _ (isSheaf_fpqc_forget_of_isAdequate.{u, m} B F hF)

/-- **[Stacks, Tag 06VL], the second conclusion of the "in particular".** An adequate
`𝒪`-module is a sheaf of `𝒪`-modules for the fppf covering families of the site: the presheaf of
abelian groups underlying `F`, and not merely its presheaf of types, satisfies the fppf sheaf
condition. That is exactly the condition `CategoryTheory.SheafOfModules.isSheaf` asks of a
presheaf of modules, so it says that `F.val` is a sheaf of modules for the fppf topology of the
site and not only for `B.topology`. -/
public theorem isSheaf_fppf_module_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck F.val.presheaf :=
  isSheaf_fppf_of_isSheaf_fpqc B _ (isSheaf_fpqc_of_isAdequate.{u, m} B F hF)

end Stacks.Adequate

end
