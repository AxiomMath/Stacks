module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateCechExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcCoveringSiteSheaves

/-!
# [Stacks, Tag 06VL] as a single statement

The library proves [Stacks, Tag 06VL] in pieces: the degree-zero exactness of the extended Čech
complex of a flat surjection of affines, its exactness in positive degrees, the fpqc sheaf
condition, and the fppf sheaf condition. This module states the tag as **one** theorem, whose
conclusion is the conjunction of all of it.

## Main results

* `Stacks.Adequate.cechExact_and_isSheaf_of_isAdequate` — **[Stacks, Tag 06VL]**, whole. For an
  adequate `𝒪`-module `F` on a chosen big `τ`-site over `S`: the extended Čech complex of every
  flat surjective morphism between affine objects of the site is exact, `F` satisfies the sheaf
  condition for the fpqc covering families of the site, and `F` is a sheaf of `𝒪`-modules for
  the fppf covering families of the site.

## Implementation notes

**The extended complex, and why exactness is two clauses.** The source's displayed complex is

`0 → F(Spec A) → F(Spec B) → F(Spec (B ⊗_A B)) → ⋯`,

the Čech complex of the one-member family `{Spec B → Spec A}` augmented by `F(Spec A)` on the
left. Its exactness at the two left-hand spots — injectivity of `F(Spec A) → F(Spec B)` and
`ker = im` at `F(Spec B)` — is precisely the uniqueness and the existence of an amalgamation for
the one-member presieve `{Spec B → Spec A}`, i.e. the sheaf condition
`CategoryTheory.Presieve.IsSheafFor` for that presieve; that is the first clause. Its exactness
at the remaining spots is the vanishing of the Čech cohomology of the family in every positive
degree; that is the second clause. Together the two clauses say exactly that the displayed
complex is exact at every one of its spots, which is the source's assertion.

The two clauses are stated in the two spellings in which they are proved, and nothing is
restated: the first is `Stacks.Adequate.isSheafFor_singleton_of_isAdequate` and the second is
`Stacks.Adequate.affineCechExactness_of_isAdequate`, which is the predicate
`Stacks.Adequate.BigSite.AffineCechExactness` written out.

**The fppf conclusion, in both readings.** The source's `F` is given as an `𝒪`-module on
`(Sch/S)_τ`, and the second "in particular" asserts of *that* `𝒪`-module that it is a sheaf of
`𝒪`-modules on `(Sch/S)_fppf`. No new datum is produced: the presheaf of `𝒪`-modules is
unchanged and what is asserted about `F` is the sheaf axiom for a finer topology, which is the
field `CategoryTheory.SheafOfModules.isSheaf` read at `(fppfPrecoverageOn B).toGrothendieck`.
That is the third clause below, and it is the whole of what Tag 06VL asserts about `F`.

Reading "is a sheaf of `𝒪`-modules on `(Sch/S)_fppf`" as a statement about the *object* rather
than about `F`'s sheaf axiom needs one thing more, which is not about `F` at all: the category
of `𝒪`-modules on `(Sch/S)_fppf` is well formed only once `𝒪` itself is known to be a sheaf of
rings for that topology, [Stacks, Tag 03OJ]. That is supplied here by
`Stacks.Adequate.isSheaf_structurePresheaf_fppf`, which carries no hypothesis on any module, and
packaged as `Stacks.Adequate.BigSite.fppfStructureSheaf`; the fourth clause below then exhibits
a term of `CategoryTheory.SheafOfModules` over it whose underlying presheaf of `𝒪`-modules is
`F.val` on the nose. Clauses three and four are equivalent given Tag 03OJ — the fourth is the
third repackaged — and both are stated so that neither reading of the source's phrase is left
to interpretation.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

/-! ### The structure sheaf of rings at the fppf topology of the site -/

/-- The structure presheaf of a chosen big site is a sheaf for the fppf topology **of the site**:
an fppf covering family of the site is an fpqc covering family of schemes, and global functions
satisfy fpqc descent. This is [Stacks, Tag 03OJ] read on a chosen big site; it is a statement
about `𝒪` and carries no hypothesis on any module. -/
public theorem isSheaf_structurePresheaf_fppf {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck
      (Stacks.Sites.structurePresheaf S B.toOver) := by
  let : CategoryTheory.Limits.PreservesFiniteLimits B.toOver :=
    B.preservesFiniteLimits_toOver
  exact Stacks.Sites.isSheaf_structurePresheaf_of_mem_fpqcPrecoverage
    (fppfPrecoverageOn B) B.toOver
    (fun _ _ hR => Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hR)

/-- The structure sheaf of rings `𝒪` of a chosen big site, read at the **fppf** topology of the
site rather than at the site's own topology. This is `Stacks.Adequate.BigSite.structureSheaf`
with its sheaf condition replaced by `Stacks.Adequate.isSheaf_structurePresheaf_fppf`, and it is
what makes the category of `𝒪`-modules on `(Sch/S)_fppf` well formed. -/
public noncomputable abbrev BigSite.fppfStructureSheaf {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) :
    Sheaf (fppfPrecoverageOn B).toGrothendieck RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S B.toOver, isSheaf_structurePresheaf_fppf B⟩

/-! ### The tag -/

/-- **[Stacks, Tag 06VL], the whole statement.**

Let `F` be an adequate `𝒪`-module on a chosen big `τ`-site over `S`. Then:

1. for every surjective flat morphism `f : Spec B ⟶ Spec A` between affine objects of the site,
   the extended Čech complex
   `0 → F(Spec A) → F(Spec B) → F(Spec (B ⊗_A B)) → ⋯`
   is exact — at its two left-hand spots, which is the sheaf condition for the one-member
   presieve `{f}`, and at every remaining spot, which is the vanishing of the Čech cohomology of
   `{f}` in every positive degree;
2. `F` satisfies the sheaf condition for the fpqc covering families of the site; and
3. `F` is a sheaf of `𝒪`-modules for the fppf covering families of the site, that is, its
   underlying presheaf of abelian groups satisfies the fppf sheaf condition; and
4. equivalently, read as a statement about the object rather than about the sheaf axiom, there
   is a sheaf of `𝒪`-modules on `(Sch/S)_fppf` — a term of `CategoryTheory.SheafOfModules` over
   `Stacks.Adequate.BigSite.fppfStructureSheaf`, the structure sheaf of rings of the site read
   at the fppf topology by [Stacks, Tag 03OJ] — whose underlying presheaf of `𝒪`-modules is
   that of `F`.

Clause (1) is the body of the tag and clauses (2) and (3) are its two "in particular"s, clause
(4) being clause (3) repackaged. -/
@[stacks 06VL "the whole statement: for an adequate `𝒪`-module on a chosen big `τ`-site over `S`,
the extended Čech complex `0 → F(Spec A) → F(Spec B) → F(Spec (B ⊗_A B)) → ⋯` of every surjective
flat morphism of affines of the site is exact at every spot -- at the two left-hand spots as the
sheaf condition for the one-member presieve, at the rest as the vanishing of the Čech cohomology
in positive degrees -- and the two `in particular` conclusions, the fpqc sheaf condition and
being a sheaf of `𝒪`-modules for the fppf coverings, the latter both as the sheaf axiom for the
fppf topology and as a term of the category of `𝒪`-modules on `(Sch/S)_fppf`."]
public theorem cechExact_and_isSheaf_of_isAdequate
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F) :
    letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
    (∀ (X Y : B.category) (f : Y ⟶ X), X ∈ B.affineObjects → Y ∈ B.affineObjects →
        Flat (B.toOver.map f).left → Surjective (B.toOver.map f).left →
          Presieve.IsSheafFor (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m})
              (Presieve.singleton f) ∧
            ∀ n : ℕ, 0 < n →
              IsZero (Stacks.CechSite.cechCohomology (PreZeroHypercover.singleton.{0} f)
                F.val.presheaf n)) ∧
      Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck F.val.presheaf ∧
      Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck F.val.presheaf ∧
      ∃ G : SheafOfModules.{max u m} B.fppfStructureSheaf, G.val = F.val := by
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  have hfppf := isSheaf_fppf_module_of_isAdequate.{u, m} B F hF
  refine ⟨fun X Y f hX hY hflat hsurj => ⟨?_, ?_⟩,
    isSheaf_fpqc_of_isAdequate.{u, m} B F hF, hfppf, ⟨F.val, hfppf⟩, rfl⟩
  · let := hflat
    let := hsurj
    exact isSheafFor_singleton_of_isAdequate B F hF f hY hX
  · exact affineCechExactness_of_isAdequate B F hF f hX hY hflat hsurj

end Stacks.Adequate

end
