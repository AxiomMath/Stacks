module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent

/-!
# The ideal sheaf of the scheme-theoretic image of a quasi-compact morphism (Stacks 082Z)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Two sheaves of ideals of `𝒪_Y` are attached to `f`: the kernel
`AlgebraicGeometry.Space.kernelIdealSheaf` of the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of
Stacks 03G8, and the defining ideal sheaf `AlgebraicGeometry.Space.definingIdealSheaf` of
Stacks 03MB of the scheme-theoretic image `AlgebraicGeometry.Space.schemeTheoreticImage` of
Stacks 082X.  Stacks 082Z asserts that for a *quasi-compact* `f` the two agree, so that the
scheme-theoretic image is cut out by the kernel of `f♯`.

One inclusion needs no hypothesis.  The morphism `f` factors through its scheme-theoretic
image `Z`, and a function on an étale chart `U` of `Y` which lies in the defining ideal of `Z`
is therefore killed by pullback along every chart of `X` above `X ×_Y U`: each such chart maps
to `U` compatibly with `f`, so it is a point of `Y` whose image lies in `Z`, and the vanishing
is `AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`.  Since the kernel of `f♯` over
`U` is exactly the set of functions killed by all those pullbacks
(`AlgebraicGeometry.Space.mem_ker_structureSharp_iff`), the defining ideal sheaf of `Z` is
contained in the kernel ideal sheaf.  Nothing in this argument is special to the
scheme-theoretic image: it holds for every closed subspace of `Y` through which `f` factors.

The reverse inclusion is where quasi-compactness enters, through
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_kernelIdealSheaf`: the kernel of `f♯` is
then quasi-coherent and is the defining ideal sheaf of a closed subspace `Z'` of `Y`.  That `f`
factors through `Z'` is the criterion
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le` of Stacks 03MB,
whose hypothesis — that the ideal be killed by pullback to any scheme over an affine chart of
`Y` which lifts to `X` — is `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift`, valid for
an arbitrary morphism.  Minimality of the scheme-theoretic image gives `Z ⊆ Z'`, and the
inclusion-reversal `AlgebraicGeometry.Space.definingIdealSheaf_antitone` turns that into the
missing inclusion of ideal sheaves.

## Main results

* `AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticImage_le_kernelIdealSheaf`: the
  defining ideal sheaf of the scheme-theoretic image of `f` is contained in the kernel of
  `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, for an arbitrary morphism `f` of algebraic spaces.
* `AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf` is
  **Stacks 082Z**: for a quasi-compact `f` the scheme-theoretic image of `f` is the closed
  subspace of `Y` defined by the kernel of `f♯ : 𝒪_Y ⟶ f_*𝒪_X`.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- The defining ideal sheaf of a closed subspace through which a morphism `f : X ⟶ Y` factors
is contained in the kernel of the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X`.

The kernel of `f♯` over an étale chart `U` of `Y` consists of the functions whose pullback to
every étale scheme chart of `X` above `X ×_Y U` vanishes, and each such chart is a point of `X`
whose image in `Y` factors through `U`, so the vanishing is Stacks 03MB. -/
theorem definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq (f : X ⟶ Y)
    (Z : ClosedSubspaces B S hS Y.1)
    (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : g ≫ ObjectProperty.homMk Z.1.ι = f) :
    definingIdealSheaf B S hS Y Z ≤ kernelIdealSheaf B S hS f := by
  intro U s hs
  refine (mem_ker_structureSharp_iff B S hS f U.unop s).2 fun j => ?_
  exact definingIdealAt_le_ker_of_comp_eq B S hS Y X Z f g hg U.unop
    (chartBaseChangeMap B S hS f U.unop j) j.right.unop.1.hom
    (chartDiagramOfIndex B S hS f U.unop j).comm.symm hs

/-- **One half of Stacks 082Z, with no hypothesis on the morphism.** The defining ideal sheaf
of the scheme-theoretic image of `f : X ⟶ Y` is contained in the kernel of the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`, because `f` factors through its scheme-theoretic image. -/
theorem definingIdealSheaf_schemeTheoreticImage_le_kernelIdealSheaf (f : X ⟶ Y) :
    definingIdealSheaf B S hS Y (schemeTheoreticImage B S hS f.hom Y.2) ≤
      kernelIdealSheaf B S hS f :=
  definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq B S hS f _
    (ObjectProperty.homMk (toSchemeTheoreticImage B S hS f.hom))
    (ObjectProperty.hom_ext _ (toSchemeTheoreticImage_ι B S hS f.hom))

/-- **The other half of Stacks 082Z.** For a quasi-compact `f : X ⟶ Y` the kernel of the
structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is contained in the defining ideal sheaf of the
scheme-theoretic image of `f`.

Quasi-compactness makes the kernel the defining ideal sheaf of a closed subspace `Z'` of `Y`;
the morphism `f` factors through `Z'` by the affine-chart criterion of Stacks 03MB, so the
scheme-theoretic image is contained in `Z'` and the defining ideal sheaves compare the other
way. -/
theorem kernelIdealSheaf_le_definingIdealSheaf_schemeTheoreticImage (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) :
    kernelIdealSheaf B S hS f ≤
      definingIdealSheaf B S hS Y (schemeTheoreticImage B S hS f.hom Y.2) := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_kernelIdealSheaf B S hS f hf
  obtain ⟨g, hg⟩ :=
    (exists_comp_eq_iff_forall_isAffine_definingIdealAt_le B S hS Y X Z f).2
      (by
        intro U _ a k y hy
        rw [← definingIdealSheaf_obj, hZ]
        exact kernelIdealSheaf_le_ker_of_lift B S hS f U k y hy)
  have hgι : g.hom ≫ Z.1.ι = f.hom := congrArg InducedCategory.Hom.hom hg
  have hrange : Subfunctor.range f.hom ≤ Z.1 := by
    simpa only [hgι, Subfunctor.range_ι] using Subfunctor.range_comp_le g.hom Z.1.ι
  rw [← hZ]
  exact definingIdealSheaf_antitone B S hS Y _ Z
    (schemeTheoreticImageSubfunctor_le B S hS f.hom Z.2 hrange)

/-- **Stacks 082Z.** For a quasi-compact morphism `f : X ⟶ Y` of algebraic spaces over `S` the
scheme-theoretic image of `f` is the closed subspace of `Y` cut out by the kernel of the
structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X`: its defining ideal sheaf of Stacks 03MB is that kernel. -/
@[stacks 082Z "part (2): the image is the closed subspace cut out by that ideal"]
theorem definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) :
    definingIdealSheaf B S hS Y (schemeTheoreticImage B S hS f.hom Y.2) =
      kernelIdealSheaf B S hS f :=
  le_antisymm (definingIdealSheaf_schemeTheoreticImage_le_kernelIdealSheaf B S hS f)
    (kernelIdealSheaf_le_definingIdealSheaf_schemeTheoreticImage B S hS f hf)

end AlgebraicGeometry.Space

end
