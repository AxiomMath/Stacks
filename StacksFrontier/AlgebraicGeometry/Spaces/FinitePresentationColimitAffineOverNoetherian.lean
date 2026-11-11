module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCokernelPresentation

/-!
# Quasi-coherent modules on a space affine over a Noetherian space

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` with `Y` Noetherian.
**Stacks 07UW** asserts that every quasi-coherent `𝒪_X`-module is a filtered colimit of
`𝒪_X`-modules of finite presentation.

The source's proof has two halves.  The first is geometric: write `f_*F = colim H_i` with the
`H_i` coherent — hence of finite presentation — using Stacks 07UV and Stacks 07UB on the
Noetherian space `Y`, pull the presentation back along `f^*`, and observe that the counit
`f^*f_*F ⟶ F` is surjective because `f` is affine.  This exhibits every quasi-coherent
`𝒪_X`-module as a *quotient* of a filtered colimit of modules of finite presentation, and
therefore, applied once to `F` and once to the kernel of the quotient map, exhibits `F` as the
cokernel of a map `colim_j G_j ⟶ colim_i H_i` between two such colimits.  The second half is
formal: the cokernel is the filtered colimit of the cokernels of the individual representing maps
`α : G_j ⟶ H_i`, indexed by the triples `(i, j, α)`.

The second half is `StacksFrontier.CategoryTheory.Limits.FilteredColimitCokernelPresentation`, pure
category theory, which is used here as a theorem; its compactness hypothesis is Stacks 07U7,
which is available as
`AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`.

## Main results

* `AlgebraicGeometry.Space.exists_epi_isColimit_isFinitePresentation_of_isAffineHom` — the
  source's intermediate claim, *"every quasi-coherent module on `X` is a quotient of a filtered
  colimit of finitely presented modules"*, from the four general inputs below.
* `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isAffineHom` — the source's
  argument for Stacks 07UW, from those four inputs together with `hqcqs`.

Each of the five inputs is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherianUnconditional`,
which applies the second theorem to them and registers Stacks 07UW unconditionally, as
`Space.exists_isFiltered_isColimit_isFinitePresentation_of_isAffineHom_of_isNoetherian`.

## Implementation notes

### The inputs, and why each is general

The five inputs are stated about *arbitrary* algebraic spaces, morphisms and modules of their
own — none of them `f`, `X`, `Y` or `F` — so that this file needs none of the geometry behind
them.  None of them has the tag's conclusion as its consequent: `hNoeth` is the conclusion for a
*Noetherian* space, while `X` is only affine over a Noetherian space.

* `hNoeth` is Stacks 07UV together with Stacks 07UB, for every Noetherian algebraic space: every
  quasi-coherent module on one is a filtered colimit of modules of finite presentation.  It is
  `AlgebraicGeometry.Space.exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian`.
* `hpush` is the preservation of quasi-coherence by the direct image along an affine morphism,
  Stacks 07U8: `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`.
* `hpull` is the preservation of quasi-coherence (Stacks 03GA) and of finite presentation
  (Stacks 03DO (7)) by pullback of modules:
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` and
  `AlgebraicGeometry.Space.isFinitePresentation_modulePullback`.
* `hepi` is step 3 of the source's proof, the surjectivity of the counit `g^*g_*M ⟶ M` for an
  affine morphism: `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_counit_app_of_isAffineHom`.
* `hqcqs` is the step the source leaves implicit when it applies Stacks 07U7 on `X`: an algebraic
  space affine over a Noetherian algebraic space is quasi-compact and quasi-separated
  (`AlgebraicGeometry.Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom`).

### The universe of the index category

The hypothesis `hNoeth` produces a diagram indexed by a `SmallCategory` on a `Type u`, which is
what Stacks 07U7 requires of the shape it is applied to.  The conclusion's index category is the
one the second half of the proof constructs: the category of triples `(i, j, α)`, whose objects
carry a morphism of `𝒪_X`-modules and so live in `Type (u + 1)` — the universe of the Hom-types of
`AlgebraicGeometry.Space.Modules`, with Hom-types still in `Type u`.  This is the size of the
source's own index set `K`, which is literally a set of such triples; no smallness of the
conclusion's index is claimed, and the tag claims none.

## References

* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryTheory.FilteredColimitCokernelPresentation (IsCompactDiagram
  exists_isColimit_cokernel)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The intermediate claim of the proof of Stacks 07UW**: with `f : X ⟶ Y` an affine morphism
of algebraic spaces and `Y` Noetherian, every quasi-coherent `𝒪_X`-module `M` is a quotient of a
filtered colimit of `𝒪_X`-modules of finite presentation.  The colimit produced is
`f^*f_*M = colim_i f^*H_i`, and the quotient map is the counit of `f^* ⊣ f_*`.

The four hypotheses are the general cited inputs described in the module docstring: `hNoeth` is
Stacks 07UV with Stacks 07UB for an arbitrary Noetherian algebraic space, `hpush` is the
direct-image half of Stacks 08AI for an arbitrary affine morphism, `hpull` is Stacks 03LU and
Stacks 05VR for an arbitrary morphism, and `hepi` is step 3 of the source's proof for an
arbitrary affine morphism.  None of them mentions `f`, `X`, `Y` or `M`. -/
theorem exists_epi_isColimit_isFinitePresentation_of_isAffineHom
    (hNoeth : ∀ Z : AlgebraicSpaces B S hS, IsNoetherian B S hS hZ Z.1 →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        ∃ (I : Type u) (inst : SmallCategory I),
          let _ := inst
          ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS Z.1 Z.2)
            (φ : D ⟶ (Functor.const I).obj N),
            (∀ i, (D.obj i).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ)))
    (hpush : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W), IsAffineHom B S hS g.hom →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        ((modulePushforward B S hS g).obj N).IsQuasicoherentOnSite)
    (hpull : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W) (N : Modules.{u, u} B S hS W.1 W.2),
      (N.IsQuasicoherentOnSite → ((modulePullback B S hS g).obj N).IsQuasicoherentOnSite) ∧
        (N.IsFinitePresentation → ((modulePullback B S hS g).obj N).IsFinitePresentation))
    (hepi : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W), IsAffineHom B S hS g.hom →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        Epi ((modulePullbackAdjunction B S hS g).counit.app N))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    ∃ (I : Type u) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (H : I ⥤ Modules.{u, u} B S hS X.1 X.2) (c : Cocone H)
        (e : c.pt ⟶ M),
        (∀ i, (H.obj i).IsFinitePresentation) ∧ Nonempty (IsColimit c) ∧ Epi e ∧
          c.pt.IsQuasicoherentOnSite := by
  have hfM : ((modulePushforward B S hS f).obj M).IsQuasicoherentOnSite := hpush X Y f hf M hM
  obtain ⟨I, inst, hfil, D, φ, hDfp, ⟨hcol⟩⟩ :=
    hNoeth Y hY ((modulePushforward B S hS f).obj M) hfM
  let _ := inst
  have : PreservesColimitsOfSize.{u, u} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  exact ⟨I, inst, hfil, D ⋙ modulePullback B S hS f,
    (modulePullback B S hS f).mapCocone (Cocone.mk _ φ),
    (modulePullbackAdjunction B S hS f).counit.app M,
    fun i => (hpull X Y f (D.obj i)).2 (hDfp i),
    ⟨isColimitOfPreserves _ hcol⟩, hepi X Y f hf M hM,
    (hpull X Y f ((modulePushforward B S hS f).obj M)).1 hfM⟩

/-- **The source's argument for Stacks 07UW.**  Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over a scheme `S` with `Y` Noetherian.  Granted the five general inputs `hNoeth`,
`hpush`, `hpull`, `hepi` and `hqcqs` (see the module docstring), every quasi-coherent
`𝒪_X`-module is a filtered colimit of `𝒪_X`-modules of finite presentation.

All five inputs are proved, and Stacks 07UW is registered without them as
`Space.exists_isFiltered_isColimit_isFinitePresentation_of_isAffineHom_of_isNoetherian`.

The proof: the quotient presentation of an arbitrary quasi-coherent module
(`AlgebraicGeometry.Space.exists_epi_isColimit_isFinitePresentation_of_isAffineHom`), applied to
`F` and to the kernel of its quotient map, identifies `F` as a cokernel of a map between two
such colimits; Stacks 07U7 on `X` and the formal passage from that cokernel to the filtered
colimit of the cokernels of the representing maps conclude. -/
theorem isFilteredColimit_isFinitePresentation_of_isAffineHom
    (hNoeth : ∀ Z : AlgebraicSpaces B S hS, IsNoetherian B S hS hZ Z.1 →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        ∃ (I : Type u) (inst : SmallCategory I),
          let _ := inst
          ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS Z.1 Z.2)
            (φ : D ⟶ (Functor.const I).obj N),
            (∀ i, (D.obj i).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ)))
    (hpush : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W), IsAffineHom B S hS g.hom →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        ((modulePushforward B S hS g).obj N).IsQuasicoherentOnSite)
    (hpull : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W) (N : Modules.{u, u} B S hS W.1 W.2),
      (N.IsQuasicoherentOnSite → ((modulePullback B S hS g).obj N).IsQuasicoherentOnSite) ∧
        (N.IsFinitePresentation → ((modulePullback B S hS g).obj N).IsFinitePresentation))
    (hepi : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W), IsAffineHom B S hS g.hom →
      ∀ N : Modules.{u, u} B S hS Z.1 Z.2, N.IsQuasicoherentOnSite →
        Epi ((modulePullbackAdjunction B S hS g).counit.app N))
    (hqcqs : ∀ (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W), IsAffineHom B S hS g.hom →
      IsNoetherian B S hS hZ W.1 →
        IsQuasiCompactSpace B S hS Z.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ Z.1)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ∃ (K : Type (u + 1)) (inst : Category.{u} K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ Modules.{u, u} B S hS X.1 X.2)
        (φ : D ⟶ (Functor.const K).obj F),
        (∀ k, (D.obj k).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) := by
  classical
  obtain ⟨I, instI, hfilI, H, cH, e, hHfp, ⟨hcolH⟩, hepie, hqcH⟩ :=
    exists_epi_isColimit_isFinitePresentation_of_isAffineHom B S hS hZ hNoeth hpush hpull hepi
      f hf hY F hF
  let _ := instI
  have := hfilI
  have := hepie
  have := hqcH
  have := hF
  have hkerqc : (kernel e).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_isCartesian B S hS X.1 X.2 e
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2)
  obtain ⟨J, instJ, hfilJ, G, cG, e', hGfp, ⟨hcolG⟩, hepie', -⟩ :=
    exists_epi_isColimit_isFinitePresentation_of_isAffineHom B S hS hZ hNoeth hpush hpull hepi
      f hf hY (kernel e) hkerqc
  let _ := instJ
  have := hfilJ
  have := hepie'
  obtain ⟨hqcX, hqsX⟩ := hqcqs X Y f hf hY
  have hcompact : IsCompactDiagram I G := by
    intro j
    have := hGfp j
    exact preservesColimitsOfShape_coyoneda_of_isFinitePresentation B S hS X.1 X.2 hZ
      hqcX hqsX (G.obj j) I
  obtain ⟨K, instK, hfilK, D, c, hcpt, ⟨hc⟩, hk⟩ :=
    exists_isColimit_cokernel cH cG (e' ≫ kernel.ι e) hcolH hcolG hcompact
  let _ := instK
  have hcok := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι e) (kernel.condition e)) (kernelIsKernel e)
  have hiso : c.pt ≅ F :=
    eqToIso hcpt ≪≫ cokernelEpiComp e' (kernel.ι e) ≪≫
      IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι e)) hcok
  refine ⟨K, instK, hfilK, D, c.ι ≫ (Functor.const K).map hiso.hom, ?_,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext hiso fun k => rfl)⟩⟩
  intro k
  obtain ⟨j, i, α, -, heq⟩ := hk k
  have := hHfp i
  have := hGfp j
  rw [heq]
  infer_instance

end AlgebraicGeometry.Space

end
