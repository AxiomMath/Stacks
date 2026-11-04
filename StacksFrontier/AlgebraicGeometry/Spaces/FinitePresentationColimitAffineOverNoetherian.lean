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
  colimit of finitely presented modules"*, granted the four general hypotheses below.
* `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isAffineHom` —
  **Stacks 07UW**, granted those four together with `hqcqs`.

## Implementation notes

### The carried inputs, and why each is general

Five hypotheses are carried.  Each is stated about *arbitrary* algebraic spaces, morphisms and
modules of its own — none of them `f`, `X`, `Y` or `F` — exactly as `hscheme` of
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections` carries the case of
schemes of Stacks 05ID under Stacks 0CVY, and as `hEKP` of
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated` carries the
chain (1) ⇒ (4) of Stacks 0EKP under Stacks 0EKS.  In particular none of them has this theorem's
conclusion as its consequent: `hNoeth` is the conclusion for a *Noetherian* space, which is a
different assertion — Stacks 07UV with Stacks 07UB — and is precisely what the source quotes at
this point, while `X` is not assumed Noetherian but only affine over a Noetherian space, which is
the whole content of the tag.

* `hNoeth` is Stacks 07UV together with Stacks 07UB, for every Noetherian algebraic space: every
  quasi-coherent module on one is a filtered colimit of modules of finite presentation.  Stacks
  07UV is `AlgebraicGeometry.Space.isFiltered_and_nonempty_isColimit_coherentSubobjectCocone`;
  of Stacks 07UB this repository has
  only the special cases listed in
  `StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence` and
  `StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent`, not the implication from coherence
  to finite presentation on the small étale site.  The two are therefore carried jointly, in the
  finite-presentation form in which the source's proof uses them, and in the spelling of the
  companion hypothesis `h07V9` of
  `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone`.
* `hpush` is the direct-image half of Stacks 08AI for an affine morphism:
  `AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence` is still a `def … : Prop` and the
  tagged functor `AlgebraicGeometry.Space.quasicoherentDirectImage` takes it as an argument.
* `hpull` is pullback of modules preserving quasi-coherence (Stacks 03LU) and finite presentation
  (Properties of Spaces, Section 05VR); neither is available in this tree.
* `hepi` is step 3 of the source's proof, the surjectivity of the counit `g^*g_*M ⟶ M` for an
  affine morphism.  Stacks 03LX is proved, as
  `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, but that is the compatibility of
  direct image with étale base change, which is what the source *uses* to reduce the
  surjectivity to the case of schemes; the surjectivity itself is not proved here.
* `hqcqs` is the step the source leaves implicit when it applies Stacks 07U7 on `X`: an algebraic
  space affine over a Noetherian algebraic space is quasi-compact and quasi-separated.  Stacks
  07U7 is proved, and this is all that is missing to apply it to `X`.

### The universe of the index category

The hypothesis `hNoeth` produces a diagram indexed by a `SmallCategory` on a `Type u`, which is
what Stacks 07U7 requires of the shape it is applied to, and is the spelling already used by
`h07V9` above.  The conclusion's index category is the one the second half of the proof
constructs: the category of triples `(i, j, α)`, whose objects carry a morphism of
`𝒪_X`-modules and so live in `Type (u + 1)` — the universe of the Hom-types of
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

/-- **Stacks 07UW.**  Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S`
with `Y` Noetherian.  Then every quasi-coherent `𝒪_X`-module is a filtered colimit of
`𝒪_X`-modules of finite presentation.

No clause of the tag's conclusion is dropped or weakened, and the tag's own hypotheses — `f`
affine, `Y` Noetherian, the module quasi-coherent — are the hypotheses here.  What is granted
beyond them are the five general cited inputs `hNoeth`, `hpush`, `hpull`, `hepi` and `hqcqs`,
each quantified over its own algebraic spaces, morphisms and modules and none of them mentioning
`f`, `X`, `Y` or `F`; see the module docstring for what each one is and for which tag it stands
in.  In particular `hNoeth` is the assertion for a *Noetherian* space, namely Stacks 07UV with
Stacks 07UB, which the source quotes here and which is not the conclusion below: `X` is affine
over a Noetherian space, not Noetherian, and the transfer along `f` is the content of the tag.

Everything else in the source's proof is discharged: the pullback of the presentation and the
quotient presentation of an arbitrary quasi-coherent module
(`AlgebraicGeometry.Space.exists_epi_isColimit_isFinitePresentation_of_isAffineHom`), the
identification of `F` as a cokernel of a map between two such colimits, Stacks 07U7 on `X`, and
the formal passage from that cokernel to the filtered colimit of the cokernels of the
representing maps. -/
@[stacks 07UW "granted five general cited inputs: hNoeth (the Noetherian case, Stacks 07UV with \
07UB), hpush (Stacks 08AI), hpull (Stacks 03LU, 05VR), hepi (Stacks 03LX, step 3) and hqcqs"]
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
