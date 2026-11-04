module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechElementChase.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# A sheaf epimorphism of quasi-coherent modules is surjective on sections over an affine open

Let `X` be a scheme, `ψ : M ⟶ N` an epimorphism of quasi-coherent `𝒪_X`-modules and `U ⊆ X` an
affine open. Then `Γ(U, M) → Γ(U, N)` is surjective. Equivalently `Γ(U, -)` is exact on
quasi-coherent modules, which is the `H¹`-vanishing half of [Stacks, Tag 01XB]. The statement is
an input to [Stacks, Tag 0817], extracted from the proof of [Stacks, Tag 01XB].

The proof assembles the following.

* `Stacks.CechElementChase.epi_secF_map_g` is [Stacks, Tag 01EU]: for a short exact sequence of
  `𝒪_X`-modules whose first term has vanishing higher Čech cohomology for a set `Cov` of
  coverings, and for an open `W` every covering of which is refined by one in `Cov`, the last map
  is surjective on sections over `W`.
* The affine-open vanishing of [Stacks, Tag 01XB] supplies both hypotheses at
  an affine open, with `Cov` the finite standard coverings:
  `Stacks.Cohomology.AffineOpen.cechCohomologyIsZero_of_mem_standardCovers` is the Čech vanishing
  and `Stacks.Cohomology.AffineOpen.exists_standardCover_refines` is the cofinality.
* The short exact sequence is `0 → ker ψ → M → N → 0`, and its first term is quasi-coherent by
  `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, which is what makes the Čech
  vanishing applicable to it.

## Main definitions

* `Stacks.SectionEpiAffine.standardCovers`: the finite standard coverings of the affine opens of
  `X`, as a set of `Stacks.CohomologyVanishing.OpenCover`s.

## Main results

* `Stacks.SectionEpiAffine.epi_secF_map_of_isAffineOpen`: `Γ(U, -)` carries an epimorphism of
  quasi-coherent `𝒪_X`-modules to an epimorphism, for `U` an affine open.
* `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`: the same statement, read on elements.
* `Stacks.SectionEpiAffine.hasVanishingHigherCech_standardCovers` and
  `Stacks.SectionEpiAffine.exists_standardCover_refines`: the two hypotheses of
  [Stacks, Tag 01EU], in the vocabulary it is stated in.

## Implementation notes

**There are two `OpenCover` structures, and the two halves of the argument use different ones.**
`Stacks.Cohomology.Basis.OpenCover` (the cover type of [Stacks, Tag 01EW]) is what Tag 01XB and
its cofinality lemma speak about; `Stacks.CohomologyVanishing.OpenCover` is what the element
chase of [Stacks, Tag 01EU] speaks about. The two are field-for-field identical and are *not* the
same type, so `ofBasisCover` and `toBasisCover` convert. Because they agree on `ι`, `carrier` and
`obj`, everything stated about a cover transports by definitional unfolding and not by rewriting:
the two spellings of `Refines` are the same proposition, and so are the two spellings of
`CechCohomologyIsZero`, both of which depend on the cover only through `obj`. That is why
`exists_standardCover_refines` below can return the refinement produced by Tag 01XB unchanged,
and why `hasVanishingHigherCech_standardCovers` is one `exact`.

**No quasi-compactness or quasi-separatedness of `X` is used.** The quasi-compactness the argument
needs is that of the affine open `U`, and it enters inside Tag 01XB's cofinality lemma, in the
algebraic form `Ideal.span_eq_top_iff_finite`. So no hypotheses `[CompactSpace X]` or
`[QuasiSeparatedSpace X]` are needed.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.CohomologyVanishing

universe u

namespace Stacks.SectionEpiAffine

variable (X : Scheme.{u})

/-! ### Transporting a covering between the two `OpenCover` structures -/

/-- A `Stacks.Cohomology.Basis.OpenCover`, read as a `Stacks.CohomologyVanishing.OpenCover`. The
two structures have the same four fields; see the implementation notes. -/
def ofBasisCover (W : Stacks.Cohomology.Basis.OpenCover ↥X) : OpenCover ↥X where
  ι := W.ι
  carrier := W.carrier
  obj := W.obj
  iSup_eq := W.iSup_eq

/-- A `Stacks.CohomologyVanishing.OpenCover`, read as a `Stacks.Cohomology.Basis.OpenCover`. -/
def toBasisCover (W : OpenCover ↥X) : Stacks.Cohomology.Basis.OpenCover ↥X where
  ι := W.ι
  carrier := W.carrier
  obj := W.obj
  iSup_eq := W.iSup_eq

/-- **The finite standard open coverings of the affine opens of `X`**, as a set of
`Stacks.CohomologyVanishing.OpenCover`s: the image of
`Stacks.Cohomology.AffineOpen.standardCovers` under `ofBasisCover`. This is the `Cov` that
[Stacks, Tag 01EU] is applied to. -/
def standardCovers : Set (OpenCover ↥X) :=
  ofBasisCover X '' Stacks.Cohomology.AffineOpen.standardCovers X

/-! ### The two hypotheses of [Stacks, Tag 01EU] at an affine open -/

/-- **A quasi-coherent module has vanishing higher Čech cohomology for the finite standard
coverings.** This is `Stacks.Cohomology.AffineOpen.cechCohomologyIsZero_of_mem_standardCovers`,
which is [Stacks, Tag 01X9] after reindexing, stated for `standardCovers`. -/
theorem hasVanishingHigherCech_standardCovers (F : X.Modules) [F.IsQuasicoherent] :
    HasVanishingHigherCech X.ringCatSheaf (standardCovers X) F := by
  rintro V ⟨W, hW, rfl⟩ p hp
  exact Stacks.Cohomology.AffineOpen.cechCohomologyIsZero_of_mem_standardCovers X F hW p hp

/-- **Every covering of an affine open is refined by a finite standard one.** This is
`Stacks.Cohomology.AffineOpen.exists_standardCover_refines`, the only hypothesis of
[Stacks, Tag 01EU] with mathematical content, stated for `standardCovers`. -/
theorem exists_standardCover_refines (U : X.Opens) (hU : IsAffineOpen U)
    (𝒲 : OpenCover ↥X) (h𝒲 : 𝒲.carrier = U) :
    ∃ V ∈ standardCovers X, V.Refines 𝒲 := by
  obtain ⟨W, hW, -, hrefines⟩ :=
    Stacks.Cohomology.AffineOpen.exists_standardCover_refines X U hU (toBasisCover X 𝒲) h𝒲
  exact ⟨ofBasisCover X W, ⟨W, hW, rfl⟩, hrefines⟩

/-! ### Sections over an affine open are surjective -/

/-- **`Γ(U, -)` preserves epimorphisms of quasi-coherent modules over an affine open `U`.** The
short exact sequence `0 → ker ψ → M → N → 0` has quasi-coherent first term, so
[Stacks, Tag 01EU] applies with `Cov` the finite standard coverings of the affine opens. -/
theorem epi_secF_map_of_isAffineOpen {M N : X.Modules} (ψ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi ψ] (U : X.Opens) (hU : IsAffineOpen U) :
    Epi ((secF X.ringCatSheaf U).map ψ) := by
  have hker : (kernel ψ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel ψ
  have hS : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)).ShortExact :=
    { exact := ShortComplex.exact_kernel ψ }
  exact Stacks.CechElementChase.epi_secF_map_g X.ringCatSheaf _ hS
    (hasVanishingHigherCech_standardCovers X (kernel ψ)) U (exists_standardCover_refines X U hU)

/-- **An epimorphism of quasi-coherent `𝒪_X`-modules is surjective on sections over an affine
open**, read on elements: `epi_secF_map_of_isAffineOpen` through
`AddCommGrpCat.epi_iff_surjective`. -/
theorem surjective_app_of_isAffineOpen {M N : X.Modules} (ψ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi ψ] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (ψ.val.app (op U)) :=
  (AddCommGrpCat.epi_iff_surjective _).1 (epi_secF_map_of_isAffineOpen X ψ U hU)

end Stacks.SectionEpiAffine

end
