module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeOfRank

/-!
# The vector bundle of a virtual normal bundle, and the normal cone inside it

Let `i : Z ⟶ X` be an immersion of schemes and let `𝒩` be a virtual normal bundle for `i` in
the sense of Stacks 0FBQ (2): a finite locally free `𝒪_Z`-module together with a surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` onto the conormal sheaf. Write `p : N = 𝐕(𝒩^∨) ⟶ Z` for the vector bundle
of `𝒩^∨` (`Stacks.Chow.VirtualNormalBundle.totalSpace`). The construction preceding Stacks 0FBK
uses `N`, its projection, and the canonical closed immersions

  `C_ZX ⟶ N_ZX ⟶ N`,

the first of Stacks 0637 and the second the morphism of vector bundles attached to `σ`. This file
constructs them, and supplies what makes `N` usable with no hypothesis: `Sym(𝒩^∨)` is a
quasi-coherent algebra sheaf (Stacks 01CK), and `p` is locally of finite type.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.normalBundleEmbedding` — the canonical closed immersion
  `N_ZX ⟶ N` over `Z` induced by the surjection `Sym(𝒩^∨) ⟶ Sym(𝒞_{Z/X})` that `σ` induces.
* `Stacks.Chow.VirtualNormalBundle.normalConeEmbedding` — **the canonical closed immersion
  `ι : C_ZX ⟶ N`** over `Z`, the closed immersion `C_ZX ⟶ N_ZX` of Stacks 0637 followed by
  `N_ZX ⟶ N`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.isQuasicoherent_symmetricAlgebraSheaf` — `Sym(𝒩^∨)` is a
  quasi-coherent algebra sheaf, so `N` and `p` need no hypothesis.
* `Stacks.Chow.VirtualNormalBundle.locallyOfFiniteType_projection_of_finitePresentation` — the
  projection `p : N ⟶ Z` is locally of finite type, for any virtual normal bundle;
  `Stacks.Chow.VirtualNormalBundle.flat_projection_of_rank` and
  `Stacks.Chow.VirtualNormalBundle.relativeDimension_projection_of_rank` — when `𝒩` has constant
  rank `r`, it is flat of relative dimension `r`.
* `Stacks.Chow.VirtualNormalBundle.isClosedImmersion_normalConeEmbedding` and
  `Stacks.Chow.VirtualNormalBundle.normalConeEmbedding_projection` — `ι : C_ZX ⟶ N` is a closed
  immersion and a morphism over `Z`.

## Implementation notes

The dual `𝒩^∨` is quasi-coherent because `𝒩` is finite locally free, hence of finite
presentation, and `Sym(𝒩^∨)` is then a quasi-coherent algebra sheaf by Stacks 01CK
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`). `𝒩^∨` is moreover
of finite presentation, so the projection is locally of finite presentation whatever the ranks
of `𝒩`. When `𝒩` has constant rank `r` so has `𝒩^∨`, and the projection is an affine-space
bundle of rank `r`; this is where its flatness and relative dimension come from.

The source's `ι` is the composite of two canonical closed immersions over `Z`. The first,
`C_ZX ⟶ N_ZX`, is the relative spectrum of the surjection `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks
0632 (`Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle`). The second, `N_ZX ⟶ N`, is
the morphism of vector bundles attached to `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}`, read as a surjection onto the
degree-one piece `𝒞_{Z/X,1}` through `Stacks.Conormal.conormalDegreeOneIso`; a surjection of
quasi-coherent modules gives a closed immersion of vector bundles
(`AlgebraicGeometry.Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi`).

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

section TotalSpace

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]

/-- **`Sym(𝒩^∨)` is a quasi-coherent algebra sheaf** for a virtual normal bundle `𝒩`
(Stacks 01CK): `𝒩^∨` is quasi-coherent. So the vector bundle `N = 𝐕(𝒩^∨)` and its projection
need no hypothesis. -/
instance VirtualNormalBundle.isQuasicoherent_symmetricAlgebraSheaf (N : VirtualNormalBundle i) :
    (Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf N.bundle)).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf Z (dualSheaf N.bundle)

/-- The dual `𝒩^∨` of a virtual normal bundle is of finite presentation: it is finite locally free
(Stacks 0FA7), whatever the ranks of `𝒩` on the components of `Z`. -/
instance VirtualNormalBundle.isFinitePresentation_dualSheaf (N : VirtualNormalBundle i) :
    (dualSheaf N.bundle).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree (dualSheaf N.bundle)
    (isFiniteLocallyFree_dualSheaf N.bundle N.isFiniteLocallyFree)

/-- **The projection of the vector bundle of a virtual normal bundle is locally of finite type**:
it is even locally of finite presentation, `Sym(𝒩^∨)` being an algebra of finite presentation. No
constancy of the rank of `𝒩` is needed. -/
instance VirtualNormalBundle.locallyOfFiniteType_projection_of_finitePresentation
    (N : VirtualNormalBundle i) :
    LocallyOfFiniteType N.projection :=
  haveI := @Stacks.SymAlgSections.locallyOfFinitePresentation_vectorBundleToBase _
    (dualSheaf N.bundle) _ N.isFinitePresentation_dualSheaf
  show LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase Z (dualSheaf N.bundle)) from
    inferInstance

/-- **The projection of the vector bundle of a virtual normal bundle of rank `r` is flat**: it is
an affine-space bundle of rank `r`. -/
theorem VirtualNormalBundle.flat_projection_of_rank (N : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] :
    Flat N.projection :=
  flat_vectorBundleToBase (dualSheaf N.bundle) r

/-- **The projection of the vector bundle of a virtual normal bundle of rank `r` has relative
dimension `r`**: it is an affine-space bundle of rank `r`, the dual of `𝒩` having the rank of
`𝒩`. -/
theorem VirtualNormalBundle.relativeDimension_projection_of_rank (N : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] :
    RelativeDimension N.projection r :=
  relativeDimension_vectorBundleToBase (dualSheaf N.bundle) r

/-! ### The normal cone inside the vector bundle of a virtual normal bundle -/

/-- **The surjection `𝒩^∨ ⟶ 𝒞_{Z/X,1}` of a virtual normal bundle onto the degree-one piece of
the conormal algebra**: the surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` of the virtual normal bundle followed
by the identification `𝒞_{Z/X} ≅ 𝒞_{Z/X,1}` of Stacks 0632. -/
def VirtualNormalBundle.conormalDegreeOneSurjection (N : VirtualNormalBundle i) :
    dualSheaf N.bundle ⟶ Stacks.Conormal.conormalSheafDegreeOne i :=
  N.surjection ≫ (Stacks.Conormal.conormalDegreeOneIso i).hom

/-- The surjection `𝒩^∨ ⟶ 𝒞_{Z/X,1}` is an epimorphism: `σ` is one and the identification of
Stacks 0632 is an isomorphism. -/
instance VirtualNormalBundle.epi_conormalDegreeOneSurjection (N : VirtualNormalBundle i) :
    Epi N.conormalDegreeOneSurjection :=
  @epi_comp _ _ _ _ _ _ N.epi _ (Stacks.Conormal.conormalDegreeOneIso i).isIso_hom.epi_of_iso

/-- **The canonical closed immersion `N_ZX ⟶ N` of a virtual normal bundle**: the morphism of
vector bundles over `Z` induced by the surjection `Sym(𝒩^∨) ⟶ Sym(𝒞_{Z/X})` that `σ` induces.
Its source is `N_ZX = Stacks.Conormal.normalBundle i`, written as the vector bundle it is by
definition, which is the target of `Stacks.Conormal.normalConeToNormalBundle`. -/
def VirtualNormalBundle.normalBundleEmbedding (N : VirtualNormalBundle i) :
    Scheme.Modules.vectorBundle Z (Stacks.Conormal.conormalSheafDegreeOne i) ⟶ N.totalSpace :=
  (Scheme.Modules.vectorBundleMap Z N.conormalDegreeOneSurjection).left

/-- The canonical morphism `N_ZX ⟶ N` is a closed immersion: `σ` is surjective. -/
instance VirtualNormalBundle.isClosedImmersion_normalBundleEmbedding (N : VirtualNormalBundle i) :
    IsClosedImmersion N.normalBundleEmbedding :=
  @Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi Z _ _ _ _ N.conormalDegreeOneSurjection
    N.epi_conormalDegreeOneSurjection

/-- The canonical morphism `N_ZX ⟶ N` is a morphism over `Z`. -/
@[reassoc]
theorem VirtualNormalBundle.normalBundleEmbedding_projection (N : VirtualNormalBundle i) :
    N.normalBundleEmbedding ≫ N.projection =
      Scheme.Modules.vectorBundleToBase Z (Stacks.Conormal.conormalSheafDegreeOne i) :=
  Scheme.Modules.vectorBundleMap_left_comp Z N.conormalDegreeOneSurjection

/-- **The canonical closed immersion `ι : C_ZX ⟶ N` of the normal cone into the vector bundle of
a virtual normal bundle**: the closed immersion `C_ZX ⟶ N_ZX` of Stacks 0637 followed by the
closed immersion `N_ZX ⟶ N` induced by `σ`. -/
def VirtualNormalBundle.normalConeEmbedding (N : VirtualNormalBundle i) :
    Stacks.Conormal.normalCone i ⟶ N.totalSpace :=
  Stacks.Conormal.normalConeToNormalBundle i ≫ N.normalBundleEmbedding

/-- **The canonical morphism `ι : C_ZX ⟶ N` is a closed immersion**, as the composite of two
closed immersions. -/
instance VirtualNormalBundle.isClosedImmersion_normalConeEmbedding (N : VirtualNormalBundle i) :
    IsClosedImmersion N.normalConeEmbedding := by
  unfold VirtualNormalBundle.normalConeEmbedding
  infer_instance

/-- **The canonical morphism `ι : C_ZX ⟶ N` is a morphism over `Z`.** -/
@[reassoc]
theorem VirtualNormalBundle.normalConeEmbedding_projection (N : VirtualNormalBundle i) :
    N.normalConeEmbedding ≫ N.projection = Stacks.Conormal.normalConeToBase i := by
  rw [VirtualNormalBundle.normalConeEmbedding, Category.assoc,
    VirtualNormalBundle.normalBundleEmbedding_projection,
    Stacks.Conormal.normalConeToNormalBundle_toBase]

end TotalSpace

end Stacks.Chow

end
