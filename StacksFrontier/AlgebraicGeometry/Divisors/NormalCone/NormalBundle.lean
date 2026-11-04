module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle

/-!
# The normal cone and the normal bundle of an immersion

Let `i : Z ⟶ X` be an immersion of schemes, with conormal algebra `𝒞_{Z/X,*}` and conormal sheaf
`𝒞_{Z/X} = 𝒞_{Z/X,1}` its degree-one piece. **Stacks Tag 0636** defines two schemes over `Z` as
relative spectra of quasi-coherent algebras on `Z`, in the sense of Tags 062Q and 062R:

* the *normal cone* `C_ZX = Spec_Z(𝒞_{Z/X,*})`, the relative spectrum of the **graded conormal
  algebra**, which is a **cone over `Z`** in the sense of Tag 062R, and
* the *normal bundle* `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))`, the relative spectrum of the symmetric
  algebra on the **single sheaf** `𝒞_{Z/X}`, which is a **vector bundle over `Z`** in the sense of
  Tag 062M, namely the one of Tag 01M2 associated to `𝒞_{Z/X}`.

The normal cone is `Stacks.Conormal.normalCone`, already constructed in
`StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle` for the sake of the
Tag 0637 morphism `C_ZX ⟶ N_ZX`; this file names the normal bundle, which that module only used
inline as `AlgebraicGeometry.Scheme.Modules.vectorBundle Z (conormalSheafDegreeOne i)`, and
equips both of them with the structure Tag 0636 asserts they carry.

## Which conormal sheaf

`𝒞_{Z/X}` is taken here to be the degree-one piece `𝒞_{Z/X,1}` of the conormal algebra, i.e.
`Stacks.Conormal.conormalSheafDegreeOne`, which is the identification the source itself makes in
Tag 0632 when it writes the canonical map as `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`. It is **not** the
independently constructed sheaf `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`, the
pullback of the defining ideal along `i.liftCoborder`; those are two different objects, and
`Stacks.Conormal.conormalDegreeOneIso` is the comparison isomorphism between them. Taking the
degree-one piece is what makes `N_ZX` the target of the Tag 0637 morphism out of `C_ZX` without
transporting along that comparison.

## Main definitions

* `Stacks.Conormal.normalBundle`: **the normal bundle `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))`**, with
  `Stacks.Conormal.normalBundleToBase` its projection to `Z`.
* `Stacks.Conormal.normalBundleVectorBundle`: **`N_ZX` as a vector bundle over `Z`**, and
  `Stacks.Conormal.normalConeCone`: **`C_ZX` as a cone over `Z`.**

## Main results

* `Stacks.Conormal.normalBundle_eq_relativeSpec` and
  `Stacks.Conormal.normalCone_eq_relativeSpec`: `N_ZX` and `C_ZX` are the relative spectra of
  `Sym(𝒞_{Z/X})`, respectively of `𝒞_{Z/X,*}`, on the nose.
* `Stacks.Conormal.conormalPieceZeroIso_hom_one`: the identification `𝒞_{Z/X,0} ≅ 𝒪_Z` carries
  the graded unit of the conormal algebra to `1`, which is the one input the cone structure needs
  beyond `Stacks.Conormal.ConormalAlgebraData`.
* `Stacks.Conormal.isAffineHom_normalBundleToBase` and
  `Stacks.Conormal.isAffineHom_normalConeToBase`: **both projections are affine morphisms**, and
  `isAffineOpen_preimage_normalBundleToBase`, `isAffineOpen_preimage_normalConeToBase`: the part
  of either over an affine open of `Z` is affine.
* `Stacks.Conormal.normalConeToNormalBundle_normalBundleToBase`: the Tag 0637 morphism
  `C_ZX ⟶ N_ZX` is a morphism over `Z` for the projection named here.

## Implementation notes

### The two structures Tag 0636 asserts

Tag 0636 calls `C_ZX` a *cone* over `Z` and `N_ZX` a *vector bundle* over `Z`, in the senses of
Tags 062R and 062M, and both are exhibited here rather than assumed.

`N_ZX` is the vector bundle `AlgebraicGeometry.VectorBundle.ofModule Z (conormalSheafDegreeOne i)`
of Tag 01M2, whose total space and projection are `normalBundle` and `normalBundleToBase` on the
nose. `C_ZX` is the cone `AlgebraicGeometry.GradedAlgebraCone.cone` of the conormal algebra: its
homogeneous pieces decompose the direct image of the structure sheaf of the relative spectrum,
uniquely over every open and locally surjectively, because that direct image is the
sheafification of the ungraded realization. The one input which is not already a field of
`Stacks.Conormal.ConormalAlgebraData` is that the degree-zero identification `𝒞_{Z/X,0} ≅ 𝒪_Z` be
unital, which is `Stacks.Conormal.conormalPieceZeroIso_hom_one`: the canonical map
`Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` carries unit to unit and is an isomorphism in degree zero, and
degree zero of a symmetric algebra is the structure sheaf unitally.

Neither relative spectrum carries quasi-coherence of its algebra sheaf as a hypothesis:
`Sym(𝒞_{Z/X})` is quasi-coherent by Tag 01CK, in the form
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`, and `𝒞_{Z/X,*}` by
`Stacks.Conormal.isQuasicoherent_conormalAlgebraSheaf`.

## References

* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 062Q](https://stacks.math.columbia.edu/tag/062Q)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 062M](https://stacks.math.columbia.edu/tag/062M)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-! ### The normal bundle -/

section NormalBundle

/-- **Stacks Project, Tag 0636.** **The normal bundle `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))`** of an
immersion `i : Z ⟶ X`: the relative spectrum over `Z` of the symmetric algebra on the conormal
sheaf `𝒞_{Z/X} = 𝒞_{Z/X,1}`, that is, the vector bundle of Tag 01M2 associated to `𝒞_{Z/X}`. -/
@[stacks 0636 "the normal bundle N_ZX = Spec_Z(Sym(C_{Z/X}))"]
def normalBundle : Scheme.{u} :=
  Scheme.Modules.vectorBundle Z (conormalSheafDegreeOne i)

/-- **The projection `N_ZX ⟶ Z`** of the normal bundle to its base, the structure morphism of the
relative spectrum of `Sym(𝒞_{Z/X})`. -/
def normalBundleToBase : normalBundle i ⟶ Z :=
  Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i)

/-- The normal bundle is the vector bundle associated to the conormal sheaf, on the nose. -/
theorem normalBundle_eq_vectorBundle :
    normalBundle i = Scheme.Modules.vectorBundle Z (conormalSheafDegreeOne i) :=
  rfl

/-- **`N_ZX` is the relative spectrum of `Sym(𝒞_{Z/X})`** on the nose, which is the content of
the second half of Tag 0636. -/
theorem normalBundle_eq_relativeSpec :
    normalBundle i = Stacks.AffineAlgebraEquivalence.relativeSpec (normalBundleAlgebra i) :=
  rfl

/-- **The part of `N_ZX` lying over an affine open of `Z` is affine.** -/
theorem isAffineOpen_preimage_normalBundleToBase (U : Z.affineOpens) :
    IsAffineOpen (normalBundleToBase i ⁻¹ᵁ (U : Z.Opens)) :=
  Scheme.Modules.isAffineOpen_preimage_vectorBundleToBase Z (conormalSheafDegreeOne i) U

/-- **The projection of the normal bundle is an affine morphism**, so that `N_ZX` is affine over
`Z` as a vector bundle must be. -/
instance isAffineHom_normalBundleToBase : IsAffineHom (normalBundleToBase i) :=
  Scheme.Modules.isAffineHom_vectorBundleToBase Z (conormalSheafDegreeOne i)

/-- **Stacks Project, Tag 0636.** **`N_ZX` is a vector bundle over `Z`** in the sense of Tag
062M: it is the vector bundle `𝐕(𝒞_{Z/X})` of Tag 01M2 attached to the conormal sheaf, the
relative spectrum of `Sym(𝒞_{Z/X})` graded by the symmetric powers `Symⁿ(𝒞_{Z/X})`. -/
@[stacks 0636 "N_ZX is a vector bundle over Z in the sense of 062M"]
def normalBundleVectorBundle : VectorBundle Z :=
  VectorBundle.ofModule Z (conormalSheafDegreeOne i)

/-- The total space of the normal bundle read as a vector bundle is `N_ZX`. -/
@[simp] theorem C_normalBundleVectorBundle :
    (normalBundleVectorBundle i).C = normalBundle i :=
  rfl

/-- The projection of the normal bundle read as a vector bundle is the projection `N_ZX ⟶ Z`. -/
@[simp] theorem π_normalBundleVectorBundle :
    (normalBundleVectorBundle i).π = normalBundleToBase i :=
  rfl

/-- The direct-image algebra of the normal bundle read as a vector bundle is `Sym(𝒞_{Z/X})`. -/
@[simp] theorem grading_normalBundleVectorBundle :
    (normalBundleVectorBundle i).grading =
      Scheme.Modules.symmetricAlgebra Z (conormalSheafDegreeOne i) :=
  rfl

end NormalBundle

/-! ### The normal cone -/

section NormalCone

/-- **`C_ZX` is the relative spectrum of `𝒞_{Z/X,*}`** on the nose, which is the content of the
first half of Tag 0636. -/
theorem normalCone_eq_relativeSpec :
    normalCone i = Stacks.AffineAlgebraEquivalence.relativeSpec (conormalAlgebraSheaf i) :=
  rfl

/-- **The part of `C_ZX` lying over an affine open of `Z` is affine.** -/
theorem isAffineOpen_preimage_normalConeToBase (U : Z.affineOpens) :
    IsAffineOpen (normalConeToBase i ⁻¹ᵁ (U : Z.Opens)) :=
  Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase
    (conormalAlgebraSheaf i) U

/-- **The projection of the normal cone is an affine morphism**, which is the affineness
requirement a cone over `Z` in the sense of Tag 062R must satisfy. -/
instance isAffineHom_normalConeToBase : IsAffineHom (normalConeToBase i) :=
  Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (conormalAlgebraSheaf i)

/-- **The identification `𝒞_{Z/X,0} ≅ 𝒪_Z` is unital**: it carries the graded unit of the
conormal algebra to the unit function, over every open of `Z`.

The identification is the canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Tag 0632 inverted in
degree zero and followed by the degree-zero identification of a symmetric algebra. The canonical
map is unital, and so is that identification. -/
theorem conormalPieceZeroIso_hom_one (U : (Opens ↥Z)ᵒᵖ) :
    (conormalPieceZeroIso i).hom.val.app U ((conormalAlgebra i).algebra.one.eval U) =
      (1 : Z.ringCatSheaf.obj.obj U) := by
  have := isIso_conormalSymmetricHom_app_zero i
  have hcomp : (conormalSymmetricHom i).app 0 ≫ (conormalPieceZeroIso i).hom =
      (Scheme.Modules.symmetricAlgebraPieceZeroIso Z (conormalSheafDegreeOne i)).hom := by
    rw [conormalPieceZeroIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc,
      IsIso.hom_inv_id, Category.id_comp]
  have key : (conormalPieceZeroIso i).hom.val.app U
        (((conormalSymmetricHom i).app 0).val.app U
          ((conormalSymmetricAlgebra i).one.eval U)) =
      (Scheme.Modules.symmetricAlgebraPieceZeroIso Z (conormalSheafDegreeOne i)).hom.val.app U
        ((conormalSymmetricAlgebra i).one.eval U) :=
    CategoryTheory.congr_fun (congrArg (fun k => k.val.app U) hcomp) _
  rw [(conormalSymmetricHom i).map_one U] at key
  exact key.trans
    (AbstractCone.symmetricAlgebraPieceZeroIso_hom_one Z (conormalSheafDegreeOne i) U)

/-- **Stacks Project, Tag 0636.** **`C_ZX` is a cone over `Z`** in the sense of Tag 062R: it is
affine over `Z`, and the homogeneous pieces `𝒞_{Z/X,n}` of the conormal algebra decompose the
direct image of its structure sheaf — uniquely over every open, locally surjectively, and
multiplicatively — with the degree-zero piece the structure sheaf of `Z`. -/
@[stacks 0636 "C_ZX is a cone over Z in the sense of 062R"]
def normalConeCone : AbstractCone Z :=
  haveI : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Stacks.RelativeSpec.gradedAlgebraSheaf Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int) :=
    isQuasicoherent_conormalAlgebraSheaf i
  GradedAlgebraCone.cone Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
    (conormalPieceZeroIso i) (conormalPieceZeroIso_hom_one i)
    (conormalAlgebra i).negative_isZero

/-- The total space of the normal cone read as a cone over `Z` is `C_ZX`. -/
@[simp] theorem C_normalConeCone : (normalConeCone i).C = normalCone i := rfl

/-- The projection of the normal cone read as a cone over `Z` is the projection `C_ZX ⟶ Z`. -/
@[simp] theorem π_normalConeCone : (normalConeCone i).π = normalConeToBase i := rfl

/-- The grading of the normal cone read as a cone over `Z` is the conormal algebra. -/
@[simp] theorem grading_normalConeCone :
    (normalConeCone i).grading = (conormalAlgebra i).algebra :=
  rfl

end NormalCone

/-! ### The canonical morphism, over the base -/

/-- The canonical morphism `C_ZX ⟶ N_ZX` of Tag 0637 is a morphism over `Z` for the projection
`Stacks.Conormal.normalBundleToBase` named here. -/
theorem normalConeToNormalBundle_normalBundleToBase :
    normalConeToNormalBundle i ≫ normalBundleToBase i = normalConeToBase i :=
  normalConeToNormalBundle_toBase i

end Stacks.Conormal

/-! ### Tag registration for the normal cone

`Stacks.Conormal.normalCone` is an existing library declaration, so Tag 0636's naming of the cone
is registered against it with `add_to_stacks` rather than by editing its defining module. -/

add_to_stacks 0636 "the normal cone C_ZX = Spec_Z(C_{Z/X,*})" Stacks.Conormal.normalCone

end
