module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEquivalence
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.DegreeOnePiece
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vector bundle associated to a quasi-coherent module

Let `S` be a scheme. This file constructs the cone `Spec_S(𝒜)` of a quasi-coherent sheaf of
graded `𝒪_S`-algebras `𝒜` concentrated in nonnegative degrees with `𝒜_0 = 𝒪_S`, as an
`AlgebraicGeometry.AbstractCone`; applied to `𝒜 = Sym(ℰ)` it is `𝐕(ℰ)`, whose degree-one piece
is `ℰ`, and that cone is **the vector bundle `𝐕(ℰ)` of Tag 01M2** in the sense of Tag 062M.

The same construction is the essential-surjectivity clause of Tag 062N, which asserts that the
category of vector bundles over `S` is anti-equivalent to the category of quasi-coherent
`𝒪_S`-modules: every quasi-coherent `ℰ` is the degree-one piece of `𝐕(ℰ)`. That clause, and the
anti-equivalence it completes, are not assembled here — only `𝐕(ℰ)` itself, which is what the
normal bundle of Tag 0636 is built from.

## Main definitions

* `AlgebraicGeometry.GradedAlgebraCone.projection` is the projection `Spec_S(𝒜) ⟶ S`,
  `AlgebraicGeometry.GradedAlgebraCone.ringIso` the identification of `π_* 𝒪` with the ungraded
  realization of `𝒜` as sheaves of rings, and `AlgebraicGeometry.GradedAlgebraCone.ι` the
  inclusion of the homogeneous piece of degree `n` into `π_* 𝒪`.
* `AlgebraicGeometry.GradedAlgebraCone.cone` is **the cone over `S` carried by `Spec_S(𝒜)`**.
* `AlgebraicGeometry.AbstractCone.symmetricPresentation` is the presentation of a quasi-coherent
  `𝒪_S`-module `ℰ` as the degree-one piece of the cone `𝐕(ℰ) = Spec_S(Sym(ℰ))`.
* `AlgebraicGeometry.VectorBundle.ofModule` is **the vector bundle associated to `ℰ` of Tag
  01M2**, `𝐕(ℰ) = Spec_S(Sym(ℰ))` read as a vector bundle over `S` in the sense of Tag 062M; its
  total space is `AlgebraicGeometry.Scheme.Modules.vectorBundle` and its projection
  `vectorBundleToBase`, both on the nose.

## Main results

* `AlgebraicGeometry.GradedAlgebraCone.decomposition_unique`: **a finite homogeneous
  decomposition of a local section of `π_* 𝒪` is unique**, over an arbitrary open. This is the
  clause that needed `Stacks.isSeparated_directSum_sheaves`.

## Implementation notes

### Which ungraded realization

There are two ungraded realizations of a sheaf of graded algebras in this library, and the one
used here is `Stacks.RelativeSpec.gradedAlgebraSheaf`, the `RingCat`-sheafification
`SheafOfModules.GradedAlgebra.ungradedSheaf` upgraded to `CommRingCat` without re-sheafifying.
That is the realization whose multiplication is computed on homogeneous local sections by
`SheafOfModules.GradedAlgebra.ungradedIncl_mul`, which is what the axioms `ι_mul` and `ι_zero`
of a cone are. It is also the realization `Sym(ℰ)` is put into by
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`, so `𝐕(ℰ)` is literally the cone built
here. The other realization, `Stacks.RelativeSpec.ungradedAlgebraSheaf`, is the one
`StacksFrontier.AlgebraicGeometry.Constructions.ConeOfGradedAlgebra` uses; the comparison of the
two is only as sheaves of rings, so nothing is transported across it.

### How the inclusions are built

`AlgebraicGeometry.GradedAlgebraCone.ι n` sends a homogeneous local section to its image under
the sheafification unit, read through the identification
`AlgebraicGeometry.GradedAlgebraCone.ringIso` of Tag 01LX(3). Its `𝒪_S`-linearity is the
multiplicativity of that identification together with its compatibility with the two structure
morphisms: a scalar multiple of a homogeneous section is the product with the image of the
scalar under the structure map of the realization
(`SheafOfModules.GradedAlgebra.ungradedIncl_smul`), and the identification carries that image to
the pullback of functions
(`AlgebraicGeometry.GradedAlgebraCone.ringIso_inv_structureMap`). The isomorphism of *modules*
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso` is deliberately not used: its sections
carry an `eqToHom` along an equality of restriction-of-scalars objects, and multiplicativity
cannot be read off it.

### Where the separatedness of a direct sum enters

`AlgebraicGeometry.AbstractCone.decomposition_unique` asks for injectivity of the sum map
`⨁_n 𝒜_n(U) ⟶ Γ(Spec_S(𝒜), π⁻¹U)` over an *arbitrary* open `U`. That map is the sheafification
unit of the objectwise direct sum followed by an isomorphism, so the content is injectivity of
the unit over an arbitrary object, which is
`SheafOfModules.GradedAlgebra.injective_ungradedUnit`. Bijectivity of the same unit is false
over a general open — sections of a sheafified direct sum need not be finitely supported — and
`Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app` gives it only over a
quasi-compact object; injectivity needs no such hypothesis.

## References

* [Stacks Project, Tag 062N](https://stacks.math.columbia.edu/tag/062N)
* [Stacks Project, Tag 062M](https://stacks.math.columbia.edu/tag/062M)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

namespace AlgebraicGeometry

universe u

namespace GradedAlgebraCone

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc)]

/-- The projection `Spec_S(𝒜) ⟶ S` of the relative spectrum of the ungraded realization of a
sheaf of graded algebras. -/
def projection : relativeSpec (gradedAlgebraSheaf X A hc) ⟶ X :=
  relativeSpecToBase (gradedAlgebraSheaf X A hc)

/-- The projection of the relative spectrum of a quasi-coherent algebra is affine. -/
instance isAffineHom_projection : IsAffineHom (projection X A hc) :=
  isAffineHom_relativeSpecToBase (gradedAlgebraSheaf X A hc)

/-- **The direct image `π_* 𝒪` of the relative spectrum of the ungraded realization of a sheaf of
graded algebras is that realization**, as sheaves of rings. This is Tag 01LX(3) read on the
underlying sheaves of rings. -/
def ringIso :
    AlgebraSheaf.ringSheaf (pushforwardAlgebra (projection X A hc)) ≅ A.ungradedSheaf :=
  AlgebraSheaf.ringSheafIso (pushforwardAlgebraIso (gradedAlgebraSheaf X A hc))

/-- The identification of `π_* 𝒪` with the ungraded realization carries the structure map
`r ↦ r • 1` of the realization to the pullback of functions along the projection. -/
theorem ringIso_inv_structureMap (U : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U) :
    ((ringIso X A hc).inv.hom.app U).hom ((A.ungradedStructureMap.hom.app U).hom r) =
      ((AlgebraSheaf.structureMap (pushforwardAlgebra (projection X A hc))).hom.app U).hom r :=
  congrArg (fun k : X.ringCatSheaf ⟶
      AlgebraSheaf.ringSheaf (pushforwardAlgebra (projection X A hc)) => (k.hom.app U).hom r)
    (AlgebraSheaf.structureMap_comp_ringSheafMap
      (pushforwardAlgebraIso (gradedAlgebraSheaf X A hc)).inv)

/-- An isomorphism of sheaves of rings followed by its inverse is the identity on sections. -/
private theorem inv_app_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J RingCat} (e : F ≅ G) (U : Cᵒᵖ) (a : F.obj.obj U) :
    (e.inv.hom.app U).hom ((e.hom.hom.app U).hom a) = a :=
  congrArg (fun k : F ⟶ F => (k.hom.app U).hom a) e.hom_inv_id

/-- The identification of `π_* 𝒪` with the ungraded realization is injective on sections, being
an isomorphism. -/
theorem injective_ringIso_inv_app (U : (Opens ↥X)ᵒᵖ) :
    Function.Injective ((ringIso X A hc).inv.hom.app U).hom :=
  fun a b hab =>
    (inv_app_hom_app_apply (ringIso X A hc).symm U a).symm.trans
      ((congrArg _ hab).trans (inv_app_hom_app_apply (ringIso X A hc).symm U b))

/-- **The inclusion of the homogeneous piece of degree `n` into the direct image `π_* 𝒪`**: a
homogeneous local section goes to the function it is. -/
def ι (n : ℤ) :
    A.piece n ⟶ Stacks.Morphisms.pushforwardStructureSheaf (projection X A hc) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := (A.piece n).val.obj U)
        (Y := (Stacks.Morphisms.pushforwardStructureSheaf (projection X A hc)).val.obj U)
        { toFun := fun x => ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl n x)
          map_add' := fun x y => by
            rw [A.ungradedIncl_add, map_add]
            rfl
          map_smul' := fun r x => by
            rw [A.ungradedIncl_smul, map_mul, ringIso_inv_structureMap]
            rfl }
      naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun x =>
        (congrArg (fun z : A.ungradedSheaf.obj.obj V =>
              ((ringIso X A hc).inv.hom.app V).hom z)
            (A.ungradedIncl_naturality f n x)).symm.trans
          (NatTrans.naturality_apply (ringIso X A hc).inv.hom f (A.ungradedIncl n x))) }

/-- The inclusion `ι n` sends a section `x` of the degree-`n` piece to the image of
`A.ungradedIncl n x` under the identification of the ungraded algebra with `π_* 𝒪`. -/
@[simp] theorem ι_app (n : ℤ) (U : (Opens ↥X)ᵒᵖ) (x : (A.piece n).val.obj U) :
    (ι X A hc n).val.app U x =
      ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl n x) := rfl

/-- The inclusions turn the graded multiplication into the multiplication of `π_* 𝒪`: that is
the multiplicativity of the sheafification unit, read through the identification. -/
theorem ι_mul_apply (i j : ℤ) (U : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj U)
    (b : (A.piece j).val.obj U) :
    ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl (i + j) ((A.mul i j).app U a b)) =
      ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl i a) *
        ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl j b) := by
  rw [← A.ungradedIncl_mul, map_mul]

variable (pz : A.piece 0 ≅ SheafOfModules.unit X.ringCatSheaf)
  (hpz : ∀ U : (Opens ↥X)ᵒᵖ, pz.hom.val.app U (A.one.eval U) = (1 : X.ringCatSheaf.obj.obj U))

include pz hpz in
/-- The inclusion of the degree-zero piece is the structure map `𝒪_S ⟶ π_* 𝒪`: a degree-zero
local section is a multiple of the algebra unit, and a multiple of the unit is the image of that
scalar. -/
theorem ι_zero_apply (U : (Opens ↥X)ᵒᵖ) (a : (A.piece 0).val.obj U)
    (r : X.ringCatSheaf.obj.obj U) (hr : pz.hom.val.app U a = r) :
    ((ringIso X A hc).inv.hom.app U).hom (A.ungradedIncl 0 a) =
      ((AlgebraSheaf.structureMap (pushforwardAlgebra (projection X A hc))).hom.app U).hom r := by
  have ha : r • A.one.eval U = a :=
    SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit A pz hpz U a r hr
  rw [← ha, A.ungradedIncl_smul_one, ringIso_inv_structureMap]

include pz hpz in
/-- The degree-zero identification respects multiplication: degree-zero local sections are
multiples of the algebra unit, which is idempotent. -/
theorem degreeZero_mul_apply (U : (Opens ↥X)ᵒᵖ) (a b : (A.piece 0).val.obj U)
    (r s : X.ringCatSheaf.obj.obj U) (hr : pz.hom.val.app U a = r)
    (hs : pz.hom.val.app U b = s) :
    pz.hom.val.app U ((A.mul 0 0).app U a b) = r * s := by
  have ha : r • A.one.eval U = a :=
    SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit A pz hpz U a r hr
  have hb : s • A.one.eval U = b :=
    SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit A pz hpz U b s hs
  have hone : (A.mul 0 0).app U (A.one.eval U) (A.one.eval U) = A.one.eval U :=
    eq_of_heq (A.mul_one 0 U (A.one.eval U))
  rw [← ha, ← hb, (A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right, hone, map_smul,
    map_smul, hpz]
  show r * (s * (1 : X.ringCatSheaf.obj.obj U)) = r * s
  rw [_root_.mul_one]

/-- The sum of a finitely supported family of homogeneous local sections inside `π_* 𝒪`, as the
sheafification unit of the ungraded realization followed by the identification. -/
def sumHom (U : X.Opens) :
    A.toPresheafGradedAlgebra.Total (op U) →+
      (Stacks.Morphisms.pushforwardStructureSheaf (projection X A hc)).val.obj (op U) :=
  (((ringIso X A hc).inv.hom.app (op U)).hom.toAddMonoidHom).comp
    (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat))
      (op U)).toAddMonoidHom

/-- The finite-support sum of homogeneous local sections used by `AbstractCone` is the
sheafification unit followed by the identification. -/
theorem pushforwardHomogeneousSum_eq (U : X.Opens) :
    pushforwardHomogeneousSum (projection X A hc) A (ι X A hc) U = sumHom X A hc U := by
  refine DFinsupp.addHom_ext fun n x => ?_
  simp only [pushforwardHomogeneousSum, DFinsupp.sumAddHom_single]
  rfl

/-- **A finite homogeneous decomposition of a local section of `π_* 𝒪` is unique**, over an
arbitrary open. The sum map is the sheafification unit of the objectwise direct sum of the
homogeneous pieces followed by an isomorphism, and that unit is injective on sections over every
open because an objectwise direct sum of sheaves is a separated presheaf. -/
theorem decomposition_unique (U : X.Opens) :
    Function.Injective (pushforwardHomogeneousSum (projection X A hc) A (ι X A hc) U) := by
  intro z z' h
  have h1 : sumHom X A hc U z = sumHom X A hc U z' :=
    (DFunLike.congr_fun (pushforwardHomogeneousSum_eq X A hc U) z).symm.trans
      (h.trans (DFunLike.congr_fun (pushforwardHomogeneousSum_eq X A hc U) z'))
  exact A.injective_ungradedUnit (Stacks.RelativeSpec.isLocallyInjective_toTotalSheaf X A) (op U)
    (injective_ringIso_inv_app X A hc (op U) h1)

/-- **Every local section of `π_* 𝒪` is locally a finite sum of homogeneous sections.** The
direct image is the sheafification of the ungraded realization, so the sheafification unit is
locally surjective. -/
theorem decomposition_locally (U : X.Opens)
    (a : (Stacks.Morphisms.pushforwardStructureSheaf (projection X A hc)).val.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : Π₀ n : ℤ, (A.piece n).val.obj (op V),
        pushforwardHomogeneousSum (projection X A hc) A (ι X A hc) V s =
          (Stacks.Morphisms.pushforwardStructureSheaf
            (projection X A hc)).val.map (homOfLE hVU).op a := by
  obtain ⟨V, f, ⟨s, hs⟩, hxV⟩ :=
    (Stacks.RelativeSpec.isLocallySurjective_toTotalSheaf X A).imageSieve_mem
      (((ringIso X A hc).hom.hom.app (op U)).hom a) x hx
  refine ⟨V, leOfHom f, hxV, s, ?_⟩
  have key : A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat))
        (op V) s =
      (A.ungradedSheaf.obj.map f.op).hom (((ringIso X A hc).hom.hom.app (op U)).hom a) := hs
  refine Eq.trans (DFunLike.congr_fun (pushforwardHomogeneousSum_eq X A hc V) s) ?_
  show ((ringIso X A hc).inv.hom.app (op V)).hom
      (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) (op V) s) = _
  rw [key]
  refine Eq.trans (NatTrans.naturality_apply (ringIso X A hc).inv.hom f.op _) ?_
  exact congrArg _ (inv_app_hom_app_apply (ringIso X A hc) (op U) a)

include pz hpz in
/-- **The cone over `S` carried by the relative spectrum of the ungraded realization of a
quasi-coherent sheaf of graded algebras** concentrated in nonnegative degrees whose degree-zero
piece is the structure sheaf. -/
def cone (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) : AbstractCone X where
  C := relativeSpec (gradedAlgebraSheaf X A hc)
  π := projection X A hc
  isAffine := isAffineHom_projection X A hc
  grading := A
  ι := ι X A hc
  decomposition_unique := decomposition_unique X A hc
  decomposition_locally := decomposition_locally X A hc
  ι_mul i j U a b := ι_mul_apply X A hc i j (op U) a b
  negative_isZero := hzero
  degreeZero := pz
  degreeZero_mul U a b := degreeZero_mul_apply X A pz hpz (op U) a b _ _ rfl rfl
  degreeZero_one U := hpz (op U)
  ι_zero U a := ι_zero_apply X A hc pz hpz (op U) a _ rfl

/-- The grading of the cone `Spec_X(A)` is the graded algebra `A`. -/
@[simp] theorem cone_grading (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (cone X A hc pz hpz hzero).grading = A := rfl

end GradedAlgebraCone

/-! ### The cone `𝐕(ℰ) = Spec_S(Sym(ℰ))` of a quasi-coherent module -/

namespace AbstractCone

variable (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf) [E.IsQuasicoherent]

/-- Quasi-coherence of `Sym(ℰ)` in the spelling the cone construction takes it: the instance of
Tag 01CK is stated for `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`, whose head
symbol instance search does not unfold to `Stacks.RelativeSpec.gradedAlgebraSheaf`. -/
theorem isQuasicoherent_gradedAlgebraSheaf_symmetricAlgebra :
    AlgebraSheaf.IsQuasicoherent
      (gradedAlgebraSheaf S (Scheme.Modules.symmetricAlgebra S E)
        (Scheme.Modules.symmetricAlgebra_mul_comm S E)) :=
  Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf S E

omit [E.IsQuasicoherent] in
/-- The degree-zero identification of `Sym(ℰ)` carries the algebra unit to `1`. -/
theorem symmetricAlgebraPieceZeroIso_hom_one (U : (Opens ↥S)ᵒᵖ) :
    (Scheme.Modules.symmetricAlgebraPieceZeroIso S E).hom.val.app U
        ((Scheme.Modules.symmetricAlgebra S E).one.eval U) =
      (1 : S.ringCatSheaf.obj.obj U) :=
  @PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso_hom_one.{u, u, u} _ _ _ S.sheaf.obj
    S.ringCatSheaf (𝟙 S.ringCatSheaf.obj)
    (Scheme.Modules.isLocallyInjective_id_ringCatSheaf S)
    (Scheme.Modules.isLocallySurjective_id_ringCatSheaf S)
    inferInstance inferInstance E.val U

/-- **The cone `𝐕(ℰ) = Spec_S(Sym(ℰ))` over `S` attached to a quasi-coherent `𝒪_S`-module**, the
relative spectrum of the symmetric algebra of `ℰ` with the grading of its direct-image algebra by
the symmetric powers `Symⁿ ℰ`. -/
@[ega "IV 18.5.2"]
def symmetricCone : AbstractCone S :=
  haveI := isQuasicoherent_gradedAlgebraSheaf_symmetricAlgebra S E
  GradedAlgebraCone.cone S (Scheme.Modules.symmetricAlgebra S E)
    (Scheme.Modules.symmetricAlgebra_mul_comm S E)
    (Scheme.Modules.symmetricAlgebraPieceZeroIso S E)
    (symmetricAlgebraPieceZeroIso_hom_one S E)
    (fun n hn => Scheme.Modules.isZero_symmetricAlgebra_piece S E n hn)

/-- The total space of the cone attached to `ℰ` is the vector bundle `𝐕(ℰ)` of Tag 01M2. -/
@[simp] theorem C_symmetricCone : (symmetricCone S E).C = Scheme.Modules.vectorBundle S E := rfl

/-- The grading of the cone attached to `ℰ` is `Sym(ℰ)`. -/
@[simp] theorem grading_symmetricCone :
    (symmetricCone S E).grading = Scheme.Modules.symmetricAlgebra S E := rfl

/-- **Every quasi-coherent `𝒪_S`-module is the degree-one piece of a cone whose direct-image
algebra is its symmetric algebra**, namely of `𝐕(ℰ) = Spec_S(Sym(ℰ))`. This is the data whose
existence is the essential surjectivity of `V ↦ ℰ_1`. -/
def symmetricPresentation : SymmetricPresentation S E where
  cone := symmetricCone S E
  gen := Scheme.Modules.symmetricAlgebraGen S E
  isIso_gen := Scheme.Modules.isIso_symmetricAlgebraGen S E
  isSymmetricAlgebra := Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S E

end AbstractCone

/-! ### The vector bundle associated to a quasi-coherent module -/

namespace VectorBundle

section OfModule

variable (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf) [E.IsQuasicoherent]

/-- **Stacks Project, Tag 01M2.**  *The vector bundle associated to a quasi-coherent
`𝒪_S`-module `ℰ`*, `𝐕(ℰ) = Spec_S(Sym(ℰ))`, as a vector bundle over `S` in the sense of Tag
062M: the relative spectrum of `Sym(ℰ)`, with the grading of its direct-image algebra by the
symmetric powers `Symⁿ ℰ`, whose canonical maps `Symⁿ(ℰ_1) ⟶ ℰ_n` are isomorphisms because the
degree-one piece is `ℰ` itself.

Its total space is `AlgebraicGeometry.Scheme.Modules.vectorBundle` and its projection is
`AlgebraicGeometry.Scheme.Modules.vectorBundleToBase`, by `VectorBundle.C_ofModule` and
`VectorBundle.π_ofModule`.  Following EGA II, Definition 1.7.8, `ℰ` is not assumed finite locally
free. -/
@[ega "II 1.7.8",
  ega "II 8.4.1",
  ega "IV 16.4.7",
  ega "IV 18.5.2",
  sga "3 I 4.6.3.1" "partial",
  sga "6 VIII 5.2"]
def ofModule : VectorBundle S := (AbstractCone.symmetricPresentation S E).vectorBundle

/-- The total space of the vector bundle associated to `ℰ` is `𝐕(ℰ) = Spec_S(Sym(ℰ))`. -/
@[simp] theorem C_ofModule : (ofModule S E).C = Scheme.Modules.vectorBundle S E := rfl

/-- The projection of the vector bundle associated to `ℰ` is the projection of
`𝐕(ℰ) = Spec_S(Sym(ℰ))` to `S`. -/
@[simp] theorem π_ofModule : (ofModule S E).π = Scheme.Modules.vectorBundleToBase S E := rfl

/-- The direct-image algebra of the vector bundle associated to `ℰ` is `Sym(ℰ)`. -/
@[simp] theorem grading_ofModule :
    (ofModule S E).grading = Scheme.Modules.symmetricAlgebra S E := rfl

/-- The degree-one piece of the vector bundle associated to `ℰ` is `ℰ`. -/
def pieceOneIsoOfModule : E ≅ (ofModule S E).grading.piece 1 :=
  (AbstractCone.symmetricPresentation S E).pieceOneIso

end OfModule

/-- The functor `V ↦ (π_* 𝒪_V)_1` from vector bundles over `S` to quasi-coherent
`𝒪_S`-modules is essentially surjective. -/
instance essSurj_degreeOneFunctor' (S : Scheme.{u}) : (degreeOneFunctor S).EssSurj :=
  essSurj_degreeOneFunctor S fun E hE =>
    haveI := hE
    AbstractCone.symmetricPresentation S E

/-- The functor `V ↦ ℰ_1` is an equivalence: it is faithful, full and essentially surjective. -/
instance isEquivalence_degreeOneFunctor (S : Scheme.{u}) :
    (degreeOneFunctor S).IsEquivalence where

/-- The category of vector bundles over a scheme `S` is anti-equivalent to the category of
quasi-coherent `𝒪_S`-modules.

The anti-equivalence is recorded in the contravariant form `(VectorBundle S)ᵒᵖ ≌ QCoh(𝒪_S)`, the
functor being `V ↦ (π_* 𝒪_V)_1` and its quasi-inverse `ℰ ↦ 𝐕(ℰ) = Spec_S(Sym(ℰ))`. Of the two
standard forms of an anti-equivalence this is the one with the opposite taken on the *geometric*
side, which is the side the source's two functors are contravariant on, and it is the form of
Tag 01SA's `(AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S` that this one restricts. -/
@[stacks 062N "the anti-equivalence between vector bundles over S and quasi-coherent O_S-modules"]
def degreeOneEquivalence (S : Scheme.{u}) :
    (VectorBundle S)ᵒᵖ ≌ Scheme.QuasicoherentModules S :=
  (degreeOneFunctor S).asEquivalence

/-- The functor of `degreeOneEquivalence S` is `degreeOneFunctor S`. -/
@[simp] theorem degreeOneEquivalence_functor (S : Scheme.{u}) :
    (degreeOneEquivalence S).functor = degreeOneFunctor S := rfl

end VectorBundle

end AlgebraicGeometry

end
