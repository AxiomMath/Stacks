module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.QcohExtension
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport

/-!
# The quotient of a sheaf-level graded algebra by a graded ideal

Situation 01NN fixes a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`. Tags 0801 and
0802 both name the quotient `𝒜/ℐ` of `𝒜` by a graded ideal `ℐ`. **This file constructs it**, as
the degreewise sheafification of the sectionwise quotient, together with the quotient
homomorphism `𝒜 ⟶ 𝒜/ℐ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.presheafMul`: the multiplication of `𝒜` as a
  bilinear map of the underlying presheaves of modules.
* `…preQuotPiece` and `…preQuotProj`: the sectionwise quotient `U ↦ Γ(U, 𝒜_n)/ℐ_n(U)` and its
  projection.
* `…quotMul`, `…preQuotOne` and `…quotPresheafAlgebra`: the sectionwise quotient as a graded algebra
  of presheaves of modules.
* `…quotSheafAlgebra`: **`𝒜/ℐ` as a sheaf of graded `𝒪_S`-algebras**, the degreewise
  sheafification of the sectionwise quotient.
* `…IsQuasicoherentQuotPieces`: quasi-coherence of its homogeneous pieces.
* `…coforkDesc`: the morphism out of `(𝒜/ℐ)_n` determined by a cokernel cofork.
* `…quotSheafGradedAlgebra`: `𝒜/ℐ` as the input of the relative Proj construction, given that
  hypothesis, and `…quotMk` the quotient homomorphism.
* `…quotShortComplex`: the short complex `ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ℐ)_n`.
* `…quotAmbientHom`: **`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`**, the relative analogue of
  `Stacks.ClosedSubschemeProjQuotient.ambientHom`.

## Main results

* `…piece_mul_mem_right`: **a graded ideal absorbs multiplication in the second variable
  too**, which is what lets the multiplication descend in both variables.
* `…preQuotProj_app_eq_zero_iff`: a local section of `𝒜_n` dies in the *sectionwise* quotient
  exactly when it lies in `ℐ_n`.
* `…quotMul_comm` and `…isCommutative_quotSheafAlgebra`: the multiplication of the quotient is
  commutative, sectionwise and after sheafification.
* `…vanishesInNegativeDegrees_quotSheafAlgebra`: the quotient is concentrated in nonnegative
  degrees.
* `…quotSheafAlgebra_mul_unit`: the multiplication of `𝒜/ℐ` on the unit-images of two classes.
* `…quotMkAppIsColimit`: **`(𝒜/ℐ)_n` is a cokernel of the inclusion `ℐ_n ⟶ 𝒜_n`**, with the
  degree-`n` component of the quotient homomorphism as the projection.
* `…isQuasicoherentQuotPieces`: the pieces of `𝒜/ℐ` are quasi-coherent when those of `ℐ` are.
* `…shortExact_quotShortComplex`: **`ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ℐ)_n` is short exact.**
* `…surjective_quotMkApp_app` and `…surjectiveOnAffineSections_quotMk`: the quotient
  homomorphism is surjective on the sections over an affine open of the base, which is the
  `surjective` clause of `…GradedQuotientPresentation`.
* `…isClosedImmersion_quotAmbientHom`: **`Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.**
* `…quotMkApp_app_eq_zero_iff`: **the kernel clause** — a local section of `𝒜_n` dies in
  `(𝒜/ℐ)_n` exactly when it lies in `ℐ_n`, over every open of the base.

## Implementation notes

**Why the sheafification route.** `SheafGradedAlgebra.mul` is a map on *sections*, and the
sections of a cokernel of sheaves of modules are not the quotient of the sections, so the
multiplication of `𝒜/ℐ` cannot be written down degreewise from `CategoryTheory.Limits.cokernel`.
The route taken is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean` for the degreewise
cokernel of graded *modules*, and of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Scheme.lean` for the symmetric algebra: form
the quotient first at the level of presheaves, where it *is* sectionwise
(`Stacks.quotPresheaf`), and then sheafify degreewise with `Stacks.GradedAlgebra.sheafify`. The
comparison `α` that sheafification needs is the identity of the structure presheaf, which is
locally bijective because it is an isomorphism. No monoidal structure on `SheafOfModules` and no
internal hom is used.

**The bridge between the two bilinear-map types.** `SheafGradedAlgebra` carries its
multiplication as a `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap`, indexed by
`S.Opens`, while every sheafification tool is stated for `Stacks.BilinearMap`, indexed by
`(Opens S)ᵒᵖ`. The two are the same data — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Bridge.lean` — and `presheafMul` is the
conversion, with every field the given field at `X.unop`.

**Descending in both variables.** `Stacks.BilinearMap.quotDescBil` descends a bilinear map
through the sectionwise quotient in its *first* variable only. The second variable is reached by
`Stacks.BilinearMap.flip` on either side, and the hypothesis it then needs is `piece_mul_mem_right`:
that `ℐ` absorbs multiplication from the right. That is not a field of `GradedIdeal` and is not
formally symmetric to the one that is, because the two products live in the pieces of the degrees
`i + j` and `j + i`, which are propositionally but not definitionally equal; `mem_piece_congr`
carries membership across that equality.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)

## Not done here

No Stacks tag is claimed. The Stacks project introduces the graded ideal sheaf and the quotient
`𝒜/ℐ` inline, inside the statements of Tags 0801 and 0802; neither tag is stated here.

Of the five fields of `…RelativeProjGradedIdeal.GradedQuotientPresentation`, four are supplied
here — `target` is `quotSheafGradedAlgebra`, `hom` is `quotMk`, `surjective` is
`surjectiveOnAffineSections_quotMk`, and `quotAmbientHom` is the morphism `iso_comp` compares
against. The fifth, `iso`, is an equality of kernel ideal sheaves, since both morphisms are
closed immersions; the whole presentation is built from such an equality by
`…RelativeProjGradedIdeal.gradedQuotientPresentation_of_ker_eq` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/IsoClause.lean`, and **the equality itself
is proved** in `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`
(`…RelativeProjTwists.ker_eq_chartMap_ker`), so Tag 0801's relative case is formalized as
`…RelativeProjTwists.vanishingIdealPresentation` and Tag 0803 is registered unconditionally in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

Two apparent obstructions are not inputs at all. The `Submodule`-versus-`AddSubgroup` grading mismatch between the absolute
chain and `…SheafGradedAlgebra.grading` is not bridged but bypassed: every input of the absolute
chain was already stated at an `AddSubgroupClass`-valued grading, and
`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk` reassembles it there. And the
chart-level comparison of the relative twists and of the relative section map with the absolute
ones exists outright, as `…RelativeProjTwists.ChartData.chartIso` and
`…RelativeProjTwists.TwistData.ψ_chart`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) (ℐ : GradedIdeal 𝒜)

/-! ### The multiplication of `𝒜` as a bilinear map of presheaves of modules -/

/-- The multiplication of `𝒜`, read as a bilinear map of the underlying presheaves of modules.
The data is unchanged: a section over `U : S.Opens` is a section over `op U : (Opens S)ᵒᵖ`. -/
def presheafMul (i j : ℤ) :
    Stacks.BilinearMap (𝒜.piece i).val (𝒜.piece j).val (𝒜.piece (i + j)).val where
  app X := (𝒜.mul i j).app X.unop
  map_smul_left X r x y := (𝒜.mul i j).map_smul_left X.unop r x y
  map_smul_right X r x y := (𝒜.mul i j).map_smul_right X.unop r x y
  naturality f x y := (𝒜.mul i j).naturality (leOfHom f.unop) x y

/-- `presheafMul` evaluated at `op U` is the multiplication of `𝒜` over `U`. -/
@[simp]
theorem presheafMul_app (i j : ℤ) (U : S.Opens) :
    (presheafMul 𝒜 i j).app (op U) = (𝒜.mul i j).app U := rfl

/-! ### Membership in a graded ideal, transported along an equality of degrees -/

/-- Membership in a graded ideal transported along an equality of degrees: the two sections are
heterogeneously equal and live in the pieces of the two equal degrees. -/
theorem mem_piece_congr {m n : ℤ} (h : m = n) (U : S.Opens) {x : Γ(𝒜.piece m, U)}
    {y : Γ(𝒜.piece n, U)} (hxy : HEq x y)
    (hx : x ∈ (ℐ.piece m).toSubmodule.obj (op U)) :
    y ∈ (ℐ.piece n).toSubmodule.obj (op U) := by
  subst h
  rw [← eq_of_heq hxy]
  exact hx

/-- **A graded ideal absorbs multiplication in the second variable too.** This is
`GradedIdeal.mul_mem` read through the commutativity of `𝒜`, whose two sides live in the pieces
of the degrees `i + j` and `j + i`. -/
theorem piece_mul_mem_right (i j : ℤ) (U : S.Opens) (a : Γ(𝒜.piece i, U)) {x : Γ(𝒜.piece j, U)}
    (hx : x ∈ (ℐ.piece j).toSubmodule.obj (op U)) :
    (𝒜.mul i j).app U a x ∈ (ℐ.piece (i + j)).toSubmodule.obj (op U) :=
  mem_piece_congr 𝒜 ℐ (add_comm j i) U (𝒜.mul_comm j i U x a) (ℐ.mul_mem j i U hx a)

/-! ### The sectionwise quotient -/

/-- The degree-`n` piece of the sectionwise quotient of `𝒜` by `ℐ`: the presheaf of modules
`U ↦ Γ(U, 𝒜_n)/ℐ_n(U)`. -/
def preQuotPiece (n : ℤ) : PresheafOfModules.{u} S.ringCatSheaf.obj :=
  Stacks.quotPresheaf (ℐ.piece n).ι.val

/-- The projection of `𝒜_n` onto the degree-`n` piece of the sectionwise quotient. -/
def preQuotProj (n : ℤ) : (𝒜.piece n).val ⟶ preQuotPiece 𝒜 ℐ n :=
  Stacks.quotπ (ℐ.piece n).ι.val

/-- Membership in a submodule over `U` means being the image of a section of the submodule. -/
private theorem mem_iff_exists_ι_app {M : S.Modules} (N : M.Submodule) (U : S.Opens)
    (a : M.val.obj (op U)) : a ∈ N.toSubmodule.obj (op U) ↔ ∃ x, N.ι.val.app (op U) x = a := by
  rw [← AlgebraicGeometry.range_submodule_ι_app N U]
  exact LinearMap.mem_range

/-- The projection onto the sectionwise quotient is surjective on the sections over every open. -/
theorem preQuotProj_surjective (n : ℤ) (U : S.Opens) :
    Function.Surjective ((preQuotProj 𝒜 ℐ n).app (op U)) :=
  Stacks.quotπ_surjective _ _

/-- **A local section of `𝒜_n` dies in the sectionwise quotient exactly when it lies in `ℐ_n`.**
-/
theorem preQuotProj_app_eq_zero_iff (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U)) :
    (preQuotProj 𝒜 ℐ n).app (op U) a = 0 ↔ a ∈ (ℐ.piece n).toSubmodule.obj (op U) :=
  (Stacks.quotπ_eq_zero_iff (ℐ.piece n).ι.val a).trans
    (Iff.of_eq (congrArg (fun N : _root_.Submodule Γ(S, U) Γ(𝒜.piece n, U) => a ∈ N)
      (AlgebraicGeometry.range_submodule_ι_app (ℐ.piece n) U)))

/-- A local section of a submodule, read in the ambient module, lies in the submodule. -/
theorem ι_app_mem {M : S.Modules} (N : M.Submodule) (U : S.Opens)
    (x : Γ(N.toSheafOfModules, U)) : N.ι.val.app (op U) x ∈ N.toSubmodule.obj (op U) := by
  exact (mem_iff_exists_ι_app N U _).2 ⟨x, rfl⟩

/-! ### The multiplication of the sectionwise quotient -/

/-- The multiplication of `𝒜` followed by the projection, descended in the first variable. -/
def quotMulLeft (i j : ℤ) :
    Stacks.BilinearMap (preQuotPiece 𝒜 ℐ i) (𝒜.piece j).val (preQuotPiece 𝒜 ℐ (i + j)) :=
  Stacks.BilinearMap.quotDescBil (ℐ.piece i).ι.val
    ((presheafMul 𝒜 i j).postcomp (preQuotProj 𝒜 ℐ (i + j)))
    fun U x y =>
      (preQuotProj_app_eq_zero_iff 𝒜 ℐ (i + j) U.unop _).2
        (ℐ.mul_mem i j U.unop (ι_app_mem (ℐ.piece i) U.unop x) y)

/-- `quotMulLeft` on the class of `a` and on `b` is the class of the product `a * b`. -/
@[simp]
theorem quotMulLeft_app (i j : ℤ) (U : S.Opens) (a : Γ(𝒜.piece i, U)) (b : Γ(𝒜.piece j, U)) :
    (quotMulLeft 𝒜 ℐ i j).app (op U) ((preQuotProj 𝒜 ℐ i).app (op U) a) b =
      (preQuotProj 𝒜 ℐ (i + j)).app (op U) ((𝒜.mul i j).app U a b) := rfl

/-- **The multiplication of the sectionwise quotient `𝒜/ℐ`**: the multiplication of `𝒜`
descended in both variables, which is possible because `ℐ` absorbs multiplication on either
side. -/
def quotMul (i j : ℤ) :
    Stacks.BilinearMap (preQuotPiece 𝒜 ℐ i) (preQuotPiece 𝒜 ℐ j) (preQuotPiece 𝒜 ℐ (i + j)) :=
  (Stacks.BilinearMap.quotDescBil (ℐ.piece j).ι.val (quotMulLeft 𝒜 ℐ i j).flip
    (by
      intro U x y
      obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece i).ι.val U y
      exact (preQuotProj_app_eq_zero_iff 𝒜 ℐ (i + j) U.unop _).2
        (piece_mul_mem_right 𝒜 ℐ i j U.unop a (ι_app_mem (ℐ.piece j) U.unop x)))).flip

/-- The multiplication of the sectionwise quotient on the classes of `a` and `b` is the class of
the product `a * b`. -/
@[simp]
theorem quotMul_app (i j : ℤ) (U : S.Opens) (a : Γ(𝒜.piece i, U)) (b : Γ(𝒜.piece j, U)) :
    (quotMul 𝒜 ℐ i j).app (op U) ((preQuotProj 𝒜 ℐ i).app (op U) a)
        ((preQuotProj 𝒜 ℐ j).app (op U) b) =
      (preQuotProj 𝒜 ℐ (i + j)).app (op U) ((𝒜.mul i j).app U a b) := rfl

/-- The unit of the sectionwise quotient: the class of the unit of `𝒜`. -/
def preQuotOne : (preQuotPiece 𝒜 ℐ 0).sections :=
  PresheafOfModules.sectionsMk (fun X => (preQuotProj 𝒜 ℐ 0).app X (𝒜.one X.unop))
    fun {X Y} f => by
      rw [show (preQuotPiece 𝒜 ℐ 0).map f ((preQuotProj 𝒜 ℐ 0).app X (𝒜.one X.unop)) =
          (preQuotProj 𝒜 ℐ 0).app Y ((𝒜.piece 0).val.map f (𝒜.one X.unop)) from
        Stacks.restr_quotπ (ℐ.piece 0).ι.val f (𝒜.one X.unop)]
      exact congrArg ((preQuotProj 𝒜 ℐ 0).app Y) (𝒜.one_res (leOfHom f.unop))

/-- The unit of the sectionwise quotient, over `U`, is the class of the unit of `𝒜` over `U`. -/
@[simp]
theorem preQuotOne_eval (U : S.Opens) :
    (preQuotOne 𝒜 ℐ).eval (op U) = (preQuotProj 𝒜 ℐ 0).app (op U) (𝒜.one U) := rfl

/-! ### The sectionwise quotient as a graded algebra of presheaves of modules -/

/-- **The sectionwise quotient `𝒜/ℐ`**, as a graded algebra of presheaves of modules: in degree
`n` the presheaf `U ↦ Γ(U, 𝒜_n)/ℐ_n(U)`, with the multiplication and unit of `𝒜`. -/
def quotPresheafAlgebra : Stacks.GradedAlgebra (preQuotPiece 𝒜 ℐ) where
  mul := quotMul 𝒜 ℐ
  one := preQuotOne 𝒜 ℐ
  mul_assoc i j k X x y z := by
    obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece i).ι.val X x
    obtain ⟨b, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece j).ι.val X y
    obtain ⟨c, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece k).ι.val X z
    exact Stacks.heq_apply _ _ (fun n s => (preQuotProj 𝒜 ℐ n).app X s) (add_assoc i j k)
      (𝒜.mul_assoc i j k X.unop a b c)
  one_mul i X x := by
    obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece i).ι.val X x
    exact Stacks.heq_apply _ _ (fun n s => (preQuotProj 𝒜 ℐ n).app X s) (zero_add i)
      (𝒜.one_mul i X.unop a)
  mul_one i X x := by
    obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece i).ι.val X x
    exact Stacks.heq_apply _ _ (fun n s => (preQuotProj 𝒜 ℐ n).app X s) (add_zero i)
      (𝒜.mul_one i X.unop a)

/-- The multiplication of `quotPresheafAlgebra` is `quotMul`. -/
@[simp]
theorem quotPresheafAlgebra_mul (i j : ℤ) : (quotPresheafAlgebra 𝒜 ℐ).mul i j = quotMul 𝒜 ℐ i j :=
  rfl

/-- The unit of `quotPresheafAlgebra` is `preQuotOne`. -/
@[simp]
theorem quotPresheafAlgebra_one : (quotPresheafAlgebra 𝒜 ℐ).one = preQuotOne 𝒜 ℐ := rfl

/-- **The multiplication of the sectionwise quotient is commutative**, in every pair of degrees:
the two sides are the classes of the two sides of the commutativity of `𝒜`, which live in the
pieces of the degrees `i + j` and `j + i`. -/
theorem quotMul_comm (i j : ℤ) (X : (S.Opens)ᵒᵖ) (x : (preQuotPiece 𝒜 ℐ i).obj X)
    (y : (preQuotPiece 𝒜 ℐ j).obj X) :
    HEq ((quotMul 𝒜 ℐ i j).app X x y) ((quotMul 𝒜 ℐ j i).app X y x) := by
  obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece i).ι.val X x
  obtain ⟨b, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece j).ι.val X y
  exact Stacks.heq_apply _ _ (fun n s => (preQuotProj 𝒜 ℐ n).app X s) (add_comm i j)
    (𝒜.mul_comm i j X.unop a b)

/-- A local section of a zero object of `S.Modules` vanishes.

`Stacks.SheafOfModules.section_eq_zero_of_isZero` says this for the category `SheafOfModules R`;
the hypothesis here is `CategoryTheory.Limits.IsZero` for the `Category` instance of
`AlgebraicGeometry.Scheme.Modules`, which is a different instance term, and the import that
carries the other statement is the whole internal-hom cohomology stack. -/
private theorem eq_zero_of_isZero {M : S.Modules} (h : IsZero M) {X : (S.Opens)ᵒᵖ}
    (a : M.val.obj X) : a = 0 :=
  congrArg (fun φ : M ⟶ M => φ.val.app X a) ((IsZero.iff_id_eq_zero M).mp h)

/-- Every local section of a negative-degree piece of the sectionwise quotient vanishes. -/
theorem preQuotPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : (S.Opens)ᵒᵖ)
    (t : (preQuotPiece 𝒜 ℐ n).obj X) : t = 0 := by
  obtain ⟨a, rfl⟩ := Stacks.quotπ_surjective (ℐ.piece n).ι.val X t
  rw [eq_zero_of_isZero (𝒜.negative_isZero n hn) a]
  exact map_zero _

/-! ### The quotient as a sheaf of graded algebras -/

/-- **The quotient `𝒜/ℐ` as a sheaf of graded `𝒪_S`-algebras**: the degreewise sheafification of
the sectionwise quotient. -/
def quotSheafAlgebra : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf :=
  (quotPresheafAlgebra 𝒜 ℐ).sheafify (𝟙 S.ringCatSheaf.obj)

/-- The degree-`n` piece is the sheafification of `U ↦ Γ(U, 𝒜_n)/ℐ_n(U)`, on the nose. -/
theorem quotSheafAlgebra_piece (n : ℤ) :
    (quotSheafAlgebra 𝒜 ℐ).piece n =
      (PresheafOfModules.sheafification (𝟙 S.ringCatSheaf.obj)).obj (preQuotPiece 𝒜 ℐ n) := rfl

/-- The multiplication of `𝒜/ℐ` on the unit-images of two classes is the unit-image of the class
of their product. -/
theorem quotSheafAlgebra_mul_unit (i j : ℤ) (X : (S.Opens)ᵒᵖ) (x : (preQuotPiece 𝒜 ℐ i).obj X)
    (y : (preQuotPiece 𝒜 ℐ j).obj X) :
    ((quotSheafAlgebra 𝒜 ℐ).mul i j).app X
        (PresheafOfModules.Hom.app
          (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ i)) X x)
        (PresheafOfModules.Hom.app
          (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ j)) X y) =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ (i + j))) X
        ((quotMul 𝒜 ℐ i j).app X x y) :=
  (quotPresheafAlgebra 𝒜 ℐ).sheafify_mul_unit (𝟙 S.ringCatSheaf.obj) i j X x y

/-- **The multiplication of `𝒜/ℐ` is commutative**, in every pair of degrees. -/
theorem isCommutative_quotSheafAlgebra : IsCommutative (quotSheafAlgebra 𝒜 ℐ) :=
  fun i j U a b =>
    Stacks.GradedAlgebra.heq_sheafify_mul_comm (𝟙 S.ringCatSheaf.obj)
      (quotPresheafAlgebra 𝒜 ℐ) (quotMul_comm 𝒜 ℐ) i j U.unop a b

/-- **`𝒜/ℐ` is concentrated in nonnegative degrees.** -/
theorem vanishesInNegativeDegrees_quotSheafAlgebra :
    VanishesInNegativeDegrees (quotSheafAlgebra 𝒜 ℐ) := by
  intro n hn U x
  refine Stacks.eq_of_isSeparated ((quotSheafAlgebra 𝒜 ℐ).piece n)
    (Stacks.liftSieve_mem (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n) x) ?_
  rintro Y f ⟨t, ht⟩
  have ht' : PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)) (op Y) t =
    ((quotSheafAlgebra 𝒜 ℐ).piece n).val.map f.op x := ht
  rw [← ht', preQuotPiece_eq_zero_of_neg 𝒜 ℐ hn (op Y) t]
  simp only [map_zero]
  rfl

/-! ### The quotient as sheaf-level graded algebra data -/

/-- **Quasi-coherence of every homogeneous piece of `𝒜/ℐ`.** This is the one hypothesis the
quotient still needs to be the input of the relative Proj construction; it holds when the pieces
of `ℐ` are quasi-coherent, by `isQuasicoherentQuotPieces`. -/
def IsQuasicoherentQuotPieces : Prop :=
  ∀ n : ℤ, (((quotSheafAlgebra 𝒜 ℐ).piece n : S.Modules)).IsQuasicoherent

variable (hqc : IsQuasicoherentQuotPieces 𝒜 ℐ)

/-- **The quotient `𝒜/ℐ` as sheaf-level graded algebra data**, the input of the relative Proj
construction: a commutative, nonnegatively graded, quasi-coherent graded `𝒪_S`-algebra. -/
def quotSheafGradedAlgebra : SheafGradedAlgebra S :=
  toSheafGradedAlgebra (quotSheafAlgebra 𝒜 ℐ) (isCommutative_quotSheafAlgebra 𝒜 ℐ)
    (vanishesInNegativeDegrees_quotSheafAlgebra 𝒜 ℐ) hqc

/-- The homogeneous pieces of `quotSheafGradedAlgebra` are those of `quotSheafAlgebra`. -/
theorem quotSheafGradedAlgebra_piece (n : ℤ) :
    (quotSheafGradedAlgebra 𝒜 ℐ hqc).piece n = (quotSheafAlgebra 𝒜 ℐ).piece n := rfl

/-! ### The quotient homomorphism -/

/-- The degree-`n` component of the quotient homomorphism `𝒜 ⟶ 𝒜/ℐ`: the class of a local
section, read in the sheafification. -/
def quotMkApp (n : ℤ) : 𝒜.piece n ⟶ (quotSheafAlgebra 𝒜 ℐ).piece n :=
  ⟨preQuotProj 𝒜 ℐ n ≫ PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)⟩

/-- Over `U`, `quotMkApp` sends a local section of `𝒜_n` to the image under the sheafification
unit of its class in the sectionwise quotient. -/
@[simp]
theorem quotMkApp_app (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U)) :
    (quotMkApp 𝒜 ℐ n).app U a =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)) (op U)
        ((preQuotProj 𝒜 ℐ n).app (op U) a) := rfl

/-- **The quotient homomorphism `𝒜 ⟶ 𝒜/ℐ`** of sheaf-level graded algebras. -/
def quotMk : SheafGradedAlgebraHom 𝒜 (quotSheafGradedAlgebra 𝒜 ℐ hqc) where
  app n := quotMkApp 𝒜 ℐ n
  app_mul i j U a b :=
    (quotSheafAlgebra_mul_unit 𝒜 ℐ i j (op U) ((preQuotProj 𝒜 ℐ i).app (op U) a)
      ((preQuotProj 𝒜 ℐ j).app (op U) b)).symm
  app_one _ := rfl

/-! ### The quotient homomorphism is a cokernel of the inclusion of the ideal -/

/-- **Morphisms of sheaves of modules out of `(𝒜/ℐ)_n` are morphisms of presheaves of modules out
of the sectionwise quotient.** The sheafification unit is locally bijective, so this is
`PresheafOfModules.homEquivOfIsLocallyBijective` read through the fully faithful forgetful
functor, exactly as `SheafOfModules.PreGradedModule.transferHomEquiv`. -/
def quotHomEquiv (n : ℤ) (T : S.Modules) :
    ((quotSheafAlgebra 𝒜 ℐ).piece n ⟶ T) ≃ (preQuotPiece 𝒜 ℐ n ⟶ T.val) :=
  (SheafOfModules.fullyFaithfulForget S.ringCatSheaf).homEquiv.trans
    (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)) T.isSheaf)

/-- `quotHomEquiv` precomposes a morphism out of `(𝒜/ℐ)_n` with the sheafification unit. -/
theorem quotHomEquiv_apply (n : ℤ) (T : S.Modules)
    (φ : (quotSheafAlgebra 𝒜 ℐ).piece n ⟶ T) :
    quotHomEquiv 𝒜 ℐ n T φ =
      PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n) ≫ φ.val := rfl

/-- The quotient homomorphism kills the inclusion of the ideal. -/
theorem ι_comp_quotMkApp (n : ℤ) : (ℐ.piece n).ι ≫ quotMkApp 𝒜 ℐ n = 0 := by
  ext U x
  show PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)) U
      ((preQuotProj 𝒜 ℐ n).app U ((ℐ.piece n).ι.val.app U x)) = 0
  exact Eq.trans
    (congrArg (PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n)) U)
      (Stacks.quotπ_app_comp_apply (ℐ.piece n).ι.val x))
    (map_zero _)

section Cokernel

variable (n : ℤ) (s : CokernelCofork ((ℐ.piece n).ι))

/-- The sectionwise condition of a cokernel cofork of the inclusion of the ideal. -/
theorem coforkCondition :
    (ℐ.piece n).ι.val ≫ (Cofork.π s).val = 0 :=
  congrArg (fun φ : (ℐ.piece n).toSheafOfModules ⟶ s.pt => φ.val)
    (CokernelCofork.condition s)

/-- The morphism out of `(𝒜/ℐ)_n` determined by a cokernel cofork: the sectionwise descent,
carried through `quotHomEquiv`. -/
def coforkDesc : (quotSheafAlgebra 𝒜 ℐ).piece n ⟶ s.pt :=
  (quotHomEquiv 𝒜 ℐ n s.pt).symm
    (Stacks.quotDesc (ℐ.piece n).ι.val (Cofork.π s).val (coforkCondition 𝒜 ℐ n s))

/-- The descent reads, after the sheafification unit, as the sectionwise descent. -/
theorem unit_comp_coforkDesc :
    PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n) ≫
        (coforkDesc 𝒜 ℐ n s).val =
      Stacks.quotDesc (ℐ.piece n).ι.val (Cofork.π s).val (coforkCondition 𝒜 ℐ n s) :=
  (quotHomEquiv_apply 𝒜 ℐ n s.pt (coforkDesc 𝒜 ℐ n s)).symm.trans
    ((quotHomEquiv 𝒜 ℐ n s.pt).apply_symm_apply _)

/-- The defining equation of the descent, read on the sectionwise quotient. -/
theorem preQuotProj_comp_unit_comp_coforkDesc :
    preQuotProj 𝒜 ℐ n ≫ PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj)
        (preQuotPiece 𝒜 ℐ n) ≫ (coforkDesc 𝒜 ℐ n s).val = (Cofork.π s).val := by
  rw [unit_comp_coforkDesc]
  exact Stacks.quotπ_comp_quotDesc _ _ _

/-- **`(𝒜/ℐ)_n` is a cokernel of the inclusion `ℐ_n ⟶ 𝒜_n`**, with `quotMkApp` the projection.

The sectionwise quotient is the cokernel at the level of presheaves, by `Stacks.quotDesc` and
`Stacks.quot_hom_ext`, and the sheafification unit turns morphisms out of it into morphisms out
of the sheafification, by `quotHomEquiv`. -/
def quotMkAppIsColimit :
    IsColimit (CokernelCofork.ofπ (quotMkApp 𝒜 ℐ n) (ι_comp_quotMkApp 𝒜 ℐ n)) :=
  Cofork.IsColimit.mk _ (fun s => coforkDesc 𝒜 ℐ n s)
    (fun s => (SheafOfModules.fullyFaithfulForget S.ringCatSheaf).map_injective
      (preQuotProj_comp_unit_comp_coforkDesc 𝒜 ℐ n s))
    (fun s m hm => (quotHomEquiv 𝒜 ℐ n s.pt).injective (by
      change PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n) ≫ m.val =
        PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj) (preQuotPiece 𝒜 ℐ n) ≫
          (coforkDesc 𝒜 ℐ n s).val
      refine Eq.trans ?_ (unit_comp_coforkDesc 𝒜 ℐ n s).symm
      refine Stacks.quot_hom_ext (ℐ.piece n).ι.val ?_
      refine Eq.trans ?_ (Stacks.quotπ_comp_quotDesc _ _ _).symm
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun φ : 𝒜.piece n ⟶ s.pt => φ.val) hm)))

end Cokernel

/-- **Quasi-coherence of the pieces of `𝒜/ℐ`**, when the pieces of `ℐ` are quasi-coherent: the
degree-`n` piece is a cokernel of a morphism of quasi-coherent modules. -/
theorem isQuasicoherentQuotPieces
    (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent) :
    IsQuasicoherentQuotPieces 𝒜 ℐ := by
  intro n
  have := hℐ n
  exact (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (ℐ.piece n).ι)
      (quotMkAppIsColimit 𝒜 ℐ n))
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (ℐ.piece n).ι)

/-! ### The short exact sequence, and the quotient homomorphism on affine sections -/

/-- The short complex `ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ℐ)_n`. -/
def quotShortComplex (n : ℤ) : ShortComplex S.Modules :=
  ShortComplex.mk (ℐ.piece n).ι (quotMkApp 𝒜 ℐ n) (ι_comp_quotMkApp 𝒜 ℐ n)

/-- The degree-`n` component of the quotient homomorphism is an epimorphism: it is a cokernel
projection. -/
theorem epi_quotMkApp (n : ℤ) : Epi (quotMkApp 𝒜 ℐ n) :=
  ⟨fun _ _ huv => Cofork.IsColimit.hom_ext (quotMkAppIsColimit 𝒜 ℐ n) huv⟩

/-- **`ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ℐ)_n` is short exact.** -/
theorem shortExact_quotShortComplex (n : ℤ) : (quotShortComplex 𝒜 ℐ n).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (quotMkAppIsColimit 𝒜 ℐ n)
  mono_f := inferInstanceAs (Mono (ℐ.piece n).ι)
  epi_g := epi_quotMkApp 𝒜 ℐ n

/-- **The quotient homomorphism is surjective on the sections over an affine open**, when the
pieces of `ℐ` are quasi-coherent. This is the Čech vanishing of Tag 01XB, through
`Stacks.AlgebraicGeometry.QcohExtension.surjective_app_of_shortExact`. -/
theorem surjective_quotMkApp_app (n : ℤ)
    (hℐn : ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent)
    (U : S.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((quotMkApp 𝒜 ℐ n).app U) :=
  Stacks.AlgebraicGeometry.QcohExtension.surjective_app_of_shortExact
    (quotShortComplex 𝒜 ℐ n) (shortExact_quotShortComplex 𝒜 ℐ n) hℐn U hU

/-! ### The relative Proj of the quotient is a closed subscheme of the relative Proj -/

/-- **The quotient homomorphism is degreewise surjective on the sections over the affine opens of
the base.** This is what makes `Proj_S(𝒜/ℐ)` a closed subscheme of `Proj_S(𝒜)`. -/
theorem surjectiveOnAffineSections_quotMk
    (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent) :
    ProjBundleSurjection.SurjectiveOnAffineSections (quotMk 𝒜 ℐ hqc) :=
  fun U hU n => surjective_quotMkApp_app 𝒜 ℐ (n : ℤ) (hℐ (n : ℤ)) U hU

/-- **`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`**: the relative analogue of
`Stacks.ClosedSubschemeProjQuotient.ambientHom`, the morphism Tag 0801 identifies with the closed
subscheme. -/
def quotAmbientHom
    (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent) :
    (relativeProj (quotSheafGradedAlgebra 𝒜 ℐ hqc)).scheme ⟶ (relativeProj 𝒜).scheme :=
  ProjBundleSurjection.map (surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ)

/-- **`Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.** -/
theorem isClosedImmersion_quotAmbientHom
    (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent) :
    IsClosedImmersion (quotAmbientHom 𝒜 ℐ hqc hℐ) :=
  ProjBundleSurjection.isClosedImmersion_map _

/-- The closed immersion is a morphism over the base. -/
@[reassoc]
theorem quotAmbientHom_comp_toBase
    (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent) :
    quotAmbientHom 𝒜 ℐ hqc hℐ ≫ (relativeProj 𝒜).toBase =
      (relativeProj (quotSheafGradedAlgebra 𝒜 ℐ hqc)).toBase :=
  ProjBundleSurjection.map_comp_toBase _

/-! ### The kernel of the quotient homomorphism -/

/-- **The inclusion of the ideal is a kernel of the quotient homomorphism.** -/
def ι_isKernel (n : ℤ) :
    IsLimit (KernelFork.ofι (ℐ.piece n).ι (ι_comp_quotMkApp 𝒜 ℐ n)) :=
  letI : Mono (quotShortComplex 𝒜 ℐ n).f := (inferInstance : Mono (ℐ.piece n).ι)
  (shortExact_quotShortComplex 𝒜 ℐ n).exact.fIsKernel

/-- The sectionwise kernel of the quotient homomorphism is killed by it. -/
theorem kernelSubmodule_ι_comp_quotMkApp (n : ℤ) :
    (Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)).ι ≫ quotMkApp 𝒜 ℐ n = 0 := by
  ext U x
  exact (AlgebraicGeometry.mem_kernelSubmodule_iff (quotMkApp 𝒜 ℐ n) U.unop
    ((Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)).ι.val.app U x)).1
    (ι_app_mem (Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)) U.unop x)

/-- **A local section of `𝒜_n` dies in `(𝒜/ℐ)_n` exactly when it lies in `ℐ_n`**, over every
open of the base. This is Tag 0801's kernel clause for the quotient by `ℐ`. -/
theorem quotMkApp_app_eq_zero_iff (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U)) :
    (quotMkApp 𝒜 ℐ n).app U a = 0 ↔ a ∈ (ℐ.piece n).toSubmodule.obj (op U) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨x, rfl⟩ := (mem_iff_exists_ι_app _ U a).1
      ((AlgebraicGeometry.mem_kernelSubmodule_iff (quotMkApp 𝒜 ℐ n) U a).2 h)
    have hfac := (ι_isKernel 𝒜 ℐ n).fac
      (KernelFork.ofι (Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)).ι
        (kernelSubmodule_ι_comp_quotMkApp 𝒜 ℐ n)) WalkingParallelPair.zero
    refine (mem_iff_exists_ι_app _ U _).2
      ⟨((ι_isKernel 𝒜 ℐ n).lift
        (KernelFork.ofι (Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)).ι
          (kernelSubmodule_ι_comp_quotMkApp 𝒜 ℐ n))).val.app (op U) x, ?_⟩
    exact congrArg
      (fun φ : (Stacks.Algebraization.kernelSubmodule (quotMkApp 𝒜 ℐ n)).toSheafOfModules
        ⟶ 𝒜.piece n => φ.val.app (op U) x) hfac
  · obtain ⟨x, rfl⟩ := (mem_iff_exists_ι_app _ U a).1 h
    exact congrArg
      (fun φ : (ℐ.piece n).toSheafOfModules ⟶ (quotSheafAlgebra 𝒜 ℐ).piece n =>
        φ.val.app (op U) x) (ι_comp_quotMkApp 𝒜 ℐ n)

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
