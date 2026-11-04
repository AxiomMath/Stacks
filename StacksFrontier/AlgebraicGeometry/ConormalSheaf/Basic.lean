module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.FactorizationCriterion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresQuotient

/-!
# The conormal sheaf of an immersion

Let `i : Z ⟶ X` be an immersion of schemes.  It factors as the closed immersion
`i.liftCoborder : Z ⟶ i.coborderRange` followed by an open immersion, and the *conormal sheaf*
of `i` is the pullback along that closed factor of its defining ideal sheaf `I`.  On an affine
open where the closed factor is `Spec (A ⧸ I) ⟶ Spec A` the formula reads
`(A ⧸ I) ⊗_A I ≅ I / I²`, which is why the conormal sheaf is called `I / I²`.

This file supplies that pullback, the canonical comparison map from the ideal sheaf to the
pushforward of the conormal sheaf, the structural fact that the ideal acts by zero on the
conormal sheaf — so that it really is a module over the quotient — and the affine formula in
its algebraic form.

## Main definitions

* `Ideal.quotTensorEquivCotangent`: for an ideal `I` of a commutative ring `R`, the canonical
  isomorphism `(R ⧸ I) ⊗[R] I ≅ I.Cotangent = I / I²`, linear over `R ⧸ I`.  This is the
  affine form of the conormal sheaf, normalised so that `1 ⊗ a` is the class of `a` modulo
  `I²`.
* `conormalSheaf i`: the conormal sheaf of an immersion `i`, the pullback of `definingIdeal i`
  along the canonical closed factor `i.liftCoborder`.
* `conormalComparison i`: the canonical map `I ⟶ i_* (I / I²)` of sheaves of modules on
  `i.coborderRange`, the unit of the pullback-pushforward adjunction at `definingIdeal i`.

## Main results

* `Ideal.quotTensorEquivCotangent_one_tmul` and
  `Ideal.quotTensorEquivCotangent_symm_toCotangent`: the normalisation of the affine
  identification on generators, `1 ⊗ a ↦ a mod I²`.  Together with `R ⧸ I`-linearity this
  pins the identification down: no automorphism of `I / I²` can be inserted.
* `kernelSubmodule_ι_comp`: a sectionwise kernel is killed by the morphism it is the kernel of.
* `conormalComparison_comp_map` and `existsUnique_hom_conormalComparison`: the universal
  property of the comparison map.  Every map from the ideal sheaf into a pushforward factors
  uniquely through it, so a morphism out of the conormal sheaf is the same thing as a map out
  of the ideal sheaf into a pushforward.
* `pullbackIdealMap_definingIdeal_eq_zero`: the canonical map `i^* I ⟶ 𝒪_Z` is zero, i.e. the
  ideal annihilates the conormal sheaf.  This is the sheaf-level statement that the conormal
  sheaf is a module over the quotient `𝒪_{i.coborderRange} / I = i_* 𝒪_Z`, the geometric
  counterpart of the `R ⧸ I`-linearity of `Ideal.quotTensorEquivCotangent`.
* `mem_definingIdealOfHom_iff_app_eq_zero`, `definingIdealOfHom_obj_eq_ker` and
  `definingIdealOfHom_subschemeι_obj`: the defining ideal sheaf read off sections, its
  identification on affine opens with the ideal component of Mathlib's
  `AlgebraicGeometry.Scheme.Hom.ker`, and the consequence that for `I : X.IdealSheafData` the
  defining ideal sheaf of `I.subschemeι` has components `I.ideal U`.  These are the bridge
  between the sheaf-of-modules presentation of an ideal sheaf used here and the
  `IdealSheafData` presentation used by Mathlib's closed subscheme API.

## Implementation notes

The conormal sheaf is taken on the *canonical* open neighbourhood `i.coborderRange` of the
image, the largest open in which the image of `i` is closed
(`le_coborderRange_of_isClosedImmersion`).  No identification of `Z` with a closed subscheme is
chosen, and no comparison with the conormal sheaf formed on a smaller admissible open is proved
here.

`Ideal.quotTensorEquivCotangent` is *not* a new construction: it is
`TensorProduct.quotTensorEquivQuotSMulBase` — already in this library, itself Mathlib's
`TensorProduct.quotTensorEquivQuotSMul` upgraded along `LinearEquiv.extendScalarsOfSurjective`
— retyped at `Ideal.Cotangent`.  The retyping has to be done by ascription rather than by
rewriting: `I.Cotangent` is a `def` for `I ⧸ (I • ⊤)`, so the two spellings are definitionally
but not syntactically equal, and the `Module (R ⧸ I)` instances on them are different
constants.  `exact`/`:=` accept the bridge because they check definitional equality; `rw`
does not.

The same phenomenon governs the sheaf-level proofs.  `structureSheafModule X` is spelled with
`sheafCompose … X.sheaf` inlined while `structureSheafRing X` is a `def` for
the same term, so goals mixing the two are not type-correct at `implicit` transparency and
`rw` refuses them while a term-mode bridge goes through.  Hence
`pullbackIdealMap_definingIdeal_eq_zero` is proved by applying
`Stacks.ClosedImmersion.pullbackIdealMap_eq_zero_iff` as a term, not by rewriting with it, and
`mem_definingIdealOfHom_iff_app_eq_zero` is `Iff.rfl` rather than a `rw` with
`mem_definingIdealOfHom`.

Everything is at a single universe `u`, as `RingedSpaceModuleAdjunction` forces: pushforward
and pullback of sheaves of modules are available only for `RingedSpace.{u, u}`.

## References

* [Stacks Project, Section 29.2 (Tag 01R2)](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Lemma 29.2.1 (Tag 01R3)](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion
open scoped TensorProduct
open Stacks.RingedSpace

universe u

/-! ### The affine form: `I / I²` as a module over the quotient -/

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- **The affine conormal identification.** For an ideal `I` of `R` the base change of `I` to
the quotient is the cotangent module `I / I²`, by an isomorphism linear over `R ⧸ I` and not
merely over `R`.

This is `TensorProduct.quotTensorEquivQuotSMulBase` retyped at `Ideal.Cotangent`; the
retyping is an ascription because `I.Cotangent` and `I ⧸ (I • ⊤)` are definitionally but not
syntactically the same. -/
noncomputable def quotTensorEquivCotangent : ((R ⧸ I) ⊗[R] ↥I) ≃ₗ[R ⧸ I] I.Cotangent :=
  TensorProduct.quotTensorEquivQuotSMulBase R ↥I I

/-- **The normalisation of the affine conormal identification.** It carries the generator
`1 ⊗ a` to the class of `a` modulo `I²`.  Together with `R ⧸ I`-linearity this determines the
isomorphism, since those generators generate: it cannot be altered by an automorphism of
`I / I²`. -/
theorem quotTensorEquivCotangent_one_tmul (a : ↥I) :
    I.quotTensorEquivCotangent ((1 : R ⧸ I) ⊗ₜ[R] a) = I.toCotangent a :=
  TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I a

/-- The inverse of the affine conormal identification carries the class of `a` modulo `I²` back
to the generator `1 ⊗ a`. -/
theorem quotTensorEquivCotangent_symm_toCotangent (a : ↥I) :
    I.quotTensorEquivCotangent.symm (I.toCotangent a) = (1 : R ⧸ I) ⊗ₜ[R] a :=
  rfl

end Ideal

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### Sectionwise kernels -/

/-- A sectionwise kernel is killed by the morphism it is the kernel of: over each object of the
site its sections are by construction in the kernel of the component. -/
theorem kernelSubmodule_ι_comp {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmodule f).ι ≫ f = 0 := by
  ext1
  ext U s
  exact s.2

/-! ### The defining ideal sheaf on sections -/

/-- A section of `𝒪_U` lies in the defining ideal sheaf of `j : Z ⟶ U` exactly when it is
killed by the map `j` induces on sections. -/
theorem mem_definingIdealOfHom_iff_app_eq_zero {Z U : Scheme.{u}} (j : Z ⟶ U) (V : U.Opens)
    (s : Γ(U, V)) : s ∈ (definingIdealOfHom j).obj (op V) ↔ (j.app V).hom s = 0 :=
  Iff.rfl

/-- **The defining ideal sheaf is Mathlib's kernel ideal sheaf.** On an affine open the
component of `definingIdealOfHom j` is the ideal component of
`AlgebraicGeometry.Scheme.Hom.ker j`.

This is the bridge between the two presentations of an ideal sheaf: here an ideal subsheaf of
the structure sheaf module, in Mathlib a family of ideals indexed by the affine opens.  The
quasi-compactness hypothesis is the one `Scheme.Hom.ker_apply` needs and is automatic for a
closed immersion. -/
theorem definingIdealOfHom_obj_eq_ker {Z U : Scheme.{u}} (j : Z ⟶ U) [QuasiCompact j]
    (V : U.affineOpens) : (definingIdealOfHom j).obj (op V.1) = j.ker.ideal V := by
  have h := j.ker_apply V
  refine Submodule.ext fun s => ?_
  rw [h]
  exact Iff.rfl

/-- **The defining ideal sheaf of a closed subscheme is its ideal sheaf datum.** For
`I : X.IdealSheafData` the defining ideal sheaf of the closed immersion `I.subschemeι` has, on
each affine open, the component `I.ideal U`.

Composed with `definingIdealOfHom_obj_eq_ker` and Mathlib's `ker_subschemeι`, this says that
the sheaf-of-modules ideal used here and the `IdealSheafData` one agree, which is what lets a
statement phrased with `IdealSheafData` be read on the defining-ideal layer. -/
theorem definingIdealOfHom_subschemeι_obj {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (definingIdealOfHom I.subschemeι).obj (op U.1) = I.ideal U :=
  (definingIdealOfHom_obj_eq_ker I.subschemeι U).trans (by rw [I.ker_subschemeι])

/-! ### The conormal sheaf -/

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The conormal sheaf of an immersion**, `I / I²`.  An immersion `i : Z ⟶ X` factors as the
closed immersion `i.liftCoborder` into the open subscheme `i.coborderRange`; the conormal sheaf
is the pullback along `i.liftCoborder` of the defining ideal sheaf of that closed factor. -/
noncomputable abbrev conormalSheaf :
    SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) :=
  (modulePullback i.liftCoborder.toLRSHom.toShHom).obj (definingIdeal i).toSheafOfModules

/-- **The canonical comparison map** `I ⟶ i_* (I / I²)`: the unit of the adjunction
`i^* ⊣ i_*` at the defining ideal sheaf.  Stacks writes this as the surjection of the ideal
sheaf onto the pushforward of the conormal sheaf. -/
noncomputable def conormalComparison :
    (definingIdeal i).toSheafOfModules ⟶
      (modulePushforward i.liftCoborder.toLRSHom.toShHom).obj (conormalSheaf i) :=
  (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app _

/-- Composing the comparison map with the pushforward of a morphism out of the conormal sheaf
is the adjoint transpose of that morphism. -/
theorem conormalComparison_comp_map
    {F : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (h : conormalSheaf i ⟶ F) :
    conormalComparison i ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map h =
      (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).homEquiv _ F h :=
  (Adjunction.homEquiv_unit _ _ _ _).symm

/-- **The universal property of the comparison map.**  Every morphism from the defining ideal
sheaf into a pushforward factors through `conormalComparison i` by a unique morphism out of the
conormal sheaf.  This is what it means for the conormal sheaf to be `I / I²` without choosing a
presentation of the quotient. -/
theorem existsUnique_hom_conormalComparison
    {F : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (g : (definingIdeal i).toSheafOfModules ⟶
      (modulePushforward i.liftCoborder.toLRSHom.toShHom).obj F) :
    ∃! h : conormalSheaf i ⟶ F,
      conormalComparison i ≫ (modulePushforward i.liftCoborder.toLRSHom.toShHom).map h = g := by
  simp_rw [conormalComparison_comp_map]
  exact ((modulePullbackPushforwardAdjunction
    i.liftCoborder.toLRSHom.toShHom).homEquiv _ F).bijective.existsUnique g

/-- **The conormal sheaf is a module over the quotient.**  The canonical map
`i^* I ⟶ 𝒪_Z` attached to the inclusion of the defining ideal sheaf is zero: the ideal
annihilates the conormal sheaf.  Equivalently, the `𝒪_{i.coborderRange}`-module structure on
`i_*` of the conormal sheaf factors through the quotient by `I`.

This is the sheaf-level counterpart of the `R ⧸ I`-linearity of
`Ideal.quotTensorEquivCotangent`.  It holds for the formal reason that `definingIdeal i` is the
sectionwise kernel of `𝒪_{i.coborderRange} ⟶ i_* 𝒪_Z`, so no hypothesis beyond `IsImmersion i`
is used. -/
theorem pullbackIdealMap_definingIdeal_eq_zero :
    pullbackIdealMap i.liftCoborder.toLRSHom
      (definingIdeal i).toSheafOfModules (definingIdeal i).ι = 0 :=
  (pullbackIdealMap_eq_zero_iff _ _ _).2 (kernelSubmodule_ι_comp _)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
