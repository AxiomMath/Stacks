module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SplitSquareZeroModule
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.YonedaExtOne
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Deformation.RingedSpaceThickening.ModuleExtension
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.StacksAttribute

/-!
# The trivial extension across a trivialized first order thickening

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, and let `π` be a *trivialization* of it: a retraction of `i` in
the category of ringed spaces. Given two `𝒪_X`-modules `ℱ` and `𝒦` and a map
`c : i^* ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`, the direct sum `ℱ ⊕ 𝒦` carries an `𝒪_{X'}`-module structure

    r · (m, n) = (r m, r n + c(d r ⊗ m)),

where `d r = r - π^♯(i^♯ r)` is the *derivation* attached to the trivialization: writing a
section of `𝒪_{X'}` as its image under the splitting plus a remainder exhibits `d` as a
derivation into `ℐ`. The resulting module is the *trivial extension* `ℱ'_{c,triv}`; it is an
extension of `i_* ℱ` by `i_* 𝒦` in the sense of **Stacks 08L4**, and its canonical map is `c`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.structureSheafSplitEpi`: a trivialization splits the
  structure-sheaf map `i^♯ : 𝒪_{X'} ⟶ i_* 𝒪_X`, the splitting being the structure-sheaf map of
  the retraction read on the inverse image of an open of `X'`.
* `AlgebraicGeometry.RingedSpaceThickening.trivializationDerivation`: the derivation
  `d : 𝒪_{X'} ⟶ ℐ` of a trivialization, on sections.
* `AlgebraicGeometry.RingedSpaceThickening.extensionPairing`: the prescribed map `c`, read on
  pure tensors of local sections over an open of `X'`.
* `AlgebraicGeometry.RingedSpaceThickening.trivialExtensionModule`: **Stacks 08LB** part (1),
  the trivial extension `ℱ'_{c,triv} = ℱ ⊕ 𝒦`, and
  `AlgebraicGeometry.RingedSpaceThickening.trivialYonedaExtension`: part (2), the same read as
  a degree-one Yoneda extension.
* `AlgebraicGeometry.RingedSpaceThickening.splitRestriction` and
  `AlgebraicGeometry.RingedSpaceThickening.splitExtension`: **Stacks 08LB** part (3), reading an
  extension across the thickening as a sequence of `𝒪_X`-modules along the trivialization, and
  `AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass`: the resulting class
  `ξ_{ℱ'} ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)`.
* `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom`: the homomorphism
  `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦) ⟶ Ext¹_{𝒪_X}(ℱ, 𝒦)` induced by reading an extension along the
  trivialization, whose value on the class of `ℱ'` is `ξ_{ℱ'}`, and
  `AlgebraicGeometry.RingedSpaceThickening.extensionClassesWithAction`: the isomorphism classes
  of extensions with canonical map `c`, represented by their classes in
  `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.trivialExtensionModule_smul`: **Stacks 08LB**
  part (1), the displayed action of `𝒪_{X'}` on `ℱ ⊕ 𝒦`.
* `AlgebraicGeometry.RingedSpaceThickening.trivialExtensionShortComplex_shortExact`:
  **Stacks 08LB** part (2), the trivial extension sits in a short exact sequence
  `0 ⟶ i_* 𝒦 ⟶ ℱ'_{c,triv} ⟶ i_* ℱ ⟶ 0`.
* `AlgebraicGeometry.RingedSpaceThickening.trivialYonedaExtension_action`: **Stacks 08LB**
  part (2'), the canonical map of the trivial extension is `c` itself, which is what places it
  in the set of extensions the remark puts in bijection with `Ext¹_{𝒪_X}(ℱ, 𝒦)`.
* `AlgebraicGeometry.RingedSpaceThickening.splitExtension_shortExact`: **Stacks 08LB** part (3),
  an extension read along the trivialization is again short exact, which is what makes the class
  `ξ_{ℱ'}` available.
* `AlgebraicGeometry.RingedSpaceThickening.bijective_underlyingExtensionClass`: **Stacks 08LB**
  part (4), `ℱ' ↦ ξ_{ℱ'}` is a bijection from the isomorphism classes of extensions with
  `c = c_{ℱ'}` onto `Ext¹_{𝒪_X}(ℱ, 𝒦)`. Its two halves, read on extensions rather than on
  classes, are
  `AlgebraicGeometry.RingedSpaceThickening.exists_yonedaExtension_underlyingExtensionClass_eq`
  and `AlgebraicGeometry.RingedSpaceThickening.exists_iso_of_underlyingExtensionClass_eq`.
* `AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_trivialYonedaExtension`:
  **Stacks 08LB** part (5), the trivial extension maps to the zero class.
* `AlgebraicGeometry.RingedSpaceThickening.trivializationDerivation_leibniz` and the lemmas
  around it: `d` is a derivation for the `𝒪_{X'}`-module structure on `ℐ`.

## Scope

Part (4) of the remark — that `ℱ' ↦ ξ_{ℱ'}` is a *bijection* from isomorphism classes of
extensions with `c = c_{ℱ'}` onto `Ext¹_{𝒪_X}(ℱ, 𝒦)` — is the last section of this file. It is
deduced from the two clauses of **Stacks 08L7**, proved in
`StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification`: adding to an extension
one whose middle term is a direct image leaves the canonical map alone, and two extensions with
the same canonical map differ by exactly one such class. By **Stacks 08KS** those classes are
the ones coming from `Ext¹_{𝒪_X}(ℱ, 𝒦)`, so the classes of the extensions with canonical map
`c` form a coset on which `Ext¹_{𝒪_X}(ℱ, 𝒦)` acts freely and transitively; part (5) supplies the
base point that makes the coset a bijective copy of the group rather than merely a torsor.

## Implementation notes

The algebra of the construction — that `ℱ ⊕ 𝒦` with the displayed action is a module, a
presheaf of modules, and a sheaf of modules — is
`Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule`, which is indexed by a sheaf of
`RingCat` and takes the bilinear map as a bare family with its four laws as hypotheses. This
file only *specialises* it, with `𝒮 = ℛ = 𝒪_{X'}` and the quotient map the identity: `ℐ`,
`i_* ℱ` and `i_* 𝒦` are already `𝒪_{X'}`-modules, so no pushforward of the ring is involved and
the Leibniz rule comes out directly in the form `d(rs) = r · d s + s · d r`.

The derivation is produced as a section of `ℐ` by
`Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero`, and every one of its laws is
a single ring identity in `𝒪_{X'}(U)` under
`Stacks.ClosedImmersion.injective_idealSheafι_val_app`, so the choice of section is invisible.
The Leibniz rule is the only place the square-zero hypothesis enters.

The sections of the structure sheaf of a ringed space carry two spellings of their ring structure:
the `CommRingCat`-valued `X'.presheaf.obj U`, over which the tensor product of sections is formed,
and the `RingCat`-valued `structureSheafRing`, at which sheaves of modules are indexed. They are
definitionally equal but instance *search* cannot pass between them, `structureSheafRing` not being
reducible. The four bilinearity laws of the pairing are therefore stated once over abstract data in
the `TensorHom` section below and applied in term mode, where the elaborator discharges the defeq.
The same discipline is what the material on part (3) needs: `rw` checks its motive at `implicit`
transparency, so a step involving the pushforward spelling of a section ring is stated over
abstract data
(`AlgebraicGeometry.RingedSpaceThickening.trivializationDerivation_eq_zero_of_splitApp_eq`,
`AlgebraicGeometry.RingedSpaceThickening.trivialExtensionModule_smul_of_derivation_eq_zero`) and
instantiated in term mode.

Part (3) reads an `𝒪_{X'}`-module as an `𝒪_X`-module by *pushforward along the retraction*
rather than by restriction of scalars along `π^♯`, as the corresponding development for ringed
topoi (Stacks 08MI) does. The two spaces have different sites, `Opens X` and `Opens X'`, so
`CategoryTheory.SheafOfModules.restrictScalars` is not even type-correct here: the reindexing
of opens along the homeomorphism underlying `π` has to travel with the restriction of scalars,
and `π_*` is exactly that composite. Its exactness is what makes the restricted sequence short
exact: left exactness because `π_*` is a right adjoint, right exactness by
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isIso_base`, whose only
hypothesis is on the base map — and the base map of `π` is a homeomorphism even though `π`
itself is not an isomorphism of ringed spaces.

Part (4) is stated with the isomorphism classes of extensions represented by their classes in
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`, which is legitimate because the class map of short exact
sequences is surjective and separates exactly the isomorphism classes
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`); both halves of
the bijection are stated on extensions as well, so neither direction rests on that reading. The
cancellation `ξ = ξ + η ⇒ η = 0` in an `Ext` group is done with `abel`: `add_left_cancel` does
not elaborate on `CategoryTheory.Abelian.Ext` within the heartbeat limit here.

## References

* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08L7](https://stacks.math.columbia.edu/tag/08L7)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08L9](https://stacks.math.columbia.edu/tag/08L9)
* [Stacks Project, Tag 08LA](https://stacks.math.columbia.edu/tag/08LA)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Thickenings

universe e u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The underlying map of the thickening followed by that of a trivialization is the identity. -/
private theorem base_comp_retraction_base (π : SplitMono i) :
    i.hom.base ≫ π.retraction.hom.base = 𝟙 (TopCat.of X.carrier) :=
  congrArg (fun f : X ⟶ X => f.hom.base) π.id

/-- The underlying map of a trivialization is a two-sided inverse of the underlying map of the
thickening: it is a right inverse because `π` retracts `i`, hence a left inverse because the
underlying map of a thickening is a homeomorphism. -/
theorem retraction_base_comp (π : SplitMono i) (hb : IsIso i.hom.base) :
    π.retraction.hom.base ≫ i.hom.base = 𝟙 (TopCat.of X'.carrier) := by
  rw [IsIso.eq_inv_of_hom_inv_id (base_comp_retraction_base i π), IsIso.inv_hom_id]
  rfl

/-- Pulling an open of `X'` back along the thickening and then along a trivialization returns
it. -/
theorem retraction_opens_obj (π : SplitMono i) (hb : IsIso i.hom.base) (U : Opens X'.carrier) :
    (Opens.map π.retraction.hom.base).obj ((Opens.map i.hom.base).obj U) = U := by
  rw [← Opens.map_comp_obj, retraction_base_comp i π hb]
  exact Opens.map_id_obj _

/-- The same equality, in `(Opens X')ᵒᵖ`. -/
theorem retraction_opens_op_obj (π : SplitMono i) (hb : IsIso i.hom.base)
    (U : (Opens X'.carrier)ᵒᵖ) :
    (Opens.map π.retraction.hom.base).op.obj ((Opens.map i.hom.base).op.obj U) = U :=
  congrArg op (retraction_opens_obj i π hb U.unop)

/-- Pulling an open of `X` back along a trivialization and then along the thickening returns
it. Unlike `AlgebraicGeometry.RingedSpaceThickening.retraction_opens_obj` this is the easy
direction: it only uses that `π` retracts `i`. -/
theorem thickening_opens_obj (π : SplitMono i) (V : Opens X.carrier) :
    (Opens.map i.hom.base).obj ((Opens.map π.retraction.hom.base).obj V) = V := by
  rw [← Opens.map_comp_obj, base_comp_retraction_base i π]
  exact Opens.map_id_obj _

/-- The same equality, in `(Opens X)ᵒᵖ`. -/
theorem thickening_opens_op_obj (π : SplitMono i) (V : (Opens X.carrier)ᵒᵖ) :
    (Opens.map i.hom.base).op.obj ((Opens.map π.retraction.hom.base).op.obj V) = V :=
  congrArg op (thickening_opens_obj i π V.unop)

section Splitting

variable (π : SplitMono i) (hb : IsIso i.hom.base)

/-- The structure-sheaf map of a trivialization, read on sections of `𝒪_X` over the inverse
image of an open of `X'`: a ring map `𝒪_X(i^{-1} U) ⟶ 𝒪_{X'}(U)`. -/
noncomputable def retractionSectionApp (U : (Opens X'.carrier)ᵒᵖ) :
    X.presheaf.obj ((Opens.map i.hom.base).op.obj U) ⟶ X'.presheaf.obj U :=
  π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
    X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb U))

/-- `AlgebraicGeometry.RingedSpaceThickening.retractionSectionApp` commutes with restriction:
all the comparison maps involved are maps in a poset, hence equal to one another. -/
theorem retractionSectionApp_naturality {U V : (Opens X'.carrier)ᵒᵖ} (f : U ⟶ V) :
    X.presheaf.map ((Opens.map i.hom.base).op.map f) ≫ retractionSectionApp i π hb V =
      retractionSectionApp i π hb U ≫ X'.presheaf.map f := by
  have hnat : X.presheaf.map ((Opens.map i.hom.base).op.map f) ≫
        π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj V) =
      π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
        X'.presheaf.map ((Opens.map π.retraction.hom.base).op.map
          ((Opens.map i.hom.base).op.map f)) :=
    π.retraction.hom.c.naturality ((Opens.map i.hom.base).op.map f)
  calc X.presheaf.map ((Opens.map i.hom.base).op.map f) ≫ retractionSectionApp i π hb V
      = (X.presheaf.map ((Opens.map i.hom.base).op.map f) ≫
          π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj V)) ≫
            X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb V)) :=
        (Category.assoc _ _ _).symm
    _ = π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
          X'.presheaf.map ((Opens.map π.retraction.hom.base).op.map
            ((Opens.map i.hom.base).op.map f) ≫
              eqToHom (retraction_opens_op_obj i π hb V)) := by
        rw [hnat, Category.assoc, ← Functor.map_comp]
    _ = π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
          X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb U) ≫ f) :=
        congrArg (fun g => π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
          X'.presheaf.map g) (Subsingleton.elim _ _)
    _ = retractionSectionApp i π hb U ≫ X'.presheaf.map f := by
        rw [retractionSectionApp, Functor.map_comp, Category.assoc]

/-- The structure-sheaf map of the trivialization followed by that of the thickening is the
restriction map of the identity of `X`, since `i ≫ π = 𝟙 X`. -/
theorem retraction_comp_structureSheaf_app (U : (Opens X'.carrier)ᵒᵖ) :
    π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
        i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj
          ((Opens.map i.hom.base).op.obj U)) =
      X.presheaf.map (eqToHom (congrArg (Opens.map i.hom.base).op.obj
        (retraction_opens_op_obj i π hb U)).symm) := by
  refine (SheafedSpace.congr_hom_app π.id ((Opens.map i.hom.base).op.obj U)).trans ?_
  refine (Category.id_comp _).trans ?_
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- `AlgebraicGeometry.RingedSpaceThickening.retractionSectionApp` is a section of the
structure-sheaf map of the thickening. -/
theorem retractionSectionApp_comp (U : (Opens X'.carrier)ᵒᵖ) :
    retractionSectionApp i π hb U ≫ i.hom.c.app U =
      𝟙 (X.presheaf.obj ((Opens.map i.hom.base).op.obj U)) := by
  have hnat : X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb U)) ≫ i.hom.c.app U =
      i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj
          ((Opens.map i.hom.base).op.obj U)) ≫
        X.presheaf.map ((Opens.map i.hom.base).op.map
          (eqToHom (retraction_opens_op_obj i π hb U))) :=
    i.hom.c.naturality (eqToHom (retraction_opens_op_obj i π hb U))
  calc retractionSectionApp i π hb U ≫ i.hom.c.app U
      = π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
          (X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb U)) ≫ i.hom.c.app U) := by
        rw [retractionSectionApp, Category.assoc]
    _ = (π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj U) ≫
          i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj
            ((Opens.map i.hom.base).op.obj U))) ≫
          X.presheaf.map ((Opens.map i.hom.base).op.map
            (eqToHom (retraction_opens_op_obj i π hb U))) := by
        rw [hnat, Category.assoc]
    _ = X.presheaf.map (eqToHom (congrArg (Opens.map i.hom.base).op.obj
            (retraction_opens_op_obj i π hb U)).symm ≫
          (Opens.map i.hom.base).op.map (eqToHom (retraction_opens_op_obj i π hb U))) := by
        rw [retraction_comp_structureSheaf_app i π hb, Functor.map_comp]
    _ = 𝟙 (X.presheaf.obj ((Opens.map i.hom.base).op.obj U)) :=
        (congrArg X.presheaf.map (Subsingleton.elim _
          (CategoryStruct.id ((Opens.map i.hom.base).op.obj U)))).trans
          (X.presheaf.map_id _)

/-- The structure-sheaf map of the trivialization followed by that of the thickening, read over
an open of `X` rather than over the inverse image of an open of `X'`: again the restriction map
of the identity of `X`, since `i ≫ π = 𝟙 X`. -/
theorem retraction_comp_structureSheaf_app_of_opens (V : (Opens X.carrier)ᵒᵖ) :
    π.retraction.hom.c.app V ≫
        i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj V) =
      X.presheaf.map (eqToHom (thickening_opens_op_obj i π V).symm) := by
  refine (SheafedSpace.congr_hom_app π.id V).trans ?_
  refine (Category.id_comp _).trans ?_
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- **The splitting fixes every section pulled back along the trivialization.** A section of
`𝒪_X` over an open `V` of `X`, carried to `𝒪_{X'}(π^{-1} V)` by `π^♯`, is returned by the
composite `π^♯ ∘ i^♯` of
`AlgebraicGeometry.RingedSpaceThickening.retractionSectionApp` with the structure-sheaf map.

This is what makes the derivation of the trivialization vanish on such a section, and hence what
makes the trivial extension split over `𝒪_X`. -/
theorem retractionSectionApp_comp_structureSheaf (V : (Opens X.carrier)ᵒᵖ) :
    π.retraction.hom.c.app V ≫
        i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj V) ≫
          retractionSectionApp i π hb ((Opens.map π.retraction.hom.base).op.obj V) =
      π.retraction.hom.c.app V := by
  have hnat : X.presheaf.map (eqToHom (thickening_opens_op_obj i π V).symm) ≫
        π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj
          ((Opens.map π.retraction.hom.base).op.obj V)) =
      π.retraction.hom.c.app V ≫ X'.presheaf.map
        ((Opens.map π.retraction.hom.base).op.map
          (eqToHom (thickening_opens_op_obj i π V).symm)) :=
    π.retraction.hom.c.naturality (eqToHom (thickening_opens_op_obj i π V).symm)
  calc π.retraction.hom.c.app V ≫
        i.hom.c.app ((Opens.map π.retraction.hom.base).op.obj V) ≫
          retractionSectionApp i π hb ((Opens.map π.retraction.hom.base).op.obj V)
      = X.presheaf.map (eqToHom (thickening_opens_op_obj i π V).symm) ≫
          retractionSectionApp i π hb ((Opens.map π.retraction.hom.base).op.obj V) := by
        rw [← Category.assoc, retraction_comp_structureSheaf_app_of_opens]
    _ = (X.presheaf.map (eqToHom (thickening_opens_op_obj i π V).symm) ≫
          π.retraction.hom.c.app ((Opens.map i.hom.base).op.obj
            ((Opens.map π.retraction.hom.base).op.obj V))) ≫
          X'.presheaf.map (eqToHom (retraction_opens_op_obj i π hb
            ((Opens.map π.retraction.hom.base).op.obj V))) := by
        rw [retractionSectionApp, Category.assoc]
    _ = π.retraction.hom.c.app V ≫ X'.presheaf.map
          ((Opens.map π.retraction.hom.base).op.map
            (eqToHom (thickening_opens_op_obj i π V).symm) ≫
              eqToHom (retraction_opens_op_obj i π hb
                ((Opens.map π.retraction.hom.base).op.obj V))) := by
        rw [hnat, Category.assoc, ← Functor.map_comp]
    _ = π.retraction.hom.c.app V ≫ X'.presheaf.map
          (CategoryStruct.id ((Opens.map π.retraction.hom.base).op.obj V)) :=
        congrArg (fun g => π.retraction.hom.c.app V ≫ X'.presheaf.map g)
          (Subsingleton.elim _ _)
    _ = π.retraction.hom.c.app V := by simp

/-- **Stacks 08L9.** A trivialization of a thickening splits its structure-sheaf map: the
structure-sheaf map `𝒪_X ⟶ π_* 𝒪_{X'}` of the retraction, reindexed along
`AlgebraicGeometry.RingedSpaceThickening.retraction_opens_obj`, is a section of
`i^♯ : 𝒪_{X'} ⟶ i_* 𝒪_X`.

This is the step the source phrases as "using `π^♯` to split the surjection
`𝒪_{X'} ⟶ 𝒪_X`". It is the converse of `Deformation.RingThickening.retractionFromSplitting`,
and it supplies the `CategoryTheory.SplitMono` that
`Deformation.RingThickening.splittingFromTrivialization` takes as a hypothesis — so the two
together, and neither alone, give the source's "given `π` we obtain a splitting". -/
@[stacks 08L9 "a trivialization splits the structure-sheaf map"]
noncomputable def structureSheafSplitEpi : SplitEpi i.hom.c where
  section_ :=
    { app := retractionSectionApp i π hb
      naturality := fun _ _ f => retractionSectionApp_naturality i π hb f }
  id := NatTrans.ext (funext fun U => retractionSectionApp_comp i π hb U)

/-- The structure-sheaf map on sections, at the `structureSheafRing` spelling at which sheaves of
modules are indexed. -/
noncomputable def structureSheafApp (U : (Opens X'.carrier)ᵒᵖ) :
    (structureSheafRing X').obj.obj U ⟶
      (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj U) :=
  (structureSheafHom i).hom.app U

/-- The splitting of the structure-sheaf map on sections, at the `structureSheafRing` spelling. -/
noncomputable def splitApp (U : (Opens X'.carrier)ᵒᵖ) :
    (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj U) ⟶
      (structureSheafRing X').obj.obj U :=
  (forget₂ CommRingCat.{u} RingCat.{u}).map (retractionSectionApp i π hb U)

/-- Pointwise form of
`AlgebraicGeometry.RingedSpaceThickening.retractionSectionApp_comp`. -/
theorem splitApp_structureSheafApp (U : (Opens X'.carrier)ᵒᵖ)
    (a : (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj U)) :
    (structureSheafApp i U).hom ((splitApp i π hb U).hom a) = a :=
  congrArg (fun g : X.presheaf.obj ((Opens.map i.hom.base).op.obj U) ⟶
      X.presheaf.obj ((Opens.map i.hom.base).op.obj U) => g.hom a)
    (retractionSectionApp_comp i π hb U)

/-- The splitting commutes with restriction, in pointwise form. -/
theorem splitApp_naturality {U V : (Opens X'.carrier)ᵒᵖ} (f : U ⟶ V)
    (a : (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj U)) :
    ((structureSheafRing X').obj.map f).hom ((splitApp i π hb U).hom a) =
      (splitApp i π hb V).hom
        (((structureSheafRing X).obj.map ((Opens.map i.hom.base).op.map f)).hom a) :=
  (congrArg (fun g : X.presheaf.obj ((Opens.map i.hom.base).op.obj U) ⟶ X'.presheaf.obj V =>
      g.hom a) (retractionSectionApp_naturality i π hb f)).symm

/-- Pointwise form of
`AlgebraicGeometry.RingedSpaceThickening.retractionSectionApp_comp_structureSheaf`: the
splitting fixes every section pulled back along the trivialization. -/
theorem splitApp_structureSheafApp_retraction (V : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X).obj.obj V) :
    (splitApp i π hb ((Opens.map π.retraction.hom.base).op.obj V)).hom
        ((structureSheafApp i ((Opens.map π.retraction.hom.base).op.obj V)).hom
          (((structureSheafHom π.retraction).hom.app V).hom r)) =
      ((structureSheafHom π.retraction).hom.app V).hom r :=
  congrArg (fun g : X.presheaf.obj V ⟶
      X'.presheaf.obj ((Opens.map π.retraction.hom.base).op.obj V) => g.hom r)
    (retractionSectionApp_comp_structureSheaf i π hb V)

end Splitting

section Derivation

variable (π : SplitMono i) (hb : IsIso i.hom.base)

/-- The inclusion of the ideal of the thickening, on sections over an open of `X'`. -/
noncomputable def idealSection (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    (structureSheafRing X').obj.obj U :=
  ((idealSheafι i).val.app U).hom a

/-- The inclusion of the ideal sheaf is injective on sections. -/
theorem idealSection_injective (U : (Opens X'.carrier)ᵒᵖ) :
    Function.Injective (idealSection i U) :=
  Stacks.ClosedImmersion.injective_idealSheafι_val_app i U.unop

/-- The zero section of the ideal sheaf maps to zero in `𝒪_{X'}(U)`. -/
theorem idealSection_zero (U : (Opens X'.carrier)ᵒᵖ) :
    idealSection i U 0 = 0 :=
  map_zero _

/-- The inclusion of the ideal sheaf on sections is additive. -/
theorem idealSection_add (U : (Opens X'.carrier)ᵒᵖ)
    (a b : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    idealSection i U (a + b) = idealSection i U a + idealSection i U b :=
  map_add _ a b

/-- The inclusion of the ideal sheaf on sections sends `r • a` to the product `r * a`. -/
theorem idealSection_smul (U : (Opens X'.carrier)ᵒᵖ) (r : (structureSheafRing X').obj.obj U)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    idealSection i U (r • a) = r * idealSection i U a :=
  map_smul ((idealSheafι i).val.app U).hom r a

/-- The inclusion of the ideal sheaf on sections commutes with restriction. -/
theorem idealSection_naturality {U V : (Opens X'.carrier)ᵒᵖ} (f : U ⟶ V)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    idealSection i V ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val.map f a) =
      ((structureSheafRing X').obj.map f).hom (idealSection i U a) :=
  PresheafOfModules.naturality_apply (idealSheafι i).val f a

/-- A section of the ideal is killed by the structure-sheaf map. -/
theorem structureSheafApp_idealSection (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    (structureSheafApp i U).hom (idealSection i U a) = 0 :=
  congrArg
    (fun k : AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶
        (modulePushforward i).obj (SheafOfModules.unit (structureSheafRing X)) =>
      (k.val.app U).hom a)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)))

/-- The remainder `r - π^♯(i^♯ r)` of a section under the splitting lies in the ideal. -/
theorem sub_splitApp_mem_ker (U : (Opens X'.carrier)ᵒᵖ) (r : (structureSheafRing X').obj.obj U) :
    (structureSheafApp i U).hom
      (r - (splitApp i π hb U).hom ((structureSheafApp i U).hom r)) = 0 := by
  rw [map_sub, splitApp_structureSheafApp, sub_self]

/-- **The derivation attached to a trivialization.** On sections, `d r = r - π^♯(i^♯ r)`, read
as a section of the ideal sheaf `ℐ`. The lift exists by
`Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero` and is unique by
`AlgebraicGeometry.RingedSpaceThickening.idealSection_injective`. -/
noncomputable def trivializationDerivation (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U) :
    (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U :=
  (Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero i U.unop
    (r - (splitApp i π hb U).hom ((structureSheafApp i U).hom r))
    (sub_splitApp_mem_ker i π hb U r)).choose

/-- The defining property of
`AlgebraicGeometry.RingedSpaceThickening.trivializationDerivation`. -/
theorem idealSection_trivializationDerivation (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U) :
    idealSection i U (trivializationDerivation i π hb U r) =
      r - (splitApp i π hb U).hom ((structureSheafApp i U).hom r) :=
  (Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero i U.unop
    (r - (splitApp i π hb U).hom ((structureSheafApp i U).hom r))
    (sub_splitApp_mem_ker i π hb U r)).choose_spec

/-- The derivation vanishes on a section fixed by the splitting. -/
private theorem trivializationDerivation_eq_zero_aux (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U)
    (hr : (splitApp i π hb U).hom ((structureSheafApp i U).hom r) = r) :
    trivializationDerivation i π hb U r = 0 := by
  refine idealSection_injective i U ?_
  rw [idealSection_trivializationDerivation, idealSection_zero, hr, sub_self]

/-- The derivation of a trivialization vanishes on `0`. -/
theorem trivializationDerivation_zero (U : (Opens X'.carrier)ᵒᵖ) :
    trivializationDerivation i π hb U 0 = 0 := by
  refine trivializationDerivation_eq_zero_aux i π hb U 0 ?_
  rw [map_zero (structureSheafApp i U).hom, map_zero (splitApp i π hb U).hom]

/-- The derivation of a trivialization vanishes on `1`. -/
theorem trivializationDerivation_one (U : (Opens X'.carrier)ᵒᵖ) :
    trivializationDerivation i π hb U 1 = 0 := by
  refine trivializationDerivation_eq_zero_aux i π hb U 1 ?_
  rw [map_one (structureSheafApp i U).hom, map_one (splitApp i π hb U).hom]

/-- The derivation of a trivialization is additive. -/
theorem trivializationDerivation_add (U : (Opens X'.carrier)ᵒᵖ)
    (r s : (structureSheafRing X').obj.obj U) :
    trivializationDerivation i π hb U (r + s) =
      trivializationDerivation i π hb U r + trivializationDerivation i π hb U s := by
  refine idealSection_injective i U ?_
  rw [idealSection_trivializationDerivation, idealSection_add,
    idealSection_trivializationDerivation, idealSection_trivializationDerivation,
    map_add (structureSheafApp i U).hom, map_add (splitApp i π hb U).hom]
  abel

/-- The ring identity behind the Leibniz rule: in a commutative ring, if the remainders of `r`
and `s` under a split quotient multiply to zero then the remainder of `r * s` is `r` times the
remainder of `s` plus `s` times the remainder of `r`. -/
theorem sub_mul_sub_leibniz {A : Type u} [CommRing A] (r s x y : A)
    (hxy : (r - x) * (s - y) = 0) :
    r * s - x * y = r * (s - y) + s * (r - x) := by
  linear_combination -hxy

/-- Two sections of the ideal of a first order thickening multiply to zero. -/
theorem idealSection_mul_idealSection (hsq : ∀ U : Opens X'.carrier,
      (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥)
    (U : (Opens X'.carrier)ᵒᵖ) (a b : (structureSheafRing X').obj.obj U)
    (ha : (structureSheafApp i U).hom a = 0) (hb' : (structureSheafApp i U).hom b = 0) :
    a * b = 0 := by
  have hmul : (RingHom.ker ((structureSheafHom i).hom.app U).hom) *
      (RingHom.ker ((structureSheafHom i).hom.app U).hom) = ⊥ := by
    have hp := hsq U.unop
    rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one] at hp
    exact hp
  have hmem := Ideal.mul_mem_mul (I := RingHom.ker ((structureSheafHom i).hom.app U).hom)
    (J := RingHom.ker ((structureSheafHom i).hom.app U).hom)
    (RingHom.mem_ker.mpr ha) (RingHom.mem_ker.mpr hb')
  rw [hmul] at hmem
  simpa using hmem

/-- **The Leibniz rule for the derivation attached to a trivialization**, for the
`𝒪_{X'}`-module structure on the ideal. -/
theorem trivializationDerivation_leibniz
    (hsq : ∀ U : Opens X'.carrier,
      (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥)
    (U : (Opens X'.carrier)ᵒᵖ) (r s : (structureSheafRing X').obj.obj U) :
    trivializationDerivation i π hb U (r * s) =
      r • trivializationDerivation i π hb U s + s • trivializationDerivation i π hb U r := by
  refine idealSection_injective i U ?_
  have hz : (r - (splitApp i π hb U).hom ((structureSheafApp i U).hom r)) *
      (s - (splitApp i π hb U).hom ((structureSheafApp i U).hom s)) = 0 :=
    idealSection_mul_idealSection i hsq U _ _ (sub_splitApp_mem_ker i π hb U r)
      (sub_splitApp_mem_ker i π hb U s)
  rw [idealSection_trivializationDerivation, idealSection_add, idealSection_smul,
    idealSection_smul, idealSection_trivializationDerivation,
    idealSection_trivializationDerivation, map_mul (structureSheafApp i U).hom,
    map_mul (splitApp i π hb U).hom]
  exact sub_mul_sub_leibniz (A := X'.presheaf.obj U) r s _ _ hz

/-- The derivation attached to a trivialization commutes with restriction. -/
theorem trivializationDerivation_naturality {U V : (Opens X'.carrier)ᵒᵖ} (f : U ⟶ V)
    (r : (structureSheafRing X').obj.obj U) :
    (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.map f
        (trivializationDerivation i π hb U r) =
      trivializationDerivation i π hb V (((structureSheafRing X').obj.map f).hom r) := by
  refine idealSection_injective i V ?_
  have hq : ((structureSheafRing X).obj.map ((Opens.map i.hom.base).op.map f)).hom
        ((structureSheafApp i U).hom r) =
      (structureSheafApp i V).hom (((structureSheafRing X').obj.map f).hom r) :=
    congrArg (fun g : (structureSheafRing X').obj.obj U ⟶
        (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj V) => g.hom r)
      ((structureSheafHom i).hom.naturality f).symm
  rw [idealSection_naturality, idealSection_trivializationDerivation,
    idealSection_trivializationDerivation, map_sub, splitApp_naturality, hq]

/-- The derivation kills every section coming from the splitting. -/
theorem trivializationDerivation_splitApp (U : (Opens X'.carrier)ᵒᵖ)
    (a : (structureSheafRing X).obj.obj ((Opens.map i.hom.base).op.obj U)) :
    trivializationDerivation i π hb U ((splitApp i π hb U).hom a) = 0 := by
  exact trivializationDerivation_eq_zero_aux i π hb U _
    (by rw [splitApp_structureSheafApp])

/-- The derivation vanishes on a section fixed by the splitting. Stated over an abstract
section `r` so that it can be applied in term mode to a section whose ring carries the
pushforward spelling, where `rw` would reject the motive. -/
theorem trivializationDerivation_eq_zero_of_splitApp_eq (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U)
    (hr : (splitApp i π hb U).hom ((structureSheafApp i U).hom r) = r) :
    trivializationDerivation i π hb U r = 0 :=
  trivializationDerivation_eq_zero_aux i π hb U r hr

/-- **The derivation kills every section pulled back along the trivialization.** For `r` a
section of `𝒪_X` over an open `V` of `X`, the section `π^♯ r` of `𝒪_{X'}` over `π^{-1} V` is
fixed by the splitting, so `d(π^♯ r) = 0`.

This is the reason the trivial extension becomes a *split* sequence once it is read as a
sequence of `𝒪_X`-modules: the correction term `c(d r ⊗ m)` in its action vanishes on every
scalar coming from `𝒪_X`. -/
theorem trivializationDerivation_retraction (V : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X).obj.obj V) :
    trivializationDerivation i π hb ((Opens.map π.retraction.hom.base).op.obj V)
      (((structureSheafHom π.retraction).hom.app V).hom r) = 0 :=
  trivializationDerivation_eq_zero_of_splitApp_eq i π hb _ _
    (splitApp_structureSheafApp_retraction i π hb V r)

/-- The derivation restricted to the ideal is the identity: for `a` a section of `ℐ`,
`d(ι a) = a`. This is what makes the canonical map of the trivial extension equal to `c`. -/
theorem trivializationDerivation_idealSection (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    trivializationDerivation i π hb U (idealSection i U a) = a := by
  refine idealSection_injective i U ?_
  rw [idealSection_trivializationDerivation, structureSheafApp_idealSection,
    map_zero (splitApp i π hb U).hom, sub_zero]

end Derivation

/-! ### Bilinearity of a map out of a tensor product of sections

The four laws that `Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule` asks of its
bilinear map are, for a map defined on a tensor product, the `TensorProduct` relations followed by
linearity. They are stated here over abstract data: the sections of the structure sheaf of a ringed
space carry two spellings of their ring structure — the `CommRingCat`-valued one that the tensor
product of `Stacks.SheafOfModules.TensorStalkRingedSpace` forms its scalars from, and the
`RingCat`-valued `structureSheafRing` one at which sheaves of modules are indexed — and instance
*search* cannot pass between them, since `structureSheafRing` is not reducible. Stating each law
once over abstract data and applying it in term mode lets the defeq be discharged by the elaborator
instead, which does see through the two spellings.
-/

section TensorHom

variable {A : Type u} [CommRing A] {M N : Type u}
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
  {P : ModuleCat.{u} A} (f : ModuleCat.of A (TensorProduct A M N) ⟶ P)

/-- A linear map out of `M ⊗[A] N` is additive in the left factor of a pure tensor. -/
theorem tensorHom_add_tmul (a b : M) (m : N) :
    f.hom ((a + b) ⊗ₜ[A] m) = f.hom (a ⊗ₜ[A] m) + f.hom (b ⊗ₜ[A] m) :=
  (congrArg f.hom (TensorProduct.add_tmul a b m)).trans (map_add f.hom _ _)

/-- A linear map out of `M ⊗[A] N` is additive in the right factor of a pure tensor. -/
theorem tensorHom_tmul_add (a : M) (m n : N) :
    f.hom (a ⊗ₜ[A] (m + n)) = f.hom (a ⊗ₜ[A] m) + f.hom (a ⊗ₜ[A] n) :=
  (congrArg f.hom (TensorProduct.tmul_add a m n)).trans (map_add f.hom _ _)

/-- A linear map out of `M ⊗[A] N` vanishes on `a ⊗ₜ 0`. -/
theorem tensorHom_tmul_zero (a : M) : f.hom (a ⊗ₜ[A] (0 : N)) = 0 :=
  (congrArg f.hom (TensorProduct.tmul_zero N a)).trans (map_zero f.hom)

/-- A linear map out of `M ⊗[A] N` vanishes on `0 ⊗ₜ m`. -/
theorem tensorHom_zero_tmul (m : N) : f.hom ((0 : M) ⊗ₜ[A] m) = 0 :=
  (congrArg f.hom (TensorProduct.zero_tmul M m)).trans (map_zero f.hom)

/-- A linear map out of `M ⊗[A] N` sends `(r • a) ⊗ₜ m` to `r • f (a ⊗ₜ m)`. -/
theorem tensorHom_smul_tmul (r : A) (a : M) (m : N) :
    f.hom ((r • a) ⊗ₜ[A] m) = r • f.hom (a ⊗ₜ[A] m) :=
  (congrArg f.hom (TensorProduct.smul_tmul' r a m).symm).trans (map_smul f.hom r _)

/-- A linear map out of `M ⊗[A] N` sends `a ⊗ₜ (r • m)` to `r • f (a ⊗ₜ m)`. -/
theorem tensorHom_tmul_smul (r : A) (a : M) (m : N) :
    f.hom (a ⊗ₜ[A] (r • m)) = r • f.hom (a ⊗ₜ[A] m) :=
  (congrArg f.hom (TensorProduct.tmul_smul r a m)).trans (map_smul f.hom r _)

end TensorHom

section Pairing

variable (F K : SheafOfModules.{u} (structureSheafRing X))
  (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
    ((idealSheafPullback i))).obj (F)) ⟶ K)

/-- The prescribed map `c : i^* ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`, read on sections over an open of `X'` as a
single `𝒪_{X'}(U)`-linear map out of `ℐ(U) ⊗ (i_* ℱ)(U)`: the comparison of **Stacks 08L4**
followed by `i_* c`, precomposed with the sheafification unit.

Keeping this a *single* linear map, rather than an iterated `LinearMap`, is what lets the
construction below need no commutativity hypothesis on the sheaf of rings: an iterated
`ℐ(U) →ₗ (i_*ℱ)(U) →ₗ (i_*𝒦)(U)` would need `Module 𝒪_{X'}(U) ((i_*ℱ)(U) →ₗ (i_*𝒦)(U))`,
hence `SMulCommClass`, which instance search cannot reach through
`CategoryTheory.forget₂ CommRingCat RingCat`. -/
noncomputable def extensionPairingHom (U : (Opens X'.carrier)ᵒᵖ) :
    ((PresheafOfModules.tensorObj (O := (X').presheaf)
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val)
      (((modulePushforward i).obj F).val))).obj U ⟶
      ((modulePushforward i).obj K).val.obj U :=
  (sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf)
    ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val)
    (((modulePushforward i).obj F).val)))).app U ≫
    (extensionTensorComparison i F ≫ (modulePushforward i).map c).val.app U

/-- The value of `c` on a pure tensor of local sections. -/
noncomputable def extensionPairing (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    ((modulePushforward i).obj K).val.obj U :=
  (extensionPairingHom i F K c U).hom (a ⊗ₜ[X'.presheaf.obj U] m)

/-- `AlgebraicGeometry.RingedSpaceThickening.extensionPairing` written out through the Tag 08L4
comparison, which is the shape in which
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction` characterises the canonical
map of an extension. -/
theorem extensionPairing_eq_comparison (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U a m =
      (((modulePushforward i).map c).val.app U).hom
        (((extensionTensorComparison i F).val.app U).hom
          (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i)
            ((modulePushforward i).obj F) U (a ⊗ₜ[X'.presheaf.obj U] m))) := rfl

/-- The pairing is additive in the section of the ideal sheaf. -/
theorem extensionPairing_add_left (U : (Opens X'.carrier)ᵒᵖ)
    (a b : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U (a + b) m =
      extensionPairing i F K c U a m + extensionPairing i F K c U b m :=
  tensorHom_add_tmul (extensionPairingHom i F K c U) a b m

/-- The pairing is additive in the section of `i_* ℱ`. -/
theorem extensionPairing_add_right (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m n : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U a (m + n) =
      extensionPairing i F K c U a m + extensionPairing i F K c U a n :=
  tensorHom_tmul_add (extensionPairingHom i F K c U) a m n

/-- The pairing vanishes when the section of `i_* ℱ` is zero. -/
theorem extensionPairing_zero_right (U : (Opens X'.carrier)ᵒᵖ)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U) :
    extensionPairing i F K c U a 0 = 0 :=
  tensorHom_tmul_zero (extensionPairingHom i F K c U) a

/-- The pairing vanishes when the section of the ideal sheaf is zero. -/
theorem extensionPairing_zero_left (U : (Opens X'.carrier)ᵒᵖ)
    (m : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U 0 m = 0 :=
  tensorHom_zero_tmul (extensionPairingHom i F K c U) m

/-- The pairing is `𝒪_{X'}(U)`-linear in the section of the ideal sheaf. -/
theorem extensionPairing_smul_left (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U (r • a) m = r • extensionPairing i F K c U a m :=
  tensorHom_smul_tmul (extensionPairingHom i F K c U) r a m

/-- The pairing is `𝒪_{X'}(U)`-linear in the section of `i_* ℱ`. -/
theorem extensionPairing_smul_right (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    extensionPairing i F K c U a (r • m) = r • extensionPairing i F K c U a m :=
  tensorHom_tmul_smul (extensionPairingHom i F K c U) r a m

/-- The pairing commutes with restriction along an inclusion of opens. -/
theorem extensionPairing_naturality {U V : (Opens X'.carrier)ᵒᵖ} (f : U ⟶ V)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj U)
    (m : ((modulePushforward i).obj F).val.obj U) :
    ((modulePushforward i).obj K).val.map f (extensionPairing i F K c U a m) =
      extensionPairing i F K c V
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val.map f a)
        (((modulePushforward i).obj F).val.map f m) := by
  have ht := PresheafOfModules.naturality_apply
    (sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf)
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val)
      (((modulePushforward i).obj F).val)))) f (a ⊗ₜ[X'.presheaf.obj U] m)
  have hE := PresheafOfModules.naturality_apply
    (extensionTensorComparison i F ≫ (modulePushforward i).map c).val f
    (((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf)
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i).val)
      (((modulePushforward i).obj F).val)))).app U).hom (a ⊗ₜ[X'.presheaf.obj U] m))
  exact hE.symm.trans (congrArg
    (((extensionTensorComparison i F ≫ (modulePushforward i).map c).val.app V).hom) ht.symm)

end Pairing

section TrivialExtension

variable (π : SplitMono i) (F K : SheafOfModules.{u} (structureSheafRing X))
  (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
    ((idealSheafPullback i))).obj (F)) ⟶ K) (hi : IsFirstOrderThickening i)

/-- **Stacks Project, Tag 08LB, part (1).** The *trivial extension* `ℱ'_{c,triv}` of `ℱ` by
`𝒦` attached to `c` and a trivialization `π`: the direct sum `ℱ ⊕ 𝒦`, carried to `X'` by `i_*`,
with the `𝒪_{X'}`-module structure built from the splitting of **Stacks 08LA** and the map `c`,

    r · (m, n) = (r m, r n + c(d r ⊗ m)),

where `d r = r - π^♯(i^♯ r)` is the derivation of the trivialization. -/
@[stacks 08LB "part (1): the trivial extension `ℱ'_{c,triv} = ℱ ⊕ 𝒦`"]
noncomputable def trivialExtensionModule : SheafOfModules.{u} (structureSheafRing X') :=
  Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule (𝟙 (structureSheafRing X'))
    (AlgebraicGeometry.SheafOfModules.idealSheaf i) ((modulePushforward i).obj F)
    ((modulePushforward i).obj K)
    (trivializationDerivation i π hi.1.1) (extensionPairing i F K c)
    (trivializationDerivation_zero i π hi.1.1)
    (trivializationDerivation_one i π hi.1.1)
    (trivializationDerivation_add i π hi.1.1)
    (fun U r s => trivializationDerivation_leibniz i π hi.1.1 hi.2 U r s)
    (extensionPairing_add_left i F K c) (extensionPairing_add_right i F K c)
    (extensionPairing_smul_left i F K c) (extensionPairing_smul_right i F K c)
    (fun {_ _} f r => trivializationDerivation_naturality i π hi.1.1 f r)
    (fun {_ _} f a m => extensionPairing_naturality i F K c f a m)

/-- **Stacks Project, Tag 08LB, part (1).** The `𝒪_{X'}`-module structure of the trivial
extension: a section of `𝒪_{X'}` acts diagonally on `ℱ ⊕ 𝒦` and moves the `ℱ`-coordinate into
the `𝒦`-coordinate through `c` and the derivation of the trivialization. Together with
`AlgebraicGeometry.RingedSpaceThickening.trivialExtensionModule`, whose sections over `U` are
by construction the pairs `ℱ(i^{-1}U) × 𝒦(i^{-1}U)`, this is the whole content of part (1). -/
@[stacks 08LB "part (1): the action of `𝒪_{X'}` on `ℱ ⊕ 𝒦`"]
theorem trivialExtensionModule_smul (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U)
    (z : (trivialExtensionModule i π F K c hi).val.obj U) :
    r • z = (r • z.1, r • z.2 +
      extensionPairing i F K c U (trivializationDerivation i π hi.1.1 U r) z.1) := rfl

/-- The action of `AlgebraicGeometry.RingedSpaceThickening.trivialExtensionModule` written out
on an explicit pair of local sections. -/
theorem trivialExtensionModule_smul_mk (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U) (m : ((modulePushforward i).obj F).val.obj U)
    (n : ((modulePushforward i).obj K).val.obj U) :
    r • (show (trivialExtensionModule i π F K c hi).val.obj U from (m, n)) =
      (show (trivialExtensionModule i π F K c hi).val.obj U from
        (r • m, r • n +
          extensionPairing i F K c U (trivializationDerivation i π hi.1.1 U r) m)) := rfl

/-- The inclusion of the second summand is `𝒪_{X'}`-linear: the correction term `c(d r ⊗ m)`
vanishes because its `ℱ`-argument is zero. -/
theorem trivialExtensionModule_smul_inr (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U) (n : ((modulePushforward i).obj K).val.obj U) :
    (show (trivialExtensionModule i π F K c hi).val.obj U from (0, r • n)) =
      r • (show (trivialExtensionModule i π F K c hi).val.obj U from (0, n)) := by
  rw [trivialExtensionModule_smul_mk, extensionPairing_zero_right, smul_zero, add_zero]

/-- The inclusion of `i_* 𝒦` as the second summand of the trivial extension. -/
noncomputable def trivialExtensionInr :
    (modulePushforward i).obj K ⟶ trivialExtensionModule i π F K c hi := by
  refine ⟨{
    app := fun U => ModuleCat.ofHom
      (X := ((modulePushforward i).obj K).val.obj U)
      (Y := (trivialExtensionModule i π F K c hi).val.obj U) {
        toFun := fun k => (0, k)
        map_add' := by
          intro a b
          change (0, a + b) = (0 + 0, a + b)
          rw [zero_add]
        map_smul' := fun r k => trivialExtensionModule_smul_inr i π F K c hi U r k }
    naturality := ?_ }⟩
  · intro U V f
    ext k
    change (0, ((modulePushforward i).obj K).val.map f k) =
      (((modulePushforward i).obj F).val.map f 0,
        ((modulePushforward i).obj K).val.map f k)
    rw [map_zero]

/-- The projection of the trivial extension onto `i_* ℱ`. -/
noncomputable def trivialExtensionFst :
    trivialExtensionModule i π F K c hi ⟶ (modulePushforward i).obj F :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := (trivialExtensionModule i π F K c hi).val.obj U)
        (Y := ((modulePushforward i).obj F).val.obj U) {
          toFun := Prod.fst
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
     naturality := fun _ => rfl }⟩

/-- The inclusion of `i_* 𝒦` followed by the projection to `i_* ℱ` is zero. -/
theorem trivialExtensionInr_fst :
    trivialExtensionInr i π F K c hi ≫ trivialExtensionFst i π F K c hi = 0 := by
  ext U k
  rfl

/-- The inclusion of `i_* 𝒦` into the trivial extension is a monomorphism. -/
theorem trivialExtensionInr_mono : Mono (trivialExtensionInr i π F K c hi) := by
  constructor
  intro M a b h
  ext U x
  exact congrArg (fun f => ((f.val.app U).hom x).2) h

/-- The projection of the trivial extension onto `i_* ℱ` is an epimorphism. -/
theorem trivialExtensionFst_epi : Epi (trivialExtensionFst i π F K c hi) := by
  constructor
  intro M a b h
  ext U x
  exact congrArg (fun f => (f.val.app U).hom (x, 0)) h

/-- A map into the trivial extension killed by the projection factors through the inclusion. -/
noncomputable def trivialExtensionKernelLift {M : SheafOfModules.{u} (structureSheafRing X')}
    (f : M ⟶ trivialExtensionModule i π F K c hi)
    (hf : f ≫ trivialExtensionFst i π F K c hi = 0) :
    M ⟶ (modulePushforward i).obj K := by
  have hfst (U) (x : M.val.obj U) : ((f.val.app U).hom x).1 = 0 :=
    congrArg (fun g => (g.val.app U).hom x) hf
  refine ⟨{
    app := fun U => ModuleCat.ofHom
      (X := M.val.obj U) (Y := ((modulePushforward i).obj K).val.obj U) {
        toFun := fun x => ((f.val.app U).hom x).2
        map_add' := by intro x y; rw [map_add]; rfl
        map_smul' := ?_ }
    naturality := ?_ }⟩
  · intro r x
    refine Eq.trans (congrArg Prod.snd ((map_smul (f.val.app U).hom r x).trans
      (trivialExtensionModule_smul i π F K c hi U r ((f.val.app U).hom x)))) ?_
    rw [hfst, extensionPairing_zero_right]
    exact add_zero _
  · intro U V g
    ext x
    exact congrArg Prod.snd (PresheafOfModules.naturality_apply f.val g x)

/-- The lift `trivialExtensionKernelLift` composed with the inclusion of `i_* 𝒦` recovers `f`. -/
theorem trivialExtensionKernelLift_inr {M : SheafOfModules.{u} (structureSheafRing X')}
    (f : M ⟶ trivialExtensionModule i π F K c hi)
    (hf : f ≫ trivialExtensionFst i π F K c hi = 0) :
    trivialExtensionKernelLift i π F K c hi f hf ≫ trivialExtensionInr i π F K c hi = f := by
  ext U x
  exact Prod.ext (congrArg (fun g => (g.val.app U).hom x) hf).symm rfl

/-- The short complex `0 ⟶ i_* 𝒦 ⟶ ℱ'_{c,triv} ⟶ i_* ℱ ⟶ 0` of the trivial extension. -/
noncomputable abbrev trivialExtensionShortComplex :
    ShortComplex (SheafOfModules.{u} (structureSheafRing X')) :=
  ShortComplex.mk (trivialExtensionInr i π F K c hi) (trivialExtensionFst i π F K c hi)
    (trivialExtensionInr_fst i π F K c hi)

/-- **Stacks Project, Tag 08LB, part (2).** The trivial extension sits in a short exact
sequence `0 ⟶ i_* 𝒦 ⟶ ℱ'_{c,triv} ⟶ i_* ℱ ⟶ 0` of `𝒪_{X'}`-modules: the inclusion of the
second summand is a kernel of the projection onto the first. -/
@[stacks 08LB "part (2): the trivial extension is an extension as in 08L4"]
theorem trivialExtensionShortComplex_shortExact :
    (trivialExtensionShortComplex i π F K c hi).ShortExact := by
  have : Mono (trivialExtensionInr i π F K c hi) := trivialExtensionInr_mono i π F K c hi
  have : Epi (trivialExtensionFst i π F K c hi) := trivialExtensionFst_epi i π F K c hi
  have hlim : IsLimit (KernelFork.ofι (trivialExtensionInr i π F K c hi)
      (trivialExtensionShortComplex i π F K c hi).zero) :=
    KernelFork.IsLimit.ofι _ _
      (fun f hf => trivialExtensionKernelLift i π F K c hi f hf)
      (fun f hf => trivialExtensionKernelLift_inr i π F K c hi f hf)
      (fun f hf m hm => (cancel_mono (trivialExtensionInr i π F K c hi)).mp
        (hm.trans (trivialExtensionKernelLift_inr i π F K c hi f hf).symm))
  exact ⟨(trivialExtensionShortComplex i π F K c hi).exact_of_f_is_kernel hlim⟩

/-- **Stacks Project, Tag 08LB, part (2).** The trivial extension, read as an extension of
`i_* ℱ` by `i_* 𝒦` in the sense of **Stacks 08L4**. -/
@[stacks 08LB "part (2): the trivial extension as a Yoneda extension"]
noncomputable def trivialYonedaExtension :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0 :=
  Abelian.shortExactYonedaExtension (trivialExtensionShortComplex_shortExact i π F K c hi)

/-- Two prescribed maps `c` with the same pairing on sections are equal: the Tag 08L4
comparison is the adjoint transpose of an isomorphism
(`AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_cancel`). -/
theorem extensionPairing_injective (hi' : IsThickening i)
    (c c' : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i))).obj (F)) ⟶ K)
    (h : ∀ U a m, extensionPairing i F K c U a m = extensionPairing i F K c' U a m) :
    c = c' := by
  refine extensionTensorComparison_cancel i hi' c c' (tensorSheaf_hom_ext ?_)
  intro V a m
  exact h (op V) a m

/-- **Stacks Project, Tag 08LB, part (2').** The canonical map of the trivial extension is the
prescribed one: `c_{ℱ'_{c,triv}} = c`. This is what places `ℱ'_{c,triv}` in the set of
extensions with `c = c_{ℱ'}` that part (4) of the remark puts in bijection with
`Ext¹_{𝒪_X}(ℱ, 𝒦)`. -/
@[stacks 08LB "part (2'): the canonical map of the trivial extension is `c`"]
theorem trivialYonedaExtension_action :
    (firstOrderExtensionAction i F K hi (trivialYonedaExtension i π F K c hi)).1 = c := by
  refine extensionPairing_injective i F K hi.1 _ c fun U a m => ?_
  have h := (firstOrderExtensionAction i F K hi (trivialYonedaExtension i π F K c hi)).2
    U.unop a m (m, 0) rfl
  have hs := congrArg Prod.snd h
  change _ = (idealSection i U a) • (0 : ((modulePushforward i).obj K).val.obj U) +
    extensionPairing i F K c U
      (trivializationDerivation i π hi.1.1 U (idealSection i U a)) m at hs
  rw [trivializationDerivation_idealSection, smul_zero, zero_add] at hs
  exact hs

end TrivialExtension

/-! ### The underlying class of an extension over a trivialized thickening

A trivialization retracts `i`, so pushing a sheaf of `𝒪_{X'}`-modules forward along
`π.retraction` reads it as a sheaf of `𝒪_X`-modules; this is the source's "use
`π^♯ : 𝒪_X ⟶ 𝒪_{X'}` to think of `ℱ'` as an `𝒪_X`-module". Applied to an extension
`0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` it gives a short exact sequence of `𝒪_X`-modules with outer terms
`𝒦` and `ℱ` themselves, hence a class `ξ_{ℱ'} ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)`.
-/

section SplitRestriction

variable (π : SplitMono i) (hb : IsIso i.hom.base)

include hb in
/-- The underlying map of a trivialization is an isomorphism of topological spaces: the
underlying map of the thickening is a two-sided inverse, by
`AlgebraicGeometry.RingedSpaceThickening.retraction_base_comp` in one direction and because `π`
retracts `i` in the other.

The trivialization itself is *not* an isomorphism of ringed spaces: `i ≫ π.retraction = 𝟙 X`,
but `π.retraction ≫ i` need not be `𝟙 X'`. Only the base map is inverted, which is all that
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isIso_base` asks for. -/
theorem isIso_retraction_base : IsIso π.retraction.hom.base :=
  ⟨i.hom.base, retraction_base_comp i π hb, base_comp_retraction_base i π⟩

/-- **Stacks Project, Tag 08LB, part (3).** Reading a sheaf of `𝒪_{X'}`-modules as a sheaf of
`𝒪_X`-modules along a trivialization: pushforward along the retraction.

This is the ringed-space form of the source's "use `π^♯ : 𝒪_X ⟶ 𝒪_{X'}` to think of `ℱ'` as an
`𝒪_X`-module". On a single site one would restrict scalars along `π^♯`
(`Stacks.SheafOfModules.restrictScalarsSplitIso`), but here `X` and `X'` carry different sites
`Opens X` and `Opens X'`, so the reindexing of opens along the homeomorphism `π` has to be
carried along with the restriction of scalars — which is exactly what `π_*` does. -/
@[stacks 08LB "part (3): reading an extension as an `𝒪_X`-module along the trivialization"]
noncomputable abbrev splitRestriction :
    SheafOfModules.{u} (structureSheafRing X') ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  modulePushforward π.retraction

/-- Pushing an `𝒪_X`-module forward along the thickening and then back along a trivialization
returns it: the two pushforwards compose to pushforward along `i ≫ π.retraction = 𝟙 X`. -/
noncomputable def splitRestrictionCompIso :
    modulePushforward i ⋙ splitRestriction i π ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  RingedSpaceModuleAdjunction.modulePushforwardComp i π.retraction ≪≫
    eqToIso (congrArg (fun f : X ⟶ X => modulePushforward f) π.id) ≪≫
      RingedSpaceModuleAdjunction.modulePushforwardId X

/-- The identification of an `𝒪_X`-module with its pushforward along the thickening read back
along the trivialization, on a single module. -/
noncomputable def splitRestrictionIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    (splitRestriction i π).obj ((modulePushforward i).obj M) ≅ M :=
  (splitRestrictionCompIso i π).app M

variable (F K : SheafOfModules.{u} (structureSheafRing X))
  (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
    ((modulePushforward i).obj K) 0)

/-- The short complex `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` underlying an extension of `𝒪_{X'}`-modules
across the thickening, in the sense of **Stacks 08L4**. -/
noncomputable abbrev extensionShortComplex :
    ShortComplex (SheafOfModules.{u} (structureSheafRing X')) :=
  ShortComplex.mk E.f E.g (E.exact_g.toIsComplex.zero 0)

/-- An extension across the thickening is a short exact sequence of `𝒪_{X'}`-modules: a
degree-one Yoneda extension carries exactly that data. -/
theorem extensionShortComplex_shortExact : (extensionShortComplex i F K E).ShortExact where
  exact := (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g

/-- The two maps of an extension, read along the trivialization and composed with the
identifications of the outer terms, compose to zero. -/
theorem splitExtension_comp_zero :
    ((splitRestrictionIso i π K).inv ≫ (splitRestriction i π).map E.f) ≫
      ((splitRestriction i π).map E.g ≫ (splitRestrictionIso i π F).hom) = 0 := by
  rw [Category.assoc, ← Category.assoc ((splitRestriction i π).map E.f), ← Functor.map_comp,
    (extensionShortComplex i F K E).zero, Functor.map_zero, zero_comp, comp_zero]

/-- **Stacks Project, Tag 08LB, part (3).** The extension `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` of
`𝒪_{X'}`-modules, read as a short complex of `𝒪_X`-modules along the trivialization. Its outer
terms are `𝒦` and `ℱ` themselves, by
`AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`. -/
@[stacks 08LB "part (3): an extension read as a sequence of `𝒪_X`-modules"]
noncomputable def splitExtension : ShortComplex (SheafOfModules.{u} (structureSheafRing X)) :=
  ShortComplex.mk
    ((splitRestrictionIso i π K).inv ≫ (splitRestriction i π).map E.f)
    ((splitRestriction i π).map E.g ≫ (splitRestrictionIso i π F).hom)
    (splitExtension_comp_zero i π F K E)

/-- The first map of
`AlgebraicGeometry.RingedSpaceThickening.splitExtension`, by definition. -/
@[simp]
theorem splitExtension_f : (splitExtension i π F K E).f =
    (splitRestrictionIso i π K).inv ≫ (splitRestriction i π).map E.f := rfl

/-- The second map of
`AlgebraicGeometry.RingedSpaceThickening.splitExtension`, by definition. -/
@[simp]
theorem splitExtension_g : (splitExtension i π F K E).g =
    (splitRestriction i π).map E.g ≫ (splitRestrictionIso i π F).hom := rfl

include hb in
/-- **Stacks Project, Tag 08LB, part (3).** An extension across the thickening, read along the
trivialization, is again short exact — which is what makes the class `ξ_{ℱ'}` available.

Pushforward along `π.retraction` is left exact because it is a right adjoint
(`RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint`) and right exact because the
base map of a trivialization is a homeomorphism
(`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isIso_base`), so the
sequence maps across by `CategoryTheory.ShortComplex.ShortExact.map_of_exact`; the outer terms
are then only reindexed by isomorphisms. -/
@[stacks 08LB "part (3): the sequence read over `𝒪_X` is short exact"]
theorem splitExtension_shortExact : (splitExtension i π F K E).ShortExact := by
  have := isIso_retraction_base i π hb
  have hMap := (extensionShortComplex_shortExact i F K E).map_of_exact (splitRestriction i π)
  refine ShortComplex.shortExact_of_iso ?_ hMap
  refine ShortComplex.isoMk (splitRestrictionIso i π K) (Iso.refl _)
    (splitRestrictionIso i π F) ?_ ?_
  · exact (Iso.hom_inv_id_assoc (splitRestrictionIso i π K)
      ((splitRestriction i π).map E.f)).trans (Category.comp_id _).symm
  · exact Category.id_comp _

include π hb E in
/-- **Stacks Project, Tag 08LB, part (3).** The class `ξ_{ℱ'} ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)` of an
extension of `ℱ` by `𝒦` across a trivialized first order thickening of ringed spaces: the
trivialization lets the extension be read as an extension of `𝒪_X`-modules, and this is the
class of that extension. -/
@[stacks 08LB "part (3): the class `ξ_{ℱ'}` of an extension"]
noncomputable def underlyingExtensionClass
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))] :
    CategoryTheory.Abelian.Ext F K 1 :=
  (splitExtension_shortExact i π hb F K E).extClass

end SplitRestriction

/-! ### The trivial extension has class zero -/

section ExtClassZero

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt.{e} 𝒞]

/-- **A short exact sequence whose first map has a retraction has zero `Ext`-class.** The
`Ext`-class of a short exact sequence is killed by precomposition with its first map
(`CategoryTheory.ShortComplex.ShortExact.extClass_comp_assoc`); if that map has a retraction
`ρ`, then `S.f ≫ ρ = 𝟙` exhibits the identity of `S.X₁` as such a precomposition, and
composing with the identity leaves the class alone.

This is the only thing clause (5) of the remark needs: a split sequence has zero class. -/
theorem extClass_eq_zero_of_retraction {S : ShortComplex 𝒞} (hS : S.ShortExact)
    (ρ : S.X₂ ⟶ S.X₁) (hρ : S.f ≫ ρ = 𝟙 S.X₁) : hS.extClass = 0 := by
  have h : Abelian.Ext.mk₀ (𝟙 S.X₁) =
      (Abelian.Ext.mk₀ S.f).comp (Abelian.Ext.mk₀ ρ) (zero_add 0) :=
    ((Abelian.Ext.mk₀_comp_mk₀ S.f ρ).trans (congrArg Abelian.Ext.mk₀ hρ)).symm
  refine (Abelian.Ext.comp_mk₀_id hS.extClass).symm.trans ?_
  rw [h]
  exact hS.extClass_comp_assoc _

end ExtClassZero

section TrivialExtensionClass

variable (π : SplitMono i) (F K : SheafOfModules.{u} (structureSheafRing X))
  (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
    ((idealSheafPullback i))).obj (F)) ⟶ K) (hi : IsFirstOrderThickening i)

/-- The action of a section of `𝒪_{X'}` that the derivation kills is diagonal on the trivial
extension: the correction term `c(d r ⊗ m)` has a zero argument, so it vanishes. -/
theorem trivialExtensionModule_smul_of_derivation_eq_zero (U : (Opens X'.carrier)ᵒᵖ)
    (r : (structureSheafRing X').obj.obj U) (hr : trivializationDerivation i π hi.1.1 U r = 0)
    (z : (trivialExtensionModule i π F K c hi).val.obj U) :
    r • z = (r • z.1, r • z.2) := by
  rw [trivialExtensionModule_smul, hr, extensionPairing_zero_left, add_zero]

/-- **The projection of the trivial extension onto its `𝒦`-summand**, read along the
trivialization. This is where the trivial extension differs from a general extension: the
projection `(m, n) ↦ n` is *not* `𝒪_{X'}`-linear — that is exactly the content of the
correction term `c(d r ⊗ m)` — but it becomes `𝒪_X`-linear once the scalars are pulled back
along `π`, because the derivation kills every such scalar
(`AlgebraicGeometry.RingedSpaceThickening.trivializationDerivation_retraction`). -/
noncomputable def restrictedTrivialExtensionSnd :
    (splitRestriction i π).obj (trivialExtensionModule i π F K c hi) ⟶
      (splitRestriction i π).obj ((modulePushforward i).obj K) :=
  ⟨{ app := fun V => ModuleCat.ofHom
        (X := ((splitRestriction i π).obj (trivialExtensionModule i π F K c hi)).val.obj V)
        (Y := ((splitRestriction i π).obj ((modulePushforward i).obj K)).val.obj V) {
          toFun := Prod.snd
          map_add' := fun _ _ => rfl
          map_smul' := fun r z => congrArg Prod.snd
            (trivialExtensionModule_smul_of_derivation_eq_zero i π F K c hi _
              (((structureSheafHom π.retraction).hom.app V).hom r)
              (trivializationDerivation_retraction i π hi.1.1 V r) z) }
     naturality := fun _ => rfl }⟩

/-- The projection of the trivial extension onto its `𝒦`-summand retracts the inclusion of that
summand: `(0, n) ↦ n`. -/
theorem trivialYonedaExtension_f_restrictedTrivialExtensionSnd :
    (splitRestriction i π).map (trivialYonedaExtension i π F K c hi).f ≫
      restrictedTrivialExtensionSnd i π F K c hi = 𝟙 _ := by
  ext V k
  rfl

/-- The trivial extension, read along the trivialization, is a split sequence of
`𝒪_X`-modules: the composite of
`AlgebraicGeometry.RingedSpaceThickening.restrictedTrivialExtensionSnd` with the identification
of the outer term retracts its first map. -/
theorem splitExtension_trivial_f_retraction :
    (splitExtension i π F K (trivialYonedaExtension i π F K c hi)).f ≫
        (restrictedTrivialExtensionSnd i π F K c hi ≫ (splitRestrictionIso i π K).hom) =
      𝟙 K :=
  have h : (splitRestriction i π).map (trivialYonedaExtension i π F K c hi).f ≫
      (restrictedTrivialExtensionSnd i π F K c hi ≫ (splitRestrictionIso i π K).hom) =
        (splitRestrictionIso i π K).hom :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ (splitRestrictionIso i π K).hom)
        (trivialYonedaExtension_f_restrictedTrivialExtensionSnd i π F K c hi))).trans
      (Category.id_comp _)
  (Category.assoc (splitRestrictionIso i π K).inv
      ((splitRestriction i π).map (trivialYonedaExtension i π F K c hi).f)
      (restrictedTrivialExtensionSnd i π F K c hi ≫
        (splitRestrictionIso i π K).hom)).trans
    ((congrArg (fun g => (splitRestrictionIso i π K).inv ≫ g) h).trans
      (splitRestrictionIso i π K).inv_hom_id)

/-- **Stacks Project, Tag 08LB, part (5).** The trivial extension maps to the zero class:
`ξ_{ℱ'_{c,triv}} = 0` in `Ext¹_{𝒪_X}(ℱ, 𝒦)`.

Read along the trivialization the sequence `0 ⟶ 𝒦 ⟶ ℱ ⊕ 𝒦 ⟶ ℱ ⟶ 0` splits, because the
derivation `d` kills every scalar pulled back along `π` and so the correction term `c(d r ⊗ m)`
in the action disappears — the projection onto the `𝒦`-summand, which is not `𝒪_{X'}`-linear,
becomes `𝒪_X`-linear. A split short exact sequence has zero class by
`AlgebraicGeometry.RingedSpaceThickening.extClass_eq_zero_of_retraction`. -/
@[stacks 08LB "part (5): the trivial extension has class `ξ_{ℱ'_{c,triv}} = 0`"]
theorem underlyingExtensionClass_trivialYonedaExtension
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))] :
    underlyingExtensionClass i π hi.1.1 F K (trivialYonedaExtension i π F K c hi) = 0 :=
  extClass_eq_zero_of_retraction _ _ (splitExtension_trivial_f_retraction i π F K c hi)

end TrivialExtensionClass

/-! ### The bijection with `Ext¹_{𝒪_X}(ℱ, 𝒦)`

Reading an extension along the trivialization is an exact functor, so it induces a homomorphism
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦) ⟶ Ext¹_{𝒪_X}(ℱ, 𝒦)` of abelian groups, which on the class of an
extension `ℱ'` is the class `ξ_{ℱ'}` of part (3). **Stacks 08L7** says that adding to `ℱ'` an
extension whose middle term is a direct image leaves the canonical map `c_{ℱ'}` alone, and that
two extensions with the same canonical map differ by exactly one such class; by **Stacks 08KS**
those classes are precisely the ones coming from `Ext¹_{𝒪_X}(ℱ, 𝒦)`. The trivial extension of
part (1) provides a point of the set of extensions with canonical map `c`, and part (5) says it
has class zero — which is what turns that free and transitive action into a bijection.
-/

section ExtensionClassBijection

variable (π : SplitMono i)

/-- Naturality of `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`: a map of
`𝒪_X`-modules pushed forward along the thickening and read back along the trivialization is the
map itself. -/
theorem splitRestrictionIso_naturality {M N : SheafOfModules.{u} (structureSheafRing X)}
    (φ : M ⟶ N) :
    (splitRestriction i π).map ((modulePushforward i).map φ) ≫
        (splitRestrictionIso i π N).hom =
      (splitRestrictionIso i π M).hom ≫ φ :=
  (splitRestrictionCompIso i π).hom.naturality φ

variable (hb : IsIso i.hom.base) (F K : SheafOfModules.{u} (structureSheafRing X))
  [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))]
  [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X'))]

include hb in
/-- Reading a class in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` as a class in `Ext¹_{𝒪_X}(ℱ, 𝒦)` along a
trivialization: the homomorphism induced on `Ext` by the exact functor
`AlgebraicGeometry.RingedSpaceThickening.splitRestriction`, with the outer terms reindexed by
`AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`.

On the class of an extension this is `ξ_{ℱ'}`, by
`AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_eq_splitRestrictionExtHom`, so
this is the map `ℱ' ↦ ξ_{ℱ'}` of part (4) of the remark read through the identification of
isomorphism classes of extensions with classes in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`. It is additive
because `Ext` of an exact functor is
(`CategoryTheory.Abelian.Ext.mapExactFunctor_add`) and because composition in `Ext` is. -/
noncomputable def splitRestrictionExtHom :
    Abelian.Ext.{e} ((modulePushforward i).obj F) ((modulePushforward i).obj K) 1 →+
      Abelian.Ext.{e} F K 1 :=
  haveI := isIso_retraction_base i π hb
  AddMonoidHom.mk'
    (fun ξ => (Abelian.Ext.mk₀ (splitRestrictionIso i π F).inv).comp
      ((ξ.mapExactFunctor (splitRestriction i π)).comp
        (Abelian.Ext.mk₀ (splitRestrictionIso i π K).hom) (add_zero 1)) (zero_add 1))
    (fun ξ₁ ξ₂ => by
      rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add])

include hb in
/-- The value of `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom` on the class
of a short exact sequence of `𝒪_{X'}`-modules which, read along the trivialization, maps to a
short exact sequence of `𝒪_X`-modules by the identity on both end terms: the two classes agree.

A morphism of short exact sequences which is the identity on the end terms preserves the class,
by `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`; here the end terms are only
reindexed by `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`, which is what the
two isomorphisms in the statement undo. -/
theorem splitRestrictionExtHom_extClass_of_hom
    {H : SheafOfModules.{u} (structureSheafRing X')} {a : (modulePushforward i).obj K ⟶ H}
    {b : H ⟶ (modulePushforward i).obj F} {w : a ≫ b = 0}
    (hT : (ShortComplex.mk a b w).ShortExact)
    {N : SheafOfModules.{u} (structureSheafRing X)} {f : K ⟶ N} {g : N ⟶ F} {w' : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w').ShortExact) (v : (splitRestriction i π).obj H ⟶ N)
    (hv : (splitRestriction i π).map a ≫ v = (splitRestrictionIso i π K).hom ≫ f)
    (hv' : v ≫ g = (splitRestriction i π).map b ≫ (splitRestrictionIso i π F).hom) :
    splitRestrictionExtHom i π hb F K hT.extClass = hS.extClass := by
  have := isIso_retraction_base i π hb
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hT.map_of_exact (splitRestriction i π)) hS
    { τ₁ := (splitRestrictionIso i π K).hom
      τ₂ := v
      τ₃ := (splitRestrictionIso i π F).hom
      comm₁₂ := hv.symm
      comm₂₃ := hv' }
  show (Abelian.Ext.mk₀ (splitRestrictionIso i π F).inv).comp
      ((hT.extClass.mapExactFunctor (splitRestriction i π)).comp
        (Abelian.Ext.mk₀ (splitRestrictionIso i π K).hom) (add_zero 1)) (zero_add 1) =
    hS.extClass
  rw [Abelian.Ext.mapExactFunctor_extClass, hnat, Abelian.Ext.mk₀_comp_mk₀_assoc,
    Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp]

include hb in
/-- **The map of part (4) is `ℱ' ↦ ξ_{ℱ'}`.** The class `ξ_{ℱ'} ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)` of an
extension across the thickening is the image of its class in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` under
`AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom`. -/
theorem underlyingExtensionClass_eq_splitRestrictionExtHom
    (E : Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0) :
    underlyingExtensionClass i π hb F K E =
      splitRestrictionExtHom i π hb F K (Abelian.YonedaExtension.shortExact E).extClass :=
  (splitRestrictionExtHom_extClass_of_hom i π hb F K (Abelian.YonedaExtension.shortExact E)
    (splitExtension_shortExact i π hb F K E) (𝟙 _)
    (by rw [Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm) (Category.id_comp _)).symm

include hb in
/-- `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom` undoes the pushforward: the
image of the class of a short exact sequence of `𝒪_X`-modules pushed forward along the
thickening is the class of the sequence itself, because `π_* ∘ i_*` is the identity. -/
theorem splitRestrictionExtHom_extClass_map [PreservesFiniteColimits (modulePushforward i)]
    {N : SheafOfModules.{u} (structureSheafRing X)} {f : K ⟶ N} {g : N ⟶ F} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) :
    splitRestrictionExtHom i π hb F K
        (hS.map_of_exact (modulePushforward i)).extClass = hS.extClass :=
  splitRestrictionExtHom_extClass_of_hom i π hb F K (hS.map_of_exact (modulePushforward i)) hS
    (splitRestrictionIso i π N).hom (splitRestrictionIso_naturality i π f)
    (splitRestrictionIso_naturality i π g).symm

variable (hi : IsFirstOrderThickening i)

omit hb in
include hi in
/-- **Stacks Project, Tag 08LB, part (4), injectivity.** Two extensions across the thickening
with the same canonical map and the same class `ξ` have the same class in
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`.

By **Stacks 08L7** the two classes differ by the class of exactly one extension whose middle
term is a direct image; such an extension is the pushforward of an extension of `𝒪_X`-modules
(**Stacks 08KS**), and `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom` carries
its class back to the class of that descent — which is therefore zero, and so is the difference
it came from. -/
theorem extClass_eq_of_underlyingExtensionClass_eq
    (E E' : Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0)
    (hact : (firstOrderExtensionAction i F K hi E).val =
      (firstOrderExtensionAction i F K hi E').val)
    (hξ : underlyingExtensionClass i π hi.1.1 F K E =
      underlyingExtensionClass i π hi.1.1 F K E') :
    (Abelian.YonedaExtension.shortExact E).extClass =
      (Abelian.YonedaExtension.shortExact E').extClass := by
  have hbase : IsIso i.hom.base := hi.1.1
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  obtain ⟨ζ, ⟨hζ, D, hDcl, hDess⟩, -⟩ :=
    existsUnique_extClass_sub_of_firstOrderExtensionAction_eq i F K hi E E' hact.symm
  obtain ⟨N, f, g, w₀, h₀, hmap⟩ := Abelian.exists_shortExact_mapExactFunctor_extClass_eq
    (modulePushforward i) (Abelian.YonedaExtension.shortExact D) hDess
  have hD : (Abelian.YonedaExtension.shortExact D).extClass =
      (h₀.map_of_exact (modulePushforward i)).extClass :=
    hmap.symm.trans (Abelian.Ext.mapExactFunctor_extClass (modulePushforward i) h₀)
  have hζΦ : splitRestrictionExtHom i π hi.1.1 F K ζ = h₀.extClass := by
    rw [← hDcl, hD]
    exact splitRestrictionExtHom_extClass_map i π hi.1.1 F K h₀
  have hsum : underlyingExtensionClass i π hi.1.1 F K E' =
      underlyingExtensionClass i π hi.1.1 F K E + h₀.extClass := by
    rw [underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E',
      underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E, hζ, map_add, hζΦ]
  have h₀zero : h₀.extClass = 0 := by
    have hcancel : h₀.extClass =
        (underlyingExtensionClass i π hi.1.1 F K E + h₀.extClass) -
          underlyingExtensionClass i π hi.1.1 F K E := by abel
    rw [hcancel, ← hsum, ← hξ, sub_self]
  have hζzero : ζ = 0 := by
    rw [← hDcl, hD, ← Abelian.Ext.mapExactFunctor_extClass (modulePushforward i) h₀, h₀zero,
      Abelian.Ext.mapExactFunctor_zero]
  rw [hζ, hζzero, add_zero]

omit hb in
include hi in
/-- **Stacks Project, Tag 08LB, part (4).** *Injectivity of `ℱ' ↦ ξ_{ℱ'}` on isomorphism
classes:* two extensions across the thickening with the same canonical map and the same class
`ξ` are isomorphic as extensions, by an isomorphism of their middle terms compatible with both
end terms.

This is `AlgebraicGeometry.RingedSpaceThickening.extClass_eq_of_underlyingExtensionClass_eq`
together with the fact that two short exact sequences with the same class in `Ext¹` are
isomorphic over the identity of both end terms
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`). -/
@[stacks 08LB "part (4): injectivity of `ℱ' ↦ ξ_{ℱ'}` — two extensions as in 08L4 with the same \
canonical map `c` and the same class `ξ` are isomorphic as extensions"]
theorem exists_iso_of_underlyingExtensionClass_eq
    (E E' : Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0)
    (hact : (firstOrderExtensionAction i F K hi E).val =
      (firstOrderExtensionAction i F K hi E').val)
    (hξ : underlyingExtensionClass i π hi.1.1 F K E =
      underlyingExtensionClass i π hi.1.1 F K E') :
    ∃ φ : E.Z.left ≅ E'.Z.left, E.f ≫ φ.hom = E'.f ∧ φ.hom ≫ E'.g = E.g :=
  ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} (structureSheafRing X')) ((modulePushforward i).obj F)
      ((modulePushforward i).obj K)).2.1 E.Z.left E'.Z.left E.f E.g _ E'.f E'.g _
    (Abelian.YonedaExtension.shortExact E) (Abelian.YonedaExtension.shortExact E')).1
    (extClass_eq_of_underlyingExtensionClass_eq i π F K hi E E' hact hξ)

omit hb in
include hi in
/-- **Stacks Project, Tag 08LB, part (4).** *Surjectivity of `ℱ' ↦ ξ_{ℱ'}`:* every class
`η ∈ Ext¹_{𝒪_X}(ℱ, 𝒦)` is the class `ξ_{ℱ'}` of an extension `ℱ'` as in **Stacks 08L4** whose
canonical map is the prescribed `c`.

Realize `η` as an extension of `𝒪_X`-modules and push it forward along the thickening: its
middle term is a direct image, so by **Stacks 08L7** it can be added to the trivial extension
`ℱ'_{c,triv}` of part (1) without changing the canonical map, which is `c` by part (2'). The
class of the sum is `0 + η = η` by part (5) and additivity. -/
@[stacks 08LB "part (4): surjectivity of `ℱ' ↦ ξ_{ℱ'}` — every class in `Ext¹_{𝒪_X}(ℱ, 𝒦)` is \
the class of an extension as in 08L4 with canonical map `c`"]
theorem exists_yonedaExtension_underlyingExtensionClass_eq
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i))).obj (F)) ⟶ K) (η : Abelian.Ext.{e} F K 1) :
    ∃ E : Abelian.YonedaExtension ((modulePushforward i).obj F)
        ((modulePushforward i).obj K) 0,
      (firstOrderExtensionAction i F K hi E).val = c ∧
        underlyingExtensionClass i π hi.1.1 F K E = η := by
  have hbase : IsIso i.hom.base := hi.1.1
  obtain ⟨N, f, g, w₀, h₀, hcl⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} (structureSheafRing X)) F K).1 η
  have hT := h₀.map_of_exact (modulePushforward i)
  have hDess : (modulePushforward i).essImage
      (Abelian.shortExactYonedaExtension hT).Z.left := Functor.obj_mem_essImage _ N
  obtain ⟨E, hEcl, hEact⟩ := exists_extClass_add_of_essImage i F K hi
    (trivialYonedaExtension i π F K c hi) (Abelian.shortExactYonedaExtension hT) hDess
  refine ⟨E, hEact.trans (trivialYonedaExtension_action i π F K c hi), ?_⟩
  rw [underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E, hEcl, map_add,
    ← underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K
      (trivialYonedaExtension i π F K c hi),
    underlyingExtensionClass_trivialYonedaExtension i π F K c hi, zero_add,
    Abelian.extClass_shortExactYonedaExtension hT,
    splitRestrictionExtHom_extClass_map i π hi.1.1 F K h₀]
  exact hcl

omit hb π in
/-- The isomorphism classes of extensions `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` as in **Stacks 08L4**
whose canonical map of **Stacks 08L4** is the prescribed `c`, represented by their classes in
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`.

Classes in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` are exactly the isomorphism classes of extensions of
`i_* ℱ` by `i_* 𝒦`: the class map is surjective and two extensions have the same class exactly
when they are isomorphic
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`). The canonical map
depends only on the class
(`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_eq_of_extClass_eq`), so
this set is well defined by the condition on a single representative. -/
def extensionClassesWithAction
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i))).obj (F)) ⟶ K) :
    Set (Abelian.Ext.{e} ((modulePushforward i).obj F) ((modulePushforward i).obj K) 1) :=
  {ξ | ∃ E : Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0,
    (Abelian.YonedaExtension.shortExact E).extClass = ξ ∧
      (firstOrderExtensionAction i F K hi E).val = c}

omit hb in
include hi in
/-- **Stacks Project, Tag 08LB, part (4).** `ℱ' ↦ ξ_{ℱ'}` *is a bijection* from the isomorphism
classes of extensions `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` as in **Stacks 08L4** with
`c = c_{ℱ'}` onto `Ext¹_{𝒪_X}(ℱ, 𝒦)`.

The isomorphism classes are the elements of
`AlgebraicGeometry.RingedSpaceThickening.extensionClassesWithAction`, i.e. are represented by
their classes in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`, and the map is
`AlgebraicGeometry.RingedSpaceThickening.splitRestrictionExtHom`, which on the class of `ℱ'` is
`ξ_{ℱ'}` by
`AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_eq_splitRestrictionExtHom`.
The two halves of the statement, read on extensions rather than on classes, are
`AlgebraicGeometry.RingedSpaceThickening.exists_yonedaExtension_underlyingExtensionClass_eq` and
`AlgebraicGeometry.RingedSpaceThickening.exists_iso_of_underlyingExtensionClass_eq`. -/
@[stacks 08LB "part (4): `ℱ' ↦ ξ_{ℱ'}` is a bijection from the isomorphism classes of \
extensions as in 08L4 with `c = c_{ℱ'}` onto `Ext¹_{𝒪_X}(ℱ, 𝒦)`, the isomorphism classes being \
represented by their classes in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`"]
theorem bijective_underlyingExtensionClass
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i))).obj (F)) ⟶ K) :
    Function.Bijective (fun ξ : ↥(extensionClassesWithAction i F K hi c) =>
      splitRestrictionExtHom i π hi.1.1 F K ξ.1) := by
  constructor
  · intro ξ₁ ξ₂ h
    obtain ⟨E₁, hE₁cl, hE₁act⟩ := ξ₁.2
    obtain ⟨E₂, hE₂cl, hE₂act⟩ := ξ₂.2
    refine Subtype.ext (hE₁cl.symm.trans ?_)
    refine (extClass_eq_of_underlyingExtensionClass_eq i π F K hi E₁ E₂
      (hE₁act.trans hE₂act.symm) ?_).trans hE₂cl
    rwa [underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E₁,
      underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E₂, hE₁cl, hE₂cl]
  · intro η
    obtain ⟨E, hEact, hEξ⟩ :=
      exists_yonedaExtension_underlyingExtensionClass_eq i π F K hi c η
    exact ⟨⟨(Abelian.YonedaExtension.shortExact E).extClass, E, rfl, hEact⟩,
      (underlyingExtensionClass_eq_splitRestrictionExtHom i π hi.1.1 F K E).symm.trans hEξ⟩

end ExtensionClassBijection

end AlgebraicGeometry.RingedSpaceThickening

end
