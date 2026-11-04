module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsRepresentability
public import StacksFrontier.AlgebraicGeometry.Flatness.ModuleMapBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representing the isomorphism functor of a module map by a closed subscheme

Let `f : X ⟶ S` be a morphism of schemes and `u : F ⟶ G` a homomorphism of quasi-coherent
modules on `X`.  `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor` is the
subterminal functor on schemes over `S` recording where the base change of `u` becomes an
isomorphism.  [Stacks, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF) asserts that, when
`f` and `F` are of finite presentation, `F` is flat and pure relative to `S`, and `u` is
surjective, this functor is represented by a *closed* immersion into `S`, and that the closed
immersion is of finite presentation as soon as `G` is.

The formal content of the assertion, which is independent of the construction, is not restated
here: the functor is subterminal, so a representing morphism is a monomorphism and hence
automatically quasi-separated, and each of the remaining properties holds for *every*
representative as soon as it holds for one, all of this by the generic results of
`StacksFrontier/AlgebraicGeometry/Flatness/Representability.lean`.  What is proved here is a
reformulation of the construction itself
into the vocabulary the source's proof produces: a closed subscheme of `S` is the same thing as
an ideal sheaf on `S`, and a morphism to `S` factors through the closed subscheme cut out by an
ideal sheaf exactly when the ideal sheaf is contained in the kernel of that morphism.  So
representability by a closed immersion is *equivalent* to the existence of an ideal sheaf
`J ⊆ O_S` with

  `u_T` is an isomorphism `↔` `J ≤ ker (T ⟶ S)`

for every `T` over `S`; that ideal sheaf is what the source's devissage ultimately builds, out of
the flattening ideal of Tag 05PE in the affine case with projective sections.  The equivalence is
stated and proved as
`Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isFlatteningIdeal_iff`, so that the
hypothesis of the main theorem below cannot be mistaken for something weaker than its
conclusion: it is the same assertion in concrete terms, and the devissage is what remains.

Finite presentation of the representing closed immersion is reduced to a single concrete
hypothesis — that the flattening ideal sheaf is finitely generated on every affine open — which
gives all three of its constituents at once.  Local finite presentation comes from
`AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι`, and
quasi-compactness and quasi-separatedness are free, the first because a closed immersion is
affine and the second because a representing morphism is a monomorphism.  Finite generation of
the flattening ideal is the geometric form of the statement that the kernel of `u` is of finite
type, which is where the source's hypothesis that `G` is of finite presentation enters.  Here too
the exact strength of the hypothesis is recorded rather than asserted:
`Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isFlatteningIdeal_fg_iff` proves it
equivalent to the conjunction of the first assertion of Tag 05PF with local finite presentation of
the representing morphism, so what the second theorem below genuinely discharges are
quasi-compactness and quasi-separatedness, and what it leaves open is local finite presentation.

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsoFactorizationCriterion` is the elementary form
  of the representability assertion: a morphism into the base through which exactly the base
  changes making `u` an isomorphism factor.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsFlatteningIdeal` is the ideal-sheaf form of the
  same assertion.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_iff_ker_le`: a morphism factors through a closed
  immersion exactly when the kernel of the closed immersion is contained in its own kernel.
* `AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι_iff`: the closed
  immersion cut out by an ideal sheaf is locally of finite presentation exactly when the ideal
  sheaf is finitely generated on every affine open.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsFlatteningIdeal.unique`: there is at most one
  flattening ideal sheaf.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.representableByOfIsoFactorizationCriterion` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.isoFactorizationCriterion_of_representableBy`
  identify the elementary form with `CategoryTheory.Functor.RepresentableBy`.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isFlatteningIdeal_iff` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isFlatteningIdeal_fg_iff`: representability
  by a closed immersion is equivalent to the existence of a flattening ideal sheaf, and the
  refinement by finite generation to its being locally of finite presentation as well.
* `Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion` and
  `Stacks.Flatness.finitePresentation_of_representableBy_isomorphismFunctor` are the two
  assertions of Tag 05PF, the first granted a flattening ideal sheaf and the second granted a
  finitely generated one.

## Implementation notes

The slice-category glue is not rebuilt: `representableByOfSubsingleton` and
`subsingleton_over_hom_of_mono` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/FreeAtGenericPointsRepresentability.lean` are
stated for an arbitrary category and are reused verbatim.  They are what makes the naturality
check unnecessary: both `D.isomorphismFunctor.obj (op T)` and `T ⟶ W` are subsingletons when
`W.hom` is a monomorphism, so a natural bijection between them is determined by its mere
existence.

The source's conclusion "of finite presentation" is `AlgebraicGeometry.FinitePresentation` as
pinned down by Tag 01TP, the conjunction of its three constituent morphism properties.

## References

* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes factors through a closed immersion into its target exactly when the
kernel of that closed immersion is contained in its own kernel.  The forward direction is
monotonicity of the kernel under precomposition; the backward direction is the universal property
`AlgebraicGeometry.IsClosedImmersion.lift`. -/
@[ega "I 9.5.1" "criterion"]
theorem Scheme.Hom.exists_comp_eq_iff_ker_le {X Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (g : X ⟶ Y) :
    (∃ h : X ⟶ Z, h ≫ i = g) ↔ i.ker ≤ g.ker :=
  ⟨fun ⟨h, hh⟩ ↦ hh ▸ h.le_ker_comp i,
    fun H ↦ ⟨IsClosedImmersion.lift i g H, IsClosedImmersion.lift_fac _ _ _⟩⟩

/-- The closed immersion cut out by an ideal sheaf which is finitely generated on every affine
open is locally of finite presentation.

Local finite presentation is Zariski-local at the source, and on the affine open
`Spec (Γ(X, U) ⧸ J(U))` of the closed subscheme the composite with the inclusion is the quotient
map followed by an isomorphism and an open immersion; a quotient by a finitely generated ideal is
a ring map of finite presentation. -/
@[ega "IV 8.6.1" "Sufficient direction"]
theorem Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι {X : Scheme.{u}}
    (J : X.IdealSheafData) (hJ : ∀ U : X.affineOpens, (J.ideal U).FG) :
    LocallyOfFinitePresentation J.subschemeι := by
  have hlocal : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover J.subschemeCover.openCover fun U ↦ ?_
  have hcover : J.subschemeCover.openCover.f U ≫ J.subschemeι =
      J.glueDataObjι U ≫ U.1.ι := J.subschemeCover_map_subschemeι U
  have hι : J.glueDataObjι U =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) ≫ U.2.isoSpec.inv := rfl
  have hquot : (Ideal.Quotient.mk (J.ideal U)).FinitePresentation := by
    simpa using (RingHom.FinitePresentation.id Γ(X, U.1)).comp_surjective
      Ideal.Quotient.mk_surjective (by simpa using hJ U)
  have hspec : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)))) :=
    LocallyOfFinitePresentation.SpecMap_iff _ |>.mpr hquot
  rw [hcover, hι]
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.comp_mem _ _ _ hspec
      (locallyOfFinitePresentation_of_isOpenImmersion U.2.isoSpec.inv))
    (locallyOfFinitePresentation_of_isOpenImmersion U.1.ι)

/-- Conversely, an ideal sheaf whose closed immersion is locally of finite presentation is
finitely generated on every affine open: on the affine open `Spec (Γ(X, U) ⧸ J(U))` the induced
ring map is the quotient map, so its kernel `J(U)` is finitely generated because a surjection
between finitely presented algebras has finitely generated kernel. -/
@[ega "IV 8.6.1" "Necessary direction", sga "3 XI 6.4" "Forward implication"]
theorem Scheme.IdealSheafData.fg_ideal_of_locallyOfFinitePresentation_subschemeι
    {X : Scheme.{u}} (J : X.IdealSheafData) (h : LocallyOfFinitePresentation J.subschemeι)
    (U : X.affineOpens) : (J.ideal U).FG := by
  have hV : IsAffineOpen (J.subschemeι ⁻¹ᵁ U.1) := by
    rw [← J.opensRange_subschemeCover_map U]
    exact isAffineOpen_opensRange (H := J.subschemeCover.map_prop U) _
  have hfp : (J.subschemeι.app U.1).hom.FinitePresentation := by
    have happ := h.finitePresentation_appLE U.2 hV le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at happ
  rw [← J.ker_subschemeι_app U]
  let _ : Algebra Γ(X, U.1) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1) :=
    (J.subschemeι.app U.1).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(X, U.1) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1) := hfp
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(X, U.1) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1))
    (J.subschemeι_app_surjective U)

/-- The closed immersion cut out by an ideal sheaf is locally of finite presentation exactly when
the ideal sheaf is finitely generated on every affine open. -/
@[ega "IV 8.6.1"]
theorem Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι_iff {X : Scheme.{u}}
    (J : X.IdealSheafData) :
    LocallyOfFinitePresentation J.subschemeι ↔ ∀ U : X.affineOpens, (J.ideal U).FG :=
  ⟨fun h ↦ J.fg_ideal_of_locallyOfFinitePresentation_subschemeι h,
    J.locallyOfFinitePresentation_subschemeι⟩

end AlgebraicGeometry

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u})

/-- The elementary form of the representability assertion for the isomorphism functor: a morphism
`i : Z ⟶ S` such that the base change of `u` to a scheme over `S` is an isomorphism exactly when
the structure morphism of that scheme factors through `i`. -/
abbrev IsoFactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ D.S) : Prop :=
  ∀ T : Over D.S, D.IsIsomorphismAfterBaseChange T ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom

/-- A monomorphism satisfying the factorization criterion represents the isomorphism functor. -/
noncomputable def representableByOfIsoFactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ D.S)
    (hmono : Mono i) (hi : D.IsoFactorizationCriterion i) :
    D.isomorphismFunctor.RepresentableBy (Over.mk i) :=
  FreeAtGenericPointsSituation.representableByOfSubsingleton _ (Over.mk i) hmono fun T ↦
    (D.isomorphismFunctor_obj_nonempty_iff T).trans <| (hi T).trans
      ⟨fun ⟨g, hg⟩ ↦ ⟨Over.homMk g hg⟩, fun ⟨f⟩ ↦ ⟨f.left, Over.w f⟩⟩

/-- Conversely, the structure morphism of an object representing the isomorphism functor satisfies
the factorization criterion, so the criterion is an exact reformulation of representability and
not merely sufficient for it. -/
theorem isoFactorizationCriterion_of_representableBy {W : Over D.S}
    (e : D.isomorphismFunctor.RepresentableBy W) : D.IsoFactorizationCriterion W.hom := fun T ↦
  ⟨fun h ↦ ⟨(e.homEquiv.symm ⟨h⟩ : T ⟶ W).left, Over.w _⟩,
    fun ⟨g, hg⟩ ↦ (e.homEquiv (Over.homMk g hg)).down⟩

/-- An ideal sheaf on the base is a *flattening ideal* for the situation when it detects the
locus where the base change of `u` is an isomorphism: a scheme over `S` makes `u` an isomorphism
exactly when the ideal sheaf dies on it, that is, when it is contained in the kernel of the
structure morphism. -/
abbrev IsFlatteningIdeal (J : D.S.IdealSheafData) : Prop :=
  ∀ T : Over D.S, D.IsIsomorphismAfterBaseChange T ↔ J ≤ T.hom.ker

/-- The inclusion of the closed subscheme cut out by a flattening ideal sheaf satisfies the
factorization criterion. -/
private theorem isoFactorizationCriterion_subschemeι {J : D.S.IdealSheafData}
    (hJ : D.IsFlatteningIdeal J) : D.IsoFactorizationCriterion J.subschemeι := fun T ↦ by
  rw [hJ T, Scheme.Hom.exists_comp_eq_iff_ker_le J.subschemeι T.hom,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The closed subscheme cut out by a flattening ideal sheaf represents the isomorphism
functor. -/
theorem representableBy_closedImmersion_of_isFlatteningIdeal {J : D.S.IdealSheafData}
    (hJ : D.IsFlatteningIdeal J) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) :=
  ⟨Over.mk J.subschemeι, inferInstanceAs (IsClosedImmersion J.subschemeι),
    ⟨D.representableByOfIsoFactorizationCriterion J.subschemeι inferInstance
      (D.isoFactorizationCriterion_subschemeι hJ)⟩⟩

/-- Conversely, the kernel of a closed immersion representing the isomorphism functor is a
flattening ideal sheaf. -/
theorem isFlatteningIdeal_ker_of_representableBy {W : Over D.S} [IsClosedImmersion W.hom]
    (e : D.isomorphismFunctor.RepresentableBy W) : D.IsFlatteningIdeal W.hom.ker := by
  intro T
  rw [D.isoFactorizationCriterion_of_representableBy e T,
    Scheme.Hom.exists_comp_eq_iff_ker_le W.hom T.hom]

/-- A flattening ideal sheaf is unique: each of two of them dies on the closed subscheme cut out
by the other. -/
theorem IsFlatteningIdeal.unique {J J' : D.S.IdealSheafData} (hJ : D.IsFlatteningIdeal J)
    (hJ' : D.IsFlatteningIdeal J') : J = J' := by
  have key : ∀ K K' : D.S.IdealSheafData, D.IsFlatteningIdeal K → D.IsFlatteningIdeal K' →
      K' ≤ K := fun K K' hK hK' ↦ by
    simpa using (hK' _).mp ((hK (Over.mk K.subschemeι)).mpr (by simp))
  exact le_antisymm (key J' J hJ' hJ) (key J J' hJ hJ')

/-- Representability of the isomorphism functor by a closed immersion is *equivalent* to the
existence of a flattening ideal sheaf on the base.

This is the honest measure of the reduction carried out in this file: the hypothesis of
`Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion` is not weaker than its
conclusion, it is the same assertion written in terms of an ideal sheaf instead of a functor.
What the source's devissage supplies, and what is still missing, is the ideal sheaf itself. -/
theorem exists_isFlatteningIdeal_iff :
    (∃ J : D.S.IdealSheafData, D.IsFlatteningIdeal J) ↔
      ∃ W : Over D.S, IsClosedImmersion W.hom ∧
        Nonempty (D.isomorphismFunctor.RepresentableBy W) := by
  refine ⟨fun ⟨_, hJ⟩ ↦ D.representableBy_closedImmersion_of_isFlatteningIdeal hJ,
    fun ⟨W, hW, e⟩ ↦ ?_⟩
  have := hW
  exact ⟨W.hom.ker, D.isFlatteningIdeal_ker_of_representableBy e.some⟩

/-- Refining the previous equivalence by finite generation: a *finitely generated* flattening
ideal sheaf exists exactly when the isomorphism functor is represented by a closed immersion that
is locally of finite presentation.

This measures the hypothesis of
`Stacks.Flatness.finitePresentation_of_representableBy_isomorphismFunctor` exactly.  That
hypothesis is equivalent to the conjunction of Tag 05PF's first assertion with local finite
presentation of the representing morphism; what the theorem below genuinely discharges are the
other two constituents of finite presentation, quasi-compactness and quasi-separatedness. -/
theorem exists_isFlatteningIdeal_fg_iff :
    (∃ J : D.S.IdealSheafData, D.IsFlatteningIdeal J ∧ ∀ U : D.S.affineOpens, (J.ideal U).FG) ↔
      ∃ W : Over D.S, IsClosedImmersion W.hom ∧ LocallyOfFinitePresentation W.hom ∧
        Nonempty (D.isomorphismFunctor.RepresentableBy W) := by
  refine ⟨fun ⟨J, hJ, hfg⟩ ↦ ⟨Over.mk J.subschemeι,
    inferInstanceAs (IsClosedImmersion J.subschemeι), J.locallyOfFinitePresentation_subschemeι hfg,
    ⟨D.representableByOfIsoFactorizationCriterion J.subschemeι inferInstance
      (D.isoFactorizationCriterion_subschemeι hJ)⟩⟩,
    fun ⟨W, hci, hlfp, e⟩ ↦ ?_⟩
  have := hci
  refine ⟨W.hom.ker, D.isFlatteningIdeal_ker_of_representableBy e.some, fun U ↦ ?_⟩
  refine W.hom.ker.fg_ideal_of_locallyOfFinitePresentation_subschemeι ?_ U
  have hfac : inv W.hom.toImage ≫ W.hom = W.hom.ker.subschemeι := by
    rw [IsIso.inv_comp_eq]
    exact (Scheme.Hom.toImage_imageι W.hom).symm
  rw [← hfac]
  exact MorphismProperty.comp_mem _ _ _
    (locallyOfFinitePresentation_of_isOpenImmersion (inv W.hom.toImage)) hlfp

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness

/-- **Stacks Project, Tag 05PF.** The isomorphism-after-base-change functor of a surjection from a
finitely presented, flat and pure module is represented by a closed immersion into the base.

The construction of the representing closed subscheme is the hypothesis `hJ`: it asks for an ideal
sheaf on the base which dies exactly on those schemes over the base on which `u` becomes an
isomorphism.  By
`Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isFlatteningIdeal_iff` that hypothesis is
equivalent to the conclusion, so nothing of the source's devissage is discharged here; what the
theorem does supply is the dictionary between the two formulations, which is the form in which
the devissage's output — the flattening ideal of Tag 05PE — presents itself. -/
theorem isomorphismFunctor_representableBy_closedImmersion
    (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [Epi D.hom]
    (_hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (_hpure : IsPureRelative D.f D.F)
    (hJ : ∃ J : D.S.IdealSheafData, D.IsFlatteningIdeal J) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) :=
  D.exists_isFlatteningIdeal_iff.mp hJ

/-- **Stacks Project, Tag 05PF.** If the target module is finitely presented, every morphism
representing the isomorphism-after-base-change functor is of finite presentation.

All three constituents are obtained from the single hypothesis `hJ`, that the flattening ideal
sheaf of the situation exists and is finitely generated on every affine open of the base; unlike
the hypothesis of
`Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion`, the finite generation is
genuine new input and not a restatement of the conclusion.  Quasi-separatedness in fact needs no
hypothesis at all — the functor is subterminal, so a representing morphism is a monomorphism —
and quasi-compactness follows because a closed immersion is an affine morphism. -/
theorem finitePresentation_of_representableBy_isomorphismFunctor
    (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [D.G.IsFinitePresentation] [Epi D.hom]
    (_hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (_hpure : IsPureRelative D.f D.F)
    (hJ : ∃ J : D.S.IdealSheafData, D.IsFlatteningIdeal J ∧
      ∀ U : D.S.affineOpens, (J.ideal U).FG)
    (W : Over D.S) (hW : Nonempty (D.isomorphismFunctor.RepresentableBy W)) :
    FinitePresentation W.hom := by
  obtain ⟨J, hJ, hfg⟩ := hJ
  have e₀ := D.representableByOfIsoFactorizationCriterion J.subschemeι inferInstance
    (D.isoFactorizationCriterion_subschemeι hJ)
  exact FinitePresentation.mk
    (locallyOfFinitePresentation_hom_of_representableBy e₀ hW.some
      (J.locallyOfFinitePresentation_subschemeι hfg))
    (quasiCompact_hom_of_representableBy e₀ hW.some
      (inferInstanceAs (QuasiCompact J.subschemeι)))
    (quasiSeparated_hom_of_representableBy hW.some)

end Stacks.Flatness
