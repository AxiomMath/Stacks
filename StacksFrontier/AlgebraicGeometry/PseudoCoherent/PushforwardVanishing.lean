module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardOXMod

/-!
# `i_*F` vanishes away from the closed image, and what that gives Stacks 09VA

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and let `U` be an open subspace of `X` disjoint from the image of `i`. Then every
pushforward `i_*F` restricts to the zero module on `U`: the sections of `(i_*F)|_U` over an open
`W` of `U` are the sections of `F` over `i⁻¹(W) = ∅`, and a sheaf has a terminal, hence zero,
module of sections over the empty open.

This is the half-sentence with which Stacks 09VA disposes of a point `x ∈ X` lying outside `Z`
("If `x \notin Z` then this is clear"): on the open complement of the closed image, `Ri_*E` is a
zero object of the derived category, so the zero complex — which is strictly perfect — is already
a strictly perfect approximation of it in every degree.

## Main results

* `AlgebraicGeometry.RingedSpace.isZero_restrictModules_pushforward_of_preimage_eq_bot`:
  `(i_*F)|_U = 0` as an `𝒪_{X|U}`-module when `i⁻¹U = ∅`.
* `AlgebraicGeometry.RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot`:
  `(Ri_*E)|_U = 0` in `D(𝒪_{X|U})` under the same hypothesis.
* `AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_isZero`: a zero object
  of a derived category of `𝒪`-modules is approximated by the zero complex in every degree.
* `AlgebraicGeometry.RingedSpace.exists_local_approximation_derivedPushforward_of_notMem_range`:
  the resulting clause for a point of `X` outside the closed image, in exactly the shape
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derivedRestrict` consumes.

## Implementation notes

The vanishing is proved on sections and nowhere else. `(i_*F)|_U` is a single pushforward of
sheaves of modules, along the functor `W ↦ i⁻¹(ι_U W)` on opens
(`AlgebraicGeometry.RingedSpace.pushforward_comp_restrictModules_eq`, which holds by `rfl`), and
pushforward does not change the underlying module of sections. So the sections of `(i_*F)|_U` over
`W` are literally the sections of `F` over `i⁻¹(ι_U W)`, which is below `i⁻¹U = ∅`; the sheaf
condition makes those sections terminal in `AddCommGrpCat`
(`TopCat.Sheaf.isTerminalOfEqEmpty`), hence a zero object, hence trivial.

Passing to derived categories does not use any general theory either: a representative `𝒦` of `E`
is chosen by essential surjectivity of `DerivedCategory.Q`, and the two factorisations
`AlgebraicGeometry.RingedSpace.derivedPushforwardOXModFactors` and
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso` identify `(Ri_*E)|_U` with the image
under `DerivedCategory.Q` of the complex `(i_*𝒦)|_U`, every term of which is zero by the module
statement.

Both `AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` and
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` are used as the canonical functors; neither
is rebuilt, since `CategoryTheory.Limits.PreservesFiniteColimits` is data and a rebuilt functor
would not be provably the same one.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace StrictlyPerfect
open scoped ZeroObject

universe d d' u

namespace AlgebraicGeometry.RingedSpace

/-! ### Sections over the empty open -/

/-- A sheaf of `𝒪_Z`-modules has trivial sections over an open which is empty: the sheaf
condition for the empty covering of `∅` makes those sections a terminal object of
`AddCommGrpCat`, and a terminal object of an additive category is a zero object. -/
public theorem subsingleton_sections_of_eq_bot {Z : RingedSpace.{u, u}} (F : OXMod.{u, u} Z)
    {W : Opens Z.carrier} (hW : W = ⊥) : Subsingleton (F.val.obj (op W)) :=
  AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEqEmpty
      (⟨F.val.presheaf, F.isSheaf⟩ : TopCat.Sheaf _ Z.carrier) hW).isZero

/-- An `𝒪_Y`-module all of whose modules of sections are trivial is a zero object: its identity
morphism is zero, because on sections it is a map between trivial modules. -/
public theorem isZero_of_subsingleton_sections {Y : RingedSpace.{u, u}} (M : OXMod.{u, u} Y)
    (h : ∀ W : (Opens Y.carrier)ᵒᵖ, Subsingleton (M.val.obj W)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext W x
  exact (h W).elim _ _

/-! ### Vanishing of the restricted pushforward -/

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-- **`(i_*F)|_U = 0` when `U` misses the image of `i`.** If the preimage `i⁻¹U` is empty then
every `𝒪_Z`-module pushes forward to a module whose restriction to `U` is a zero object: the
sections of `(i_*F)|_U` over an open `W` of `U` are the sections of `F` over `i⁻¹(ι_U W)`, an open
below `i⁻¹U = ∅`. -/
public theorem isZero_restrictModules_pushforward_of_preimage_eq_bot
    (hU : (Opens.map i.hom.base).obj U = ⊥) (F : OXMod.{u, u} Z) :
    IsZero ((restrictModules X U).obj ((pushforwardOXMod i).obj F)) := by
  refine isZero_of_subsingleton_sections _ fun W => ?_
  have hle : U.isOpenEmbedding.functor.obj W.unop ≤ U := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := hy
    exact z.2
  refine subsingleton_sections_of_eq_bot F (W := (Opens.map i.hom.base).obj
    (U.isOpenEmbedding.functor.obj W.unop)) ?_
  rw [eq_bot_iff, ← hU]
  exact fun y hy => hle hy

/-- The restriction to `U` of the degreewise pushforward of a complex of `𝒪_Z`-modules is a zero
complex when `i⁻¹U` is empty: each of its terms is zero by
`AlgebraicGeometry.RingedSpace.isZero_restrictModules_pushforward_of_preimage_eq_bot`. -/
public theorem isZero_restrictComplex_pushforward_of_preimage_eq_bot
    (hU : (Opens.map i.hom.base).obj U = ⊥) (K : CochainComplex (OXMod.{u, u} Z) ℤ) :
    IsZero (restrictComplex
      (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) U) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  exact (isZero_restrictModules_pushforward_of_preimage_eq_bot i U hU (K.X j)).eq_of_src _ _

variable [HasDerivedCategory.{d} (OXMod.{u, u} Z)] [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **`(Ri_*E)|_U = 0` when `U` misses the image of `i`.** Choose a complex `𝒦` representing `E`;
then `Ri_*E` is the image under `DerivedCategory.Q` of the degreewise pushforward `i_*𝒦`
(`AlgebraicGeometry.RingedSpace.derivedPushforwardOXModFactors`) and its restriction to `U` is the
image of `(i_*𝒦)|_U` (`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`), a complex
with zero terms. -/
public theorem isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hU : (Opens.map i.hom.base).obj U = ⊥) (E : DerivedCategory (OXMod.{u, u} Z)) :
    IsZero ((derivedRestrictModules X U).obj ((derivedPushforwardOXMod i hi).obj E)) := by
  set K := DerivedCategory.Q.objPreimage E
  refine IsZero.of_iso (DerivedCategory.Q.isZero_obj
    (isZero_restrictComplex_pushforward_of_preimage_eq_bot i U hU K))
    ((derivedPushforwardOXMod i hi ⋙ derivedRestrictModules X U).mapIso
      (Functor.objObjPreimageIso DerivedCategory.Q E).symm ≪≫
      (derivedRestrictModules X U).mapIso ((derivedPushforwardOXModFactors i hi).app K) ≪≫
      derivedRestrictModulesObjQIso X U
        (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-! ### The approximation clause at a point outside the closed image -/

/-- A zero object of the derived category of `𝒪`-modules on a ringed space has a strictly perfect
approximation in every degree, namely the zero complex and the zero morphism: all the cohomology
objects in sight vanish, so that morphism is an isomorphism in every degree and in particular an
epimorphism. -/
public theorem exists_strictlyPerfect_approximation_of_isZero {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d'} (OXMod.{u, u} Y)] {F : DerivedCategory (OXMod.{u, u} Y)}
    (hF : IsZero F) (m : ℤ) :
    ∃ P : CochainComplex (OXMod.{u, u} Y) ℤ, IsStrictlyPerfect P ∧
      ∃ α : DerivedCategory.Q.obj P ⟶ F,
        (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map α) := by
  have hQ : IsZero (DerivedCategory.Q.obj (0 : CochainComplex (OXMod.{u, u} Y) ℤ)) :=
    DerivedCategory.Q.isZero_obj (isZero_zero _)
  refine ⟨0, isStrictlyPerfect_of_forall_isZero fun j =>
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) j).isZero_obj (isZero_zero _), 0,
    fun j _ => ?_, ?_⟩
  · exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).isZero_obj hQ).isIso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).isZero_obj hF) _
  · exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) m).isZero_obj hF).epi _

/-- **Stacks 09VA at a point outside `Z`.** Let `i : Z ⟶ X` be a morphism of ringed spaces whose
underlying continuous map is a closed embedding and let `x` be a point of `X` not in the image of
`i`. Then `x` has an open neighbourhood on which `Ri_*E` admits a strictly perfect approximation
in every degree, for every object `E` of `D(𝒪_Z)` and with no hypothesis on `E` at all.

The neighbourhood is the complement of the image, which is open because the image is closed, and
on it `Ri_*E` is a zero object
(`AlgebraicGeometry.RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot`).

This is the clause of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derivedRestrict` for the points of
`X` outside `Z`; the source dismisses it in one sentence, but it is the only place where the
*closedness* of the image, rather than merely the exactness of `i_*`, is used. -/
public theorem exists_local_approximation_derivedPushforward_of_notMem_range
    [∀ V : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    (hi : Topology.IsClosedEmbedding i.hom.base) (E : DerivedCategory (OXMod.{u, u} Z)) (m : ℤ)
    {x : X.carrier} (hx : x ∉ Set.range i.hom.base) :
    ∃ V : Opens X.carrier, x ∈ V ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶
            (derivedRestrictModules X V).obj ((derivedPushforwardOXMod i hi).obj E),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α) := by
  refine ⟨⟨(Set.range i.hom.base)ᶜ, hi.isClosed_range.isOpen_compl⟩, hx, ?_⟩
  refine exists_strictlyPerfect_approximation_of_isZero
    (isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot i _ hi ?_ E) m
  ext z
  simp

end AlgebraicGeometry.RingedSpace

end
