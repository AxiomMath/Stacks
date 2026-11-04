module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.AlgebraicTopology.SimplicialObject.HomotopyEquivalenceProjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.HomologyOnACategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution

/-!
# Restriction along a point resolution preserves projective diagrams

Let `C` be a small category, let `D` be an abelian category with coproducts indexed by the
morphism universe of `C`, and let `U_•` be a cosimplicial object of `C` which is a point
resolution in the sense of `Stacks.ChaoticSite.IsPointResolution`. This file proves that
restriction of diagrams along `U.op : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ` carries **projective** diagrams
`Cᵒᵖ ⥤ D` to projective simplicial objects of `D`.

The point to notice is that this is *not* a formality, and that the companion statement for an
arbitrary functor between the index categories is **false**: restriction along a functor does not
preserve projectives in general. Already for `C` the terminal category and `U` the constant
cosimplicial object at `⦋0⦌` — a point resolution on the nose, every `Mor_C(U_•, W)` being a
singleton — the restriction of a free diagram is the *constant* simplicial object on a projective
object `P` of `D`, whose projectivity amounts, through the adjunction `const ⊣ lim`, to the
exactness of `lim` over `SimplexCategory`, which is a kernel of two cofaces and is only left
exact. What rescues the statement here is that `Mor_C(U_•, W)` is homotopy equivalent to a point,
so `U.op ⋙ freeYoneda W P` is a simplicial object with projective terms *homotopy equivalent* to
a constant one, and such an object is projective by Dold–Kan
(`CategoryTheory.SimplicialObject.projective_of_homotopyEquivalence_const`).

From the free diagrams the statement propagates to all projectives: when the coefficients have
enough projectives, every diagram is a quotient of a coproduct of free diagrams, so a projective
diagram is a *retract* of such a coproduct, and restriction preserves coproducts and retracts.

## Main results

* `Stacks.ChaoticSite.projective_restrict_freeYoneda`:
  `Projective (U.op ⋙ CategoryTheory.Presheaf.freeYoneda W P)`.
* `Stacks.ChaoticSite.epi_freeYonedaPresentation`: every diagram is a quotient of the coproduct
  of the free diagrams on a projective cover of each of its values.
* `Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`: restriction
  along `U.op` preserves projective objects.
* `Stacks.ChaoticSite.preservesEpimorphisms_rightAdjoint_restrictAlongPointResolution`: the
  equivalent statement about the right adjoint `Ran_{U.op}`, wherever that right adjoint exists —
  it preserves epimorphisms, i.e. it is exact.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe uD vD v u

namespace Stacks.ChaoticSite

/-- **A three-fold factorisation of an epimorphism makes its last factor an epimorphism.**
`CategoryTheory.epi_of_epi_fac` read after re-associating, which spares the caller writing out
the implicit index type of the first factor. -/
theorem epi_of_epi_threeFac {A : Type*} [Category* A] {X Y Z T : A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ T} {k : X ⟶ T} (w : f ≫ g ≫ h = k) [Epi k] : Epi h :=
  epi_of_epi_fac ((Category.assoc f g h).trans w)

variable {C : Type u} [SmallCategory C] {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasCoproducts.{u} D]

/-- **The restriction of a free diagram along a point resolution is projective.** The free
diagram `CategoryTheory.Presheaf.freeYoneda W P` is `yoneda.obj W` followed by the functor
`CategoryTheory.Limits.sigmaConst.obj P` taking a set to the coproduct of copies of `P`; so its
restriction along `U.op` is that functor applied to the simplicial set `Mor_C(U_•, W)`. Its terms
are coproducts of copies of `P`, hence projective, and the chosen homotopy equivalence of
`Mor_C(U_•, W)` with the constant singleton simplicial set is carried to a homotopy equivalence
with the constant simplicial object on a coproduct of copies of `P`; so
`CategoryTheory.SimplicialObject.projective_of_homotopyEquivalence_const` applies. -/
theorem projective_restrict_freeYoneda {U : CosimplicialObject C} (hU : IsPointResolution U)
    (W : C) (P : D) [Projective P] :
    Projective (U.op ⋙ Presheaf.freeYoneda W P) := by
  obtain ⟨a, ha⟩ := hU W
  let T : Type u ⥤ D := sigmaConst.obj P
  have hobj : ∀ m : SimplexCategoryᵒᵖ, Projective (((U.op ⋙ yoneda.obj W) ⋙ T).obj m) :=
    fun m ↦ projective_sigma (X := fun _ : (U.op ⋙ yoneda.obj W).obj m ↦ P)
  have hpt : Projective (T.obj PUnit.{u + 1}) :=
    projective_sigma (X := fun _ : PUnit.{u + 1} ↦ P)
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} ⋙ T ≅
      (SimplicialObject.const D).obj (T.obj PUnit.{u + 1}) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact SimplicialObject.projective_of_homotopyEquivalence_const
    ((U.op ⋙ yoneda.obj W) ⋙ T) (T.obj PUnit.{u + 1}) (Functor.whiskerRight a T ≫ e.hom)
    (SimplicialObject.homotopyEquivalences_comp_iso
      (SimplicialObject.homotopyEquivalences_whiskerRight T ha) e)

section Presentation

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasCoproducts.{v} D] [HasCoproducts.{u} D] [EnoughProjectives D] (Z : Cᵒᵖ ⥤ D)

/-- The coproduct, over the objects of `C`, of the free diagrams on a projective cover of the
corresponding value of `Z`. -/
abbrev freeYonedaPresentationSrc : Cᵒᵖ ⥤ D :=
  ∐ fun W : C ↦ Presheaf.freeYoneda W (Projective.over (Z.obj (op W)))

/-- The canonical morphism from `Stacks.ChaoticSite.freeYonedaPresentationSrc` to `Z`, whose
component at `W` is the projective cover of `Z(W)` read through
`CategoryTheory.Presheaf.freeYonedaHomEquiv`. -/
def freeYonedaPresentation : freeYonedaPresentationSrc Z ⟶ Z :=
  Sigma.desc fun W ↦ Presheaf.freeYonedaHomEquiv.symm (Projective.π (Z.obj (op W)))

/-- **A coproduct of free diagrams on projective covers is projective.** -/
instance projective_freeYonedaPresentationSrc : Projective (freeYonedaPresentationSrc Z) :=
  projective_sigma
    (X := fun W : C ↦ Presheaf.freeYoneda W (Projective.over (Z.obj (op W))))

/-- **Every diagram is a quotient of a coproduct of free diagrams on projective covers.** At the
object `V` the composite of the inclusion of the summand indexed by `V.unop` with the free
diagram's own unit is the projective cover of `Z(V)`, which is an epimorphism. -/
instance epi_freeYonedaPresentation : Epi (freeYonedaPresentation Z) := by
  have happ : ∀ V : Cᵒᵖ, Epi ((freeYonedaPresentation Z).app V) := by
    rintro ⟨W⟩
    have hι : Sigma.ι (fun W' : C ↦ Presheaf.freeYoneda W' (Projective.over (Z.obj (op W'))))
          W ≫ freeYonedaPresentation Z =
        Presheaf.freeYonedaHomEquiv.symm (Projective.π (Z.obj (op W))) :=
      Sigma.ι_desc _ _
    have h2 := congrArg Presheaf.freeYonedaHomEquiv hι
    rw [Equiv.apply_symm_apply] at h2
    simp only [Presheaf.freeYonedaHomEquiv, Equiv.coe_fn_mk, NatTrans.comp_app] at h2
    exact epi_of_epi_threeFac h2
  exact NatTrans.epi_of_epi_app _

end Presentation

/-- **Restriction along a point resolution preserves projective diagrams.** A projective diagram
`Z` is a retract of the coproduct `Stacks.ChaoticSite.freeYonedaPresentationSrc Z` of free
diagrams, because `Stacks.ChaoticSite.freeYonedaPresentation` is an epimorphism out of it onto
`Z`. Restriction along `U.op` preserves coproducts, being precomposition, and carries each free
summand to a projective simplicial object by
`Stacks.ChaoticSite.projective_restrict_freeYoneda`; so it carries the coproduct to a projective
object and the retract to a retract of it. -/
theorem preservesProjectiveObjects_restrictAlongPointResolution [EnoughProjectives D]
    {U : CosimplicialObject C} (hU : IsPointResolution U) :
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op).PreservesProjectiveObjects := by
  constructor
  intro Z hZ
  set r := (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op
  have hsum : Projective (r.obj (freeYonedaPresentationSrc Z)) := by
    have : ∀ W : C, Projective
        (r.obj (Presheaf.freeYoneda W (Projective.over (Z.obj (op W))))) :=
      fun W ↦ projective_restrict_freeYoneda hU W _
    exact Projective.of_iso (PreservesCoproduct.iso r
      (fun W : C ↦ Presheaf.freeYoneda W (Projective.over (Z.obj (op W))))).symm projective_sigma
  exact Retract.projective
    { i := r.map (Projective.factorThru (𝟙 Z) (freeYonedaPresentation Z))
      r := r.map (freeYonedaPresentation Z)
      retract := by rw [← r.map_comp, Projective.factorThru_comp, CategoryTheory.Functor.map_id] }

/-- **The right adjoint of restriction along a point resolution preserves epimorphisms**, that
is, it is exact — the form in which the previous statement enters the transfer of a derived
functor along the restriction. It is the general equivalence
`CategoryTheory.Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects` read
at `Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`; the right
adjoint is taken as data, so nothing is assumed about which limits in `D` make it exist. -/
theorem preservesEpimorphisms_rightAdjoint_restrictAlongPointResolution [EnoughProjectives D]
    [EnoughProjectives (Cᵒᵖ ⥤ D)] {U : CosimplicialObject C} (hU : IsPointResolution U)
    (R : (SimplexCategoryᵒᵖ ⥤ D) ⥤ (Cᵒᵖ ⥤ D))
    (adj : (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ D).obj U.op ⊣ R) :
    R.PreservesEpimorphisms := by
  have := preservesProjectiveObjects_restrictAlongPointResolution (D := D) hU
  exact Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects adj

end Stacks.ChaoticSite

end
