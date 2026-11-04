module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericLocalConstancy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeZeroRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# Generic local constancy of a constructible sheaf on Mathlib's small étale site

On a reduced Noetherian scheme `Y`, let `G` be a constructible abelian sheaf on Mathlib's small
étale site and `η` the generic point of an irreducible component. Inside any open neighbourhood of
`η` there is an open `U ∋ η`, contained in the closure of `η`, on which `G` is finite locally
constant. This is the definition of constructibility on a Noetherian scheme (a stratification into
locally closed pieces on which the sheaf is finite locally constant), read at the generic point.

The statement on the site of Tag 021B is
`AlgebraicGeometry.exists_opens_isFiniteLocallyConstant_of_mem_irreducibleComponents`, for sheaves
of sets. It produces an object `O` of the big étale site and an open immersion `O ⟶ Y`; the open
`U` is its range, which again lies in the big étale site, and the inverse image to `U` is the
inverse image to `O` pulled back along the isomorphism `U ≅ O`. The passage to Mathlib's site uses
`AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_sheafEquiv_functor_iff`, the compatibility
of the equivalence of the two sheaf categories with inverse image
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`), Stacks 00YT on Mathlib's site
(`Stacks.EtaleCohomology.isIso_inverseImageForgetComparison`) and the passage from the underlying
sheaf of sets back to the abelian sheaf
(`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget`).

## Main results

* `Stacks.EtaleCohomology.exists_opens_isFiniteLocallyConstant_etaleRestriction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Passing to the underlying sheaf of sets commutes with the restriction of an abelian sheaf on
Mathlib's small étale site to the site of Tag 021B: both are precomposition and postcomposition
with fixed functors. -/
def toBoundedSiteForgetIso {X : Scheme.{u}} (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (smallEtaleUnderlyingSetSheaf B (B.obj X hX)).obj ((toBoundedSiteAb B hX).obj F) ≅
      (SmallEtale.sheafEquiv B X hX (Type (u + 1))).inverse.obj ((etaleForget X).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)

/-- **Generic local constancy on Mathlib's small étale site.** On a reduced Noetherian scheme, a
constructible abelian sheaf is finite locally constant on an open neighbourhood of the generic
point of any irreducible component, contained in the closure of that point and in any prescribed
open neighbourhood of it. -/
theorem exists_opens_isFiniteLocallyConstant_etaleRestriction (Y : Scheme.{u}) [IsNoetherian Y]
    [IsReduced Y] (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsConstructibleSmallEtaleSheaf G) (η : Y) (hη : closure {η} ∈ irreducibleComponents Y)
    (N : Set Y) (hN : IsOpen N) (hηN : η ∈ N) :
    ∃ U : Y.Opens, η ∈ U ∧ (U : Set Y) ⊆ closure {η} ∧ (U : Set Y) ⊆ N ∧
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (U : Scheme.{u}).smallEtaleTopology
        ((etaleRestriction.{u, u + 1} U.ι).obj G) := by
  obtain ⟨B, hY, hB⟩ := hG
  let W : B.Scheme := B.obj Y hY
  have : IsReduced W.obj := ‹IsReduced Y›
  have : CompactSpace W.obj := (inferInstance : CompactSpace Y)
  have : QuasiSeparatedSpace W.obj := (inferInstance : QuasiSeparatedSpace Y)
  have : NoetherianSpace W.obj := (inferInstance : NoetherianSpace Y)
  let F := (smallEtaleUnderlyingSetSheaf B W).obj ((toBoundedSiteAb B hY).obj G)
  have hF : IsConstructibleSetSheaf B W F :=
    isConstructibleSetSheaf_underlying B W (smallEtaleUnderlyingSetCommutes B W) hB
  obtain ⟨O, o, ho, hηo, hcl, hNo, hlc⟩ :=
    exists_opens_isFiniteLocallyConstant_of_mem_irreducibleComponents B W F hF hη N hN hηN
  let φ : O.obj ⟶ Y := B.inclusion.map o
  let U : Y.Opens := φ.opensRange
  have hU : B.Contains U :=
    (Scheme.size_le_of_mono_quasiCompact φ.isoOpensRange.inv).trans_lt O.property
  let WU : B.Scheme := B.obj U hU
  let a : WU ⟶ O := ObjectProperty.homMk φ.isoOpensRange.inv
  let b : WU ⟶ W := ObjectProperty.homMk U.ι
  have hab : a ≫ o = b := by
    ext1
    exact φ.isoOpensRange_inv_comp
  have h1 : Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B WU.obj WU.property)
      ((smallEtaleSheafPullback B (Type (u + 1)) b).obj F) := by
    have := isFiniteLocallyConstant_smallEtaleSheafPullback_comp B (Type (u + 1)) o a F hlc
    rwa [hab] at this
  have h2 := (SmallEtale.isFiniteLocallyConstant_sheafEquiv_functor_iff B WU _).mpr h1
  let adjU := smallEtaleInverseImageAdjunction.{u, 0} U.ι
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B b
  let adjB := Functor.sheafAdjunctionContinuous (AlgebraicGeometry.smallEtaleBaseChange B b)
    (Type (u + 1)) (SmallEtale.topology B W.obj W.property)
    (SmallEtale.topology B WU.obj WU.property)
  let e1 := (SmallEtale.sheafEquivPullbackBaseChangeIso B b (Type (u + 1)) adjU adjB).app F
  let e2 : (SmallEtale.sheafEquiv B Y hY (Type (u + 1))).functor.obj F ≅ (etaleForget Y).obj G :=
    (SmallEtale.sheafEquiv B Y hY (Type (u + 1))).functor.mapIso (toBoundedSiteForgetIso B hY G) ≪≫
      (SmallEtale.sheafEquiv B Y hY (Type (u + 1))).counitIso.app _
  have := isIso_inverseImageForgetComparison U.ι G
  have h5 : Stacks.ConstantSheaf.IsFiniteLocallyConstant (U : Scheme.{u}).smallEtaleTopology
      ((etaleForget U).obj ((etaleRestriction.{u, u + 1} U.ι).obj G)) :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      (e1.symm ≪≫ (smallEtaleInverseImage.{u, 0} U.ι).mapIso e2 ≪≫
        asIso (inverseImageForgetComparison U.ι G) ≪≫
        (etaleForget U).mapIso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} U.ι).app G))
      (hF := h2)
  exact ⟨U, hηo, hcl, hNo, Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget _ _ h5⟩

end Stacks.EtaleCohomology

end
