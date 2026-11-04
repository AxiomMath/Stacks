module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# Finite coproducts of quasi-compact algebraic spaces

A coproduct of finitely many algebraic spaces over `S` is an algebraic space over `S`, and it
is quasi-compact as soon as all the summands are.

Algebraicity is Tag 02WQ once the chosen surjective étale atlases of the summands are known to
have a coproduct inside the big fppf site over `S`; finitely many objects of the site always
do, because the size cutoff is closed under finite coproducts of schemes. Quasi-compactness is
read on points: the ranges of the legs are open subspaces which cover the point space, each is
the continuous image of a quasi-compact point space by Tag 03E4, and a finite union of
quasi-compact sets is quasi-compact, so Tag 03E4 applies in the other direction.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_finiteCoproduct` and
  `AlgebraicGeometry.Space.isQuasiCompactSpace_finiteCoproduct` are the two assertions of
  **Stacks 040T**.
* `AlgebraicGeometry.BigFppfSite.hasFiniteCoproducts_schemes` and
  `AlgebraicGeometry.Space.hasFiniteCoproducts_bigFppfOver`: the big fppf site and its slice
  over `S` have finite coproducts.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 040T](https://stacks.math.columbia.edu/tag/040T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The schemes of a big fppf site are closed under finite coproducts, so the underlying
category of the site has them: a finite coproduct of schemes below the cutoff is below the
cutoff by `AlgebraicGeometry.Scheme.size_sigmaObj_lt`. -/
theorem BigFppfSite.hasFiniteCoproducts_schemes (B : BigFppfSite.{u}) :
    HasFiniteCoproducts B.Schemes := by
  have hclosed : (schemeSizeBelow B.cutoff).IsClosedUnderFiniteCoproducts :=
    ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
      (fun J _ ↦ by
        refine ⟨?_⟩
        rintro X ⟨hX⟩
        set Y : J → Scheme.{u} := fun i ↦ hX.diag.obj ⟨i⟩ with hY
        have hYsize : ∀ i, (Y i).size < B.cutoff := fun i ↦ hX.prop_diag_obj ⟨i⟩
        have hsum : (∐ Y).size < B.cutoff :=
          Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
            Cardinal.mk_le_aleph0 Y hYsize
        have hsumColim : IsColimit ((Cocone.precompose
            (Discrete.natIsoFunctor (F := hX.diag)).symm.hom).obj hX.cocone) :=
          (IsColimit.precomposeHomEquiv (Discrete.natIsoFunctor (F := hX.diag)).symm
            hX.cocone).symm hX.isColimit
        let eX : X ≅ ∐ Y := hsumColim.coconePointUniqueUpToIso (coproductIsCoproduct Y)
        show X.size < B.cutoff
        rw [Scheme.size_congr eX]
        exact hsum)
  show HasFiniteCoproducts (schemeSizeBelow B.cutoff).FullSubcategory
  infer_instance

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf category over `S` has finite coproducts, being a slice of a category with
finite coproducts over an object. -/
theorem hasFiniteCoproducts_bigFppfOver : HasFiniteCoproducts (BigFppfOver B S hS) := by
  show HasFiniteCoproducts (Over (B.obj hS))
  have := B.hasFiniteCoproducts_schemes
  infer_instance

/-- **Stacks 040T, algebraicity.** A coproduct of finitely many algebraic spaces over `S` is
an algebraic space over `S`. -/
@[stacks 040T "algebraicity"]
theorem isAlgebraicSpace_finiteCoproduct {I : Type v} [Finite I]
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) : IsAlgebraicSpace B S hS G.obj := by
  classical
  have := hasFiniteCoproducts_bigFppfOver B S hS
  choose U f hUf using fun i ↦ (hF i).exists_atlas
  exact isAlgebraicSpace_coproduct B S hS F hF G ι hG U f (fun i ↦ (hUf i).1)
    (fun i ↦ (hUf i).2) (∐ U) (fun i ↦ Sigma.ι U i) (coproductIsCoproduct U)

/-- **Stacks 040T, quasi-compactness.** A coproduct of finitely many quasi-compact algebraic
spaces over `S` is quasi-compact. -/
@[stacks 040T "quasi-compactness"]
theorem isQuasiCompactSpace_finiteCoproduct {I : Type v} [Finite I]
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (F i))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) : IsQuasiCompactSpace B S hS G.obj := by
  classical
  have hAlg : IsAlgebraicSpace B S hS G.obj :=
    isAlgebraicSpace_finiteCoproduct B S hS F hF G ι hG
  -- Re-index the finite family by a type of the working universe.
  have hfin : Fintype I := Fintype.ofFinite I
  let e : ULift.{u} (Fin (Fintype.card I)) ≃ I :=
    Equiv.ulift.trans (Fintype.equivFin I).symm
  let F' : ULift.{u} (Fin (Fintype.card I)) → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun j ↦ F (e j)
  have hF' : ∀ j, IsAlgebraicSpace B S hS (F' j) := fun j ↦ hF (e j)
  let ι' : ∀ j, (⟨F' j, (hF' j).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G := fun j ↦ ι (e j)
  have hG' : IsColimit (Cofan.mk G ι') := by
    show IsColimit (Cofan.mk G fun j ↦ ι (e j))
    exact (Cofan.isColimitEquivOfEquiv e (Cofan.mk G ι)).toFun hG
  -- The ranges of the legs are open subspaces which cover the point space.
  let W : ULift.{u} (Fin (Fintype.card I)) → Subfunctor G.obj :=
    fun j ↦ Subfunctor.range (ι' j).hom
  have hWopen (j) : IsOpenSubspace B S hS (W j) :=
    isOpenSubspace_range_cofan_inj ι' hG' j (hF' j)
  have hcover : IsZariskiCover B S hS (ULift.{u} (Fin (Fintype.card I))) W :=
    ⟨hWopen, Sheaf.isLocallySurjective_sigmaDesc_of_range_le _ ι' hG' (fun j ↦ (W j).ι)
      fun j ↦ by rw [Subfunctor.range_ι]⟩
  have hpoints := (isZariskiCover_iff_iUnion_points B S hS G.obj hAlg _ W hWopen).mp hcover
  -- Each range is the continuous image of the quasi-compact point space of a summand.
  have hrange (j) : Set.range (pointsMap B S hS (W j).toFunctor (W j).ι) =
      Set.range (pointsMap B S hS (F' j) (ι' j).hom) := by
    have hmono : Mono (ι' j).hom := Sheaf.mono_hom_cofan_inj ι' hG' j
    have hiso : IsIso (Subfunctor.toRange (ι' j).hom) := inferInstance
    rw [show (ι' j).hom = Subfunctor.toRange (ι' j).hom ≫ (W j).ι from
      (Subfunctor.toRange_ι (ι' j).hom).symm, pointsMap_comp, Set.range_comp,
      Set.range_eq_univ.mpr (pointsMap_surjective_of_isIso B S hS
        (Subfunctor.toRange (ι' j).hom)), Set.image_univ]
  have hcompact (j) : IsCompact (Set.range (pointsMap B S hS (F' j) (ι' j).hom)) := by
    have : CompactSpace (points B S hS (F' j)) :=
      (isQuasiCompactSpace_iff_compactSpace_points B S hS (F' j) (hF' j)).mp (hqc (e j))
    exact isCompact_range (continuous_pointsMap B S hS (ι' j).hom)
  have : CompactSpace (points B S hS G.obj) := by
    refine ⟨?_⟩
    rw [← hpoints]
    exact isCompact_iUnion fun j ↦ (hrange j).symm ▸ hcompact j
  exact (isQuasiCompactSpace_iff_compactSpace_points B S hS G.obj hAlg).mpr inferInstance

end Space

end AlgebraicGeometry

end
