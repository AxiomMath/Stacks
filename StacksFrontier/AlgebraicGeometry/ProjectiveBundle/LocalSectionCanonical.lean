module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSectionMap
public import StacksFrontier.AlgebraicGeometry.SymmetricDehomogenize.UnitScaling

/-!
# The local section of a projective bundle does not depend on the trivialization

`Stacks.RelativeProj.localSection` is built from an invertible quotient `q : F ⟶ L` and a
trivialization `e` of `L` over an affine open `V`. A trivialization is never canonical: it is an
isomorphism of `L|_V` with the structure sheaf, and `L|_V` has as many of those as `Γ(V, 𝒪)` has
units. **This file shows that the local section is the same for all of them**, so it is a
function of `(V, q)` alone — which is what a gluing argument needs, since two members of a cover
carry unrelated trivializations and their restrictions to the overlap must be compared there.

## The two steps

1. **The difference is a unit.** Two trivializations differ by an automorphism `α` of the
   structure sheaf of `V`, and `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.eq_unitMulBy`
   identifies `α` as multiplication by a global function, invertible by
   `unitOfUnitIso`. Transporting that across the restriction/pushforward adjunction —
   `CategoryTheory.Adjunction.homEquiv_naturality_right`, the adjunction being Mathlib's
   `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` — turns it into the statement that the
   two `κ`s of `Stacks.RelativeProj.trivializedQuotientHom` differ by
   `pushforwardUnitMulBy`. That is
   `Stacks.RelativeProj.exists_unit_trivializedQuotientHom`.
2. **A unit rescaling of `κ` does not move the classified morphism.** This is
   `Stacks.SymmetricDehomogenize.fromOfGlobalSections_dehomogenize_congr_mulBy`, which is
   residue item (R2) of [Stacks, Tag 01NE] fed with the degreewise rescaling of the
   dehomogenization.

## Main results

* `Stacks.RelativeProj.exists_unit_trivializedQuotientHom`: two trivializations of one quotient
  give `κ`s differing by multiplication by a global unit of `V`.
* `Stacks.RelativeProj.localChartMap_congr` and `Stacks.RelativeProj.localSection_congr`:
  **the morphism into the chart, and the local section of `π : 𝐏(F) ⟶ X` over `V`, do not depend
  on the trivialization.**

## Implementation notes

The surjectivity of `q` on sections over `V` appears twice in the statements, once for each
trivialization, rather than once: it is a `Prop` and plays no part in the comparison, and leaving
both occurrences free lets a caller that has two different proofs of it — which a gluing argument
restricting from two cover members does — apply the lemma without transporting one along the
other.

`fromOfGlobalSections_congr_fun` is the dependent-rewrite bookkeeping: the irrelevant-ideal
hypothesis of `AlgebraicGeometry.Proj.fromOfGlobalSections` mentions the ring map, so replacing
the ring map by an equal one has to carry the hypothesis along. It is `subst` followed by proof
irrelevance.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between the sections of `π` and
the invertible quotients of `F`; independence of a local construction from a choice is not a
covering part of it. What remains of the gluing for the bijection is the restriction
compatibility of the local section.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent] (V : X.Opens) (q : F ⟶ L)

omit [F.IsQuasicoherent] in
/-- **Two trivializations of one quotient give `κ`s differing by multiplication by a global unit
of `V`.** The two trivializations differ by an automorphism of the structure sheaf of `V`, which
is multiplication by a global unit; transposing across the restriction/pushforward adjunction
turns that into the statement below. -/
public theorem exists_unit_trivializedQuotientHom
    (e e' : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    ∃ w : Γ(V.toScheme, ⊤)ˣ, trivializedQuotientHom V q e' =
      trivializedQuotientHom V q e ≫
        pushforwardUnitMulBy V.ι ((w : Γ(V.toScheme, ⊤)ˣ) : Γ(V.toScheme, ⊤)) := by
  refine ⟨unitOfUnitIso ((restrictIsoUnitOfOverIsoUnit V L e).symm ≪≫
    restrictIsoUnitOfOverIsoUnit V L e'), ?_⟩
  have hinner : ((Scheme.Modules.restrictFunctor V.ι).map q ≫
        (restrictIsoUnitOfOverIsoUnit V L e).hom) ≫
      ((restrictIsoUnitOfOverIsoUnit V L e).symm ≪≫
        restrictIsoUnitOfOverIsoUnit V L e').hom =
      (Scheme.Modules.restrictFunctor V.ι).map q ≫
        (restrictIsoUnitOfOverIsoUnit V L e').hom :=
    (Category.assoc _ _ _).trans
      (congrArg ((Scheme.Modules.restrictFunctor V.ι).map q ≫ ·)
        (Iso.hom_inv_id_assoc (restrictIsoUnitOfOverIsoUnit V L e)
          (restrictIsoUnitOfOverIsoUnit V L e').hom))
  exact (congrArg ((Scheme.Modules.restrictAdjunction V.ι).homEquiv F
        (SheafOfModules.unit V.toScheme.ringCatSheaf)) hinner.symm).trans
    (((Scheme.Modules.restrictAdjunction V.ι).homEquiv_naturality_right _ _).trans
      (congrArg (trivializedQuotientHom V q e ≫ ·)
        (congrArg (Scheme.Modules.pushforward V.ι).map
          (eq_unitMulBy ((restrictIsoUnitOfOverIsoUnit V L e).symm ≪≫
            restrictIsoUnitOfOverIsoUnit V L e').hom))))

/-- Replacing the ring map by an equal one does not change the morphism to `Proj` it classifies.
The irrelevant-ideal hypothesis mentions the ring map, so it has to be carried along; once the
two maps are identified the two hypotheses are proofs of the same `Prop`. -/
private theorem fromOfGlobalSections_congr_fun
    {f f' : (schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).sectionRing V →+* Γ(V.toScheme, ⊤)}
    (hf : (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
      (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
      (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).toIdeal.map f' = ⊤)
    (h : f = f') :
    AlgebraicGeometry.Proj.fromOfGlobalSections _ f hf =
      AlgebraicGeometry.Proj.fromOfGlobalSections _ f' hf' := by
  subst h
  rfl

/-- **The morphism into the chart of `𝐏(F)` over `V` does not depend on the trivialization.** -/
public theorem localChartMap_congr
    (e e' : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (hq hq' : Function.Surjective (q.val.app (op V))) :
    localChartMap V q e hq = localChartMap V q e' hq' := by
  obtain ⟨w, hw⟩ := exists_unit_trivializedQuotientHom V q e e'
  have hdeh : localDehomogenize V q e' =
      Stacks.SymmetricDehomogenize.dehomogenize V.ι F
        (trivializedQuotientHom V q e ≫
          pushforwardUnitMulBy V.ι ((w : Γ(V.toScheme, ⊤)ˣ) : Γ(V.toScheme, ⊤)))
        V (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F) :=
    congrArg (fun κ => Stacks.SymmetricDehomogenize.dehomogenize V.ι F κ V
      (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F)) hw
  calc localChartMap V q e hq
      = AlgebraicGeometry.Proj.fromOfGlobalSections _
          (Stacks.SymmetricDehomogenize.dehomogenize V.ι F
            (trivializedQuotientHom V q e ≫
              pushforwardUnitMulBy V.ι ((w : Γ(V.toScheme, ⊤)ˣ) : Γ(V.toScheme, ⊤)))
            V (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F))
          (hdeh ▸ map_irrelevant_localDehomogenize_eq_top V q e' hq') :=
        Stacks.SymmetricDehomogenize.fromOfGlobalSections_dehomogenize_congr_mulBy V.ι F
          (trivializedQuotientHom V q e) V (preimageSelfTopRingHom V)
          (isQuasicoherentPieces_of_isQuasicoherent F) w
          (map_irrelevant_localDehomogenize_eq_top V q e hq) _
    _ = localChartMap V q e' hq' := fromOfGlobalSections_congr_fun V _ _ hdeh.symm

/-- **The local section of `π : 𝐏(F) ⟶ X` over `V` does not depend on the trivialization**, so it
is a function of `V` and of the quotient alone. This is what lets local sections built on two
members of a cover be compared on their overlap. -/
public theorem localSection_congr (hV : IsAffineOpen V)
    (e e' : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (hq hq' : Function.Surjective (q.val.app (op V))) :
    localSection V q e hV hq = localSection V q e' hV hq' :=
  congrArg (· ≫ (symGradedBundle F).chart V hV ≫ (bundlePresentationIso F).hom)
    (localChartMap_congr V q e e' hq hq')

end Stacks.RelativeProj

end
