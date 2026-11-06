module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AllChartLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit

/-!
# The image system on a later tail, with no bound on the index type

In Situation 0CP6, for a diagram as in Stacks 0CP8 for an algebraic space `X` quasi-separated
over `B`, the system `(X_i)_{i ≥ i₀}` of scheme-theoretic images restricted to the stages above
a later stage `i₀` has the properties the limit arguments of Stacks 0CPC, 0CPD and 0CPF use, with
no bound on the size of the index type: its limit is `X`, its members are quasi-separated, the
legs `X ⟶ X_i` of the canonical cone are quasi-compact with scheme-theoretic image all of `X_i`,
and its systems of affine charts have limit bridges. The same holds for the system of base
changes `Y_l ×_{Y_n} U` of such a system along a flat morphism `U ⟶ Y_n`.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.isLimit_tailCone_of_algebraicLimit`: **Stacks 0CP9 on a
  later tail**.
* `AlgebraicGeometry.Space.GoodDiagram.tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit`:
  the members of the restricted image system are quasi-separated.
* `AlgebraicGeometry.Space.GoodDiagram.isQuasiCompact_tailCone_π_of_algebraicLimit`: the legs of
  the canonical cone are quasi-compact.
* `AlgebraicGeometry.Space.GoodDiagram.tailSystem_hasChartLimitBridges` and
  `AlgebraicGeometry.Space.GoodDiagram.tailSystem_hasAllChartLimitBridges`: the restricted image
  system has limit bridges.
* `AlgebraicGeometry.Space.baseChangeSystem_hasChartLimitBridges`: the system of base changes of
  an inverse system with dominant quasi-compact projections along a flat morphism to a stage has
  limit bridges.

## Implementation notes

The forms carrying the bound `#I < B.cutoff.ord.cof` are those of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem`.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The system of base changes along a flat morphism -/

section BaseChangeSystem

variable {J : Type u} [Category.{u} J] (Ys : J ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (m : J)
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (u : U ⟶ Ys.obj m)

/-- **Density of the base-changed cone.** If the legs `Y ⟶ Y_l` of a cone are quasi-compact with
scheme-theoretic image all of `Y_l`, then so are, after base change along a flat morphism
`u : U ⟶ Y_m`, the legs `Y ×_{Y_m} U ⟶ Y_l ×_{Y_m} U`: each is the base change of `Y ⟶ Y_l`
along the flat projection `Y_l ×_{Y_m} U ⟶ Y_l` (Stacks 089E). -/
theorem schemeTheoreticImage_baseChangeCone_π_of_isFlat (c : Cone Ys)
    (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j)) (algY : IsAlgebraicSpace B S hS c.pt)
    (algU : IsAlgebraicSpace B S hS U) (flat : IsFlat B S hS u)
    (qc : ∀ j, IsQuasiCompact B S hS (c.π.app j))
    (dom : ∀ j, schemeTheoreticImageSubfunctor B S hS (c.π.app j) = ⊤) (l : Over m) :
    schemeTheoreticImageSubfunctor B S hS ((baseChangeCone Ys m u c).π.app l) = ⊤ := by
  have sq := isPullback_baseChangeCone_π Ys m u c l
  have algUl : IsAlgebraicSpace B S hS (pullback (Ys.map l.hom) u) :=
    isAlgebraicSpace_pullback B S hS _ _ (algYs _) algU (algYs m)
  have flatl : IsFlat B S hS (pullback.fst (Ys.map l.hom) u) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback (Ys.map l.hom) u)
      algU (algYs m) flat
  haveI : Epi sq.flip.isoPullback.hom := IsIso.epi_of_iso _
  rw [← sq.flip.isoPullback_hom_snd, schemeTheoreticImageSubfunctor_comp_of_epi,
    schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS _ _ algUl
      (algYs _) algY flatl (qc l.left), dom]
  rfl

/-- If the legs of a limit cone have full scheme-theoretic image, so do the limit projections. -/
private theorem schemeTheoreticImageSubfunctor_limit_π_eq_top {K : Type u} [Category.{u} K]
    {F : K ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (dom : ∀ j, schemeTheoreticImageSubfunctor B S hS (c.π.app j) = ⊤) (j : K) :
    schemeTheoreticImageSubfunctor B S hS (limit.π F j) = ⊤ := by
  have hπ : (hc.conePointUniqueUpToIso (limit.isLimit F)).inv ≫ c.π.app j = limit.π F j :=
    hc.conePointUniqueUpToIso_inv_comp (limit.isLimit F) j
  haveI hepi : Epi (hc.conePointUniqueUpToIso (limit.isLimit F)).inv := IsIso.epi_of_iso _
  rw [← hπ, schemeTheoreticImageSubfunctor_comp_of_epi, dom]

/-- **The system of base changes along a flat morphism has limit bridges.** Let `(Y_j)` be a
cofiltered inverse system of algebraic spaces with affine transition morphisms and a limit cone
whose vertex is an algebraic space and whose legs are quasi-compact with scheme-theoretic image
all of `Y_j`. Then the system of base changes `Y_l ×_{Y_m} U` along a flat morphism
`U ⟶ Y_m` has limit bridges, with no bound on the size of the index category. -/
theorem baseChangeSystem_hasChartLimitBridges [IsCofiltered J] {c : Cone Ys} (hc : IsLimit c)
    (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j))
    (affYs : ∀ {j k : J} (a : j ⟶ k), IsAffineHom B S hS (Ys.map a))
    (algY : IsAlgebraicSpace B S hS c.pt) (algU : IsAlgebraicSpace B S hS U)
    (flat : IsFlat B S hS u) (qc : ∀ j, IsQuasiCompact B S hS (c.π.app j))
    (dom : ∀ j, schemeTheoreticImageSubfunctor B S hS (c.π.app j) = ⊤) :
    HasChartLimitBridges (baseChangeSystem Ys m u) := by
  have hcU := isLimitBaseChangeCone Ys m u hc
  refine hasChartLimitBridges_of_dominant
    (fun l => isAlgebraicSpace_pullback B S hS _ _ (algYs _) algU (algYs m))
    (fun a => isAffineHom_of_isPullback (isPullback_baseChangeSystem_map Ys m u a).flip
      (affYs _))
    (isAlgebraicSpace_of_iso B S hS
      (hcU.conePointUniqueUpToIso (limit.isLimit (baseChangeSystem Ys m u)))
      (isAlgebraicSpace_pullback B S hS _ _ algY algU (algYs m)))
    (schemeTheoreticImageSubfunctor_limit_π_eq_top hcU
      (schemeTheoreticImage_baseChangeCone_π_of_isFlat Ys m u c algYs algY algU flat qc dom))

end BaseChangeSystem

/-! ### The image system on a later tail -/

namespace GoodDiagram

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
  (G : GoodDiagram B S hS hZ D pX) {i₀ : I} (le : G.index ≤ i₀)

/-- **Stacks 0CP9 on a later tail.** The restriction of the image system to the stages above a
later stage still has `X` as its limit, the restriction being along an initial functor; no
bound on the index type is needed. -/
noncomputable def isLimit_tailCone_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X) :
    IsLimit (tailCone G le) :=
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm (isLimit_imageCone_of_algebraicLimit G algX)

/-- The members of the restricted image system are quasi-separated, when `X` is quasi-separated
over `B`; no bound on the index type is needed. -/
lemma tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X)
    (qsX : IsQuasiSeparated B S hS pX) (j : Over (op i₀)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((tailSystem G le).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit G algX qsX _

/-- A leg `X ⟶ X_i` of the canonical cone on the restricted image system is quasi-compact:
followed by the closed immersion `X_i ⟶ B_i ×_{B_{i₁}} W` it is the stage map, which is
quasi-compact; no bound on the index type is needed. -/
lemma isQuasiCompact_tailCone_π_of_algebraicLimit (j : Over (op i₀)) :
    IsQuasiCompact B S hS ((tailCone G le).π.app j) :=
  isQuasiCompact_of_comp_mono B S hS _ (stageImage G _).ι
    (by rw [Cone.whisker_π, Functor.whiskerLeft_app, imageCone_π_app, toSchemeTheoreticImage_ι]
        exact isQuasiCompact_stageMap_of_algebraicLimit G _)

/-- The limit of the restricted image system is an algebraic space, being `X`. -/
lemma isAlgebraicSpace_limit_tailSystem_of_algebraicLimit (algX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (limit (tailSystem G le)) :=
  isAlgebraicSpace_of_iso B S hS
    ((isLimit_tailCone_of_algebraicLimit G le algX).conePointUniqueUpToIso (limit.isLimit _)) algX

/-- **The restricted image system has limit bridges**, with no bound on the index type: its
limit is `X`, an algebraic space, and the legs `X ⟶ X_i` are scheme-theoretically dominant. -/
theorem tailSystem_hasChartLimitBridges (algX : IsAlgebraicSpace B S hS X) :
    HasChartLimitBridges (tailSystem G le) := by
  exact hasChartLimitBridges_of_dominant (tailSystem_isAlgebraicSpace G le)
    (fun a => tailSystem_map_isAffineHom G le a)
    (isAlgebraicSpace_limit_tailSystem_of_algebraicLimit G le algX)
    (schemeTheoreticImageSubfunctor_limit_π_eq_top
      (isLimit_tailCone_of_algebraicLimit G le algX) (schemeTheoreticImage_tailCone_π G le))

/-- **The restricted image system has limit bridges along all affine points**, with no bound on
the index type, when `X` is quasi-separated over `B`. -/
theorem tailSystem_hasAllChartLimitBridges (algX : IsAlgebraicSpace B S hS X)
    (qsX : IsQuasiSeparated B S hS pX) :
    HasAllChartLimitBridges (tailSystem G le) :=
  hasAllChartLimitBridges_of_hasChartLimitBridges (hZ := hZ) (tailSystem_isAlgebraicSpace G le)
    (fun a => tailSystem_map_isAffineHom G le a)
    (isAlgebraicSpace_limit_tailSystem_of_algebraicLimit G le algX)
    (tailSystem_isQuasiCompactSpace G le)
    (tailSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit G le algX qsX)
    (tailSystem_hasChartLimitBridges G le algX)

end GoodDiagram

end AlgebraicGeometry.Space

end
