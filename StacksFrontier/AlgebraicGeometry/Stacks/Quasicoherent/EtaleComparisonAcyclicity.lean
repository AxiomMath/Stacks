module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AcyclicityForAContinuousPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# The reduction of Stacks 075R (1) to the affine-object vanishing

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` and let
`ε : 𝒳_fppf ⟶ 𝒳_étale` be the comparison morphism of **Stacks 06TU** — the morphism of ringed
sites given by the identity functor on `𝒳`, whose direct image reads an fppf sheaf of
`𝒪_𝒳`-modules as an étale one.  **Stacks 075R** (1) says that for a module `ℱ` which is locally
quasi-coherent (**Stacks 06WJ**) and has the flat base change property (**Stacks 0762**),

`Rε_*ℱ = ε_*ℱ`,

that is, the higher direct images `R^iε_*ℱ` vanish for `i > 0`.

## The source's argument, and what of it is here

`ε` is a morphism of sites given by the identity functor, so by **Stacks 072W** the sheaf
`R^iε_*ℱ` is the *étale* sheafification of the presheaf `x ↦ H^i_{fppf}(x, ℱ)`.  The source then
says: to prove (1) it suffices to show `H^i_{fppf}(x, ℱ) = 0` for `i > 0` whenever `x` lies over
an affine scheme, and obtains that vanishing by combining **Stacks 075F** with Descent
**Stacks 0756** and Cohomology of Schemes **Stacks 01XB**.

This file proves the *suffices* step, at any hom universe of `𝒳`: the reduction of 075R (1) to
the affine vanishing, stated with the affine vanishing as the hypothesis `hvan` — exactly the
predicate `AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules` that
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc'` and
`AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedLqcFbc` use — and with the étale
covering class of the objects over affine schemes as the hypothesis `hB`.

The full statement of **Stacks 075R** is proved, with neither hypothesis, for an essentially small
category fibred in groupoids whose morphisms lie in the universe of the schemes:

* the first assertion and clause (1) in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfEtaleComparisonLqcFbc.lean`
  (`AlgebraicGeometry.Stack.isSheaf_fppf_of_lqc_flatLfp`,
  `AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`), where
  the affine vanishing is `AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules` and the étale
  covering is `AlgebraicGeometry.Stack.exists_affine_ofArrows_etale`;
* clause (2) in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LqcFbcModuleFppfEtaleCohomology.lean`
  (`AlgebraicGeometry.Stack.nonempty_fppfCohomologyIso_etaleCohomology_lqcFbcModule`);
* clause (3) in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LqcFbcModuleFppfEtaleHigherDirectImage.lean`
  (`AlgebraicGeometry.Stack.nonempty_higherDirectImageIso_sheafify_etale_lqcFbcModule`).

## Main definitions

* `AlgebraicGeometry.Stack.etaleComparisonRingMap`: the morphism of structure sheaves of rings
  underlying `ε`, which is the identity because all five associated topologies have the same
  structure presheaf.
* `AlgebraicGeometry.Stack.etaleComparisonPushforward`: the direct image `ε_*` on sheaves of
  `𝒪_𝒳`-modules.

## Main results

* `Stacks.Cohomology.ModuleLocalVanishing.isZero_sheafification_of_locallyZero`: a presheaf of
  modules each of whose sections dies on a covering sieve has zero sheafification.
* `AlgebraicGeometry.Stack.etaleComparisonPushforward_eq_comparisonPushforward`: `ε_*` is the
  comparison pushforward `Stacks.SheafOfModules.comparisonPushforward` the library already has.
* `AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_of_lqcFbc`: the
  reduction of **Stacks 075R (1)** to the affine-object vanishing, at any hom universe.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.Cohomology.ModuleLocalVanishing

universe t v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{t})]

/-- **A presheaf of modules whose sections die locally has zero sheafification.**  The
sheafification of presheaves of modules does not change the underlying sheaf of abelian groups
(`PresheafOfModules.sheafificationCompToSheaf`), so this is
`Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero` read through
the forgetful functor to abelian sheaves, which is faithful and additive and therefore reflects
zero objects. -/
theorem isZero_sheafification_of_locallyZero (P : PresheafOfModules.{t} R₀)
    (h : ∀ (U : C) (x : ToType (P.presheaf.obj (op U))),
      Presheaf.equalizerSieve (F := P.presheaf) (X := op U) x 0 ∈ J U) :
    IsZero ((PresheafOfModules.sheafification α).obj P) := by
  have hz : IsZero ((SheafOfModules.toSheaf R).obj ((PresheafOfModules.sheafification α).obj P)) :=
    (Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero
      J P.presheaf h).of_iso ((PresheafOfModules.sheafificationCompToSheaf α).app P)
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf R).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hz

end Stacks.Cohomology.ModuleLocalVanishing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The structure sheaf of rings on the *étale* site of a category fibred in groupoids: the sheaf
of **Stacks 06TV** at the étale topology.  It has the same underlying presheaf as
`AlgebraicGeometry.Stack.fppfSiteRingSheaf`, only a weaker sheaf condition. -/
abbrev etaleSiteRingSheaf :
    Sheaf (BigFppfOver.associatedTopology B S hS p .etale) RingCat.{u} :=
  FibredSite.ringStructureSheafCore B S hS p hp .etale

/-- The identity functor on `𝒳` is continuous from the étale associated topology to the fppf one:
every fppf sheaf is an étale sheaf.  This is the underlying functor of the comparison morphism
`ε : 𝒳_fppf ⟶ 𝒳_étale` of **Stacks 06TU**. -/
instance isContinuous_id_etale_fppf :
    (Functor.id 𝒳).IsContinuous (BigFppfOver.associatedTopology B S hS p .etale)
      (BigFppfOver.associatedTopology B S hS p .fppf) :=
  Stacks.SheafOfModules.isContinuous_id_of_le
    (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)

/-- **The morphism of structure sheaves of rings underlying the comparison morphism
`ε : 𝒳_fppf ⟶ 𝒳_étale`.**  All five associated topologies of a category fibred in groupoids have
the same underlying category and the same structure presheaf, so this morphism is the identity;
what it records is that `ε` is a morphism of *ringed* sites. -/
def etaleComparisonRingMap :
    etaleSiteRingSheaf B S hS p hp ⟶
      ((Functor.id 𝒳).sheafPushforwardContinuous RingCat.{u}
          (BigFppfOver.associatedTopology B S hS p .etale)
          (BigFppfOver.associatedTopology B S hS p .fppf)).obj (fppfSiteRingSheaf B S hS p hp) :=
  ⟨𝟙 _⟩

/-- **The direct image `ε_*` of the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` on sheaves of
`𝒪_𝒳`-modules.**  It reads a sheaf of modules on the fppf site of `𝒳` as a sheaf of modules on
the étale site, changing neither the underlying presheaf nor the scalars. -/
abbrev etaleComparisonPushforward :
    fppfSiteModules B S hS p hp ⥤ SheafOfModules.{u} (etaleSiteRingSheaf B S hS p hp) :=
  SheafOfModules.pushforward.{u} (etaleComparisonRingMap B S hS p hp)

/-- **`ε_*` is the comparison pushforward the library already has.**  Neither functor changes the
underlying presheaf of modules, so the two are equal on the nose. -/
theorem etaleComparisonPushforward_eq_comparisonPushforward :
    etaleComparisonPushforward B S hS p hp =
      Stacks.SheafOfModules.comparisonPushforward.{v, w, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
        (fppfSiteRingSheaf B S hS p hp) :=
  rfl

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (fppfSiteModules B S hS p hp)]

/-- **The reduction of Stacks 075R (1) to the affine-object vanishing.**  Let `𝒳` be a category
fibred in groupoids over the big fppf site of `S`, let `ε : 𝒳_fppf ⟶ 𝒳_étale` be the comparison
morphism, and let `ℱ` be a sheaf of `𝒪_𝒳`-modules on the fppf site which is locally
quasi-coherent (**Stacks 06WJ**) and has the flat base change property (**Stacks 0762**).  If
the higher fppf cohomology of such modules vanishes over the objects lying over an affine scheme
(`hvan`), and those objects cover every object étale-locally (`hB`), then

`R^iε_*ℱ = 0` for `i > 0`,

that is, `Rε_*ℱ = ε_*ℱ`.

This is the source's reduction: by **Stacks 072W** the sheaf `R^iε_*ℱ` is the étale
sheafification of the presheaf `x ↦ H^i_{fppf}(x, ℱ)`, and that presheaf vanishes on the objects
lying over an affine scheme, which cover étale-locally.

This form keeps the affine vanishing `hvan` and the étale covering class `hB` as hypotheses so
that it applies at any hom universe; see this file's module documentation.  On an essentially
small category fibred in groupoids whose morphisms lie in the universe of the schemes both are
proved (`AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules`,
`AlgebraicGeometry.Stack.exists_affine_ofArrows_etale`), and Stacks 075R (1) is
`AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`. -/
theorem isZero_rightDerived_etaleComparisonPushforward_of_lqcFbc
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u}]
    [(BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hB : (BigFppfOver.associatedTopology B S hS p .etale).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)))
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp)
    (ℱ : fppfSiteModules B S hS p hp)
    (hℱ : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp ℱ.val)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived i).obj ℱ) := by
  set Je := BigFppfOver.associatedTopology B S hS p .etale
  set R := fppfSiteRingSheaf B S hS p hp
  set Re := etaleSiteRingSheaf B S hS p hp
  set φ := etaleComparisonRingMap B S hS p hp
  set P := cohPresheafModule (Functor.id 𝒳) R Re φ i ℱ
  -- Stacks 072W: the higher direct image is the sheafification of the cohomology presheaf.
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf (Functor.id 𝒳) R Re φ i ℱ
  refine IsZero.of_iso ?_ e
  have hPzero (V : 𝒳) (hV : IsAffineOver B S hS (p.obj V)) : IsZero (P.obj (op V)) := by
    obtain ⟨eV⟩ := cohPresheafModule_evaluation_iso (Functor.id 𝒳) R Re φ i ℱ V
    refine IsZero.of_iso ?_ eV
    exact Functor.map_isZero _ (hvan ℱ hℱ V hV i hi)
  refine Stacks.Cohomology.ModuleLocalVanishing.isZero_sheafification_of_locallyZero _ P
    fun U x => ?_
  obtain ⟨I, y, ψ, hcov, hyaff⟩ := hB U
  refine Je.superset_covering (fun V g hg => ?_) hcov
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, b, rfl⟩ := hg
  have hsub : Subsingleton (ToType (P.obj (op (y j)))) :=
    ModuleCat.isZero_iff_subsingleton.1 (hPzero (y j) (hyaff j))
  change P.presheaf.map (b ≫ ψ j).op x = P.presheaf.map (b ≫ ψ j).op 0
  rw [op_comp, P.presheaf.map_comp]
  simp only [ConcreteCategory.comp_apply,
    hsub.elim (P.presheaf.map (ψ j).op x) (P.presheaf.map (ψ j).op 0)]

end

end AlgebraicGeometry.Stack

end
